(*
  Defines the Translation Look-aside Buffer, which translates virtual
  addresses into physical addresses and caches the results.
*)
Require Import Kami.AllNotations.
Require Import StdLibKami.Cam.Ifc.
Require Import StdLibKami.Cam.SimpleCam.
Require Import StdLibKami.ReplacementPolicy.Ifc.
Require Import StdLibKami.ReplacementPolicy.PseudoLru.
Require Import ProcKami.FU.
Require Import ProcKami.Devices.MemDevice.
Require Import ProcKami.RiscvPipeline.MemUnit.PhysicalMem.
Require Import Vector.
Require Import ProcKami.RiscvPipeline.MemUnit.Pmp.
Require Import ProcKami.RiscvPipeline.MemUnit.PageTable.
Import VectorNotations.
Require Import List.
Import ListNotations.

Section tlb.
  Context `{procParams: ProcParams}.

  Variable mem_devices : list MemDevice.
  Variable mem_table : list (MemTableEntry mem_devices).
  Definition DeviceTag := (DeviceTag mem_devices).

  Local Open Scope kami_expr.
  Local Open Scope kami_action.

  Variable Tag: Kind.

  Variable memSendReq : forall ty, DeviceTag @# ty -> PAddr @# ty -> ActionT ty Bool.
  
  Variable TlbEntriesNum: nat.

  Definition PtLevel := Bit (Nat.log2_up maxPageLevels).

  Definition VpnWidth := (Xlen - LgPageSize)%nat.

  Definition TlbEntry
    := STRUCT_TYPE {
           "pte" :: PteEntry;
           "level" :: PtLevel (* TODO: removable *)
       }.

  Section ty.
    Variable ty: Kind -> Type.

    Definition CamTag
      := STRUCT_TYPE {
           "level" :: PtLevel;
           "vpn" :: Bit VpnWidth
         }.

    (* Definition CamCtxt := Pair (Bit SatpModeWidth) PtLevel. *)
    Definition CamCtxt := Bit SatpModeWidth.

    (*
      Returns true iff the given virtual address's vpn matches the
      vpn associated with the given entry.
    *)
    Definition tlbVpnMatch
      (ctxt : CamCtxt @# ty)
      (entry : CamTag @# ty)
      (vaddr : CamTag @# ty)
      :  Bool @# ty
      := let vpn_field_size
           :  Bit (Nat.log2_up 26) @# ty (* TODO *)
           := satp_select ctxt (fun mode => $(vm_mode_vpn_size mode)) in
         let num_vpn_fields
           :  PtLevel @# ty
           := satp_select ctxt (fun mode => $(length (vm_mode_sizes mode))) in
         let num_spanned_vpn_fields
           :  PtLevel @# ty
           := $((maxPageLevels - 1)%nat) - (entry @% "level") in
         let vpn_fields_size
           :  Bit (Nat.log2_up VpnWidth) @# ty
           := (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) num_vpn_fields) *
              (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) vpn_field_size) in
         let vpn_spanned_fields_size
           :  Bit (Nat.log2_up VpnWidth) @# ty
           := (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) num_spanned_vpn_fields) *
              (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) vpn_field_size) in
         let offset
           :  Bit (Nat.log2_up VpnWidth) @# ty
           := (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) (num_vpn_fields - num_spanned_vpn_fields)) *
              (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) vpn_field_size) in
         slice offset vpn_spanned_fields_size (vaddr @% "vpn") ==
         slice offset vpn_spanned_fields_size (entry @% "vpn").

  End ty.

  Instance camParams : Cam.Ifc.CamParams
    := {|
         Cam.Ifc.Data := TlbEntry;
         MatchRead :=
         (fun ty (tag : CamTag @# ty)
           (ctxt : CamCtxt @# ty)
           (entryTag : CamTag @# ty)
           => tlbVpnMatch ctxt entryTag tag);
         MatchClear :=
         (fun ty (tag : CamTag @# ty)
           (ctxt : CamCtxt @# ty)
           (entryTag : CamTag @# ty)
           => tlbVpnMatch ctxt entryTag tag)
       |}.

  Definition pseudoLruParams : PseudoLruParams := {|
    num := TlbEntriesNum; (* TODO: redundant w.r.t. simpleCamParams *)
    stateRegName := @^"tlbCacheLru";
  |}.

  Definition simpleCamParams : SimpleCamParams := {|
    regName := @^"tlbCache";
    size := TlbEntriesNum;
    policy := @PseudoLru pseudoLruParams;
    CamParamsInst := camParams
  |}.

  Definition cam : Cam camParams := SimpleCam simpleCamParams. 

  Definition TlbReqId := Bit 1.
  Definition TlbReqIdFetch := 0.
  Definition TlbReqIdMem := 1.

  Definition TlbReq
    := STRUCT_TYPE {
         "req_id" :: TlbReqId;
         "vaddr"  :: VAddr
       }.

  Definition TlbContext
    := STRUCT_TYPE {
         "satp_mode" :: Bit SatpModeWidth;
         "mode" :: PrivMode
       }.

  Definition TlbState
    := STRUCT_TYPE {
         "ready"  :: Bool; (* waiting for caller to retrieve result *)
         "active" :: Bool; (* performing page walks *)
         "level"  :: PtLevel
       }.

  Record tlbReg
    := {
         tlbRegName : string;
         tlbRegKind : Kind;
         tlbRegInit : option (ConstT tlbRegKind)
       }.

  Definition tlbMemReqActiveName := @^"tlbMemReqActive".

  Local Definition tlbRegSpecs
    := [
         {|
           tlbRegName := tlbMemReqActiveName;
           tlbRegKind := Bool;
           tlbRegInit := Some (ConstBool false)
         |};
         {|
           tlbRegName := @^"tlbMemReq";
           tlbRegKind := Pair DeviceTag PAddr;
           tlbRegInit := Some (getDefaultConst (Pair DeviceTag PAddr))
         |};
         {|
           tlbRegName := @^"tlbContext";
           tlbRegKind := TlbContext;
           tlbRegInit := None
         |};
         {|
           tlbRegName := @^"tlbReqException";
           tlbRegKind := Maybe Exception;
           tlbRegInit := None
         |};
         {|
           tlbRegName := @^"tlbReq";
           tlbRegKind := TlbReq;
           tlbRegInit := Some (getDefaultConst TlbReq)
         |};
         {|
           tlbRegName := @^"tlbState";
           tlbRegKind := TlbState;
           tlbRegInit := Some (getDefaultConst TlbState)
         |};
         {|
           tlbRegName := @^"tlbCacheLru";
           tlbRegKind := Array (TlbEntriesNum - 1) Bool;
           tlbRegInit := Some (getDefaultConst (Array (TlbEntriesNum - 1) Bool))
         |};
         {|
           tlbRegName := @^"tlbCache";
           tlbRegKind := Array TlbEntriesNum (Maybe (Pair CamTag TlbEntry));
           tlbRegInit := Some (getDefaultConst (Array TlbEntriesNum (Maybe (Pair CamTag TlbEntry))))
         |}
       ].

  Definition tlbRegs
    := map
         (fun tlbReg
           => (tlbRegName tlbReg,
               existT RegInitValT
                 (SyntaxKind (tlbRegKind tlbReg))
                 (match tlbRegInit tlbReg with
                  | None => None
                  | Some init
                    => Some (SyntaxConst init)
                  end)))
         tlbRegSpecs.

  Section ty.
    Variable ty : Kind -> Type.

    Definition memSendReqAsync
      (req : Pair DeviceTag PAddr @# ty)
      :  ActionT ty Void
      := System [
           DispString _ "[memSendReqAsync]\n"
         ];
         Write @^"tlbMemReq" : Pair DeviceTag PAddr <- req;
         Write tlbMemReqActiveName : Bool <- $$true;
         Retv.

    (* wrap in a rule. *)
    Definition memSendReqAsyncCont
      :  ActionT ty Void
      := Read active : Bool <- tlbMemReqActiveName;
         If #active
           then
             Read req : Pair DeviceTag PAddr <- @^"tlbMemReq";
             System [
               DispString _ "[memSendReqAsyncCont]\n";
               DispString _ "[memSendReqAsyncCont] req: ";
               DispHex #req;
               DispString _ "\n"
             ];
             LETA sent : Bool <- memSendReq (#req @% "fst") (#req @% "snd");
             System [
               DispString _ "[memSendReqAsyncCont] sent: ";
               DispHex #sent;
               DispString _ "\n"
             ];
             If #sent
               then
                 Write tlbMemReqActiveName : Bool <- $$false;
                 System [
                   DispString _ "[memSendReqAsyncCont] deactivated tlb req\n"
                 ];
                 Retv;
             Retv;
         Retv.

    Definition tlbEntryVAddrPAddr
      (satp_mode : Bit SatpModeWidth @# ty)
      (entry : TlbEntry @# ty)
      (vaddr : VAddr @# ty)
      :  PAddr ## ty
      := LETE offset : PAddr
           <- getVAddrRest satp_mode
                (* (ZeroExtendTruncLsb 5 (entry @% "level")) *)
                (ZeroExtendTruncLsb 5 ($(maxPageLevels - 1) - (entry @% "level")))
                vaddr;
         LETC result : PAddr
           <- (ppnToPAddr (entry @% "pte" @% "pointer")) + #offset;
         SystemE [
           DispString _ "[tlbEntryVAddrPAddr] entry: ";
           DispHex entry;
           DispString _ "\n";
           DispString _ "[tlbEntryVAddrPAddr] vaddr: ";
           DispHex vaddr;
           DispString _ "\n";
           DispString _ "[tlbEntryVAddrPAddr] offset: ";
           DispHex #offset;
           DispString _ "\n";
           DispString _ "[tlbEntryVAddrPAddr] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         RetE #result.

    Definition tlbRet
      (vpn : Bit VpnWidth @# ty)
      (result : PktWithException TlbEntry @# ty)
      :  ActionT ty Void
      := System [
           DispString _ "[tlbRet] vpn: ";
           DispHex vpn;
           DispString _ "\n";
           DispString _ "[tlbRet] result: ";
           DispHex result;
           DispString _ "\n"
         ];
         Write @^"tlbReqException" : Maybe Exception <- result @% "snd";
         If !(result @% "snd" @% "valid")
           then
             LET tag 
               :  CamTag
               <- STRUCT {
                    "level" ::= result @% "fst" @% "level";
                    "vpn" ::= vpn
                  } : CamTag @# ty;
             System [
               DispString _ "[tlbRet] cached result.\n"
             ];
             Cam.Ifc.write cam #tag (result @% "fst");
         Write @^"tlbState" : TlbState
           <- $$(getDefaultConst TlbState)
                @%["ready" <- $$true]
                @%["active" <- $$true];
        Retv.

    Definition tlbRetException
      (exception : Exception @# ty)
      :  ActionT ty Void
      := System [
           DispString _ "[tlbRetException]\n"
         ];
         LET result
           :  PktWithException TlbEntry
           <- STRUCT {
                "fst" ::= $$(getDefaultConst TlbEntry);
                "snd" ::= Valid exception
              } : PktWithException TlbEntry @# ty;
         tlbRet $0 #result.

    (*
      Returns the exception generated by the last translation
      request.

      Note: callers using the TLB to translate a vaddr must call
      this action to finish their transaction.
    *)
    Definition tlbGetException
      (req : TlbReq @# ty)
      :  ActionT ty (Maybe Exception)
      := System [
           DispString _ "[tlbGetException]\n"
         ];
         Read state : TlbState <- @^"tlbState";
         If #state @% "ready"
           then 
             Read orig_req  : TlbReq          <- @^"tlbReq";
             Read exception : Maybe Exception <- @^"tlbReqException";
             If #orig_req @% "req_id" == req @% "req_id"
               then
                 Write @^"tlbState" : TlbState
                   <- #state
                        @%["ready"  <- $$false]
                        @%["active" <- $$false];
                 Retv;
             Ret
               (IF #orig_req @% "vaddr" == req @% "vaddr"
                 then #exception
                 else Invalid)
           else Ret Invalid
           as result;
         System [
           DispString _ "[tlbGetException] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         Ret #result.

    Definition tlb
      (access_type : VmAccessType @# ty)
      (satp_mode: Bit SatpModeWidth @# ty)
      (mode: PrivMode @# ty)
      (satp_ppn: Bit 44 @# ty)
      (req : TlbReq @# ty)
      :  ActionT ty (Maybe TlbEntry)
      := System [
           DispString _ "[tlb] satp_mode: ";
           DispHex satp_mode;
           DispString _ "\n";
           DispString _ "[tlb] mode: ";
           DispHex mode;
           DispString _ "\n";
           DispString _ "[tlb] satp_ppn: ";
           DispHex satp_ppn;
           DispString _ "\n";
           DispString _ "[tlb] req: ";
           DispHex req;
           DispString _ "\n"
         ];
         LET tag : CamTag
           <- STRUCT {
                "level" ::= $0; (* TODO: a bit wasteful. *)
                "vpn" ::= ZeroExtendTruncMsb VpnWidth (ZeroExtendTruncLsb (VpnWidth + 12) (req @% "vaddr"))
              } : CamTag @# ty;
         LETA mentry : Maybe TlbEntry
           <- Cam.Ifc.read cam #tag satp_mode;
         Read state : TlbState <- @^"tlbState";
         System [
           DispString _ "[tlb] mentry: ";
           DispHex #mentry;
           DispString _ "\n";
           DispString _ "[tlb] state: ";
           DispHex #state;
           DispString _ "\n"
         ];
         If !((#mentry @% "valid") || (#state @% "active"))
           then 
             Write @^"tlbReq" : TlbReq <- req;
             LETA vpnOffset
               :  Bit VpnWidth
               <- convertLetExprSyntax_ActionT
                    (getVpnOffset satp_mode $0 (* TODO level not incrementing *)
                      (ZeroExtendTruncMsb VpnWidth (req @% "vaddr")));
             LET pte_addr
               :  PAddr
               <- (ppnToPAddr satp_ppn) +
                  (SignExtendTruncLsb PAddrSz #vpnOffset);
             LETA pmp_result
               :  Pair (Pair DeviceTag PAddr) MemErrorPkt
               <- checkForFault mem_table access_type satp_mode mode #pte_addr $2 $$false;
             System [
               DispString _ "[tlb] vpnOffset: ";
               DispHex #vpnOffset;
               DispString _ "\n";
               DispString _ "[tlb] pte_addr: ";
               DispHex #pte_addr;
               DispString _ "\n";
               DispString _ "[tlb] pmp_result: ";
               DispHex #pmp_result;
               DispString _ "\n"
             ];
             If mem_error (#pmp_result @% "snd")
               then
                 tlbRetException
                   (IF #pmp_result @% "snd" @% "misaligned"
                      then misalignedException access_type
                      else accessException access_type)
               else
                 LET context
                   :  TlbContext
                   <- STRUCT {
                        "satp_mode" ::= satp_mode;
                        "mode" ::= mode
                      } : TlbContext @# ty;
                 LET state
                   :  TlbState
                   <- STRUCT {
                        "ready"  ::= $$false;
                        "active" ::= $$true;
                        "level"  ::= $(maxPageLevels - 2)
                      } : TlbState @# ty;
                 System [
                   DispString _ "[tlb] context: ";
                   DispHex #context;
                   DispString _ "\n";
                   DispString _ "[tlb] state: ";
                   DispHex #state;
                   DispString _ "\n"
                 ];
                 Write @^"tlbState" : TlbState <- #state;
                 Write @^"tlbContext" : TlbContext <- #context;
                 memSendReqAsync (#pmp_result @% "fst")
               as _;
             Retv;
         Ret #mentry.

    (* method called by mem when response is ready. *)
    Definition tlbHandleMemRes
      (access_type : VmAccessType @# ty)
      (pte : PteEntry @# ty)
      :  ActionT ty Void
      := System [
           DispString _ "[tlbHandleMemRes]\n"
         ];
         Read state : TlbState <- @^"tlbState";
         Read req : TlbReq <- @^"tlbReq";
         Read context : TlbContext <- @^"tlbContext";
         LET index
           :  Bit 5
           <- ZeroExtendTruncLsb 5 ($(maxPageLevels - 1) - (#state @% "level"));
         System [
           DispString _ "[tlbHandleMemRes] index: ";
           DispHex #index;
           DispString _ "\n"
         ];
         LETA trans_result
           :  Pair Bool (PktWithException PAddr)
           <- convertLetExprSyntax_ActionT
                (translatePte
                  (#context @% "satp_mode")
                  access_type
                  #index
                  (#req @% "vaddr")
                  pte);
         System [
           DispString _ "[tlbHandleMemRes] pte: ";
           DispHex pte;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] state: ";
           DispHex #state;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] req: ";
           DispHex #req;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] context: ";
           DispHex #context;
           DispString _ "\n";
           DispString _ "[tlbHandleMemRes] trans_result: ";
           DispHex #trans_result;
           DispString _ "\n"
         ];
         If #trans_result @% "fst" || (* done *)
            #trans_result @% "snd" @% "snd" @% "valid" (* exception *)
           then
             LET vpn_field_size
               :  Bit (Nat.log2_up 26) (* TODO *)
               <- satp_select (#context @% "satp_mode") (fun mode => $(vm_mode_vpn_size mode));
             LET num_vpn_fields
               :  PtLevel
               <- satp_select (#context @% "satp_mode") (fun mode => $(length (vm_mode_sizes mode)));
             LET num_spanned_vpn_fields
               :  PtLevel
               <- $((maxPageLevels - 1)%nat) - (#state @% "level");
             LET vpn_fields_size
               :  Bit (Nat.log2_up VpnWidth)
               <- (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) #num_vpn_fields) *
                  (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) #vpn_field_size);
             LET vpn_spanned_fields_size
               :  Bit (Nat.log2_up VpnWidth)
               <- (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) #num_spanned_vpn_fields) *
                  (ZeroExtendTruncLsb (Nat.log2_up VpnWidth) #vpn_field_size);
             LET vpn_value
               <- slice 
                    ($12 : Bit (Nat.log2_up 12) @# ty) (* page size *)
                    #vpn_spanned_fields_size
                    (#req @% "vaddr");
             LET entry
               :  TlbEntry
               <- STRUCT {
                    "pte" ::= pte;
                    "level" ::= #state @% "level"
                  } : TlbEntry @# ty;
             LET result
               :  PktWithException TlbEntry
               <- STRUCT {
                    "fst" ::= #entry;
                    "snd" ::= #trans_result @% "snd" @% "snd"
                  } : PktWithException TlbEntry @# ty;
             System [
               DispString _ "[tlbHandleMemRes] max page levels: ";
               DispHex ($maxPageLevels : Bit 64 @# ty);
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] vpn_field_size: ";
               DispHex #vpn_field_size;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] num_vpn_fields: ";
               DispHex #num_vpn_fields;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] num_spanned_vpn_fields: ";
               DispHex #num_spanned_vpn_fields;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] vpn_fields_size: ";
               DispHex #vpn_fields_size;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] vpn_spanned_fields_size: ";
               DispHex #vpn_spanned_fields_size;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] vpn_value: ";
               DispHex #vpn_value;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] result: ";
               DispHex #result;
               DispString _ "\n";
               DispString _ "[tlbHandleMemRes] done.\n"
             ];
             tlbRet
               (* (msb #width (ZeroExtendTruncMsb VpnWidth (#req @% "vaddr"))) *) (* TODO: consider storing vpn rather than full vaddr, but note that doing so complicates matching later. *)
               (ZeroExtendTruncMsb VpnWidth (ZeroExtendTruncLsb (VpnWidth + 12) (#req @% "vaddr")))
               #result
           else (* loop *)
             LETA pmp_result
               :  Pair (Pair DeviceTag PAddr) MemErrorPkt
               <- checkForFault mem_table
                    access_type
                    (#context @% "satp_mode")
                    (#context @% "mode")
                    (#trans_result @% "snd" @% "fst")
                    $2 $$false;
             If mem_error (#pmp_result @% "snd")
               then
                 tlbRetException
                   (IF #pmp_result @% "snd" @% "misaligned"
                      then misalignedException access_type
                      else accessException access_type)
               else
                 (* submit memory request for next pte and loop. *)
                 (* TODO: poll for response. *)
                 LET next_state
                   :  TlbState
                   <- #state
                        @%["active" <- $$true]
                        @%["level" <- #state @% "level" - $1];
                 System [
                   DispString _ "[tlbHandleMemRes] next_state: ";
                   DispHex #next_state;
                   DispString _ "\n";
                   DispString _ "[tlbHandleMemRes] pmp_result: ";
                   DispHex #pmp_result;
                   DispString _ "\n"
                 ];
                 Write @^"tlbState" : TlbState <- #next_state;
                 memSendReqAsync (#pmp_result @% "fst")
               as _;
             Retv
           as _;
         Retv.

    Definition tlbHandleReq
      (satp_mode : Bit SatpModeWidth @# ty)
      (mxr: Bool @# ty)
      (sum: Bool @# ty)
      (mode: PrivMode @# ty)
      (satp_ppn: Bit 44 @# ty)
      (req_id : TlbReqId @# ty)
      (access_type: VmAccessType @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty (Maybe (PktWithException PAddr))
      := System [
           DispString _ "[tlbHandleReq]\n"
         ];
         LET req
           :  TlbReq
           <- STRUCT {
                "req_id" ::= req_id;
                "vaddr"  ::= vaddr
              } : TlbReq @# ty;
         LETA mentry
           :  Maybe TlbEntry <- tlb access_type satp_mode mode satp_ppn #req;
         LETA mexception
           :  Maybe Exception <- tlbGetException #req;
         If #mentry @% "valid"
           then 
             convertLetExprSyntax_ActionT
               (tlbEntryVAddrPAddr satp_mode (#mentry @% "data") vaddr)
           else Ret $0
           as paddr;
         LET pkt
           :  PktWithException PAddr
           <- STRUCT {
                "fst" ::= #paddr;
                "snd"
                  ::= IF #mexception @% "valid"
                        then #mexception
                        else
                          (IF pte_grant mxr sum mode access_type
                               (#mentry @% "data" @% "pte")
                            then Invalid
                            else Valid (faultException access_type))
              } : PktWithException PAddr @# ty;
         LET result
           :  Maybe (PktWithException PAddr)
           <- STRUCT {
                "valid" ::= (#mexception @% "valid" || #mentry @% "valid");
                "data"  ::= #pkt
              } : Maybe (PktWithException PAddr) @# ty;
         System [
           DispString _ "[tlbHandleReq] mentry: ";
           DispHex #mentry;
           DispString _ "\n";
           DispString _ "[tlbHandleReq] mexception: ";
           DispHex #mexception;
           DispString _ "\n";
           DispString _ "[tlbHandleReq] result: ";
           DispHex #result;
           DispString _ "\n"
         ];
         Ret #result.

    (*
      The method called by the fetch unit to translate virtual
      addresses.
    *)
    Definition tlbFetchPAddr
      (satp_mode : Bit SatpModeWidth @# ty)
      (mxr: Bool @# ty)
      (sum: Bool @# ty)
      (mode: PrivMode @# ty)
      (satp_ppn: Bit 44 @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty (Maybe (PktWithException PAddr))
      := System [
           DispString _ "[tlbFetchPAddr] satp_mode: ";
           DispHex satp_mode;
           DispString _ "\n";
           DispString _ "[tlbFetchPAddr] mxr: ";
           DispHex mxr;
           DispString _ "\n";
           DispString _ "[tlbFetchPAddr] sum: ";
           DispHex sum;
           DispString _ "\n";
           DispString _ "[tlbFetchPAddr] mode: ";
           DispHex mode;
           DispString _ "\n";
           DispString _ "[tlbFetchPAddr] satp_ppn: ";
           DispHex satp_ppn;
           DispString _ "\n";
           DispString _ "[tlbFetchPAddr] vaddr: ";
           DispHex vaddr;
           DispString _ "\n"
         ];
         tlbHandleReq satp_mode mxr sum mode satp_ppn $TlbReqIdFetch $VmAccessInst vaddr.

    (*
      The method called by the memory unit to translate virtual
      addresses.
    *)
    Definition tlbMemPAddr
      (satp_mode : Bit SatpModeWidth @# ty)
      (mxr: Bool @# ty)
      (sum: Bool @# ty)
      (mode: PrivMode @# ty)
      (satp_ppn: Bit 44 @# ty)
      (access_type: VmAccessType @# ty)
      (vaddr : VAddr @# ty)
      :  ActionT ty (Maybe (PktWithException PAddr))
      := tlbHandleReq satp_mode mxr sum mode satp_ppn $TlbReqIdMem access_type vaddr.

  End ty.

  Local Close Scope kami_action.
  Local Close Scope kami_expr.
End tlb.
