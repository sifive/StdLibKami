Require Import Kami.All RegStruct.
Require Import Utila.
Require Import List.
Import ListNotations.

Section Granule.
  Variable lgGranuleSize : nat.
  Notation n := (pow2 lgGranuleSize).
  
  Notation divCeil x y := (Nat.div (x + (y - 1)) y).
  Notation div_packn k := (divCeil (size k) n).
  Notation lg_packn k := (Nat.log2_up (divCeil (size k) n)).
  Notation pow2_packn k := (pow2 (lg_packn k)).

  Notation getStartGranule addr := (wordToNat (split1 _ _ addr)).
  Notation getFinishGranule addr k := (getStartGranule addr + div_packn k).
  Notation getFinishPacket addr k maskSz :=
    (divCeil (getFinishGranule addr k) maskSz).
  Notation getFinishPacketGranule addr k maskSz :=
    (getFinishPacket addr k maskSz * maskSz).


  Definition putRightPosition ty k (val: k @# ty) start finish :=
    {< $$ (natToWord (finish - (start + size k)) 0), pack val, $$ (natToWord start 0)>}%kami_expr.

  Lemma divCeil_ge x y: y <> 0 -> divCeil x y * y >= x.
  Proof.
    intros.
    pose proof (Nat.div_mod (x + (y-1)) y ltac:(Omega.omega)) as sth.
    rewrite Nat.mul_comm in sth.
    pose proof (Nat.mod_le (x + (y-1)) _ H) as sth2. 
    assert (sth3: divCeil x y * y = x + (y-1) - ((x + (y-1))mod y)) by Omega.omega.
    Opaque Nat.div.
    simpl.
    rewrite sth3.
    Transparent Nat.div.
    pose proof (Nat.mod_bound_pos (x + (y-1)) y ltac:(Omega.omega) ltac:(Omega.omega)).
    Omega.omega.
  Qed.

  Definition byteAlign ty k (e: k @# ty): (Bit (div_packn k * n) @# ty).
    refine (castBits _ (ZeroExtend (div_packn k * n - size k) (pack e))).
    abstract (pose proof (@divCeil_ge (size k) n (pow2_ne_zero _)); Omega.omega).
  Defined.

  Section RegMapper.
    Variable ty: Kind -> Type.
    Variable lgMaskSz realAddrSz: nat.
    
    Local Notation maskSz := (pow2 lgMaskSz).
    Local Notation addrSz := (lgMaskSz + realAddrSz).
    Local Notation dataSz := (maskSz * n).

    (* For tile-link, addr, mask and size should all be compatible,
       which is why maskSz, dataSz are powers of 2 *)

    (* Each entry represents a single data entry of size dataSz,
       indexed by an addr of size realAddrSz.
       The mask represents the granuleEnable for granules of size n that make up the data *)
    Definition RegMapT :=
      STRUCT_TYPE
        { "addr" :: Bit realAddrSz ;
          "mask" :: Bit maskSz ;
          "data" :: Bit dataSz }.

    Definition FullRegMapT :=
      STRUCT_TYPE
        { "isRd" :: Bool ;
          "info" :: RegMapT }.

    Record GenRegField :=
      { grf_addr  : word realAddrSz ;
        grf_mask  : Bit maskSz @# ty;
        grf_read  : RegMapT @# ty -> ActionT ty (Bit dataSz) ;
        grf_write : RegMapT @# ty -> ActionT ty Void }.

    Local Open Scope kami_action.
    Local Open Scope kami_expr.

    (* Given an addr of size realAddrSz and a mask, if the addr matches any entry's address
       and if any granule in the data is enabled by the mask, then do the corresponding
       read or write, sending the whole mask, data and the address itself (address is
       redundant for the final reader/writer) *)
    Definition createRegMap (rq: Maybe FullRegMapT @# ty) (ls: list GenRegField): ActionT ty (Bit dataSz) :=
      If rq @% "valid"
    then (If rq @% "data" @% "isRd"
          then GatherActions (map (fun x =>
                                     If (rq @% "data" @% "info" @% "addr") ==
                                     ($$ (grf_addr x))
                                       && ((rq @% "data" @% "info" @% "mask" & (grf_mask x)) != $ 0)
                                   then (LETA retVal <- grf_read x (rq @% "data" @% "info");
                                           Ret #retVal)
                                   else Ret ($$ (natToWord dataSz 0))
                                    as retVal;
                                     Ret #retVal) ls) as listVals;
                 Ret (CABit Bor listVals)
          else GatherActions (map (fun x =>
                                     If (rq @% "data" @% "info" @% "addr") ==
                                     ($$ (grf_addr x))
                                       && ((rq @% "data" @% "info" @% "mask" & (grf_mask x)) != $ 0)
                                   then grf_write x (rq @% "data" @% "info")
                                   else Retv; Retv) ls) as _;
            Ret ($$ (natToWord dataSz 0))
            as retVal;
            Ret #retVal)
    else Ret $0
    as retVal;
      Ret #retVal.
    Local Close Scope kami_expr.
    Local Close Scope kami_action.

    Definition makeSplitBits (addr: word addrSz) (k: Kind) (e: k @# ty): Array (getFinishPacket addr k maskSz) (Bit dataSz) @# ty.
      refine
        (unpack (Array (getFinishPacket addr k maskSz) (Bit dataSz))
                (castBits _ (putRightPosition (byteAlign e) (getStartGranule addr * n) (getFinishPacketGranule addr k maskSz * n)))).
      Opaque Nat.div.
      abstract (
          simpl;
          assert (divCeil (getStartGranule addr + (size k + (n - 1)) / n) maskSz * maskSz * n >= getStartGranule addr * n + (size k + (n-1)) / n * n) by
            (pose proof (divCeil_ge (getStartGranule addr + div_packn k) (pow2_ne_zero lgMaskSz)); simpl in *;
             nia);
          rewrite Nat.mul_assoc;
          lia).
      Transparent Nat.div.
    Defined.

    Definition makeSplitMask (addr: word addrSz) (k: Kind): Array (getFinishPacket addr k maskSz) (Bit maskSz) @# ty.
      refine
        (unpack (Array (getFinishPacket addr k maskSz) (Bit maskSz))
                (castBits _ (putRightPosition ($$ (wones (getFinishGranule addr k - getStartGranule addr)))%kami_expr
                                              (getStartGranule addr) (getFinishPacketGranule addr k maskSz)))).
      Opaque Nat.div.
      abstract (
          simpl;
          assert (divCeil (getStartGranule addr + (size k + (n-1)) / n) maskSz * maskSz >= getStartGranule addr + (size k + (n-1)) / n) by
              (pose proof (divCeil_ge (getStartGranule addr + div_packn k) (pow2_ne_zero lgMaskSz)); simpl in *;
               lia);
          lia).
      Transparent Nat.div.
    Defined.

    Definition makeJoinBits (addr: word addrSz) (k: Kind) (e: Array (getFinishPacket addr k maskSz) (Bit dataSz) @# ty): k @# ty.
      refine
        (unpack k (UniBit
                     (TruncLsb _ (div_packn k * n - size k))
                     (castBits
                        _
                        (ConstExtract (getStartGranule addr * n)
                                      (div_packn k * n)
                                      (getFinishPacket addr k maskSz * dataSz - getFinishGranule addr k * n)
                                      (castBits _ (pack e)))))).
      abstract (pose proof (@divCeil_ge (size k) n (pow2_ne_zero _)); Omega.omega).
      Opaque Nat.div.
      abstract (
          simpl;
          pose proof (@divCeil_ge (getStartGranule addr + (size k + (n-1)) / n) maskSz (pow2_ne_zero lgMaskSz));
          nia).
      Transparent Nat.div.
    Defined.

    (* Represents a register group starting at address represented by srg_addr.
       Note that srg_addr is of size addrSz, which means it indexes into a single
       granule, unlike grf_addr, which indexes into the entire data.
       IMPORTANT: The size of srg_kind can be well beyond dataSz of RegMapT.
       The value is just loaded contiguously starting from srg_addr and padded to fill entire data boundaries *)
    Record SimpleRegGroup :=
      { srg_addr  : word addrSz ;
        srg_kind  : Kind ;
        srg_read  : ActionT ty srg_kind ;
        srg_write : (srg_kind @# ty) -> ActionT ty Void;
        srg_name  : option string 
      }.

    Definition expandRqMask (m: Bit maskSz @# ty): Bit dataSz @# ty.
      refine (castBits _ (pack (BuildArray (fun i => replicate (ReadArrayConst (unpack (Array maskSz (Bit 1)) (castBits _ m)) i) n))));
        abstract (auto; simpl; lia).
    Defined.

    Local Open Scope kami_action.
    Local Open Scope kami_expr.
    Definition readWriteGranules_Gen (x: SimpleRegGroup): list GenRegField :=
      map (fun y => {| grf_addr  := (split2 _ realAddrSz (srg_addr x) ^+ $(proj1_sig (Fin.to_nat y)))%word ;
                       grf_mask  := ReadArrayConst (makeSplitMask (srg_addr x) (srg_kind x)) y ;
                       grf_read  :=
                         fun rm =>
                           (LETA readK: srg_kind x <- srg_read x ;
                              LET readVal: Bit dataSz <-
                                               ReadArrayConst (makeSplitBits (srg_addr x) #readK)
                                               y;
                              LET maskVal: Bit dataSz <-
                                               ReadArrayConst
                                               (makeSplitBits
                                                  (srg_addr x)
                                                  (Const ty (wones (size (srg_kind x)))))
                                               y;
                              LET finalVal: Bit dataSz <- expandRqMask (rm @% "mask") & #readVal & #maskVal;
                              Ret #finalVal) ;
                       grf_write :=
                         fun rm =>
                           (LETA readK: srg_kind x <- srg_read x ;
                              LET readVal <- makeSplitBits (srg_addr x) #readK;
                              LET maskVal <- makeSplitBits (srg_addr x)
                                  (Const ty (wones (size (srg_kind x))));
                              LET maskVali <- ReadArrayConst #maskVal y;
                              LET t1Val <- (expandRqMask (rm @% "mask") & #maskVali) & rm @% "data";
                              LET t2Val <- (~(expandRqMask (rm @% "mask") & #maskVali)) & (ReadArrayConst # readVal y);
                              LET t3Val <- (#t1Val | #t2Val);
                              LET finalVal <- UpdateArrayConst #readVal y #t3Val;
                              srg_write x (makeJoinBits (srg_addr x) (srg_kind x) #finalVal)
                           )
                    |})
          (getFins (getFinishPacket (srg_addr x) (srg_kind x) maskSz)).

    Definition readWriteGranules rq ls :=
      createRegMap rq (concat (map readWriteGranules_Gen ls)).

    Record SingleReg :=
      { sr_addr : word addrSz ;
        sr_kind : Kind ;
        sr_name : sum (string * bool) (ConstT sr_kind)}.

    Definition SingleReg_Gen (x: SingleReg) := {| srg_addr  := sr_addr x ;
                                                  srg_kind  := sr_kind x ;
                                                  srg_read  :=
                                                    match sr_name x with
                                                    | inl (name, _) =>
                                                      (Read val : (sr_kind x) <- name ;
                                                         Ret #val)
                                                    | inr uval =>
                                                      Ret ($$ uval)
                                                    end ;
                                                  srg_write :=
                                                    fun val =>
                                                      match sr_name x with
                                                      | inl (name, true) =>
                                                        (Write name : (sr_kind x) <- val ;
                                                           Retv)
                                                      | _ =>
                                                        Retv
                                                      end ;
                                                  srg_name := match sr_name x with
                                                              | inl (name, _) => Some name
                                                              | _ => None
                                                              end
                                               |}.

    Definition readWriteGranules_SingleReg rq ls := createRegMap rq (concat (map (fun x => readWriteGranules_Gen (SingleReg_Gen x)) ls)).

    (* Record SingleNonReg := *)
    (*   { snr_addr : word addrSz ; *)
    (*     snr_kind : Kind ; *)
    (*     snr_val  : ConstT snr_kind }. *)

    (* Definition readWriteGranules_SingleNonReg_Gen (x: SingleNonReg) := *)
    (*   readWriteGranules_Gen {| srg_addr  := snr_addr x ; *)
    (*                         srg_kind  := snr_kind x ; *)
    (*                         srg_read  := Ret (Const ty (snr_val x)) ; *)
    (*                         srg_write := fun val => Retv |}. *)

    (* Definition readWriteGranules_SingleNonReg rq ls := createRegMap rq (concat (map readWriteGranules_SingleNonReg_Gen ls)). *)
    
    Record GroupReg :=
      { gr_addr : word addrSz ;
        gr_kind : Kind ;
        gr_name : string
      }.

    Definition GroupReg_Gen (x: GroupReg) := {| srg_addr  := gr_addr x ;
                                                srg_kind  := gr_kind x ;
                                                srg_read  := Struct_RegReads ty (gr_kind x) ;
                                                srg_write := fun val => Struct_RegWrites val ;
                                                srg_name  := Some (gr_name x)
                                             |}.
    
    Definition readWriteGranules_GroupReg rq ls := createRegMap rq (concat (map (fun x => readWriteGranules_Gen (GroupReg_Gen x)) ls)).

    Record MayGroupReg :=
      { mgr_addr : word addrSz ;
        mgr_size : nat ;
        mgr_kind : MayStruct mgr_size ;
        mgr_name : string
      }.

    Definition MayStruct_Struct n (x: MayStruct n) := Struct (fun i => projT1 (vals x i)) (names x).


    Definition MayGroupReg_Gen (x: MayGroupReg) := {| srg_addr  := mgr_addr x ;
                                                      srg_kind  := MayStruct_Struct (mgr_kind x) ;
                                                      srg_read  := MayStruct_RegReads ty (mgr_kind x) ;
                                                      srg_write := fun val => MayStruct_RegWrites (mgr_kind x) val ;
                                                      srg_name  := Some (mgr_name x)
                                                   |}.

    Definition readWriteGranules_MayGroupReg rq ls := createRegMap rq (concat (map (fun x => readWriteGranules_Gen (MayGroupReg_Gen x)) ls)).

    Definition mayStructKind (n : nat) (x : MayStruct n)
      :  Kind
      := Struct (fun i : Fin.t n => projT1 (vals x i)) (names x).

    Variable ContextCodeWidth : nat.
    Definition ContextCodeT := Bit ContextCodeWidth.

    Definition LocationReadWriteInputT
      (k : Kind)
      := STRUCT_TYPE {
           "isRd"        :: Bool;
           "addr"        :: Bit addrSz;
           "contextCode" :: ContextCodeT;
           "data"        :: k
         }.

    Record View :=
      {
        view_context : ContextCodeT @# ty;
        view_size : nat ;
        view_kind : MayStruct view_size
      }.

    (* Represents a memory location supporting context-dependent views. *)
    Record Location :=
      {
        loc_name : string ;
        loc_addr : word addrSz ;
        loc_views : list View
      }.

    Definition viewReadWrite
      (n : nat)
      (k : Kind)
      (req : LocationReadWriteInputT k @# ty)
      (view : MayStruct n)
      :  ActionT ty k
      := LETA read_result
           :  mayStructKind view
           <- MayStruct_RegReads ty view;
         System [
           DispString _ "[viewReadWrite]\n";
           DispString _ "  read context code: ";
           DispDecimal (req @% "contextCode");
           DispString _ "\n";
           DispString _ "  read address: ";
           DispHex (req @% "addr");
           DispString _ "\n";
           DispString _ "  read result: ";
           DispBinary (pack #read_result);
           DispString _ "\n"
         ];
         If !(req @% "isRd")
           then
             LET write_value
               :  mayStructKind view
               <- unpack (mayStructKind view)
                    (ZeroExtendTruncLsb
                      (size (mayStructKind view))
                      (pack (req @% "data")));
             LETA write_result
               :  Void
               <- MayStruct_RegWrites view #write_value;
             System [
               DispString _ "  is write request.\n";
               DispString _ "  write value: ";
               DispBinary (pack #write_value);
               DispString _ "\n"
             ];
             Retv;
         Ret
           (unpack k
             (ZeroExtendTruncLsb (size k)
               (pack (#read_result)))).

    (*
      This function reads and writes to memory. Every memory
      location has an associated set of "views." A view is a set of
      fields. When this function reads a memory location, it selects
      one of the location's views, reads the values stored within
      the view fields, concatenates these field values together,
      and returns them.

      When this function writes to a memory location, it selects a
      view associated with the location. It then parses the write
      value into bit ranges corresponding to the view fields. It
      then writes the values stored within these bit ranges to the
      corresponding view fields.

      This function accepts three arguments: [k], [req] and [entries].

      [req] represents a memory request. Every memory request has
      an associated address and context code.

      [entries] represents a list of memory locations. Each entry
      contains a vector of views - one for each context code
      value. Each view contains a MayStruct that lists the fields
      that comprise the view.

      When the [isRd] field in [req] is true, this function reads
      the word at location [req @% "addr"] and converts it into a
      packet of type [k].

      When the [isRd] fields is false, this function writes the
      value given in [req @% "data"] to memory location [req @%
      "addr"].

    *)
    Definition locationReadWrite
      (k : Kind) 
      (req : LocationReadWriteInputT k @# ty)
      (entries : list Location)
      :  ActionT ty (Maybe k)
      := System [
           DispString _ "[locationReadWrite]\n";
           DispString _ "[locationReadWrite] request:\n";
           DispHex req;
           DispString _ "\n"
         ];
         utila_acts_find_pkt
           (map
             (fun addr_entry : Location
               => utila_acts_find_pkt
                    (map
                      (fun view_entry : View
                        => LET entry_match
                             :  Bool
                             <- ((req @% "addr") == $$(loc_addr addr_entry) &&
                                 (req @% "contextCode") == view_context view_entry);
                           If #entry_match
                             then
                               System [
                                 DispString _ "[locationReadWrite]\n";
                                 DispString _ "  location name: ";
                                 DispString _ (loc_name addr_entry);
                                 DispString _ "\n"
                               ];
                               viewReadWrite req (view_kind view_entry)
                             else
                               Ret (unpack k $0)
                             as result;
                           (utila_acts_opt_pkt #result #entry_match))
                      (loc_views addr_entry)))
             entries).

    Local Close Scope kami_expr.
    Local Close Scope kami_action.

  End RegMapper.
End Granule.

  (* Lemma helper_pow2_packn k: (pow2_packn k * n >= size k)%nat. *)
  (* Proof. *)
  (*   remember (size k) as x; clear Heqx. *)
  (*   pose proof (@divCeil_ge x n ltac:(Omega.omega)) as sth. *)
  (*   pose proof (log2_up_pow2 (divCeil x n)). *)
  (*   Omega.omega. *)
  (* Qed. *)

  (* Fixpoint wordSplitter' n t: word (t * n) -> list (word n) := *)
  (*   match t return word (t * n) -> list (word n) with *)
  (*   | 0 => fun _ => nil *)
  (*   | S m => fun w => split1 n (m * n) w :: @wordSplitter' _ m (split2 n (m * n) w) *)
  (*   end. *)

  (* Definition wordSplitter n (pf: n <> 0) sz (w: word sz): list (word n). *)
  (*   refine *)
  (*     (wordSplitter' n (divCeil sz n) (nat_cast word _ ({< natToWord (divCeil sz n * n - sz) 0, w>})%word)). *)
  (*   abstract (pose proof (divCeil_ge sz pf); *)
  (*             Omega.omega). *)
  (* Defined. *)

  (* Fixpoint exprSplitter' ty n t: (Bit (t * n) @# ty) -> list (Bit n @# ty) := *)
  (*     match t return Bit(t * n) @# ty -> list (Bit n @# ty) with *)
  (*     | 0 => fun _ => nil *)
  (*     | S m => fun w => UniBit (TruncLsb n (m * n)) w :: @exprSplitter' _ _ m (UniBit (TruncMsb n (m * n)) w) *)
  (*     end. *)

  (* Definition exprSplitter ty n (pf: n <> 0) sz (w: Bit sz @# ty): list (Bit n @# ty). *)
  (*   refine *)
  (*     (exprSplitter' n (divCeil sz n) (castBits _ ({< Const ty (natToWord (divCeil sz n * n - sz) 0), w>})%kami_expr)). *)
  (*   abstract (pose proof (divCeil_ge sz pf); *)
  (*             Omega.omega). *)
  (* Defined. *)

  (* Fixpoint convertBoolsToWord ls: word (length ls) := *)
  (*   match ls return word (length ls) with *)
  (*   | nil => WO *)
  (*   | x :: xs => WS x (convertBoolsToWord xs) *)
  (*   end. *)

  (* Definition byteAlignMask k: word (div_packn k * n). *)
  (*   refine (nat_cast word _ (combine (wones (size k)) (natToWord (div_packn k * n - size k) 0))). *)
  (*   abstract (pose proof (@divCeil_ge (size k) n ltac:(Omega.omega)); Omega.omega). *)
  (* Defined. *)

  (* Definition putRightPositionWord n (w: word n) start finish := *)
  (*   {< (natToWord (finish - (start + n)) 0), w, (natToWord start 0)>}%word. *)



  (* Eval compute in (map (@evalExpr _) (@exprSplitter type 3 ltac:(Omega.omega) 4 (Const type WO~0~1~0~1))). *)
  (* Eval compute in (map (@evalExpr _) (@exprSplitter type 3 ltac:(Omega.omega) _ (Const type WO~1~1~0~1~1~0~1~0))). *)
  (* Eval compute in ((@wordSplitter 3 ltac:(Omega.omega) _ (WO~1~1~0~1~1~0~1~0))). *)

  (* Goal True. *)
  (*   pose (evalExpr (putRightPosition (Const type (WO~1~1~1)%word) 4 16)). *)
  (*   simpl in f. *)
  (*   assert (f = ($0)~1~1~1~0~0~0~0). *)
  (*   unfold f. *)
  (*   auto. *)
  (*   auto. *)
  (* Defined. *)


