
From Coq Require Import
     Lists.List
     ZArith.ZArith.

Import ListNotations.

From Cava Require Import
     Expr
     Primitives
     Semantics
     TLUL
     Types
     Util.BitArithmetic.

Section Var.
  Import ExprNotations.
  Import PrimitiveNotations.

  Context {var : tvar}.

  Local Open Scope N.

  Definition incr_state := BitVec 2.
  Definition Idle       := Constant incr_state 0.
  Definition Busy1      := Constant incr_state 1.
  Definition Busy2      := Constant incr_state 2.
  Definition Done       := Constant incr_state 3.

  Definition incr
    : Circuit _ [tl_h2d_t] tl_d2h_t
    := {{
      fun tl_h2d =>
        (* Destruct and reconstruct tl_h2d with a_address that matches the
           tlul_adapter_reg interface. *)
        let '(a_valid
              , a_opcode
              , a_param
              , a_size
              , a_source
              , a_address
              , a_mask
              , a_data
              , a_user
              ; d_ready) := tl_h2d in
        (* Bit #2 of the address determines if STATUS or VALUE register. We zero
           out all the rest. *)
        let a_address := a_address & (`K 1` << 2) in
        let tl_h2d := (a_valid
                       , a_opcode
                       , a_param
                       , a_size
                       , a_source
                       , a_address
                       , a_mask
                       , a_data
                       , a_user
                       , d_ready) in

        let/delay '(istate, value; tl_d2h) :=
           let '(_, _, _, _, _, _, _, _, _; a_ready) := tl_d2h in

           (* Compute the value of the status register *)
           let status :=
               if istate == `Done` then `K 4`
               else if istate == `Busy1` || istate == `Busy2` then `K 2`
                    else (* istate == `Idle` *) `K 1` in

           let '(tl_d2h'; req) := `tlul_adapter_reg` tl_h2d (value :> status :> []) in

           let '(is_write
                 , _write_addr
                 , write_data
                 ; _write_mask) := req in

           let is_value_read_req := a_valid
                                    && a_ready
                                    && a_opcode == `Get`
                                    && a_address == `K 0` in

           let istate' :=
               if istate == `Busy1` then `Busy2`
               else if istate == `Busy2` then `Done`
                    else if istate == `Done` then
                           if is_value_read_req then `Idle` else `Done`
                         else (* istate == `Idle` *)
                           if is_write then `Busy1` else `Idle` in

           let value' :=
               if istate == `Busy2` then value + `K 1`
               else if istate == `Idle` then write_data
                    else value in

           (istate', value', tl_d2h')
             initially (0,
                        (0,
                         (false, (0, (0, (0, (0, (0, (0, (0, (false, false)))))))))))
           : denote_type (incr_state ** BitVec 32 ** tl_d2h_t)
        in

        tl_d2h
       }}.
End Var.

Section TLUL.
  Record tl_h2d_t := mk_tl_h2d_t {
                         a_valid : bool
                         ; a_opcode : N
                         ; a_param : N
                         ; a_size : N
                         ; a_source : N
                         ; a_address : N
                         ; a_mask : N
                         ; a_data : N
                         ; a_user : N
                         ; d_ready : bool
                       }.
  Record tl_d2h_t := mk_tl_d2h_t {
                         d_valid : bool
                         ; d_opcode : N
                         ; d_param : N
                         ; d_size : N
                         ; d_source : N
                         ; d_sink : N
                         ; d_data : N
                         ; d_user : N
                         ; d_error : bool
                         ; a_ready : bool
                       }.
End TLUL.

Example sample_trace :=
  Eval compute in
    let nop :=
        ((false,        (* a_valid   *)
          (0,           (* a_opcode  *)
           (0,          (* a_param   *)
            (0,         (* a_size    *)
             (0,        (* a_source  *)
              (0,       (* a_address *)
               (0,      (* a_mask    *)
                (0,     (* a_data    *)
                 (0,    (* a_user    *)
                  (true (* d_ready   *)
         )))))))))), tt)%N in

    let read_reg (r : N) :=
        ((true,         (* a_valid   *)
          (4,           (* a_opcode  Get *)
           (0,          (* a_param   *)
            (0,         (* a_size    *)
             (0,        (* a_source  *)
              (r,       (* a_address *)
               (0,      (* a_mask    *)
                (0,     (* a_data    *)
                 (0,    (* a_user    *)
                  (true (* d_ready   *)
         )))))))))), tt)%N in

    let write_val (v : N) :=
        ((true,         (* a_valid   *)
          (0,           (* a_opcode  PutFullData *)
           (0,          (* a_param   *)
            (0,         (* a_size    *)
             (0,        (* a_source  *)
              (0,       (* a_address value-reg *)
               (0,      (* a_mask    *)
                (v,     (* a_data    *)
                 (0,    (* a_user    *)
                  (true (* d_ready   *)
         )))))))))), tt)%N in

    simulate incr
             [ nop
               ; read_reg 4 (* status *)
               ; nop
               ; write_val 42
               ; nop
               ; nop
               ; read_reg 4 (* status *)
               ; nop
               ; read_reg 0 (* value *)
               ; nop
               ; read_reg 4 (* status *)
             ]%N.
Print sample_trace.
(* d_valid;  *)
(* d_opcode; *)
(* d_param;  *)
(* d_size;   *)
(* d_source; *)
(* d_sink;   *)
(* d_data;   *)
(* d_user;   *)
(* d_error;  *)
(* a_ready;  *)

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.

Require Import riscv.Utility.Utility.

Require Import coqutil.Datatypes.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.Simp.

Require Import bedrock2.ZnWords.

Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.IncrementWait.Constants.
Require Import Bedrock2Experiments.IncrementWait.IncrementWaitSemantics.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

Require Import Cava.Expr.
Require Import Cava.ExprProperties.
Require Import Cava.Primitives.
Require Import Cava.Semantics.
Require Import Cava.Types.
Require Import Cava.Util.Identity.
Require Import Cava.Util.If.
Require Import Cava.Util.List.
Require Import Cava.Util.Nat.
Require Import Cava.Util.Tactics.

Section TLULProperties.
  Local Open Scope bool_scope.
  Local Open Scope N_scope.

  Variant op :=
  | Read
  | Write (data : N).

  (* State invariant *)
  Definition tlul_adapter_reg_invariant
             (state :  denote_type (BitVec 8 ** BitVec 2 ** BitVec 3 ** Bit ** Bit ** Bit ** Bit))
             (* ghost *)
    : Prop :=
    let '(reqid, (reqsz, (rspop, (error, (outstanding, (we_o, re_o)))))) := state in
    error = false.

  (* Precondition *)
  Definition tlul_adapter_reg_pre {reg_count}
             (input : denote_type [TLUL.tl_h2d_t; Vec (BitVec 32) reg_count])
             (* ghost *)
             index op
    : Prop :=
    let '(incoming_tlp, (registers, tt)) := input in
    let '(a_valid,
          (a_opcode,
           (_a_param,
            (a_size,
             (a_source,
              (a_address,
               (a_mask,
                (a_data,
                 (_a_user,
                  d_ready))))))))) := incoming_tlp in
    (* if a_valid then *)
      List.length registers = reg_count /\
      N.shiftr a_address 2 < N.of_nat reg_count /\
      (* (a_opcode = 0 \/ a_opcode = 4) /\ *)
      N.shiftl (N.of_nat index) 2 = a_address /\
      (* index = N.to_nat (N.shiftr a_address 2) /\ *)
      ((a_opcode = 0 /\ op = Write a_data) \/
       (* a_opcode = 1 \/ a_opcode = 2 \/ a_opcode = 3 \/ *)
       (a_opcode = 4 /\ op = Read)).
    (* else True. *)

  Definition tlul_adapter_reg_spec {reg_count}
             (input : denote_type [TLUL.tl_h2d_t; Vec (BitVec 32) reg_count])
             (state :  denote_type (BitVec 8 ** BitVec 2 ** BitVec 3 ** Bit ** Bit ** Bit ** Bit))
             (* ghost *)
             index op
    : denote_type (TLUL.tl_d2h_t ** io_req) :=
    let '(incoming_tlp, (registers, tt)) := input in
    let '(reqid, (reqsz, (rspop, (error, (outstanding, (_we_o, _re_o)))))) := state in

    let '(a_valid,
          (_a_opcode,
           (_a_param,
            (a_size,
             (a_source,
              (a_address,
               (a_mask,
                (a_data,
                 (_a_user,
                  d_ready))))))))) := incoming_tlp in

    if outstanding then
      ((negb d_ready,
        (rspop,
         (0,
          (reqsz,
           (reqid,
            (0,
             (List.nth index registers 0,
              (0,
               (error,
                d_ready))))))))),
       (false, (a_address, (a_data, a_mask))))
    else if a_valid then
           ((true,
             (match op with | Read => 1 | Write _ => 0 end (* if a_opcode =? 4 then 1 else 0 *),
              (0,
               (a_size,
                (a_source,
                 (0,
                  (List.nth index registers 0,
                   (0,
                    (false,
                     false))))))))),
            match op with
            | Write data => (true, (N.shiftl (N.of_nat index) 2, (data, a_mask)))
            | _ => (false, (a_address, (a_data, a_mask)))
            end)
         else
           ((false,
             (rspop,
              (0,
               (reqsz,
                (reqid,
                 (0,
                  (List.nth index registers 0,
                   (0,
                    (error,
                     true))))))))),
            (false, (a_address, (a_data, a_mask)))).

  Lemma step_tlul_adapter_reg_invariant {reg_count}
        (input : denote_type [TLUL.tl_h2d_t; Vec (BitVec 32) reg_count])
        (state :  denote_type (BitVec 8 ** BitVec 2 ** BitVec 3 ** Bit ** Bit ** Bit ** Bit))
        (* ghost *)
        (index : nat) (op : op) :
    tlul_adapter_reg_pre input index op ->
    tlul_adapter_reg_invariant state ->
    tlul_adapter_reg_invariant
      (fst (Semantics.step TLUL.tlul_adapter_reg state input)).
  Proof.
    destruct input as (incoming_tlp, (registers, [])).
    destruct incoming_tlp as (a_valid, (a_opcode, (a_param, (a_size, (a_source, (a_address, (a_mask, (a_data, (a_user, d_ready))))))))).
    destruct state as (reqid, (reqsz, (rspop, (error, (outstanding, (we_o, re_o)))))).
    cbv [tlul_adapter_reg_invariant tlul_adapter_reg_pre].
    intros ? Hinv. logical_simplify. clear H. subst.
    cbv [tlul_adapter_reg K]. stepsimpl.
    repeat (destruct_pair_let; cbn [fst snd]).
    autorewrite with tuple_if; cbn [fst snd].
    cbn. destruct (a_valid && negb outstanding); reflexivity.
  Qed.

  Axiom denote_bv_max : forall (n : N) (m : denote_type (BitVec (N.to_nat n))),
      m < 2 ^ n.

  Lemma land_shiftr : forall (n v : N) (m : denote_type (BitVec (N.to_nat n))),
      0 < n -> v <= n ->
      N.land (N.shiftr m v) (2 ^ (n - v) - 1) = N.shiftr m v.
  Proof.
    intros. rewrite <- ? N.pred_sub. rewrite <- ? N.ones_equiv.
    rewrite <- N.ones_div_pow2; auto. rewrite <- N.shiftr_div_pow2.
    rewrite <- N.shiftr_land. rewrite N.land_ones_low. 1: reflexivity.
    destruct m.
    - (* 0 = m *) simpl. assumption.
    - (* 0 < m *) apply N.log2_lt_pow2. 1: Lia.lia. apply denote_bv_max.
  Qed.

  Lemma shiftl_shiftr : forall n n' m,
      N.shiftl n m = n' -> n = N.shiftr n' m.
  Proof.
    intros. apply f_equal with (f := fun x => N.shiftr x m) in H.
    rewrite <- H. rewrite N.shiftr_shiftl_l; try Lia.lia. rewrite N.sub_diag.
    rewrite N.shiftl_0_r. reflexivity.
  Qed.

  Lemma step_tlul_adapter_reg {reg_count}
        (input : denote_type [TLUL.tl_h2d_t; Vec (BitVec 32) reg_count])
        (state :  denote_type (BitVec 8 ** BitVec 2 ** BitVec 3 ** Bit ** Bit ** Bit ** Bit))
        (* ghost *)
        (index : nat) (op : op) :
    tlul_adapter_reg_pre input index op ->
    tlul_adapter_reg_invariant state ->
    snd (step tlul_adapter_reg state input) = tlul_adapter_reg_spec input state index op.
  Proof.
    destruct input as (incoming_tlp, (registers, [])).
    destruct incoming_tlp as (a_valid, (a_opcode, (a_param, (a_size, (a_source, (a_address, (a_mask, (a_data, (a_user, d_ready))))))))).
    destruct state as (reqid, (reqsz, (rspop, (error, (outstanding, (we_o, re_o)))))).
    destruct outstanding eqn:Eoutstanding.
    - (* outstanding = true *)
      cbv [tlul_adapter_reg_invariant tlul_adapter_reg_pre tlul_adapter_reg_spec].
      intros. logical_simplify.
      cbn. repeat (destruct_pair_let; cbn [fst snd]).
      boolsimpl.
      autorewrite with tuple_if; cbn [fst snd].
      rewrite <- Bool.negb_if. rewrite <- Bool.andb_lazy_alt. boolsimpl.
      repeat (rewrite pair_equal_spec).
      ssplit; try reflexivity.
      push_resize.
      apply shiftl_shiftr in H2. apply f_equal with (f := N.to_nat) in H2.
      rewrite Nnat.Nat2N.id in H2. subst index.
      rewrite ? N.div2_spec.
      rewrite N.shiftr_shiftr. cbn -[N.shiftr].
      rewrite <- land_shiftr with (n := 32) (v := 2) at 2; try Lia.lia; []. reflexivity.
    - (* outstanding = false *)
      cbv [tlul_adapter_reg_invariant tlul_adapter_reg_pre tlul_adapter_reg_spec].
      intros. logical_simplify.
      cbn. repeat (destruct_pair_let; cbn [fst snd]).
      boolsimpl.
      autorewrite with tuple_if; cbn [fst snd].
      destruct a_valid eqn:Ea_valid.
      + (* a_valid = true *)
        repeat (rewrite pair_equal_spec).
        ssplit; try reflexivity; [| |].
        * boolsimpl. clear H. destruct H3 as [H3 | H3]; destruct H3; subst; auto.
        * push_resize.
          apply shiftl_shiftr in H2. apply f_equal with (f := N.to_nat) in H2.
          rewrite Nnat.Nat2N.id in H2. subst index.
          rewrite ? N.div2_spec.
          rewrite N.shiftr_shiftr. cbn -[N.shiftr].
          rewrite <- land_shiftr with (n := 32) (v := 2) at 2; try Lia.lia; []. reflexivity.
        * boolsimpl. clear H. destruct H3 as [H3 | H3]; destruct H3; subst; auto.
      + (* a_valid = false *)
        repeat (rewrite pair_equal_spec).
        ssplit; try reflexivity; [].
        push_resize.
        apply shiftl_shiftr in H2. apply f_equal with (f := N.to_nat) in H2.
        rewrite Nnat.Nat2N.id in H2. subst index.
        rewrite ? N.div2_spec.
        rewrite N.shiftr_shiftr. cbn -[N.shiftr].
        rewrite <- land_shiftr with (n := 32) (v := 2) at 2; try Lia.lia; []. reflexivity.
  Qed.
End TLULProperties.

Section WithParameters.
  Instance var : tvar := denote_type.

  Context {word: Interface.word 32} {word_ok: word.ok word}
          {Mem: map.map word byte} {Registers: map.map Z word}.

  Definition incr_device_step s '((is_read_req, is_write_req, req_addr, req_value) : (bool * bool * N * N))
    : _ * (bool * N) :=
    let input := ((is_read_req || is_write_req,     (* a_valid   *)
                   (if is_read_req then 4 else 0, (* a_opcode  *)
                    (0,                           (* a_param   *)
                     (0,                          (* a_size    *)
                      (0,                         (* a_source  *)
                       (req_addr,                 (* a_address *)
                        (0,                       (* a_mask    *)
                         (req_value,              (* a_data    *)
                          (0,                     (* a_user    *)
                           true                   (* d_ready   *)
                  ))))))))), tt)%N%bool in
    let '(s', output) := Semantics.step incr s input in
    let '(d_valid,
          (_d_opcode,
           (_d_param,
            (_d_size,
             (_d_source,
              (_d_sink,
               (d_data,
                (_d_user,
                 (_d_error,
                  _a_ready))))))))) := output in
    (s', (d_valid, d_data)).

  Definition tl_d2h_of_tlul_state '((reqid, (reqsz, (rspop, (error, (outstanding, (_we_o, _re_o)))))) : (N * (N * (N * (bool * (bool * (bool * bool)))))))
             (v : N) :=
    (outstanding,
     (rspop,
      (0,
       (reqsz,
        (reqid,
         (0,
          (v,
           (0,
            (error,
             (negb outstanding
    ))))))))))%N.

  Definition mk_counter_state (istate : N) (val : N) tl_d2h tlul_state
    : denote_type (state_of incr) :=
    ((istate, (val, tl_d2h)), tlul_state).

  Global Instance counter_device: device := {|
    device.state := denote_type (state_of incr);
    device.is_ready_state s := exists val ival tl_d2h tlul_state,
        tl_d2h = tl_d2h_of_tlul_state tlul_state ival
        /\ s = mk_counter_state 0 val tl_d2h tlul_state;
    device.run1 := incr_device_step;
    device.addr_range_start := INCR_BASE_ADDR;
    device.addr_range_pastend := INCR_END_ADDR;
    device.maxRespDelay := 1;
  |}.

  (* conservative upper bound matching the instance given in IncrementWaitToRiscv *)
  Global Instance circuit_spec : circuit_behavior :=
  {| ncycles_processing := 15%nat |}.

  Inductive counter_related: IncrementWaitSemantics.state -> denote_type (state_of incr) -> Prop :=
  | IDLE_related: forall val ival tl_d2h tlul_state,
      tl_d2h = tl_d2h_of_tlul_state tlul_state ival ->
      counter_related IDLE (mk_counter_state 0 val tl_d2h tlul_state)
  | BUSY1_related: forall val ival tl_d2h tlul_state ncycles,
      (1 < ncycles)%nat ->
      tl_d2h = tl_d2h_of_tlul_state tlul_state ival ->
      counter_related (BUSY val ncycles) (mk_counter_state 1 (word_to_N val) tl_d2h tlul_state)
  | BUSY2_related: forall val ival tl_d2h tlul_state ncycles,
      (0 < ncycles)%nat ->
      tl_d2h = tl_d2h_of_tlul_state tlul_state ival ->
      counter_related (BUSY val ncycles) (mk_counter_state 2 (word_to_N val) tl_d2h tlul_state)
  (* the hardware is already done, but the software hasn't polled it yet to find out,
     so we have to relate a software-BUSY to a hardware-done: *)
  | BUSY_done_related: forall val ival tl_d2h tlul_state ncycles,
      tl_d2h = tl_d2h_of_tlul_state tlul_state ival ->
      counter_related (BUSY val ncycles)
                      (mk_counter_state 3 (word_to_N (word.add (word.of_Z 1) val)) tl_d2h tlul_state)
  | DONE_related: forall val ival tl_d2h tlul_state,
      tl_d2h = tl_d2h_of_tlul_state tlul_state ival ->
      counter_related (DONE val) (mk_counter_state 3 (word_to_N val) tl_d2h tlul_state).

  (* This should be in bedrock2.ZnWords. It is use by ZnWords, which is used in
     the two following Lemmas. *)
  Ltac better_lia ::= Zify.zify; Z.to_euclidean_division_equations; Lia.lia.

  Lemma incrN_word_to_bv: forall x,
      ((N.add (word_to_N x) 1) mod 4294967296)%N = word_to_N (word.add (word.of_Z 1) x).
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Lemma Z_word_N: forall x,
      (0 <= x < 2 ^ 32) -> word_to_N (word.of_Z x) = Z.to_N x.
  Proof. intros. unfold word_to_N. ZnWords. Qed.

  Set Printing Depth 100000.

  Ltac destruct_pair_let_hyp :=
    match goal with
    | H: context [ match ?p with
                   | pair _ _ => _
                   end ] |- _ =>
      destruct p as [?p0 ?p1] eqn:?H0
    end.

  Ltac destruct_pair_equal_hyp :=
    match goal with
    | H: context [ (?l0, ?l1) = (?r0, ?r1) ] |- _ =>
      eapply pair_equal_spec in H; destruct H as [?H0 ?H1]
    end.

  (* Set Printing All. *)
  Global Instance cava_counter_satisfies_state_machine:
    device_implements_state_machine counter_device increment_wait_state_machine.
  Proof.
    eapply Build_device_implements_state_machine with (device_state_related := counter_related);
      intros.
    - (* mmioAddrs_match: *)
      reflexivity.
    - (* initial_state_is_ready_state: *)
      simpl in *. subst. inversion H0. do 4 eexists. subst. eauto.
    - (* initial_states_are_related: *)
      simpl in *. destruct H0 as (val & ival & tl_d2h & tlul_state & H0 & H1). subst.
      eauto using IDLE_related.
    - (* initial_state_exists: *)
      simpl in *. destruct H as (val & ival & tl_d2h & tlul_state & H0 & H1). subst.
      eauto using IDLE_related.
    - (* nonMMIO_device_step_preserves_state_machine_state: *)
      simpl in sL1, sL2.
      cbn in H0.
      (* simp. *)
      repeat destruct_pair_let_hyp. (* <-- very slow *)
      repeat (destruct_pair_equal_hyp; subst; cbn).
      inversion H; subst; simp;
        (* try rewrite N.land_0_r; *)
        try rewrite Bool.andb_false_r;
        unfold tl_d2h_of_tlul_state in *;
        cbn.
      + (* IDLE_related: *)
        eapply IDLE_related.
        rewrite Bool.andb_true_r. rewrite <- Bool.negb_if.
        rewrite <- Bool.andb_lazy_alt. rewrite Bool.andb_negb_l.
        simpl.
        repeat (apply pair_equal_spec; split; try reflexivity).
      + (* BUSY1_related: *)
        eapply BUSY2_related.
        * Lia.lia.
        * rewrite Bool.andb_true_r. rewrite <- Bool.negb_if.
          rewrite <- Bool.andb_lazy_alt. rewrite Bool.andb_negb_l.
          simpl.
          repeat (apply pair_equal_spec; split; try reflexivity).
      + (* BUSY2_related: *)
        rewrite incrN_word_to_bv.
        eapply BUSY_done_related.
        rewrite Bool.andb_true_r. rewrite <- Bool.negb_if.
        rewrite <- Bool.andb_lazy_alt. rewrite Bool.andb_negb_l.
        simpl.
        repeat (apply pair_equal_spec; split; try reflexivity).
      + (* BUSY_done_related: *)
        eapply BUSY_done_related.
        rewrite Bool.andb_true_r. rewrite <- Bool.negb_if.
        rewrite <- Bool.andb_lazy_alt. rewrite Bool.andb_negb_l.
        simpl.
        repeat (apply pair_equal_spec; split; try reflexivity).
      + (* DONE_related: *)
        eapply DONE_related.
        rewrite Bool.andb_true_r. rewrite <- Bool.negb_if.
        rewrite <- Bool.andb_lazy_alt. rewrite Bool.andb_negb_l.
        simpl.
        repeat (apply pair_equal_spec; split; try reflexivity).
    - (* state_machine_read_to_device_read: *)
      (* simpler because device.maxRespDelay=1 *)
      unfold device.maxRespDelay, device.runUntilResp, device.state, device.run1, counter_device.
      unfold state_machine.read_step, increment_wait_state_machine in *.
      simp.
      unfold read_step in *.
      destruct r.
      + (* r=VALUE *)
        simp. cbn.
        destruct tlul_state as [reqid [reqsz [rspop [error [outstanding [we_o re_o]]]]]].
        (* destruct tl_d2h as [d_valid [d_opcode [d_param [d_size [d_source [d_sink [d_data [d_user [d_error a_ready]]]]]]]]]. *)
        cbn.
        destruct outstanding; [|];
          rewrite Z_word_N; try Lia.lia;
            (* rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate). *)
            do 3 eexists; ssplit; try reflexivity;
              eapply IDLE_related; reflexivity.
      + (* r=STATUS *)
        destruct sH.
        * (* sH=IDLE *)
          destruct Hp1. subst. inversion H0. subst.
          cbn. repeat (rewrite Z_word_N; try Lia.lia; []; cbn).
          unfold status_value, STATUS_IDLE, word_to_N.
          (* rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate). *)
          do 3 eexists. ssplit; try reflexivity.
          -- rewrite word.unsigned_slu; try ZnWords; [].
             rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
             destruct tlul_state as [reqid [reqsz [rspop [error [outstanding [we_o re_o]]]]]].
             destruct outstanding; reflexivity.
          -- simpl. eapply IDLE_related. reflexivity.
        * (* sH=BUSY *)
          destruct Hp1 as [H | H].
          -- (* transition to DONE *)
             destruct H. subst.
             simpl (state_machine.reg_addr _).
             unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_N, status_value, STATUS_DONE.
             rewrite !word.unsigned_of_Z. unfold word.wrap. simpl.
             inversion H0; subst; [| |].
             ++ (* BUSY1_related *)
               destruct max_cycles_until_done; [|].
               ** exfalso. eapply NPeano.Nat.nlt_0_r. apply H2.
               **
                  (* clear H0. *)
                  exists (word.of_Z 2). (* <- bit #1 (busy) is set, all others are 0 *)
                  do 2 eexists.
                  destruct tlul_state as [reqid [reqsz [rspop [error [outstanding [we_o re_o]]]]]].
                  cbn.
                  rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                  ssplit; try reflexivity; [| |].
                  { destruct outstanding; [|].
                    { cbn. reflexivity. }
                    { cbn. reflexivity. }
                    admit. }
                  { admit. }
                  { right. exists max_cycles_until_done. ssplit; try reflexivity; []. ZnWords. }

                 inversion H0; subst.
                ** eapply BUSY2_related.
                   instantiate ( 1 := max_cycles_until_done ).
                   inversion H0; subst.
                   Lia.lia.
                ** right. eexists; ssplit; try reflexivity; []. ZnWords.
             ++ (* BUSY2_related *)
                (* the transition that was used to show that sH is not stuck was *)
                (* a transition from BUSY to DONE returning a done flag, but *)
                (* since the device is still in BUSY state, it will still return *)
                (* the busy flag in this transition, so the transition we use to *)
                (* simulate what happened in the device is a BUSY-to-DONE *)
                (* transition returning a busy flag instead of a done flag. *)
               exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                (* destruct max_cycles_until_done. 1: inversion H3. clear H3. *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity; [|].
                ** rewrite incrN_word_to_bv.
                   eapply DONE_related.
                ** left. eexists; ssplit; try reflexivity; []. ZnWords.
             ++ (* BUSY_done_related *)
               exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity; [|].
                ** eapply DONE_related.
                ** left. split; try reflexivity; []. ZnWords.
          -- (* stay BUSY *)
             destruct H as (n & ? & ? & ?); subst.
             simpl (state_machine.reg_addr _).
             unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_N, status_value, STATUS_BUSY.
             rewrite !word.unsigned_of_Z. unfold word.wrap. simpl.
             inversion H0; subst.
             ++ (* BUSY1_related *)
                exists (word.of_Z 2). (* <- bit #1 (busy) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity.
                ** eapply BUSY2_related. instantiate (1 := n).
                   Lia.lia.
                ** right. eexists; ssplit; try reflexivity; []. ZnWords.
             ++ (* BUSY2_related *)
                exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity; [|].
                ** rewrite incrN_word_to_bv.
                   eapply DONE_related.
                ** left. eexists; ssplit; try reflexivity; []. ZnWords.
             ++ (* BUSY_done_related *)
                (* the transition that was used to show that sH is not stuck was *)
                (* a transition from BUSY to BUSY returning a busy flag, but *)
                (* since the device already is in done state, it will return a *)
                (* done flag in this transition, so the transition we use to *)
                (* simulate what happened in the device is a BUSY-to-DONE *)
                (* transition returning a done flag instead of a BUSY-to-BUSY *)
                (* transition returning a busy flag. *)
                exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
                do 2 eexists.
                rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
                ssplit; try reflexivity.
                ** simpl. eapply DONE_related.
                ** left. split. 2: reflexivity. ZnWords.
        * (* sH=DONE *)
          destruct Hp1. subst. inversion H0. subst.
          simpl (state_machine.reg_addr _).
          unfold STATUS_ADDR, INCR_BASE_ADDR, word_to_N, status_value, STATUS_DONE.
          cbn.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
          exists (word.of_Z 4). (* <- bit #2 (done) is set, all others are 0 *)
          do 2 eexists.
          rewrite !word.unsigned_of_Z. unfold word.wrap. cbn.
          ssplit; try reflexivity.
          ** simpl. eapply DONE_related.
          ** ZnWords.
    - (* state_machine_write_to_device_write: *)
      destruct H as (sH' & ? & ?). subst.
      unfold write_step in H1.
      destruct r. 2: contradiction.
      destruct sH; try contradiction. subst.
      inversion H0. subst.
      cbn.
      unfold word_to_N.
      rewrite word.unsigned_of_Z_nowrap by (cbv; intuition discriminate).
      cbn.
      eexists _, _, _. ssplit; try reflexivity. destruct idle; eapply BUSY1_related; Lia.lia.
    - (* read_step_unique: *)
      cbn in *. unfold read_step in *. simp.
      destruct v; destruct r; try contradiction; simp; try reflexivity.
      destruct Hp1; destruct H0p1; simp; try reflexivity;
        unfold status_value in *; exfalso; ZnWords.
    - (* write_step_unique: *)
      cbn in *. unfold write_step in *. simp. subst. reflexivity.
    - (* initial_state_unique: *)
      cbn in *. subst. reflexivity.
  Qed.

End WithParameters.
