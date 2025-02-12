Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import coqutil.Word.Interface coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Simp.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricSane.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.SeparationLogic.
Require Import compiler.Pipeline.
Require Import compiler.LowerPipeline.
Require Import compiler.CompilerInvariant.
Require Import Bedrock2Experiments.StateMachineSemantics.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.InternalMMIOMachine.
Require Import Bedrock2Experiments.StateMachineMMIOSpec.
Require Import Bedrock2Experiments.StateMachineMMIO.
Require Import Bedrock2Experiments.RiscvMachineWithCavaDevice.MMIOToCava.

(* TODO move to compiler.DivisibleBy4 *)
Require Import compiler.DivisibleBy4 compiler.mod4_0.
Ltac divisibleBy4_pre ::=
  lazymatch goal with
  | |- ?G => assert_fails (has_evar G)
  end;
  unfold divisibleBy4 in *;
  lazymatch goal with
  | |- _ mod 4 = 0 => idtac
  | |- _ => fail "not a divisibleBy4 goal"
  end;
  repeat match goal with
         | H: _ mod 4 = 0 |- _ => revert H
         end;
  repeat match goal with
         (* TODO might fail to find Words instance *)
         | H: word.unsigned _ mod 4 = 0 |- _ => unique pose proof (divisibleBy4Signed _ H)
         end;
  repeat match goal with
         | H: ?T |- _ => lazymatch T with
                         | word.ok _ => fail
                         | _ => clear H
                         end
         end;
  repeat match goal with
         | |- _ mod 4 = 0 -> _ => intro
         end;
  try apply mod4_0_opp;
  try apply divisibleBy4Signed;
  repeat (rewrite ?word.unsigned_add, ?word.signed_add,
                  ?word.unsigned_sub, ?word.signed_sub,
                  ?word.unsigned_mul, ?word.signed_mul,
                  ?word.unsigned_of_Z, ?word.signed_of_Z
          || unfold word.wrap, word.swrap).

Existing Instance SortedListString.map.
Existing Instance SortedListString.ok.

Section WithParams.
  Context {word : Interface.word.word 32} {word_ok: word.ok word}
          {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}
          {Registers: map.map Z word} {Registers_ok: map.ok Registers}
          {mem : Interface.map.map word Byte.byte} {mem_ok: map.ok mem}
          {M: state_machine.parameters} {M_ok: state_machine.ok M}
          {D: device}
          {DI: device_implements_state_machine D M}
          (sched: schedule).

  Open Scope ilist_scope.

  Definition regs_initialized(regs: Registers): Prop :=
    forall r : Z, 0 < r < 32 -> exists v : word, map.get regs r = Some v.

  (* similar to compiler.LowerPipeline.machine_ok, but takes an `ExtraRiscvMachine D` instead of
     a `MetricRiscvMachine` *)
  Definition machine_ok(p_functions: word)(f_entry_rel_pos: Z)(stack_start stack_pastend: word)
             (finstrs: list byte)(p_call pc: word)(mH: mem)(Rdata Rexec: mem -> Prop)
             (mach: ExtraRiscvMachine D): Prop :=
      let CallInst := Jal RegisterNames.ra
                          (f_entry_rel_pos + word.signed (word.sub p_functions p_call)) : Instruction in
      (ptsto_bytes p_functions finstrs *
       ptsto_bytes p_call (instrencode [CallInst]) *
       mem_available stack_start stack_pastend *
       Rdata * Rexec * eq mH
      )%sep mach.(getMem) /\
      subset (footpr (ptsto_bytes p_functions finstrs *
                      ptsto_bytes p_call (instrencode [CallInst]) *
                      Rexec)%sep)
             (of_list (getXAddrs mach)) /\
      word.unsigned (mach.(getPc)) mod 4 = 0 /\
      mach.(getPc) = pc /\
      mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
      regs_initialized mach.(getRegs) /\
      map.get mach.(getRegs) RegisterNames.sp = Some stack_pastend /\
      device.is_ready_state mach.(getExtraState) /\
      (* Note: Even though we cancel out the fact that communication between the processor
         and the Cava device happens via MMIO, we still have to expose the fact that we
         need a reserved address range for MMIO which cannot be used as regular memory: *)
      map.undef_on mach.(getMem) device.isMMIOAddr /\
      disjoint (of_list mach.(getXAddrs)) device.isMMIOAddr.

  Lemma mod4_to_mod2: forall x, x mod 4 = 0 -> x mod 2 = 0.
  Proof. intros. Z.div_mod_to_equations. Lia.lia. Qed.

  Lemma bedrock2_and_cava_system_correct: forall fs instrs pos_map required_stack_space
        f_entry_name fbody p_functions f_entry_rel_pos stack_start stack_pastend
        p_call mH Rdata Rexec (initialL: ExtraRiscvMachine D) steps_done postH,
      ExprImp.valid_funs (map.of_list fs) ->
      NoDup (map fst fs) ->
      compile compile_ext_call (map.of_list fs) = Some (instrs, pos_map, required_stack_space) ->
      Forall (fun i : Instruction => verify i RV32I) instrs ->
      -2^20 <= f_entry_rel_pos + word.signed (word.sub p_functions p_call) < 2^20 ->
      map.get (map.of_list fs) f_entry_name = Some ([], [], fbody) ->
      map.get pos_map f_entry_name = Some f_entry_rel_pos ->
      required_stack_space <= word.unsigned (word.sub stack_pastend stack_start) / 4 ->
      word.unsigned (word.sub stack_pastend stack_start) mod 4 = 0 ->
      word.unsigned p_functions mod 4 = 0 ->
      word.unsigned p_call mod 4 = 0 ->
      f_entry_rel_pos mod 4 = 0 ->
      initialL.(getLog) = [] ->
      WeakestPrecondition.cmd (WeakestPrecondition.call fs)
           fbody initialL.(getLog) mH map.empty
           (fun (t': Semantics.trace) (m': mem) (l': ProgramSemantics32.locals) =>
                            postH m' /\
                            (* driver is supposed to put device back into initial state: *)
                            exists s', execution t' s' /\ state_machine.is_initial_state s') ->
      machine_ok p_functions f_entry_rel_pos stack_start stack_pastend (instrencode instrs) p_call
                 p_call mH Rdata Rexec initialL ->
      exists steps_remaining finalL mH',
        run_rec sched steps_done steps_remaining initialL = (Some tt, finalL) /\
        machine_ok p_functions f_entry_rel_pos stack_start stack_pastend (instrencode instrs) p_call
                   (word.add p_call (word.of_Z 4)) mH' Rdata Rexec finalL /\
        postH mH' /\
        finalL.(getLog) = initialL.(getLog) (* no external interactions happened *).
  Proof.
    intros.
    destruct initialL as (mach & d). destruct mach as [r pc npc m xAddrs t].
    unfold machine_ok in *; cbn -[map.get map.empty instrencode] in *. simp.
    replace device.isMMIOAddr with state_machine.isMMIOAddr in *. 2: {
      symmetry. extensionality x. apply propositional_extensionality. unfold iff.
      pose proof mmioAddrs_match as P. unfold sameset, subset in P.
      clear -P. unfold elem_of, device.isMMIOAddr in *. destruct P. eauto.
    }
    edestruct stateMachine_to_cava
      as (steps_remaining & finalL & finalH & Rn & Rfinal & Pf).
    2: {
      pose proof Pipeline.compiler_correct as P.
      unfold FlatToRiscvCommon.runsTo, GoFlatToRiscv.mcomp_sat, mcomp_sat in P.
      cbn -[map.get map.empty instrencode] in P.
      specialize P with (p_call := p_call) (p_functions := p_functions).
      eapply P with (initial := {| MetricRiscvMachine.getMachine := {| getPc := _ |} |});
        clear P; cbn -[map.get map.empty instrencode]; try eassumption.
      { apply compile_ext_call_correct. }
      { intros. reflexivity. }
      { refine (sound_cmd _ _ _ _ _ _ _ _ _).
        - assumption.
        - match goal with
          | H: WeakestPrecondition.cmd _ _ _ _ _ _ |- _ => exact H
          end. }
      unfold LowerPipeline.machine_ok; cbn -[map.get map.empty instrencode program].
      pose proof ptsto_bytes_to_program (iset := RV32I) as P.
      match goal with
      | |- context[?Q] => lazymatch Q with
                          | program _ ?p ?i => replace Q with (ptsto_bytes p (instrencode i))
                          end
      end.
      2: { eapply iff1ToEq. eapply P; eassumption. }
      match goal with
      | |- context[?Q] => lazymatch Q with
                          | program _ ?p ?i => replace Q with (ptsto_bytes p (instrencode i))
                          end
      end.
      2: {
        eapply iff1ToEq. eapply P. 1: eassumption.
        constructor. 2: constructor.
        unfold verify. cbn. unfold verify_UJ. unfold opcode_JAL, RegisterNames.ra.
        split; [|trivial].
        split; [Lia.lia|].
        split; [Lia.lia|].
        ssplit; try eassumption.
        eapply mod4_to_mod2.
        repeat match goal with
               | H: word.unsigned _ mod 4 = 0 |- _ => unique pose proof (divisibleBy4Signed _ H)
               end.
        solve_divisibleBy4.
      }
      ssplit; try eassumption; try reflexivity.
    }
    2: {
      inversion Rfinal. subst; clear Rfinal.
      unfold LowerPipeline.machine_ok in *. cbn -[map.get map.empty instrencode] in *.
      simp.
      eexists _, {| getMachine := {| getLog := [] |} |}, _; cbn -[map.get map.empty instrencode].
      split. 1: exact Rn.
      pose proof ptsto_bytes_to_program (iset := RV32I) as P. cbn in P.
      match goal with
      | |- context[?Q] => lazymatch Q with
                          | ptsto_bytes ?p (instrencode ?i) => replace Q with (program RV32I p i)
                          end
      end.
      2: { eapply iff1ToEq. symmetry. eapply P; eassumption. }
      match goal with
      | |- context[?Q] => lazymatch Q with
                          | ptsto_bytes ?p (instrencode ?i) => replace Q with (program RV32I p i)
                          end
      end.
      2: {
        eapply iff1ToEq. symmetry. eapply P. 1: eassumption.
        constructor. 2: constructor.
        unfold verify. cbn. unfold verify_UJ. unfold opcode_JAL, RegisterNames.ra.
        split; [|trivial].
        split; [Lia.lia|].
        split; [Lia.lia|].
        ssplit; try eassumption.
        eapply mod4_to_mod2.
        repeat match goal with
               | H: word.unsigned _ mod 4 = 0 |- _ => unique pose proof (divisibleBy4Signed _ H)
               end.
        solve_divisibleBy4.
      }
      ssplit.
      all: cbn -[map.get map.empty instrencode].
      all: try eassumption.
      all: try reflexivity.
      match goal with
      | E1: execution _ _, E2: execution _ _ |- _ =>
        pose proof (execution_unique _ _ _ E1 E2); subst; clear E2
      end.
      eauto using initial_state_is_ready_state.
    }
    (* `related` holds at beginning: *)
    subst t.
    edestruct initial_state_exists as (sH & ? & ?). 1: eassumption.
    eapply mkRelated; simpl; eauto.
    Unshelve.
    all: do 2 constructor.
  Qed.

End WithParams.
