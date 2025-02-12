(****************************************************************************)
(* Copyright 2020 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Cava.Cava.
Require Import Cava.CavaProperties.
Require Import Tests.CountBy.CountBy.

Existing Instance CombinationalSemantics.

Definition bvadd {n} (a b : Bvector n) : Bvector n :=
  N2Bv_sized n (Bv2N a + Bv2N b).

Definition bvsum {n} (l : list (Bvector n)) : Bvector n :=
  fold_left bvadd l (N2Bv_sized n 0).

Definition countBySpec (i : list (Bvector 8)) : list (Bvector 8) :=
  map (fun t => bvsum (firstn t i)) (seq 1 (length i)).

Lemma addNCorrect n (a b : Bvector n) :
  addN (a, b) = bvadd a b.
Admitted.
Hint Rewrite addNCorrect using solve [eauto] : simpl_ident.

Lemma bvadd_comm {n} a b : @bvadd n a b = bvadd b a.
Proof. cbv [bvadd]. rewrite N.add_comm. reflexivity. Qed.

Lemma countByCorrect: forall (i : list (Bvector 8)),
    simulate countBy i = countBySpec i.
Proof.
  intros; cbv [countBy mcompose]. autorewrite with push_simulate.
  cbn [step]. simpl_ident.
  eapply fold_left_accumulate_invariant_seq
    with (I:=fun t st acc =>
               st = (tt, bvsum (firstn t i))
               /\ acc = countBySpec (firstn t i)).
  { (* invariant holds at start *)
    ssplit; reflexivity. }
  { (* invariant holds through body *)
    cbv zeta. intros ? ? ? d; intros; logical_simplify; subst.
    cbv [step mcompose countBySpec]. simpl_ident.
    rewrite firstn_succ_snoc with (d0:=d) by length_hammer.
    cbv [combType Bvector] in *. autorewrite with push_length natsimpl.
    cbv [bvsum]. autorewrite with pull_snoc.
    rewrite bvadd_comm. split; [ reflexivity | ].
    rewrite Nat.add_1_r.
    autorewrite with pull_snoc.
    f_equal.
    { apply map_ext_in; intros.
      match goal with H : _ |- _ => apply in_seq in H end.
      autorewrite with push_length natsimpl push_firstn push_list_fold.
      reflexivity. }
    { cbn [Nat.add].
      autorewrite with push_nth push_firstn push_length push_list_fold natsimpl.
      reflexivity. } }
  { (* invariant implies postcondition *)
    intros; logical_simplify; subst.
    rewrite firstn_all; reflexivity. }
Qed.
