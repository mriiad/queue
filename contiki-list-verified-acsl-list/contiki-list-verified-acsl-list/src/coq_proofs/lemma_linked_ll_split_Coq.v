(*
  Copyright (c) 2018, Inria, CEA, Northern Arizona University.
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:
  1. Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
  2. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimer in the
     documentation and/or other materials provided with the distribution.
  3. Neither the name of the Institute nor the names of its contributors
     may be used to endorse or promote products derived from this software
     without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
  ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
  ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
  FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
  OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
  HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
  OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
  SUCH DAMAGE.

  This file is part of the verification of the Contiki operating system.

  Authors: - Allan Blanchard <mail@allan-blanchard.fr>
           - Nikolai Kosmatov <nikolai.kosmatov@cea.fr>
           - Frédéric Loulergue <frederic.loulergue@nau.edu>
*)

(* ---------------------------------------------------------- *)
(* --- Lemma 'linked_ll_split'                               --- *)
(* ---------------------------------------------------------- *)
Require Import ZArith.
Require Import Reals.
Require Import BuiltIn.
Require Import int.Int.
Require Import int.Abs.
Require Import int.ComputerDivision.
Require Import real.Real.
Require Import real.RealInfix.
Require Import real.FromInt.
Require Import map.Map.
Require Import Qedlib.
Require Import Qed.

(* --- Global Definitions (continued #1) --- *)
Require Import Memory.
Require Import Vlist.

Require Import Compound.
Require Import Axiomatic.

Hypothesis Q_in_next_not_bound_in: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_2 a_1 a : addr),
  let a_3 := t_1.[ (shiftfield_F1_list_next a) ] in (a_3 <> a_1) ->
  ((P_in_list a l)) -> ((P_linked_ll t t_1 a_2 a_1 l)) -> ((P_in_list a_3 l)).

Hypothesis Q_n_plus_1th_next: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) ->
  (forall (i : Z), ((0 <= i)%Z) -> (((2 + i) <= ((length l)))%Z) ->
   ((t_1.[ (shiftfield_F1_list_next ((nth l i%Z))) ]) =
    ((nth l (1%Z + i%Z)%Z)))).

Hypothesis Q_linked_ll_end: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((nil) <> l) -> ((P_linked_ll t t_1 a_1 a l)) ->
  ((t_1.[ (shiftfield_F1_list_next ((nth l (((length l))%Z - 1%Z)%Z))) ]) =
   a).

Hypothesis Q_separated_linked_ll_append: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), let a_2 := t_1.[ (shiftfield_F1_list_next a) ] in
  ((valid_rw t a 2%Z)) -> ((P_ptr_separated_from_list a_2 l)) ->
  ((P_linked_ll t t_1 a_1 a l)) -> ((separated a 2%Z a_2 2%Z)) ->
  ((P_linked_ll t t_1 a_1 a_2 ((concat l (cons a nil))))).

Hypothesis Q_inversion_linked_ll: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) ->
  (((a_1 = a) /\ ((nil) = l)) \/
   (exists l_1 : (list addr), (a_1 <> a) /\
    (((cons a_1 (concat l_1 nil))) = l) /\
    ((P_ptr_separated_from_list a_1 l_1)) /\ ((valid_rw t a_1 2%Z)) /\
    ((separated a_1 2%Z a 2%Z)) /\
    ((P_linked_ll t t_1 (t_1.[ (shiftfield_F1_list_next a_1) ]) a l_1)))).

Hypothesis Q_dptr_separated_concat: forall (l_1 l : (list addr)),
  forall (a : addr),
  (((P_dptr_separated_from_list a l)) /\
   ((P_dptr_separated_from_list a l_1))) <->
  ((P_dptr_separated_from_list a ((concat l_1 (concat l nil))))).

Hypothesis Q_dptr_separated_from_cons: forall (l : (list addr)),
  forall (a_1 a : addr),
  (((P_dptr_separated_from_list a_1 l)) /\ ((separated a 2%Z a_1 1%Z))) <->
  ((P_dptr_separated_from_list a_1 ((cons a (concat l nil))))).

Hypothesis Q_dptr_separated_from_nil: forall (a : addr),
  (P_dptr_separated_from_list a (nil)).

Hypothesis Q_ptr_separated_concat: forall (l_1 l : (list addr)),
  forall (a : addr),
  (((P_ptr_separated_from_list a l)) /\ ((P_ptr_separated_from_list a l_1))) <->
  ((P_ptr_separated_from_list a ((concat l_1 (concat l nil))))).

Hypothesis Q_ptr_separated_from_cons: forall (l : (list addr)),
  forall (a_1 a : addr),
  (((P_ptr_separated_from_list a_1 l)) /\ ((separated a 2%Z a_1 2%Z))) <->
  ((P_ptr_separated_from_list a_1 ((cons a (concat l nil))))).

Hypothesis Q_ptr_separated_from_nil: forall (a : addr),
  (P_ptr_separated_from_list a (nil)).

Hypothesis Q_in_list_in_sublist: forall (l_1 l : (list addr)),
  forall (a : addr), (((P_in_list a l)) \/ ((P_in_list a l_1))) <->
  ((P_in_list a ((concat l_1 (concat l nil))))).

Hypothesis Q_unchanged_sublists: forall (t_1 t : array Z),
  forall (t_3 t_2 : farray addr addr), forall (l_1 l : (list addr)),
  (((P_unchanged t_1 t_3 t t_2 l)) /\ ((P_unchanged t_1 t_3 t t_2 l_1))) <->
  ((P_unchanged t_1 t_3 t t_2 ((concat l_1 (concat l nil))))).

Goal
  forall (t : array Z),
  forall (t_1 : farray addr addr),
  forall (l_1 l : (list addr)),
  forall (a_1 a : addr),
  let a_2 := t_1.[ (shiftfield_F1_list_next
                     ((nth l_1 (((length l_1))%Z - 1%Z)%Z))) ] in
  ((nil) <> l_1) ->
  ((P_linked_ll t t_1 a_1 a ((concat l_1 (concat l nil))))) ->
  (((P_linked_ll t t_1 a_1 a_2 l_1)) /\ ((P_linked_ll t t_1 a_2 a l))).

Proof.
  Ltac back := repeat match goal with 
   | [ H: context [ (?hd :: ?l)%list ] |- _ ] =>
     replace (hd :: l)%list with (cons hd l) in H by reflexivity
   | [ |- context [ (?hd :: ?l)%list ] ] =>
     replace (hd :: l)%list with (cons hd l) by reflexivity
   | [ H: context [ Datatypes.nil ] |- _ ] =>
     replace Datatypes.nil with nil in H by reflexivity
   | [ |- context [ Datatypes.nil ] ] =>
     replace Datatypes.nil with nil by reflexivity
  end.

  intros Mi Ma l1 l2 bl el sl.
  unfold sl ; clear sl.
  revert l2 bl el.
  induction l1 as [ | hd l1' ] ; back ; [ congruence |].
  destruct l1' as [ | snd1 l1'' ] ; back.
  - intros l2 bl el Hnil NoDup.
    unfold nth, length ; simpl ; split.
    + replace nil with (concat nil nil) by apply rw_nil_concat_right.
      inversion NoDup as [| a b l d e Sep Valid sep NoDup' ] ; subst.
      constructor ; auto.
      * apply Q_ptr_separated_from_nil.
      * repeat(rewrite rw_nil_concat_right in H4) ; subst.
        inversion NoDup' ; subst ; auto.
        replace (Ma.[ shiftfield_F1_list_next hd])
           with (nth (cons (Ma .[ shiftfield_F1_list_next hd]) (concat l nil)) 0)
             by (unfold nth ; auto).
        apply separated_sym ; apply Sep ; try omega.
        rewrite Vlist.length_cons.
        assert(0 <= length (concat l nil)) by apply Vlist.length_pos ; omega.
      * constructor.
    + rewrite rw_cons_concat in NoDup.
      rewrite rw_nil_concat_left in NoDup.
      inversion NoDup ; subst.
      repeat(rewrite rw_nil_concat_right in H0) ; subst ; auto.
  - intros l2 bl el Hnil NoDup.
    rewrite Vlist.length_cons.
    set(l1' := cons snd1 l1'').
    destruct l2 as [ | hd2 l2' ] ; inversion NoDup ; subst ; back ;
      replace (1 + length l1' - 1) with (length l1') by omega.
    + rewrite <- rw_cons_concat in H0 ; repeat(rewrite rw_nil_concat_right in H0) ; subst.
      repeat(rewrite rw_nil_concat_right in NoDup).
      replace(Ma .[ shiftfield_F1_list_next (nth (cons hd l1') (length l1'))]) with el.
      replace l1' with (concat l1' nil) by apply rw_nil_concat_right.
      split ; constructor ; auto.
      apply Q_linked_ll_end in H8 ; subst.
      * replace (nth (cons hd l1') (length l1')) with (nth l1' (length l1' -1)).
        unfold l1' ; rewrite Vlist.length_cons ; auto.
        symmetry ; apply Vlist.nth_cons ; unfold l1' ; rewrite Vlist.length_cons.
        assert(0 <= length l1'') by apply Vlist.length_pos ; omega.
      * intros HF ; inversion HF.
    + repeat(rewrite rw_nil_concat_right in H0).
      set(l2 := cons hd2 l2').
      replace (nth (cons hd l1') (length l1')) with (nth l1' (length l1' - 1))
           by (symmetry ; apply Vlist.nth_cons ; unfold l1' ; intros HF ; inversion HF).
      set(sl := Ma .[ shiftfield_F1_list_next (nth l1' (length l1' - 1))]).
      assert(P_linked_ll Mi Ma (Ma .[ shiftfield_F1_list_next hd]) sl l1' /\ P_linked_ll Mi Ma sl el l2 ->
             P_linked_ll Mi Ma hd sl (cons hd l1') /\ P_linked_ll Mi Ma sl el l2). {
        split ; [ | apply H ].
        replace l1' with (concat l1' nil) by apply rw_nil_concat_right.
        constructor ; auto ; [ | | apply H ].
        + intros i LL Li Ui Eq.
          rewrite <- rw_cons_concat in H0.
          repeat(rewrite rw_nil_concat_right in H0).
          replace (nth l1' i) with (nth l i).
          apply H1 ; auto ; try omega.
          - subst ; rewrite Vlist.length_concat.
            assert (0 <= length (cons hd2 l2')) by apply Vlist.length_pos ; unfold l1' in * ; omega.
          - subst ; unfold l1'.
            apply Vlist.nth_concat ; unfold l1' in Ui ; auto.
        + unfold sl.
          replace (nth l1' (length l1' - 1)) with (nth l (length l1' - 1)).
          - rewrite Q_n_plus_1th_next 
                    with (t := Mi)(a_1 := Ma .[ shiftfield_F1_list_next hd])(a := el) ; auto.
            * replace (1 + (length l1' - 1)) with (length l1') by omega.
              apply separated_sym ; apply H1 ; try omega.
              ++ apply length_pos.
              ++ subst ; unfold l1' ; rewrite <- rw_cons_concat.
                 rewrite Vlist.length_concat.
                 repeat(rewrite Vlist.length_cons).
                 assert (0 <= length l2') by apply Vlist.length_pos ; omega.
            * unfold l1' ; rewrite Vlist.length_cons.
              assert(0 <= length l1'') by apply Vlist.length_pos ; omega.
            * unfold l1' in *  ; subst.
              repeat(rewrite Vlist.length_cons).
              rewrite Vlist.length_concat.
              rewrite Vlist.length_cons.
              assert (0 <= length l2') by apply Vlist.length_pos ; omega.
          - rewrite <- rw_cons_concat in H0 ; subst.
            apply Vlist.nth_concat ; omega.
      }
      apply H.
      apply IHl1'.
      * intros HF ; inversion HF.
      * unfold l1' ; unfold l2.
        repeat(rewrite rw_nil_concat_right) ; rewrite rw_cons_concat.
        inversion NoDup ; subst ; back.
        repeat(rewrite rw_nil_concat_right in H3) ; auto.
Qed.

