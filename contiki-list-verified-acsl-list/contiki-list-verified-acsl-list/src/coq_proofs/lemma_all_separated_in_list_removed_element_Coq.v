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
(* --- Lemma 'all_separated_in_list_removed_element'      --- *)
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

(* --- Global Definitions (continued #2) --- *)
Require Import Memory.
Require Import Vlist.

Require Import Axiomatic1.

Hypothesis Q_linked_ll_split_variant: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l_1 l : (list addr)),
  forall (a_1 a : addr), let a_2 := (concat l_1 (concat l nil)) in
  let a_3 := (nth a_2 ((length l_1))%Z) in ((nil) <> l) -> ((nil) <> l_1) ->
  ((P_linked_ll t t_1 a_1 a a_2)) ->
  (((P_linked_ll t t_1 a_1 a_3 l_1)) /\ ((P_linked_ll t t_1 a_3 a l))).

Require Import Compound.

Hypothesis Q_linked_ll_split: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l_1 l : (list addr)),
  forall (a_1 a : addr),
  let a_2 := t_1.[ (shiftfield_F1_list_next
                     ((nth l_1 (((length l_1))%Z - 1%Z)%Z))) ] in
  ((nil) <> l_1) -> ((P_linked_ll t t_1 a_1 a ((concat l_1 (concat l nil))))) ->
  (((P_linked_ll t t_1 a_1 a_2 l_1)) /\ ((P_linked_ll t t_1 a_2 a l))).

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

Goal
  forall (l_1 l : (list addr)),
  forall (a : addr),
  ((P_all_separated_in_list ((concat l_1 (cons a (concat l nil)))))) ->
  ((P_all_separated_in_list ((concat l_1 (concat l nil))))).

Proof.
  intros l1 l2 element.
  rewrite rw_nil_concat_right.
  intros H.
  intros x1 x2 Neq L2 L1 U2 U1.
  assert (H1: x1 < length(l1) \/ length(l1) <= x1 < length(l1)+length(l2)) by
    (rewrite Vlist.length_concat in U1 ; omega).
  assert (H2: x2 < length(l1) \/ length(l1) <= x2 < length(l1)+length(l2)) by
    (rewrite Vlist.length_concat in U2 ; omega).
  clear U1 U2.
  destruct H1 ; destruct H2 ;
  repeat match goal with
  | [ H: ?x < length l1 |- context [ nth (concat l1 l2) ?x ] ] =>
    replace (nth (concat l1 l2) x)
       with (nth l1 x)
         by (symmetry ; apply Vlist.nth_concat ; omega) ;
    replace (nth l1 x) with (nth (concat l1 (cons element l2)) x)
         by (apply Vlist.nth_concat ; omega)
  | [ H: length l1 <= ?x < length l1 + length l2 |- context [ nth (concat l1 l2) ?x ] ] =>
    replace (nth (concat l1 l2) x)
       with (nth l2 (x - length l1))
         by (symmetry ; apply Vlist.nth_concat ; omega) ;
    replace (nth l2 (x - length l1)) with (nth (concat l1 (cons element l2)) (x + 1)) by (
      replace (nth l2 (x - length l1)) with (nth (cons element l2) (x - length l1 + 1)) by (
        replace (x - length l1) with (x - length l1 + 1 - 1) by omega ;
        replace (x - length l1 + 1 - 1 + 1) with (x - length l1 + 1) by omega ;
        apply Vlist.nth_cons ; omega) ;
      replace (x - length l1 + 1) with (x + 1 - length l1) by omega ;
      apply Vlist.nth_concat ; omega)
  end ; try apply H ; try omega ;
  rewrite Vlist.length_concat ; 
  rewrite Vlist.length_cons ;
  assert(0 <= length l2) by apply length_pos ; omega.
Qed.

