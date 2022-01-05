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
(* --- Lemma 'separated_linked_ll_append'                    --- *)
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

Require Import Axiomatic.
Require Import Compound.

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
  forall (l : (list addr)),
  forall (a_1 a : addr),
  let a_2 := t_1.[ (shiftfield_F1_list_next a) ] in
  ((valid_rw t a 2%Z)) ->
  ((P_ptr_separated_from_list a_2 l)) ->
  ((P_linked_ll t t_1 a_1 a l)) ->
  ((separated a 2%Z a_2 2%Z)) ->
  ((P_linked_ll t t_1 a_1 a_2 ((concat l (cons a nil))))).

Proof.
  intros Mi Ma ll bl el nel Valid Sep NoDup.
  generalize dependent Sep.
  induction NoDup ; intros Sep sep_a_nel.
  + simpl ; replace nil with (concat nil nil) by (simpl ; reflexivity).
    constructor ; try apply Q_ptr_separated_from_nil ; auto ; constructor.
  + replace (concat (cons a_1 (concat l nil)) (cons a nil))
       with (cons a_1 (concat (concat l (cons a nil)) nil)).
    - replace (cons a nil) with (concat (cons a nil) nil) by (simpl ; reflexivity).
      constructor ; auto.
      * rewrite <- Q_ptr_separated_concat ; split ; auto.
        intros i ; intros LL Li Ui UU ; unfold cons in *.
        assert(i = 0) by (unfold length in Ui ; simpl in Ui ; omega) ; subst.
        simpl ; apply separated_sym ; auto.
      * rewrite <- Q_ptr_separated_from_cons in Sep.
        apply Sep.
      * apply IHNoDup ; auto.
        rewrite <- Q_ptr_separated_from_cons in Sep.
        apply Sep.
    - repeat(rewrite rw_nil_concat_right).
      rewrite rw_cons_concat.
      reflexivity.
Qed.

