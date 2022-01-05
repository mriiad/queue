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
(* --- Lemma 'dptr_separated_from_cons'                   --- *)
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

Require Import Axiomatic.
Require Import Vlist.

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
  forall (l : (list addr)),
  forall (a_1 a : addr),
  (((P_dptr_separated_from_list a_1 l)) /\ ((separated a 2%Z a_1 1%Z))) <->
  ((P_dptr_separated_from_list a_1 ((cons a (concat l nil))))).

Proof.
  intros l ; induction l ; intros e hd ; simpl.
  + unfold cons.
    repeat(split ; intros).
    - intros i ; intros.
      assert(i = 0) by (unfold length in * ; simpl in *  ; omega) ; subst.
      simpl ; apply H.
    - apply Q_dptr_separated_from_nil.
    - unfold P_dptr_separated_from_list in H.
      assert (hd = nth (hd :: nil)%list 0) by (simpl ; auto).
      rewrite H0 ; apply H ; unfold length ; simpl ; auto ; omega.
  + unfold cons, concat.
    rewrite List.app_nil_r.
    replace ((a :: l)%list) with (cons a l) by reflexivity.
    replace l with (concat l nil) by (rewrite rw_nil_concat_right ; auto).
    replace ( (hd :: cons a (concat l nil))%list)
       with (cons hd (cons a (concat l nil)))
         by reflexivity.
    repeat(split ; intros).
    - intros i LL Li Ui.
      assert (i = 0 \/ i <> 0) by omega.
      inversion_clear H0 as [ Eq | Neq ] ; intros.
      * subst ; simpl ; apply H.
      * replace (nth (cons hd (cons a (concat l nil))) i)
           with (nth (cons a (concat l nil)) (i - 1))
             by (symmetry ; apply Vlist.nth_cons ; omega).
        apply H ; rewrite Vlist.length_cons in Ui ; omega.
    - intros i LL Li Ui ; intros.
      replace i with (i + 1 - 1) by omega.
      replace (nth (cons a (concat l nil)) (i + 1 - 1))
         with (nth (cons hd (cons a (concat l nil))) (i + 1))
           by (apply Vlist.nth_cons ; omega).
      apply H ; try rewrite Vlist.length_cons ; omega.
    - assert (hd = nth (cons hd (cons a (concat l nil)))%list 0) by (simpl ; auto).
      rewrite H0 ; apply H ; try omega.
      rewrite Vlist.length_cons.
      assert (0 <= length (cons a (concat l nil))) by apply Vlist.length_pos.
      omega.
Qed.

