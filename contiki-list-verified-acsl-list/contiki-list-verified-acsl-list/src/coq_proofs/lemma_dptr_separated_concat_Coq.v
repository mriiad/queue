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
(* --- Lemma 'dptr_separated_concat'                      --- *)
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

Require Import Axiomatic.

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
  (((P_dptr_separated_from_list a l)) /\
   ((P_dptr_separated_from_list a l_1))) <->
  ((P_dptr_separated_from_list a ((concat l_1 (concat l nil))))).

Proof.
  intros l1 ; induction l1 as [| h1 l1] ; intros l2 e.
  + replace Datatypes.nil with nil by reflexivity.
    rewrite rw_nil_concat_right.
    rewrite rw_nil_concat_left.
    repeat (split ; intros) ; try apply H ; apply Q_dptr_separated_from_nil.
  + replace ((h1 :: l1)%list) with (cons h1 l1) by reflexivity.
    rewrite rw_cons_concat.
    replace (cons h1 (concat l1 (concat l2 nil))) 
       with (cons h1 (concat (concat l1 (concat l2 nil)) nil))
         by (repeat(rewrite rw_nil_concat_right) ; auto).
    split ; intros H.
    - rewrite <- Q_dptr_separated_from_cons.
      replace l1 with (concat l1 nil) in H by (apply rw_nil_concat_right).
      rewrite <- Q_dptr_separated_from_cons in H.
      split ; try (rewrite <- IHl1 ; split) ; apply H.
    - rewrite <- Q_dptr_separated_from_cons in H.
      rewrite <- IHl1 in H.
      replace l1 with (concat l1 nil) by (apply rw_nil_concat_right).
      split ; try (rewrite <- Q_dptr_separated_from_cons ; split) ; apply H.
Qed.

