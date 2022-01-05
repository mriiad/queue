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
(* --- Post-condition 'EASY_Left' at block                --- *)
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

Require Import Axiomatic1.
Require Import Memory.
Require Import Compound.
Require Import A_To_ll.
Require Import Vlist.
Require Import Axiomatic.

Goal
  forall (t : array Z),
  forall (t_2 t_1 : farray addr addr),
  forall (a_3 a_2 a_1 a : addr),
  let a_4 := (shiftfield_F1_list_next a_1) in
  let a_5 := t_2.[ a_4 ] in
  let m := t_1.[ a_3 <- a ] in
  let a_6 := m.[ a_4 ] in
  let a_7 := (shiftfield_F1_list_next a_2) in
  let a_8 := m.[ a_7 ] in
  let a_9 := t_2.[ a_7 ] in
  let a_10 := (L_to_logic_list t m a_6 (null)) in
  let a_11 := (L_to_logic_list t t_2 a_5 (null)) in
  let a_12 := t_2.[ a_3 ] in
  let a_13 := (L_to_logic_list t t_2 a_12 a_2) in
  let a_14 := (L_to_logic_list t t_2 a_2 (null)) in
  let a_15 := (concat a_13 (concat a_14 nil)) in
  let a_16 := (L_to_logic_list t t_2 a_8 (null)) in
  let a_17 := (concat a_13 (concat a_16 nil)) in
  let a_18 := (L_to_logic_list t t_2 a_9 a_5) in
  let a_19 := (concat a_18 (concat a_11 nil)) in
  let a_20 := (L_to_logic_list t m a a_6) in
  let x := ((length a_16))%Z in
  let a_21 := (L_to_logic_list t t_2 a_12 a_5) in
  let a_22 := (L_to_logic_list t t_2 a_5 a_2) in
  ((null) <> a_1) ->
  (a_5 <> a_2) ->
  (a_6 = a_5) ->
  (a_8 = a_9) ->
  (a_10 = a_11) ->
  (((L_to_logic_list t t_2 a_12 (null))) = a_15) ->
  (((L_to_logic_list t m a (null))) = a_17) ->
  (((L_to_logic_list t t_2 a_9 (null))) = a_19) ->
  (((concat a_13
      (concat ((L_to_logic_list t t_2 a_9 a_6))
        (concat ((L_to_logic_list t t_2 a_6 (null))) nil)))) =
   ((concat a_20 (concat a_10 nil)))) ->
  (((1 + x) = ((length a_14)))%Z) ->
  ((((region ((base a_1))%Z)) <= 0)%Z) ->
  ((((region ((base a_2))%Z)) <= 0)%Z) ->
  ((((region ((base a_3))%Z)) <= 0)%Z) ->
  (((((length a_13)) + x) <= 2147483645)%Z) ->
  ((framed t_2)) ->
  ((linked t)) ->
  ((valid_rw t a_2 2%Z)) ->
  ((valid_rw t a_3 1%Z)) ->
  ((separated a_1 2%Z a_2 2%Z)) ->
  ((separated a_3 1%Z a_1 2%Z)) ->
  ((separated a_3 1%Z a_2 2%Z)) ->
  ((P_in_list a_1 a_14)) ->
  ((P_linked_ll t t_2 a_2 (null) a_14)) ->
  ((P_dptr_separated_from_list a_3 a_15)) ->
  ((P_in_list a_1 a_15)) ->
  ((P_in_list a_2 a_15)) ->
  ((P_linked_ll t t_2 a_12 a_2 a_13)) ->
  ((P_ptr_separated_from_list a_2 a_17)) ->
  ((P_dptr_separated_from_list a_3 a_17)) ->
  ((P_in_list a_1 a_19)) ->
  ((P_linked_ll t t_2 a_12 (null) a_15)) ->
  ((P_linked_ll t t_2 a_9 (null) a_19)) ->
  ((P_linked_ll t m a (null) a_17)) ->
  ((a_12 <> a_2) -> (a_12 = a)) ->
  ((a_12 = a_2) -> (a_9 = a)) ->
  (((P_in_list a_1 a_13)) -> (a_20 = a_21)) ->
  (((P_in_list a_5 a_15)) -> (((concat a_21 (concat a_11 nil))) = a_15)) ->
  (((P_in_list a_1 a_13)) -> (a_13 = ((concat a_21 (concat a_22 nil))))) ->
  (((P_in_list a_1 a_13)) ->
   (a_10 = ((concat a_22 (concat a_18 (concat a_11 nil)))))) ->
  (((P_in_list a_5 a_15)) -> ((P_linked_ll t t_2 a_12 a_5 a_21))) ->
  (((P_in_list a_5 a_15)) -> ((P_linked_ll t t_2 a_5 (null) a_11))) ->
  (((P_ptr_separated_from_list a_5 a_15)) \/ ((P_in_list a_5 a_15))) ->
  ((a_5 = (null)) \/ ((P_in_list a_5 a_19))) ->
  (forall (a_23 : addr), let a_24 := (shiftfield_F1_list_next a_23) in
   ((t_2.[ a_24 ]) = a_2) -> ((P_in_list a_23 a_15)) -> (a_8 = (m.[ a_24 ]))) ->
  (forall (a_23 : addr), (a_2 <> a_23) ->
   (((P_in_list a_23 a_17)) <-> ((P_in_list a_23 a_15)))) ->
  (forall (a_23 : addr),
   (forall (a_24 : addr), let a_25 := (shiftfield_F1_list_next a_24) in
    ((t_2.[ a_25 ]) = a_2) -> ((P_in_list a_24 a_15)) -> (a_25 <> a_23)) ->
   ((t_2.[ a_23 ]) = (t_1.[ a_23 ]))) ->
  (a_20 = ((concat a_13 (concat a_18 nil)))).

Proof.
  intros.
  symmetry in H7.
  unfold a_18.
  subst.
  repeat rewrite rw_nil_concat_right.
  repeat rewrite rw_nil_concat_right in H7.
  rewrite H1 in H7.
  rewrite H3 in H7.
  assert(HH: forall l1 l2 l3, concat l2 l1 = concat l3 l1 -> l2 = l3). {
    apply List.app_inv_tail.
  }
  replace (concat a_13 (concat (L_to_logic_list t t_2 a_9 a_5) (L_to_logic_list t t_2 a_5 null)))
     with (concat (concat a_13 (L_to_logic_list t t_2 a_9 a_5)) (L_to_logic_list t t_2 a_5 null))
       in H7.
  unfold a_11 in H7.
  apply HH in H7 ; auto.
  symmetry ; apply List.app_assoc.
Qed.

