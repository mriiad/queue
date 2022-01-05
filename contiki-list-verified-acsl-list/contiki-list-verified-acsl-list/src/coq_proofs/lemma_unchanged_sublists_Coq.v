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
(* --- Lemma 'unchanged_sublists'                         --- *)
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

Goal
  forall (t_1 t : array Z),
  forall (t_3 t_2 : farray addr addr),
  forall (l_1 l : (list addr)),
  (((P_unchanged t_1 t_3 t t_2 l)) /\ ((P_unchanged t_1 t_3 t t_2 l_1))) <->
  ((P_unchanged t_1 t_3 t t_2 ((concat l_1 (concat l nil))))).

Proof.
  intros Mi1 Mi2 Ma1 Ma2 l1 l2.
  rewrite rw_nil_concat_right.
  split ; intros H.
  + inversion H as [ U2 U1 ].
    intros i a next BiInf BiSup.
    unfold a in * ; clear a.
    unfold next in * ; clear next.
    assert(Bi: i < length l1 \/ length l1 <= i) by omega.
    inversion_clear Bi as [ Inf | Sup ].
    - replace (nth (concat l1 l2) i) with (nth l1 i) 
           by (symmetry ; apply Vlist.nth_concat ; omega).
      apply U1 ; omega.
    - replace (nth (concat l1 l2) i) with (nth l2 (i - length l1))
           by (symmetry ; apply Vlist.nth_concat ; omega).
      rewrite Vlist.length_concat in BiSup.
      apply U2 ; omega.
  + split ; intros i a next BiInf BiSup ;
      unfold a in * ; clear a ;
      unfold next in * ; clear next.
    - replace (nth l2 i) with (nth (concat l1 l2) (length l1 + i)).
      apply H.
      * assert (0 <= length l1) by apply length_pos.
        omega.
      * rewrite Vlist.length_concat.
        omega.
      * replace i with (i + length l1 - length l1) by omega.
        replace (length l1 + (i + length l1 - length l1)) with (i + length l1) by omega.
        apply Vlist.nth_concat ; omega.
    - replace (nth l1 i) with (nth (concat l1 l2) i) by (apply Vlist.nth_concat ; omega).
      apply H.
      * omega.
      * rewrite Vlist.length_concat.
        assert (0 <= length l2) by apply length_pos.
        omega.
Qed.

