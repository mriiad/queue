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
(* --- Lemma 'in_list_in_sublist'                         --- *)
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

Goal
  forall (l_1 l : (list addr)),
  forall (a : addr),
  (((P_in_list a l)) \/ ((P_in_list a l_1))) <->
  ((P_in_list a ((concat l_1 (concat l nil))))).

Proof.
  intros rl ll l.
  rewrite rw_nil_concat_right.
  assert(Lenl: 0 <= length ll) by apply Vlist.length_pos.
  assert(Lenr: 0 <= length rl) by apply Vlist.length_pos.
  split ; intros H.
  + inversion_clear H as [ H' | H' ] ; inversion H' as [ v P ] ;
      [ exists (v + length rl) | exists v ] ; 
      split ; try( rewrite Vlist.length_concat ; omega ) ;
      inversion_clear P as [ Nth Bound ].
    - replace v with (v + length rl - length rl) in Nth by omega.
      rewrite <- Nth.
      apply Vlist.nth_concat ; omega.
    - rewrite <- Nth.
      apply Vlist.nth_concat ; omega.
  + inversion H as [ v P ] ; inversion_clear P as[ Nth Len ].
    rewrite Vlist.length_concat in Len.
    assert (Cases: 0 <= v < length rl \/ length rl <= v < length ll + length rl) by omega.
    inversion_clear Cases as [ R | L ].
    - right ; exists v ; split ; auto.
      rewrite <- Nth ; symmetry ; apply Vlist.nth_concat ; omega.
    - left ; exists (v - length rl) ; split ; try omega.
      rewrite <- Nth ; symmetry ; apply Vlist.nth_concat ; omega.
Qed.

