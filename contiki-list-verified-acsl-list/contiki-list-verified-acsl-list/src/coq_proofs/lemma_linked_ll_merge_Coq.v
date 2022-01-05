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
(* --- Lemma 'linked_ll_merge'                               --- *)
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
Require Import Vlist.
Require Import Memory.

Require Import Axiomatic1.
Require Import Axiomatic.

Hypothesis Q_all_separated_in_list_added_element: forall (l_1 l
                                                    : (list addr)),
  forall (a : addr), let a_1 := (concat l_1 (concat l nil)) in
  ((P_all_separated_in_list a_1)) -> ((P_ptr_separated_from_list a a_1)) ->
  ((P_all_separated_in_list ((concat l_1 (cons a (concat l nil)))))).

Hypothesis Q_all_separated_in_list_removed_element: forall (l_1 l
                                                      : (list addr)),
  forall (a : addr),
  ((P_all_separated_in_list ((concat l_1 (cons a (concat l nil)))))) ->
  ((P_all_separated_in_list ((concat l_1 (concat l nil))))).

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
  forall (t : array Z),
  forall (t_1 : farray addr addr),
  forall (l_1 l : (list addr)),
  forall (a_2 a_1 a : addr),
  let a_3 := (concat l_1 (concat l nil)) in
  ((P_ptr_separated_from_list a l_1)) ->
  ((separated a_2 2%Z a 2%Z)) ->
  ((P_all_separated_in_list a_3)) ->
  ((P_linked_ll t t_1 a_1 a l)) ->
  ((P_linked_ll t t_1 a_2 a_1 l_1)) ->
  ((P_linked_ll t t_1 a_2 a a_3)).

Proof.
  intros Mi Ma l1 l2 bl sl el ll.
  unfold ll ; clear ll.
  rewrite rw_nil_concat_right.
  revert l2 bl sl el.
  induction l1 as [ | hd1 l1' ].
  + intros l2 bl sl el Sep_end sep All_sep NoDup2 NoDup1.
    replace Datatypes.nil with nil in * by reflexivity.
    rewrite rw_nil_concat_left.
    inversion NoDup1 ; subst ; auto.
  + destruct l1' as [ | snd1 l1'' ].
    - intros l2 bl sl el Sep_end sep All_sep NoDup2 NoDup1.
      simpl in * .
      replace (hd1 :: l2)%list with (cons hd1 l2) in * by reflexivity.
      inversion NoDup1 ; subst.
      replace l2 with (concat l2 nil) by apply rw_nil_concat_right.
      constructor ; auto.
      * replace hd1 with (nth (cons hd1 l2) 0) by (unfold nth ; auto).
        intros i ; intros.
        replace (nth l2 i) with (nth (cons hd1 l2) (i+1)).
        ++ apply All_sep ; try (rewrite Vlist.length_cons) ; omega.
        ++ replace i with (i + 1 - 1) by omega.
           replace (i + 1 - 1 + 1) with (i + 1) by omega.
           apply Vlist.nth_cons ; omega.
      * replace Datatypes.nil with nil in * by reflexivity.
        rewrite rw_nil_concat_right in H0 ; subst ; inversion H8 ; subst ; auto.
    - replace (snd1 :: l1'')%list with (cons snd1 l1'') in * by reflexivity.
      set(l1' := cons snd1 l1'').
      replace (hd1 :: l1')%list with (cons hd1 l1') in * by reflexivity.
      intros l2 bl sl el Sep_end sep All_sep NoDup2 NoDup1.
      rewrite rw_cons_concat.
      inversion NoDup1 ; subst.
      rewrite rw_nil_concat_right in H0 ; subst.
      rewrite rw_nil_concat_right.
      replace (concat l1' l2) with (concat (concat l1' l2) nil)
           by apply rw_nil_concat_right.
      constructor ; auto.
      * rewrite rw_cons_concat in All_sep.
        replace hd1 with (nth (cons hd1 (concat l1' l2)) 0) by (unfold nth ; auto).
        intros i ; intros.
        replace (nth (concat l1' l2) i) with (nth (cons hd1 (concat l1' l2)) (i+1)).
        ++ apply All_sep ; try (rewrite Vlist.length_cons) ; omega.
        ++ replace i with (i + 1 - 1) by omega.
           replace (i + 1 - 1 + 1) with (i + 1) by omega.
           apply Vlist.nth_cons ; omega.
      * apply IHl1' with (sl := sl) ; auto.
        ++ intros i ; intros.
           replace (nth (cons snd1 l1'') i) with (nth (cons hd1 l1') (i+1)).
           -- apply Sep_end ; try omega.
              rewrite Vlist.length_cons ; unfold l1' ; omega.
           -- replace i with (i + 1 - 1) by omega.
              replace (i + 1 - 1 + 1) with (i + 1) by omega.
              unfold l1' ; apply Vlist.nth_cons ; omega.
        ++ unfold l1' in * ; inversion H8 ; subst.
           replace (Ma .[ shiftfield_F1_list_next hd1])
              with (nth (cons hd1 (cons (Ma .[ shiftfield_F1_list_next hd1]) (concat l nil))) 1)
                by (unfold nth ; auto).
           apply Sep_end ; try omega.
           repeat(rewrite Vlist.length_cons).
           assert(0 <= length (concat l nil)) by apply Vlist.length_pos ; omega.
        ++ rewrite rw_cons_concat in All_sep.
           intros n1 n2 ; intros.
           replace (nth (concat (cons snd1 l1'') l2) n1) with 
                   (nth (cons hd1 (concat (cons snd1 l1'') l2)) (n1+1)).
           replace (nth (concat (cons snd1 l1'') l2) n2) with 
                   (nth (cons hd1 (concat (cons snd1 l1'') l2)) (n2+1)).
           apply All_sep ; try (rewrite Vlist.length_cons ; unfold l1') ; omega.
           -- replace n2 with (n2 + 1 - 1) by omega.
              replace (n2 + 1 - 1 + 1) with (n2 + 1) by omega.
              apply Vlist.nth_cons ; omega.
           -- replace n1 with (n1 + 1 - 1) by omega.
              replace (n1 + 1 - 1 + 1) with (n1 + 1) by omega.
              apply Vlist.nth_cons ; omega.
Qed.

