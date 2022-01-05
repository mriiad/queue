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
(* --- Lemma 'to_logic_list_merge'                        --- *)
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

Require Import A_To_ll.
Require Import Axiomatic.

Hypothesis Q_to_logic_list_split: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (a_2 a_1 a : addr),
  let a_3 := (L_to_logic_list t t_1 a_2 a_1) in (a_3 <> (nil)) ->
  ((P_in_list a a_3)) -> ((P_linked_ll t t_1 a_2 a_1 a_3)) ->
  (a_3 =
   ((concat ((L_to_logic_list t t_1 a_2 a))
      (concat ((L_to_logic_list t t_1 a a_1)) nil)))).

Require Import Compound.

Hypothesis Q_separated_to_logic_list_append: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (a_1 a : addr),
  let a_2 := t_1.[ (shiftfield_F1_list_next a) ] in
  let a_3 := (L_to_logic_list t t_1 a_1 a) in ((valid_rw t a 2%Z)) ->
  ((separated a 2%Z a_2 2%Z)) -> ((P_ptr_separated_from_list a_2 a_3)) ->
  ((P_linked_ll t t_1 a_1 a a_3)) ->
  (((L_to_logic_list t t_1 a_1 a_2)) = ((concat a_3 (cons a nil)))).

Require Import Axiomatic1.

Hypothesis Q_to_logic_list_unchanged: forall (t_1 t : array Z),
  forall (t_3 t_2 : farray addr addr), forall (a_1 a : addr),
  let a_2 := (L_to_logic_list t t_2 a_1 a) in ((P_linked_ll t t_2 a_1 a a_2)) ->
  ((P_unchanged t_1 t_3 t t_2 a_2)) ->
  (((L_to_logic_list t_1 t_3 a_1 a)) = a_2).

Hypothesis Q_linked_ll_to_logic_list: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) ->
  (((L_to_logic_list t t_1 a_1 a)) = l).

Hypothesis Q_linked_ll_nth_separated_before_after: forall (i : Z),
  forall (t : array Z), forall (t_1 : farray addr addr),
  forall (l : (list addr)), forall (a_1 a : addr), let x := ((length l))%Z in
  let a_2 := (nth l i%Z) in ((0 <= i)%Z) -> ((i < x)%Z) ->
  ((P_linked_ll t t_1 a_1 a l)) ->
  (((P_ptr_separated_from_range a_2 l 0%Z i%Z)) /\
   ((P_ptr_separated_from_range a_2 l (1%Z + i%Z)%Z x))).

Hypothesis Q_linked_ll_end_separated: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) ->
  ((P_ptr_separated_from_list a l)).

Hypothesis Q_linked_ll_end_not_in: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) -> (~((P_in_list a l))).

Hypothesis Q_linked_ll_all_separated: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) ->
  ((P_all_separated_in_list l)).

Hypothesis Q_linked_ll_in_valid_with_exists: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) ->
  (forall (a_2 : addr), ((P_in_list a_2 l)) -> ((valid_rw t a_2 2%Z))).

Hypothesis Q_linked_ll_in_valid: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) ->
  (forall (i : Z), ((0 <= i)%Z) -> ((i < ((length l)))%Z) ->
   ((valid_rw t ((nth l i%Z)) 2%Z))).

Hypothesis Q_linked_ll_unique_list: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l_1 l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_1 a_1 a l)) ->
  ((P_linked_ll t t_1 a_1 a l_1)) -> (l_1 = l).

Hypothesis Q_linked_ll_unchanged: forall (t_1 t : array Z),
  forall (t_3 t_2 : farray addr addr), forall (l : (list addr)),
  forall (a_1 a : addr), ((P_linked_ll t t_2 a_1 a l)) ->
  ((P_unchanged t_1 t_3 t t_2 l)) -> ((P_linked_ll t_1 t_3 a_1 a l)).

Hypothesis Q_linked_ll_merge: forall (t : array Z),
  forall (t_1 : farray addr addr), forall (l_1 l : (list addr)),
  forall (a_2 a_1 a : addr), let a_3 := (concat l_1 (concat l nil)) in
  ((P_ptr_separated_from_list a l_1)) -> ((separated a_2 2%Z a 2%Z)) ->
  ((P_all_separated_in_list a_3)) -> ((P_linked_ll t t_1 a_1 a l)) ->
  ((P_linked_ll t t_1 a_2 a_1 l_1)) -> ((P_linked_ll t t_1 a_2 a a_3)).

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
  forall (a_2 a_1 a : addr),
  let a_3 := (L_to_logic_list t t_1 a_2 a_1) in
  let a_4 := (concat a_3 (concat ((L_to_logic_list t t_1 a_1 a)) nil)) in
  ((separated a_2 2%Z a 2%Z)) ->
  ((P_ptr_separated_from_list a a_3)) ->
  ((P_all_separated_in_list a_4)) ->
  ((P_linked_ll t t_1 a_2 a_1 a_3)) ->
  (((L_to_logic_list t t_1 a_2 a)) = a_4).

Proof.
  Ltac simpl_nth := match goal with
  | [ _ : _ |- context [ nth (cons _ ?l) (?i + 1) = nth ?l ?i ] ] =>
    replace i with (i + 1 - 1) by omega ;
    replace (i + 1 - 1 + 1) with (i + 1) by omega ;
    apply Vlist.nth_cons ; omega
  end.

  assert(Simpl : forall hd l1 l2, l1 = l2 <-> cons hd l1 = cons hd l2). {
    intros ; split ; intros ; subst ; try (inversion H) ; auto.
  }

  intros Mi Ma bl sl el il1 ill.
  assert(H1: exists l1, l1 = il1) by (exists il1 ; auto).
  unfold ill in * ; clear ill.
  unfold il1 in * ; clear il1.
  inversion_clear H1 as [ l1 Hl1 ].
  rewrite <- Hl1.
  revert Hl1 ; revert bl sl el.

  induction l1 as [ | hd1 l1' ].
  + intros bl sl el Hl1 SepBE PtrSep AllSep NoDup1.
    inversion NoDup1 ; subst.
    replace Datatypes.nil with nil in * by reflexivity.
    rewrite rw_nil_concat_left.
    rewrite rw_nil_concat_right.
    auto.
  + replace (hd1 :: l1')%list with (cons hd1 l1') by reflexivity.
    destruct l1' as [ | snd1 l1'' ].
    - intros bl sl el Hl1 SepBE PtrSep AllSep NoDup1.
      replace Datatypes.nil with nil in * by reflexivity.
      simpl in * .
      replace (hd1 :: concat (L_to_logic_list Mi Ma sl el) nil)%list 
         with (cons hd1 (concat (L_to_logic_list Mi Ma sl el) nil)) 
           in * by reflexivity.
      inversion NoDup1 ; subst.
      rewrite A_To_ll.Q_to_ll_cons ; auto.
      * apply Simpl.
        rewrite H0.
        rewrite rw_nil_concat_right in H0 ; subst.
        inversion H8 ; subst ; auto.
      * rewrite rw_nil_concat_right in H0 ; subst.
        inversion H8 ; subst.
        rewrite rw_nil_concat_right in AllSep.
        set(tail := L_to_logic_list Mi Ma (Ma .[ shiftfield_F1_list_next hd1]) el).
        replace (L_to_logic_list Mi Ma (Ma .[ shiftfield_F1_list_next hd1]) el) 
           with tail in AllSep by auto.
        intros i ; intros.
        replace hd1 with (nth (cons hd1 tail) 0) by reflexivity.
        replace (nth tail i) with (nth (cons hd1 tail) (i + 1)) by simpl_nth.
        apply AllSep ; try rewrite Vlist.length_cons ; omega.
    - replace (snd1 :: l1'')%list with (cons snd1 l1'') in * by reflexivity.
      set(l1' := cons snd1 l1'').
      intros bl sl el Hl1 SepBE PtrSep AllSep NoDup1.
      rewrite rw_cons_concat.
      inversion NoDup1 ; subst.
      rewrite A_To_ll.Q_to_ll_cons ; auto.
      apply Simpl.
      rewrite rw_nil_concat_right in H0 ; subst.
      do 2 rewrite rw_nil_concat_right.
      rewrite A_To_ll.Q_to_ll_cons in Hl1 ; auto.
      apply Simpl in Hl1.
      apply IHl1' with (sl := sl) ; auto.
      * rewrite rw_nil_concat_right in Hl1.
        rewrite <- Hl1 ; reflexivity.
      * replace (Ma .[ Compound.shiftfield_F1_list_next hd1]) with (nth (cons hd1 l1') 1).
        ++ apply PtrSep ; try omega.
           unfold l1' ; repeat(rewrite Vlist.length_cons).
           assert(0 <= length l1'') by (apply Vlist.length_pos).
           omega.
        ++ inversion H8 ; subst ; reflexivity.
      * replace (cons snd1 l1'') with l1' by reflexivity.
        clear AllSep NoDup1 H1 H2 H7 H8.
        intros x ; intros.
        replace (nth l1' x) with (nth (cons hd1 l1') (x+1)) by simpl_nth.
        apply PtrSep ; try omega.
        rewrite Vlist.length_cons ; omega.
      * rewrite rw_cons_concat in AllSep.
        clear IHl1' SepBE Hl1 PtrSep NoDup1 H1 H2 H7 H8.
        set(l2 := concat (L_to_logic_list Mi Ma sl el) nil).
        replace (concat (L_to_logic_list Mi Ma sl el) nil) with l2 in AllSep by reflexivity.
        intros n1 n2 ; intros.
        replace (nth (concat (cons snd1 l1'') l2) n1) 
           with (nth (cons hd1 (concat (cons snd1 l1'') l2)) (n1+1))
             by simpl_nth.
        replace (nth (concat (cons snd1 l1'') l2) n2) 
           with (nth (cons hd1 (concat (cons snd1 l1'') l2)) (n2+1))
             by simpl_nth.
        apply AllSep ; try (rewrite Vlist.length_cons ; unfold l1') ; omega.
      * apply Q_linked_ll_to_logic_list in H8 ; rewrite H8 ; auto.
      * rewrite rw_nil_concat_right in H0 ; subst.
        rewrite rw_cons_concat in AllSep.
        rewrite <- IHl1' with (bl := Ma .[ shiftfield_F1_list_next hd1]) in AllSep ; auto.
        ++ set (tail := L_to_logic_list Mi Ma (Ma .[ shiftfield_F1_list_next hd1]) el).
           replace (L_to_logic_list Mi Ma (Ma .[ shiftfield_F1_list_next hd1]) el) 
              with tail in AllSep by auto.
           intros i ; intros.
           replace hd1 with (nth (cons hd1 tail) 0) by reflexivity.
           replace (nth tail i) with (nth (cons hd1 tail) (i + 1)) by simpl_nth.
           apply AllSep ; try rewrite Vlist.length_cons ; omega.
        ++ apply Q_linked_ll_to_logic_list in H8 ; unfold l1' in H8 ; auto.
        ++ unfold l1' in PtrSep.
           unfold l1' in H8 ; inversion H8 ; subst.
           replace (Ma .[ shiftfield_F1_list_next hd1]) 
              with (nth (cons hd1 (cons (Ma .[ shiftfield_F1_list_next hd1]) (concat l nil))) 1) 
                by (unfold nth ; unfold cons ; simpl ; auto).
           apply PtrSep ; try omega.
           repeat rewrite length_cons ; assert (0 <= length (concat l nil)) by apply length_pos ; omega.
        ++ replace (cons snd1 l1'') with l1' by auto.
           intros i ; intros.
           replace (nth l1' i) with (nth (cons hd1 l1') (i + 1)) by simpl_nth.
           apply PtrSep ; repeat rewrite length_cons ; assert (0 <= length l1') by apply length_pos ; omega.
        ++ replace (cons snd1 l1'') with l1' by auto.
           set(tail := concat l1' (concat (L_to_logic_list Mi Ma sl el) nil)).
           replace (concat l1' (concat (L_to_logic_list Mi Ma sl el) nil)) with tail in AllSep by auto.
           intros n1 n2 ; intros.
           replace (nth tail n1) with (nth (cons hd1 tail) (n1+1)) by simpl_nth.
           replace (nth tail n2) with (nth (cons hd1 tail) (n2+1)) by simpl_nth.
           assert(0 <= length tail) by apply length_pos.
           apply AllSep ; try (rewrite Vlist.length_cons) ; omega.
Qed.

