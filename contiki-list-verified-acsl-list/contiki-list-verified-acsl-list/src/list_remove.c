/*
 * Copyright (c) 2004, Swedish Institute of Computer Science.
 * Copyright (c) 2018, Inria, CEA, Northern Arizona University.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the verification of the Contiki operating system.
 *
 * Authors: - Adam Dunkels <adam@sics.se>
 *          - Allan Blanchard <mail@allan-blanchard.fr>
 *          - Nikolai Kosmatov <nikolai.kosmatov@cea.fr>
 *          - Frédéric Loulergue <frederic.loulergue@nau.edu>
 */

#ifdef _IN_LIST_MAIN_FILE

/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ requires \valid(item) ;
  @ requires in_list(item, to_logic_list(*list, NULL)) ||
  @          ptr_separated_from_list(item, to_logic_list(*list, NULL)) ;
  @
  @ ensures ValidHandler:  \valid(list);
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures ItemUnchanged: item->next == \old(item->next) && \valid(item);
  @ ensures ItemNotIn:     ptr_separated_from_list(item, to_logic_list(*list, NULL));
  @ ensures AllOthers:    \forall struct list* l ; l != item ==> (
  @                          in_list(l, to_logic_list{Pre}(\old(*list), NULL)) <==>
  @                            in_list(l, to_logic_list(*list, NULL)));
  @ 
  @ assigns *list,
  @         { l->next 
  @           | struct list* l ; 
  @             in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && 
  @             \at(l->next, Pre) == item } ;
  @
  @ behavior does_not_contain:
  @   assumes ! in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures *list == \old(*list) ;
  @   ensures SameList:  to_logic_list{Pre}(\old(*list), NULL) == to_logic_list(*list, NULL) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ behavior contains:
  @   assumes in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures \old(*list) == item ==> *list == \old(item->next) ;
  @   ensures \old(*list) != item ==> *list == \old(*list) ;
  @   ensures Link: \forall struct list* e ; 
  @     (in_list(e, to_logic_list{Pre}(\at(*list, Pre), NULL)) && \at(e->next, Pre) == item) ==> 
  @       e->next == item->next ;
  @       
  @   ensures NewList:
  @     (to_logic_list{Pre}(\old(*list), item) ^ to_logic_list{Pre}(item->next, NULL)) ==
  @       to_logic_list(*list, NULL) ;
  @   ensures SizeReduced: \length(to_logic_list(*list, NULL)) == 
  @                        \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) - 1 ;
  @           
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void
list_remove(list_t list, struct list *item){
  /*@ assert ! in_list(item, to_logic_list(*list, NULL)) ==>
             (\forall integer n ; 0 <= n < \length(to_logic_list(*list, NULL)) ==> 
                \nth(to_logic_list(*list, NULL), n) != item) ;
  */
  if( *list == NULL ){
    /*@ assert 
        \forall struct list* e ; (in_list(e, to_logic_list(*list, NULL)) && e->next == item) ==>
	  \false ;
    */
    return ;
  }
  if( *list == item ){
    //@ assert to_logic_list(*list, item) == \Nil ;
    /*@ assert 
        \forall struct list* e ; (in_list(e, to_logic_list(*list, NULL)) && e->next == item) ==>
	  \false ;
    */
    //@ ghost struct list* next = (*list)->next ;

    /*@
      assigns \nothing ;
      ensures Where_is_l: \forall struct list* l ; l != item ==> (
        in_list(l, to_logic_list(item, NULL)) <==> in_list(l, to_logic_list(item->next, NULL))) ;
    */ {
      /*@ assert R1:
	  ptr_separated_from_list(item, to_logic_list(item->next, NULL)) ==>
            !in_list(item, to_logic_list(item->next, NULL)) ;
      */
      /*@ assert R21: to_logic_list(item, NULL) ==
	              (to_logic_list(item, item->next) ^ to_logic_list(item->next, NULL)) ;
      */
      /*@ assert R22:
	\forall struct list* l ; 
	(in_list(l, to_logic_list(item, NULL)) <==> (
	 in_list(l, to_logic_list(item, item->next)) ||
	 in_list(l, to_logic_list(item->next, NULL)))) ;
      */
      //@ assert R23: to_logic_list(item, item->next) == [| item |] ;
      //@ assert R24: \forall struct list* l ; l != item ==> !in_list(l, [| item |]) ;
    }
      

    *list = (*list)->next ;
    //@ assert UnchangedTailChangedHead: unchanged{Pre, Here}(to_logic_list{Pre}(next, NULL));
    //@ assert PostLinkedChangedHead: linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
    /*@ assert Remains:
        \forall struct list* l ; l != item ==>
          (in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
           in_list(l, to_logic_list{Here}(\at(*list, Here), NULL))) ;
    */
    /*@ assert NewList:
        (to_logic_list{Pre}(\at(*list,Pre), item) ^ to_logic_list{Pre}(item->next, NULL)) ==
	 to_logic_list(*list, NULL) ;
    */

    return ;
  }

  struct list *l = *list ;
  int n = 0 ;
  /*@ loop invariant \nth(to_logic_list(*list, NULL), n) == l && l != NULL;
    @ loop invariant linked_ll(*list, NULL, to_logic_list(*list, NULL));
    @ loop invariant linked_ll(*list, l, to_logic_list(*list, l));
    @ loop invariant linked_ll(l, NULL, to_logic_list(l, NULL));
    @ loop invariant n == \length(to_logic_list(*list, l));
    @ loop invariant 0 <= n <= \length(to_logic_list(*list, NULL)) - 1;
    @ loop invariant unchanged{Pre, Here}(to_logic_list(*list, NULL)) ;
    @ loop invariant \forall integer j ; 0 <= j <= n ==> 
    @                  \nth(to_logic_list(*list, NULL), j) != item ;
    @ loop invariant ptr_separated_from_list(item, to_logic_list(*list, l)) ;
    @ loop invariant dptr_separated_from_list(list, to_logic_list(*list, NULL)) ;
    @ loop assigns l, n ;
    @ loop variant \length(to_logic_list(l->next, NULL)); 
    @*/
  while(l->next != item && l->next != NULL){
    //@ assert in_list(l->next, to_logic_list(*list, NULL)) ;
    //@ assert all_separated_in_list(to_logic_list(*list, NULL)) ;
    //@ assert in_list(l, to_logic_list(*list, NULL)) ;
    //@ assert to_logic_list(*list, NULL) == (to_logic_list(*list, l) ^ to_logic_list(l, NULL)) ;
    /*@ assert \forall integer i ; 0 <= i < \length(to_logic_list(*list, l)) ==>
        \separated(\nth(to_logic_list(*list, NULL), i),
	           \nth(to_logic_list(*list, NULL), \length(to_logic_list(*list, l))+1)) ;
    */
    //@ assert \nth(to_logic_list(*list, NULL), \length(to_logic_list(*list, l))+1) == l->next ;
    /*@ assert \forall integer i ; 0 <= i < \length(to_logic_list(*list, l)) ==>
        \nth(to_logic_list(*list, NULL), i) == \nth(to_logic_list(*list, l), i) ;
    */
    //@ assert ptr_separated_from_list(l->next, to_logic_list(*list, l)) ;
    //@ assert to_logic_list(*list, l->next) == (to_logic_list(*list, l) ^ [| l |]) ;
    l = l->next ;
    ++n;
  }
  /*@ assert \forall integer j ; 0 <= j <= n ==> 
               \nth(to_logic_list(*list, NULL), j) != item ;
  */
  if( l->next == item ){
    /*@ assert
        \forall struct list* e ; (in_list(e, to_logic_list(*list, NULL)) && e->next == item) ==>
	  e == l ;
    */

    //@ assert n+1 < \length(to_logic_list(*list, NULL)) ;
    //@ assert \nth(to_logic_list(*list, NULL), n+1) == item ;

    /*@ assigns \nothing ;
        ensures OldLeft: linked_ll(*list, l->next, to_logic_list(*list, l->next));
	ensures ItemNotInOldLeft: ptr_separated_from_list(item, to_logic_list(*list, l->next));
    */{
      //@ assert OL_In: in_list(l->next, to_logic_list(*list, NULL));
    }

    //@ assert OldRight: linked_ll(l->next->next, NULL, to_logic_list(l->next->next, NULL));

    //@ ghost BR: ;
    l->next = l->next->next ;
    //@ ghost AR: ;
    
    /*@ assigns \nothing ;
        ensures NewLeft:  \let hlist = \at(*list, AR) ; \let ln = \at(l->next, AR) ;
	  linked_ll{AR}(hlist, ln, to_logic_list(hlist, ln));
	ensures NewLeftVal: 
	  to_logic_list{AR}(\at(*list,AR), \at(l->next, AR)) == 
	  to_logic_list{BR}(\at(*list,BR), item) ;
	ensures ItemNotInNewLeft: 
	  ptr_separated_from_list(item, to_logic_list{AR}(\at(*list, AR), \at(l->next, AR))) ;
	ensures HandlerSepNewLeft: 
	  dptr_separated_from_list(list, to_logic_list{AR}(\at(*list, AR), \at(l->next, AR))) ;
    */ {
      /*@ assert SplitLeftP1: in_list(l, to_logic_list{BR}(\at(*list, BR), NULL)) ==>
	  to_logic_list{BR}(\at(*list, BR), NULL) ==
	  (to_logic_list{BR}(\at(*list, BR), l) ^ to_logic_list{BR}(l, NULL));
      */
      /*@ assert SplitLeftP2:
	  to_logic_list{BR}(l, NULL) ==
	  (to_logic_list{BR}(l, \at(l->next, BR)) ^ to_logic_list{BR}(\at(l->next, BR), NULL));
      */
      /*@ assert SplitLeft:
	  to_logic_list{BR}(\at(*list, BR), NULL) == 
	  (to_logic_list{BR}(\at(*list, BR), l) ^ [| l |] ^ to_logic_list{BR}(item, NULL));
      */
      /*@ assert C3: 
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  l->next == \nth(all, \length(left) + 2) || l->next == NULL ;
      */
      /*@ assert C4:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \forall integer i ; 0 <= i < \length(left) ==> \nth(left, i) == \nth(all, i) ;
      */

      /*@ assigns \nothing ; 
	ensures SepEndLeftPre:
	ptr_separated_from_list(l->next, to_logic_list{BR}(\at(*list, BR), l)) ;
      */ {
	//@ assert all_separated_in_list(to_logic_list{BR}(\at(*list, BR), NULL)) ;
	/*@ assert SepEndLeftPre_P1:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \forall integer i, j ; 0 <= i < \length(left) && \length(left) <= j < \length(all) ==> 
	    \separated(\nth(all, i), \nth(all, j)) &&
	    \separated(\nth(all, i), (struct list*) NULL);
	*/
	/*@ assert SepEndLeftPre_P2_P:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \length(left) <= \length(left) + 2 < \length(all) || l->next == NULL ;
	*/
	/*@ assert SepEndLeftPre_P2_1:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \forall integer i ; 0 <= i < \length(left) && \length(left) + 2 < \length(all) ==> 
	    \separated(\nth(left, i), \nth(all, \length(left) + 2)) ;
	*/
	/*@ assert SepEndLeftPre_P2_2:
	  \let left = to_logic_list{BR}(\at(*list, BR), l); 
	  \let all  = to_logic_list{BR}(\at(*list, BR), NULL) ;
	  \forall integer i ; 0 <= i < \length(left) ==> 
	    \separated(\nth(left, i), (struct list*) NULL) ;
	*/
      }
      /*@ assert SepItemLeftPre: 
	  ptr_separated_from_list(item, to_logic_list{BR}(\at(*list, BR), l)) ;
      */
      //@ assert SepItemL: \separated(l, item);
      
      //@ assert NL_NI: ptr_separated_from_list(l, to_logic_list{BR}(\at(*list, BR), \at(l, AR))) ;
      //@ assert UnchangedLeft: unchanged{BR, AR}(to_logic_list{BR}(\at(*list, BR), \at(l, AR))) ;
      /*@ assert EqLeftP1: to_logic_list{BR}(\at(*list, BR), \at(l, AR)) == 
	                   to_logic_list{AR}(\at(*list, AR), \at(l, AR)) ;
      */
      /*@ assert OldLeftVal: 
	  to_logic_list{BR}(\at(*list, BR), item) == 
	  (to_logic_list{BR}(\at(*list, BR), \at(l, AR)) ^ [| l |]) ;
      */
      /* @ assert NewLeftVal: 
	  to_logic_list{AR}(\at(*list, AR), \at(l->next, AR)) == 
	  (to_logic_list{AR}(\at(*list, AR), l) ^ [| l |]) ;
      */
      //@ assert NewLeftP1 : linked_ll{AR}(\at(*list, AR), l, to_logic_list{AR}(\at(*list, AR), l));
      /*@ assert SepHandlerPre:
	  dptr_separated_from_list(list, to_logic_list{BR}(\at(*list, BR), NULL)) <==>
	  (dptr_separated_from_list(list, to_logic_list{BR}(\at(*list, BR), l)) &&
           dptr_separated_from_list(list, to_logic_list{BR}(l, NULL))) ;
      */
      /*@ assert SepHandlerLeftPreP1: 
	  dptr_separated_from_list(list, to_logic_list{BR}(\at(*list, BR), l)) ;
      */
      /*@ assert SepHandlerLeftPreP2: 
	  dptr_separated_from_list(list, to_logic_list{AR}(\at(*list, AR), l)) ;
      */
      /*@ assert PostNewLeftValue: 
	  to_logic_list{AR}(\at(*list, AR), \at(l->next, AR)) == 
	  to_logic_list{BR}(\at(*list, BR), item) ;
      */
      //@ assert SepHandlerEnd: \separated(l, list);
    }

    /*@ assigns \nothing ;
        ensures NewRight: linked_ll(l->next, NULL, to_logic_list(l->next, NULL));
	ensures ItemNotInNewRight: ptr_separated_from_list(item, to_logic_list(l->next, NULL)) ;
	ensures HandlerSepNewRight: dptr_separated_from_list(list, to_logic_list(l->next, NULL)) ;
	ensures NewRightVal: to_logic_list(l->next, NULL) == to_logic_list{BR}(item->next, NULL) ;
    */ {
      //@ assert NR_NI: ! in_list(l, to_logic_list{Pre}(\at(l->next, Here), NULL)) ;
      /*@ assert 
	  SepItemRightPre: ptr_separated_from_list(item, to_logic_list{BR}(item->next, NULL)) ;
      */
      /*@ assert SplitRight:
	  to_logic_list{BR}(*list, NULL) == 
	  (to_logic_list{BR}(*list, item) ^ to_logic_list{BR}(item, NULL));
      */
      /*@ assert SepHandlerRightPreP1: 
	  dptr_separated_from_list(list, to_logic_list{BR}(item, NULL)) ;
      */
      /*@ assert SepHandlerRightPreP2: 
	  dptr_separated_from_list(list, to_logic_list{BR}(item->next, NULL)) ;
      */
      //@ assert UnchangedRight: unchanged{BR, Here}(to_logic_list{Pre}(\at(l->next, Here), NULL)) ;
    }

    /*@ assigns \nothing ;
        ensures AllSepNew:
	  \let left  = to_logic_list{BR}(*list, item) ;
	  \let right = to_logic_list{BR}(item->next, NULL) ;
	  all_separated_in_list(left ^ right);
     */ {
      /*@ assert Split:
	  to_logic_list{BR}(*list, NULL) == 
	  (to_logic_list{BR}(*list, item) ^ [|item|] ^ to_logic_list{BR}(item->next, NULL));
      */
      //@ assert AllSepOld: all_separated_in_list(to_logic_list{BR}(*list, NULL));
    }

    //@ assert PostLinkedRemove: linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

    //@ assert SeparatedItemLeft: ptr_separated_from_list(item, to_logic_list(*list, l->next));
    //@ assert SeparatedItemRight: ptr_separated_from_list(item, to_logic_list(l->next, NULL));
    //@ assert PostNotInRemove: ptr_separated_from_list(item, to_logic_list(*list, NULL)) ;

    /*@ assigns \nothing ;
        ensures PostNewList:
	        (to_logic_list{Pre}(\old(*list), item) ^ to_logic_list{Pre}(item->next, NULL)) ==
	        to_logic_list(*list, NULL) ;
    */ {
      //@ assert PostNL_P1: to_logic_list{Pre}(*list, item) == to_logic_list(*list, l->next) ;
      //@ assert PostNL_P2: to_logic_list{Pre}(item->next, NULL) == to_logic_list(l->next, NULL) ;
      /*@ assert PostNL_P3: to_logic_list(*list, NULL) ==
	  (to_logic_list(*list, l->next) ^ to_logic_list(l->next, NULL));
      */
    }

    /*@
      assigns \nothing ;
      ensures Remains:
        \forall struct list* l ; l != item ==>
          (in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
           in_list(l, to_logic_list{Here}(\at(*list, Here), NULL))) ;
    */ {
      /*@ assert PIn_Split_New: in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
           to_logic_list{Here}(\at(*list, Here), NULL) ==
	    (to_logic_list{Pre}(\at(*list, Pre), item) ^ 
	     to_logic_list{Pre}(\at(item->next, Pre), NULL));
      */
      /*@ assert PIn_Split_Old_P2: in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
           to_logic_list{Pre}(item, NULL) ==
            (to_logic_list{Pre}(item, \at(item->next, Pre)) ^ 
             to_logic_list{Pre}(\at(item->next, Pre), NULL));
      */
      /*@ assert PInP: in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
          \forall struct list* l ; in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
	  (   in_list(l, to_logic_list{Pre}(\at(*list, Pre), item))
	   || in_list(l, [| item |] )
	   || in_list(l, to_logic_list{Pre}(\at(item->next, Pre), NULL))) ;
      */
      /*@ assert PNotInItem: \forall struct list* l ; l != item <==> !in_list(l, [| item |] ) ; */
      /*@ assert PInP2: in_list(item, to_logic_list{Pre}(\at(*list,Pre), NULL)) ==>
	\forall struct list* l ; l != item ==> (
	 in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
	 (  in_list(l, to_logic_list{Pre}(\at(*list, Pre), item))
	 || in_list(l, to_logic_list{Pre}(\at(item->next, Pre), NULL)))) ;
      */
      /*@ assert PIn: in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	\forall struct list* l ; l != item ==> (
	  in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) <==>
	  in_list(l, to_logic_list{Here}(\at(*list, Here), NULL))) ;
      */
    }
  } else {
    //@ assert l->next == NULL ;
    /*@ assert \forall integer j ; 0 <= j <= n ==> 
                  \nth(to_logic_list(*list, NULL), j) != item ;
    */
    /*@ assert 
        \forall struct list* e ; (in_list(e, to_logic_list(*list, NULL)) && e->next == item) ==>
	  \false ;
    */
    
    //@ assert UnchangedNoChange: unchanged{Pre, Here}(to_logic_list{Pre}(*list, NULL)) ;
    //@ assert PostLinkedNoChange: linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  }
}

#endif
