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
  @ requires \valid(item) && \separated(list, item);
  @ requires in_list(item, to_logic_list(*list, NULL)) ||
  @          ptr_separated_from_list(item, to_logic_list(*list, NULL)) ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @
  @ assigns *list,
  @         item->next,
  @         { l->next 
  @           | struct list* l ; 
  @             in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && 
  @             (\at(l->next, Pre) == NULL || \at(l->next, Pre) == item) } ;
  @
  @ behavior does_not_contain:
  @   assumes ! in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures \old(*list) != NULL ==> *list == \old(*list) ;
  @   ensures \old(*list) == NULL ==> *list == item ;
  @   ensures AddedEnd: to_logic_list(*list, NULL) == 
  @                     (to_logic_list{Pre}(\old(*list), NULL) ^ [| item |]) ;
  @   ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                    \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ behavior contains:
  @   assumes in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures NewList: to_logic_list(*list, NULL) ==
  @     (to_logic_list{Pre}(\old(*list), item) ^ 
  @      to_logic_list{Pre}(\at(item->next, Pre), NULL) ^ [| item |] ) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @           
  @ complete behaviors;
  @ disjoint behaviors;
*/
void
list_add(list_t list, struct list *item)
{
  /*@ assert ! in_list(item, to_logic_list(*list, NULL)) ==>
             (\forall integer n ; 0 <= n < \length(to_logic_list(*list, NULL)) ==> 
                \nth(to_logic_list(*list, NULL), n) != item) ;
  */  
  struct list *l;

  /* Make sure not to add the same element twice */
  list_remove(list, item);
  //@ ghost AR: ;

  /*@ assert SepReformulation: \let ll = to_logic_list{AR}(*list, NULL) ;
      \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), item) ;
  */
  
  item->next = NULL;
  //@ ghost BIN: ;

  //@ assert Unchanged1: unchanged{AR, BIN}(to_logic_list{AR}(\at(*list, AR), NULL)) ;
  //@ assert LinkedItem: linked_ll(item, NULL, to_logic_list(item, NULL));

  /*@ assigns \nothing ;
      ensures ItemStillNotIn: !in_list(item, to_logic_list(*list, NULL)) ;
  */ {
    //@ assert ISNI_1: ptr_separated_from_list(item, to_logic_list(*list, NULL));
    /*@ assert ISNI_2: \let ll = to_logic_list(*list, NULL) ;
        \forall integer i ; 0 <= i < \length(ll) ==> \nth(ll, i) != item ;
    */
  }    

  l = list_tail(list);
  //@ assert L_in_Old: l == NULL || in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) ;
  
  //@ assert HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  
  if(l == NULL) {
    *list = item;
    //@ assert HandlerSep_NULL:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  } else {
    //@ assert \at(*list, Pre) != NULL ;

    //@ ghost BN: ;

    /*@ assigns \nothing ;
        ensures RememberList: to_logic_list{BN}(*list, NULL) == to_logic_list{AR}(*list, NULL) ;
    */ {
      //@ assert RL_1: linked_ll{AR}(*list, NULL, to_logic_list{AR}(*list, NULL));
      //@ assert RL_2: unchanged{AR, BN}(to_logic_list{AR}(*list, NULL)) ;
    }
    
    /*@ assigns \nothing ;
        ensures ND: linked_ll{BN}(*list, l, to_logic_list{BN}(*list, l)) ;
	ensures LC: to_logic_list{BN}(*list, NULL) == (to_logic_list{BN}(*list, l) ^ [| l |]);
    */ {
      //@ assert ND1: *list == l ==> linked_ll{BN}(*list, l, to_logic_list{BN}(*list, l)) ;

      /*@ assert ND2: *list != l ==>
	  \let ll = to_logic_list{BN}(*list, NULL) ; \nth(ll, \length(ll)-1) == l ;
      */
      /*@ assert ND2: *list != l ==>
	  \let ll = to_logic_list{BN}(*list, NULL) ; \nth(ll, \length(ll)-1)->next == NULL ;
      */
      //@ assert ND2: \valid(l) && l->next == NULL ==> to_logic_list(l, NULL) == [| l |] ;
      //@ assert ND2: \length(to_logic_list{BN}(l, NULL)) == 1 ; 
      /*@ assert ND2: *list != l ==> \let ll = to_logic_list{BN}(*list, NULL) ; 
	  \nth(ll, \length(ll)-\length(to_logic_list{BN}(l, NULL))) == l ;
      */
      /*@ assert ND2: *list != l ==> to_logic_list{BN}(*list, NULL) ==
	  (to_logic_list{BN}(*list, l) ^ to_logic_list{BN}(l, NULL));
      */
      /*@ assert ND2: linked_ll{BN}(*list, NULL, to_logic_list{BN}(*list, l) ^ 
	                                      to_logic_list{BN}(l, NULL));
      */
      //@ assert ND2: *list != l ==> to_logic_list{BN}(*list, l) != \Nil ;
      //@ assert ND2: to_logic_list{BN}(l, NULL) != \Nil ;
      /*@ assert ND2: linked_ll{BN}(*list, l, to_logic_list{BN}(*list, l)) && 
	              linked_ll{BN}(l, NULL, to_logic_list{BN}(l, NULL)) ;
      */
    } 

    l->next = item;
    //@ ghost AN: ;

    /*@ assigns \nothing ;
        ensures LinkedPost: linked_ll{AN}(*list, item->next, to_logic_list{AN}(*list, item->next)) ;
	ensures HSepPost: dptr_separated_from_list(list, to_logic_list{AN}(*list, item->next));
	ensures NewList_1: to_logic_list{AN}(*list, NULL) == 
	                 (to_logic_list{BN}(*list, NULL) ^ [| item |]) ;
    */ {
      /*@ assert SeparationEnd: \let ll = to_logic_list{BN}(\at(*list, BN), l) ;
	  \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), l) ;
      */
      //@ assert Post12: \at(*list, BN) == \at(*list, AN) ;
      /*@ assert Post111:
	  \forall struct list* e ; \separated(e, l) ==> \at(e->next, BN) == \at(e->next, AN);
      */
      //@ assert Post11: unchanged{BN, AN}(to_logic_list{BN}(\at(*list, BN), l));
      //@ assert Post1: linked_ll{AN}(*list, l, to_logic_list{AN}(*list, l)) ;

      //@ assert Post21: \separated(l, item) ;
      //@ assert Post22: linked_ll{AN}(item, item->next, to_logic_list{AN}(item, item->next)) ;
      //@ assert Post2: linked_ll{AN}(l, item->next, to_logic_list{AN}(l, item->next)) ;

      /*@ assert Post3: all_separated_in_list(to_logic_list{AN}(*list, l) ^ 
	                                      to_logic_list{AN}(l, item->next));
      */
      //@ assert HSP1: dptr_separated_from_list(list, to_logic_list{AN}(*list, l));
      //@ assert HSP2: dptr_separated_from_list(list, to_logic_list{AN}(item, item->next));

      /*@ assert NL_1: to_logic_list{BN}(*list, NULL) == 
	         (to_logic_list{BN}(*list, l) ^ [| l |]) ;
      */
      /*@ assert NL_2: to_logic_list{AN}(*list, NULL) ==
	         (to_logic_list{BN}(*list, l) ^ to_logic_list{AN}(l, NULL));
      */
    }

    /*@
      assigns \nothing ;
      ensures to_logic_list{AN}(\at(*list, AN), NULL) == 
             (to_logic_list{BN}(\at(*list, BN), NULL) ^ [| item |]) ;
      ensures does_not_contain_begin:
        \at(*list, Pre) != NULL ==>
        !in_list(item, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
          to_logic_list{BN}(\at(*list, BN), NULL) == to_logic_list{Pre}(\at(*list, Pre), NULL) ;
      ensures contains_value:
        \let old_list = \at(*list, Pre) ; old_list != NULL ==>
        in_list(item, to_logic_list{Pre}(old_list, NULL)) ==>
          to_logic_list{BN}(\at(*list, BN), NULL) ==
         (to_logic_list{Pre}(old_list, item) ^ to_logic_list{Pre}(\at(item->next, Pre), NULL)) ;
      ensures contains_length:
        \let old_list = \at(*list, Pre) ; old_list != NULL ==>
        in_list(item, to_logic_list{Pre}(old_list, NULL)) ==>
	  \length(to_logic_list{BN}(\at(*list, BN), NULL)) ==
	  \length(to_logic_list{Pre}(old_list, NULL)) - 1 ;
    */ {}
  }
}

#endif
