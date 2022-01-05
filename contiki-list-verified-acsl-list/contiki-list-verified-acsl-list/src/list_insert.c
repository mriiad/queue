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

#include "list_split.c"
#include "list_force_insert.c"

/*@ requires ValidHandler: \valid(list);
  @ requires HandlerSep:   dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ requires Linked:        linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ requires LengthMax:    \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @ requires \valid(newitem) ;
  @ requires prev == NULL || in_list(prev, to_logic_list(*list, NULL)) ;
  @ requires in_list(newitem, to_logic_list(*list, NULL)) ||
  @          ptr_separated_from_list(newitem, to_logic_list(*list, NULL)) ;
  @ requires \separated(list, prev, newitem) ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @
  @ assigns *list,
  @         newitem->next,
  @         prev->next,
  @         { l->next | struct list* l ; in_list(l, to_logic_list{Pre}(*list, NULL)) } ;
  @
  @ behavior at_beginning_and_does_not_contain:
  @   assumes prev == NULL ;
  @   assumes !in_list(newitem, to_logic_list{Pre}(*list, NULL));
  @   ensures AddedBegin: to_logic_list(*list, NULL) ==
  @                     ([| newitem |] ^ to_logic_list{Pre}(\old(*list), NULL)) ;
  @   ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                    \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ behavior at_beginning_and_contains:
  @   assumes prev == NULL ;
  @   assumes in_list(newitem, to_logic_list{Pre}(*list, NULL));
  @   ensures NewList: to_logic_list(*list, NULL) ==
  @     ([| newitem |] ^ to_logic_list{Pre}(\old(*list), newitem) ^ 
  @      to_logic_list{Pre}(\at(newitem->next,Pre), NULL)) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ behavior somewhere_else_does_not_contain:
  @   assumes prev != NULL ;
  @   assumes !in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL));
  @   ensures NewList: to_logic_list(*list, NULL) == (
  @     to_logic_list{Pre}(\old(*list), \old(prev->next)) ^
  @     [| newitem |] ^
  @     to_logic_list{Pre}(\old(prev->next), NULL));
  @   ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                    \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ behavior somewhere_else_contains_after_prev_linked:
  @   assumes prev != NULL ;
  @   assumes in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL));
  @   assumes in_list(prev, to_logic_list{Pre}(\at(*list, Pre), newitem)) ;
  @   assumes \at(prev->next, Pre) == newitem ;
  @   ensures NewList: to_logic_list(*list, NULL) == to_logic_list{Pre}(\at(*list, Pre), NULL) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ behavior somewhere_else_contains_after_prev_not_linked:
  @   assumes prev != NULL ;
  @   assumes in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL));
  @   assumes in_list(prev, to_logic_list{Pre}(\at(*list, Pre), newitem)) ;
  @   assumes \at(prev->next, Pre) != newitem ;
  @   ensures NewList: to_logic_list(*list, NULL) == 
  @     (to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre)) ^ 
  @     [| newitem |] ^
  @     to_logic_list{Pre}(\at(prev->next, Pre), newitem) ^
  @     to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ behavior somewhere_else_contains_before:
  @   assumes prev != NULL ;
  @   assumes in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL));
  @   assumes in_list(prev, to_logic_list{Pre}(newitem, NULL));
  @   ensures NewList: to_logic_list(*list, NULL) == 
  @     (to_logic_list{Pre}(\at(*list, Pre), newitem) ^ 
  @     to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ^
  @     [| newitem |] ^
  @     to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @
  @ complete behaviors;
  @ disjoint behaviors;
*/
void
list_insert(list_t list, struct list *prev, struct list *newitem)
{
  if(prev == NULL) {
    list_push(list, newitem);
  } else {
    //@ ghost list_split(list, newitem, NULL) ;

    /*@ assigns \nothing ;
      ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
        in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	in_list(prev->next, to_logic_list{Pre}(newitem->next, NULL)) || prev->next == NULL ;
      ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
        in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem->next, NULL)) ;
      ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
        in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==> 
	prev->next != newitem ;
      ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
        in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
        linked_ll{Pre}(newitem->next, NULL, to_logic_list{Pre}(newitem->next, NULL)) ;
    */ {
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	  linked_ll{Pre}(newitem->next, NULL, to_logic_list{Pre}(newitem->next, NULL)) &&
	  ptr_separated_from_list(newitem, to_logic_list{Pre}(newitem->next, NULL)) ;
      */
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	to_logic_list{Pre}(newitem, NULL) == 
	([| newitem |] ^ to_logic_list{Pre}(newitem->next, NULL)) ;
      */
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	!in_list(prev, [| newitem |]) ;
      */
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem->next, NULL)) ;
      */
      /*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem->next, NULL)) ==>
	in_list(prev->next, to_logic_list{Pre}(newitem->next, NULL)) || prev->next == NULL ;
      */
    }
    
    if(prev->next != newitem){
      //@ ghost list_split(list, prev->next, NULL) ;

      /*@ assigns \nothing ;
	ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(prev, to_logic_list{Pre}(*list, newitem)) ==>
	to_logic_list{Pre}(*list, newitem) ==
	(to_logic_list{Pre}(*list, prev->next) ^ to_logic_list{Pre}(prev->next, newitem)) ;
      */ {
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(*list, newitem)) ==>
	  in_list(prev->next, to_logic_list{Pre}(*list, newitem)) ;
	*/
      }

      /*@ assigns \nothing ;
	ensures in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	to_logic_list{Pre}(newitem->next, NULL) ==
	(to_logic_list{Pre}(newitem->next, prev->next) ^ to_logic_list{Pre}(prev->next, NULL)) ;
      */ {
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	  linked_ll{Pre}(newitem->next, NULL, to_logic_list{Pre}(newitem->next, NULL)) ;
	*/
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	  to_logic_list{Pre}(newitem, NULL) == 
	           ([| newitem |] ^ to_logic_list{Pre}(newitem->next, NULL)) ;
	*/
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	  !in_list(prev, [| newitem |]) ;
	*/
	/*@ assert in_list(newitem, to_logic_list{Pre}(*list, NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem->next, NULL)) ;
	*/
      }
      
      list_remove(list, newitem);

      //@ ghost AR: ; 
      
      //@ assert \at(prev->next, AR) == \at(prev->next, Pre) ;
      //@ assert \at(newitem->next, AR) == \at(newitem->next, Pre) ;

      /*@ assigns \nothing ;
	ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	in_list(prev, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) == 
	to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre)) ;
      */ {
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	  (to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) ^
	   to_logic_list{AR}(\at(prev->next, AR), NULL))
	   ==
	  (to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, AR)) ^ 
	   to_logic_list{Pre}(\at(prev->next, AR), newitem) ^
	   to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
	*/
	/*@ assigns \nothing ;
	    ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(prev->next, Pre), to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	      unchanged{Pre, AR}(to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre))) ;
	*/ {
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    \forall integer i ; 0 <= i < \length(ll)-1 ==> 
	    (\valid{Pre}(\at(\nth(ll, i), Pre)) && \valid{AR}(\at(\nth(ll, i), AR)) &&
	     \at(\nth(ll, i)->next, Pre) == \at(\nth(ll, i)->next, AR)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    in_list(\at(prev->next, Pre), ll) ==>
	    to_logic_list{Pre}(\at(*list, Pre), newitem) ==
	    (to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre)) ^ 
	     to_logic_list{Pre}(\at(prev->next, Pre), newitem)) &&
	    linked_ll{Pre}(\at(*list, Pre), \at(prev->next, Pre), 
	                to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre))) &&
            linked_ll{Pre}(\at(prev->next, Pre), newitem, 
	                to_logic_list{Pre}(\at(prev->next, Pre), newitem)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    in_list(\at(prev->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre)) ;
	    \forall integer i ; 0 <= i < \length(sll) ==>
	    (\valid{Pre}(\at(\nth(ll, i), Pre)) && \valid{Pre}(\at(\nth(sll, i), Pre)) &&
	      \at(\nth(sll, i)->next, Pre) == \at(\nth(ll, i)->next, Pre)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    in_list(\at(prev->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre)) ;
	      \length(sll) <= \length(ll)-1 ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(*list, Pre), newitem) ;
	    in_list(\at(prev->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre)) ;
	    \forall integer i ; 0 <= i < \length(sll) ==>
	      (\valid{Pre}(\at(\nth(sll, i), Pre)) && \valid{AR}(\at(\nth(sll, i), AR)) &&
	      \at(\nth(sll, i)->next, Pre) == \at(\nth(sll, i)->next, AR)) ;	      
	  */
	}
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	  linked_ll{Pre}(\at(*list, Pre), \at(prev->next, Pre), 
	              to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, Pre))) ;
	*/
      }

      /*@ assigns \nothing ;
	ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	to_logic_list{AR}(\at(prev->next, AR), NULL) == 
	to_logic_list{Pre}(\at(prev->next, Pre), NULL) ;
      */ {
	/*@ assigns \nothing ;
	  ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	  (to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) ^
	   to_logic_list{AR}(\at(prev->next, AR), NULL))
	   ==
	  (to_logic_list{Pre}(\at(*list, Pre), newitem) ^
	   to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, AR)) ^
	   to_logic_list{Pre}(\at(prev->next, AR), NULL)) ;
	*/ {
	  /*@ assert in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    in_list(\at(prev->next, AR), to_logic_list{AR}(\at(*list, AR), NULL)) || 
	    \at(prev->next, AR) == NULL ;
	  */
	  /*@ assert in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    linked_ll(\at(*list, AR), NULL, to_logic_list{AR}(\at(*list, AR), NULL)) ;
	  */
	  /*@ assert in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    to_logic_list{AR}(\at(*list, AR), NULL) ==
	    (to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) ^
	    to_logic_list{AR}(\at(prev->next, AR), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    to_logic_list{AR}(\at(*list, AR), NULL) ==
	    (to_logic_list{Pre}(\at(*list, Pre), newitem) ^
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(prev->next, Pre), to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ^
	    to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \at(prev->next, Pre) == NULL ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ^
	    to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    in_list(\at(prev->next, Pre), to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) || 
	    \at(prev->next, Pre) == NULL ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ^
	    to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	  */
	}

	/*@ assigns \nothing ;
	    ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(prev->next, Pre), to_logic_list{Pre}(newitem->next, NULL)) ==>
	      unchanged{Pre, AR}(to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	*/ {
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ;
	    \forall integer i ; 0 <= i < \length(ll) ==> 
	    (\valid{Pre}(\at(\nth(ll, i), Pre)) && \valid{AR}(\at(\nth(ll, i), AR)) &&
	     \at(\nth(ll, i)->next, Pre) == \at(\nth(ll, i)->next, AR)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    linked_ll{Pre}(\at(newitem->next, Pre), NULL, to_logic_list(\at(newitem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(prev->next, Pre), to_logic_list{Pre}(newitem->next, NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ^ 
	     to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ;
	    in_list(\at(prev->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(prev->next, Pre), NULL) ;
	    \let left = to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ;
	    \forall integer i ; 0 <= i < \length(sll) ==>
	    \let off_i = i + \length(left) ;
	    (\valid{Pre}(\at(\nth(ll, off_i), Pre)) && \valid{Pre}(\at(\nth(sll, i), Pre)) &&
	      \at(\nth(sll, i)->next, Pre) == \at(\nth(ll, off_i)->next, Pre)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ;
	    in_list(\at(prev->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(prev->next, Pre), NULL) ;
	      \length(sll) <= \length(ll) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \let ll = to_logic_list{Pre}(newitem->next, NULL) ;
	    in_list(\at(prev->next, Pre), ll) ==>
	    \let sll = to_logic_list{Pre}(\at(prev->next, Pre), NULL) ;
	    \forall integer i ; 0 <= i < \length(sll) ==>
	      (\valid{Pre}(\at(\nth(sll, i), Pre)) && \valid{AR}(\at(\nth(sll, i), AR)) &&
	      \at(\nth(sll, i)->next, Pre) == \at(\nth(sll, i)->next, AR)) ;	      
	  */
	}
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem->next, NULL)) ==>
	  linked_ll{Pre}(\at(prev->next, Pre), NULL,
	              to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	*/
	/* @ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem->next, NULL)) ==>
	  \at(*list, Pre) == \at(*list, AR) ;
	*/
	/* @ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem->next, NULL)) ==>
	  unchanged{Pre, AR}(to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	*/
      }

      /*@ assigns \nothing ;
	ensures EASY_Right: in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	in_list(prev, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	to_logic_list{AR}(\at(prev->next, AR), NULL) == 
	(to_logic_list{Pre}(\at(prev->next, Pre), newitem) ^ 
	 to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
      */ {
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	  (to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) ^
	   to_logic_list{AR}(\at(prev->next, AR), NULL))
	   ==
	  (to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, AR)) ^ 
	   to_logic_list{Pre}(\at(prev->next, AR), newitem) ^
	   to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
	*/
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(\at(*list, Pre), newitem)) ==>
	  to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) ==
	  to_logic_list{Pre}(\at(*list, Pre), \at(prev->next, AR)) ;
	*/
	//@ assert \at(prev->next, AR) == \at(prev->next, Pre) ;
      }
      
      /*@ assigns \nothing ;
	ensures EASY_Left: in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) == 
	(to_logic_list{Pre}(\at(*list, Pre), newitem) ^ 
	 to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre))) ;
      */ {
	/*@ assigns \nothing ;
	  ensures in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	  (to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) ^
	   to_logic_list{AR}(\at(prev->next, AR), NULL))
	   ==
	  (to_logic_list{Pre}(\at(*list, Pre), newitem) ^
	   to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, AR)) ^
	   to_logic_list{Pre}(\at(prev->next, AR), NULL)) ;
	*/ {
	  /*@ assert in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    in_list(\at(prev->next, AR), to_logic_list{AR}(\at(*list, AR), NULL)) || 
	    \at(prev->next, AR) == NULL ;
	  */
	  /*@ assert in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    linked_ll(\at(*list, AR), NULL, to_logic_list{AR}(\at(*list, AR), NULL)) ;
	  */
	  /*@ assert in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    to_logic_list{AR}(\at(*list, AR), NULL) ==
	    (to_logic_list{AR}(\at(*list, AR), \at(prev->next, AR)) ^
	    to_logic_list{AR}(\at(prev->next, AR), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    to_logic_list{AR}(\at(*list, AR), NULL) ==
	    (to_logic_list{Pre}(\at(*list, Pre), newitem) ^
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(\at(prev->next, Pre), to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ^
	    to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    \at(prev->next, Pre) == NULL ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ^
	    to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    in_list(\at(prev->next, Pre), to_logic_list{Pre}(\at(newitem->next, Pre), NULL)) || 
	    \at(prev->next, Pre) == NULL ;
	  */
	  /*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	    in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	    to_logic_list{Pre}(\at(newitem->next, Pre), NULL) ==
	    (to_logic_list{Pre}(\at(newitem->next, Pre), \at(prev->next, Pre)) ^
	    to_logic_list{Pre}(\at(prev->next, Pre), NULL)) ;
	  */
	}
	/*@ assert in_list(newitem, to_logic_list{Pre}(\at(*list, Pre), NULL)) ==>
	  in_list(prev, to_logic_list{Pre}(newitem, NULL)) ==>
	  to_logic_list{AR}(\at(prev->next, AR), NULL) == 
	  to_logic_list{Pre}(\at(prev->next, Pre), NULL) ;
	*/
      }

      
      list_force_insert(list, prev, newitem);
    }
  }
}

#endif
