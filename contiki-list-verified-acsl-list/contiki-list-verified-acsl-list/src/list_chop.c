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
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @
  @ assigns *list,
  @         { l->next 
  @           | struct list* l ; 
  @             in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && 
  @             \at(l->next, Pre) != NULL && \at(l->next->next, Pre) == NULL } ;
  @
  @ behavior empty:
  @   assumes *list == NULL ;
  @   assigns \nothing ;
  @   ensures *list == \old(*list);
  @   ensures RemainsNull: *list == NULL ;
  @   ensures Nothing: \result == NULL ;
  @
  @ behavior single_element:
  @   assumes *list != NULL ;
  @   assumes (*list)->next == NULL ;
  @   assigns *list ;
  @   ensures NowNull: *list == NULL ;
  @   ensures Head: \result == \old(*list) ;
  @
  @ behavior more_elements:
  @   assumes *list != NULL && (*list)->next != NULL ;
  @   assigns 
  @     \nth(to_logic_list{Pre}(*list, NULL), \length(to_logic_list{Pre}(*list, NULL)) - 2)->next;
  @   ensures *list == \old(*list);
  @   ensures NewList:
  @     \let pre_ll = to_logic_list{Pre}(*list, NULL) ;
  @     to_logic_list(*list, NULL) ==
  @     to_logic_list{Pre}(\at(*list, Pre), \nth(pre_ll, \length(pre_ll)-1)) ;
  @   ensures Tail:
  @     \let pre_ll = to_logic_list{Pre}(*list, NULL) ;
  @     \result == \nth(pre_ll, \length(pre_ll) - 1) ;
  @
  @ complete behaviors ;
  @ disjoint behaviors ;
*/
struct list *
list_chop(list_t list)
{
  if(*list == NULL) {
    return NULL;
  }
  if((*list)->next == NULL) {
    struct list* l = *list;
    *list = NULL;
    return l;
  }

  struct list *l = * list;
  int n = 0 ;

  /*@ loop invariant \nth(to_logic_list(*list, NULL), n) == l && l != NULL;
    @ loop invariant \nth(to_logic_list(*list, NULL), n+1) == l->next && l->next != NULL;
    @ loop invariant linked_ll(*list, NULL, to_logic_list(*list, NULL));
    @ loop invariant linked_ll(*list, l, to_logic_list(*list, l));
    @ loop invariant linked_ll(l, NULL, to_logic_list(l, NULL));
    @ loop invariant n == \length(to_logic_list(*list, l));
    @ loop invariant 0 <= n <= \length(to_logic_list(*list, NULL)) - 2;
    @ loop invariant unchanged{Pre, Here}(to_logic_list(*list, NULL)) ;
    @ loop invariant dptr_separated_from_list(list, to_logic_list(*list, NULL));
    @ loop assigns l, n ;
    @ loop variant \length(to_logic_list(l->next, NULL)); 
    @*/
  while(l->next->next != NULL){
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
    ++n ;
  }

  //@ assert in_list(l, to_logic_list(*list, NULL)) ;
  /*@ assert 
      linked_ll(*list, NULL, to_logic_list(*list, NULL)) ==>
        linked_ll(*list, l, to_logic_list(*list, l)) &&
	linked_ll(l, NULL, to_logic_list(l, NULL)) ;
  */
  //@ ghost PreM: ;
  //@ assert ptr_separated_from_list(l, to_logic_list(*list, l)) ;
  //@ assert to_logic_list(*list, l->next) == (to_logic_list(*list, l) ^ [| l |]) ;
  struct list *r = l->next;
  l->next = NULL;
  //@ assert unchanged{PreM,Here}(to_logic_list{PreM}(*list, l)) ;
  //@ assert to_logic_list(*list, l->next) == (to_logic_list(*list, l) ^ [| l |]) ;
  
  //@ assert linked_ll(*list, l, to_logic_list(*list, l)) ;
  //@ assert linked_ll(*list, l->next, to_logic_list(*list, l->next)) ;
  
  return r;
}

#endif
