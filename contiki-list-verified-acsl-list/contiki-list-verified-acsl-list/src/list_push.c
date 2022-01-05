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
  @ ensures First:         *list == item ;
  @
  @ assigns *list,
  @         item->next,
  @         { l->next 
  @           | struct list* l ; 
  @             in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && 
  @             \at(l->next, Pre) == item } ;
  @
  @ behavior does_not_contain:
  @   assumes ! in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures AddedBegin: to_logic_list(*list, NULL) ==
  @                     ([| item |] ^ to_logic_list{Pre}(\old(*list), NULL)) ;
  @   ensures SizeInc: \length(to_logic_list(*list, NULL)) == 
  @                    \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) + 1 ;
  @
  @ behavior contains:
  @   assumes in_list(item, to_logic_list(*list, NULL)) ;
  @   ensures NewList: to_logic_list(*list, NULL) ==
  @     ([| item |] ^ to_logic_list{Pre}(\old(*list), item) ^ 
  @      to_logic_list{Pre}(\at(item->next,Pre), NULL)) ;
  @   ensures SameSize: \length(to_logic_list(*list, NULL)) == 
  @                     \length(to_logic_list{Pre}(\at(*list,Pre), NULL)) ;
  @           
  @ complete behaviors;
  @ disjoint behaviors;
*/
void
list_push(list_t list, struct list *item)
{
  /* Make sure not to add the same element twice */
  list_remove(list, item);

  //@ ghost AR: ;
  
  /*@ assert SepReformulation: \let ll = to_logic_list(*list, NULL) ;
      \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), item) ;
  */

  ((struct list *)item)->next = *list;

  //@ assert unchanged{AR, Here}(to_logic_list{AR}(\at(*list, AR), NULL));
  //@ assert to_logic_list(item, NULL) == ([| item |] ^ to_logic_list(*list, NULL));
  //@ ghost Inter: ;

  //@ assert \separated(list, item);
  //@ assert dptr_separated_from_list(list, to_logic_list(item, NULL));
  /*@ assert SepReformulation: \let ll = to_logic_list(*list, NULL) ;
      \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), list) ;
  */

  
  *list = item;
  
  //@ assert unchanged{Inter, Here}(to_logic_list{Inter}(\at(item, Inter), NULL));
  //@ assert to_logic_list(*list, NULL) == ([| item |] ^ to_logic_list{AR}(\at(*list, AR), NULL));
}

#endif
