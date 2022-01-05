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
  @ assigns \nothing ;
  @
  @ ensures HandlerSep:    dptr_separated_from_list(list, to_logic_list(*list, NULL));
  @ ensures ValidHandler:  \valid(list);
  @ ensures Linked:         linked_ll(*list, NULL, to_logic_list(*list, NULL));
  @ ensures LengthMax:     \length(to_logic_list(*list, NULL)) < INT_MAX ;
  @
  @ behavior empty:
  @   assumes *list == NULL;
  @   ensures \result == NULL;
  @
  @ behavior not_empty:
  @   assumes *list != NULL;
  @   ensures \let ll = to_logic_list(*list, NULL) ; \result == \nth(ll, \length(ll)-1);
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
struct list*
list_tail(list_t list)
{
  struct list *l;

  if(*list == NULL) {
    return NULL;
  }
  
  int n = 0;
  /*@ loop invariant \nth(to_logic_list(*list, NULL), n) == l && l != NULL;
    @ loop invariant linked_ll(l, NULL, to_logic_list(l, NULL));
    @ loop invariant linked_ll(*list, NULL, to_logic_list(*list, NULL));
    @ loop invariant n == \length(to_logic_list(*list, NULL)) - 
    @                     \length(to_logic_list(l, NULL));
    @ loop invariant 0 <= n <= \length(to_logic_list(*list, NULL))-1 ;
    @ loop assigns l, n ;
    @ loop variant \length(to_logic_list(l->next, NULL)); 
    @*/
  for(l = *list; l->next != NULL; l = l->next) {
    //@ assert \valid(l);
    //@ assert 0 <= n < \length(to_logic_list(*list, NULL))-1 ;
    ++n;
  }
  return l;
}

#endif
