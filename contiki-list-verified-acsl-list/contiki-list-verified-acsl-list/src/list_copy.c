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

/*@ requires ValidHandler: \valid(src);
  @ requires HandlerSep: dptr_separated_from_list(src, to_logic_list(*src, NULL));
  @ requires Linked: linked_ll(*src, NULL, to_logic_list(*src, NULL));
  @ requires LengthMax: \length(to_logic_list(*src, NULL)) < INT_MAX ;
  @
  @ requires \valid(dest) ;
  @ requires dptr_separated_from_list(dest, to_logic_list(*src, NULL));
  @
  @ assigns *dest ;
  @ 
  @ ensures HandlerSep1:  dptr_separated_from_list(src, to_logic_list(*src, NULL));
  @ ensures HandlerSep2:  dptr_separated_from_list(dest, to_logic_list(*src, NULL));
  @ ensures LengthMax:    \length(to_logic_list(*src, NULL)) < INT_MAX ;
  @ ensures ValidHandler: \valid(src) && \valid(dest);
  @ ensures Linked:        linked_ll(*src, NULL, to_logic_list(*src, NULL));
  @ ensures unchanged{Pre,Here}(to_logic_list{Pre}(*src, NULL));
  @ ensures linked_ll(*dest, NULL, to_logic_list(*dest, NULL));
  @ ensures to_logic_list(*dest, NULL) == to_logic_list{Pre}(*src, NULL) ;
  @*/
void
list_copy(list_t dest, list_t src)
{
  /*@ assert SepDest: 
    \let ll = to_logic_list{Pre}(*src, NULL) ;
    \forall integer i ; 0 <= i < \length(ll) ==> \separated(\nth(ll, i), dest) ;
  */
  *dest = *src;
  //@ assert unchanged{Pre,Here}(to_logic_list{Pre}(*src, NULL)) ;
  //@ assert linked_ll(*src, NULL, to_logic_list(*src, NULL));
}

#endif
