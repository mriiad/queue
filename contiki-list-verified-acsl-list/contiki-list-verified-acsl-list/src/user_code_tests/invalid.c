/*
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
 * Authors: - Allan Blanchard <mail@allan-blanchard.fr>
 *          - Nikolai Kosmatov <nikolai.kosmatov@cea.fr>
 *          - Frédéric Loulergue <frederic.loulergue@nau.edu>
 */

/*@
  requires \valid(list);

  ensures to_logic_list(*list, NULL) == [| |];
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  ensures *list == NULL;

  assigns *list ;
*/
void fail_push_pop_empty(list_t list)
{
  list_init(list);
  
  struct list l1 ;
  list = (struct list**) &l1 ; // <<< breaks list

  list_push(list, &l1); // <<< fails on precondition
  list_pop(list);
}

/*@
  // requires \valid(list); <<< removed list handler validity

  ensures to_logic_list(*list, NULL) == [| |];
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  ensures *list == NULL;

  assigns *list ;
*/
void fail_push_chop_empty(list_t list)
{
  list_init(list); // <<< fails on precondition
  
  struct list l1 ;

  list_push(list, &l1);
  list_chop(list);
}

/*@
  requires \valid(list);

  ensures to_logic_list(*list, NULL) == [| |];
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  ensures *list == NULL;

  assigns *list ;
*/
void fail_push_remove_empty(list_t list)
{
  list_init(list);
  
  struct list l1 ;

  list_push(list, &l1);
  l1.next = &l1 ; // <<< breaks list
  list_remove(list, &l1); // <<< fails on precondition
}

/*@
  requires \valid(list);

  ensures to_logic_list(*list, NULL) == [| |];
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  ensures *list == NULL;

  assigns *list ;
*/
void fail_add_pop_empty(list_t list)
{
  list_init(list);
  
  struct list l1 ;
  *list = &l1 ; // <<< breaks list

  list_add(list, &l1); // <<< fails on precondition
  list_pop(list);
}

/*@
  requires \valid(list);

  ensures to_logic_list(*list, NULL) == [| |]; // <<< will fail
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  ensures *list == NULL;

  assigns *list ;
*/
void fail_add_chop_empty(list_t list)
{
  list_init(list);
  
  struct list l1 ;

  // reversed operations
  list_chop(list);
  list_add(list, &l1);
}

/*@
  requires \valid(list);

  ensures to_logic_list(*list, NULL) == [| |];
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  ensures *list == NULL;

  assigns *list ;
*/
void fail_add_remove_empty(list_t list)
{
  //list_init(list); <<< Forgotten initialization
  
  struct list l1 ;

  list_add(list, &l1); // <<< fails on precondition
  list_remove(list, &l1);
}

/*@
  requires \valid(list);
  requires \valid(l1) && \separated(list, l1);

  ensures to_logic_list(*list, NULL) == [| l1 |];
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

  assigns *list, l1->next ;
*/
void fail_push_push_pop(list_t list, struct list* l1)
{
  list_init(list);
  
  struct list l2 ;

  //<<< reversed operations
  list_push(list, &l2);
  list_push(list, l1);
  //@ ghost L: ;
  list_pop(list);
  /*@ assert to_logic_list{L}(\at(*list, L), NULL) ==
             ([| \at(*list, L) |] ^ to_logic_list(*list, NULL)) ;
  */
  //@ assert to_logic_list(*list, NULL) == [| l1 |] ;
  //@ assert linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
}

/*@
  requires \valid(list);
  requires \valid(l1) && \separated(list, l1);

  ensures to_logic_list(*list, NULL) == [| |]; //<<< forgotten l1 
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

  assigns *list, l1->next ;
*/
void fail_push_push_chop(list_t list, struct list* l1)
{
  list_init(list);
  
  struct list l2 ;

  list_push(list, &l2);
  list_push(list, l1);
  //@ assert to_logic_list(*list, NULL) == [| l1 , &l2 |] ;
  //@ assert in_list(&l2, to_logic_list(*list, NULL)) ;
  /*@ assert to_logic_list(*list, NULL) ==
      (to_logic_list(*list, &l2) ^ to_logic_list(&l2, NULL)) ;
  */
  //@ assert to_logic_list(*list, &l2) == [| l1 |] ;
  //@ ghost L: ;
  list_chop(list);
  /*@ assert \let pre_ll = to_logic_list{L}(\at(*list, L), NULL) ; 
    \nth(pre_ll, \length(pre_ll)-1) == &l2 ;
  */
}

/*@
  requires \valid(list) ;
  requires \exists struct list* l2 ; to_logic_list(*list, NULL) == [| l2 |] &&
           \separated(l1, l2, l3) ;
  // requires \separated(list, l1, l3) ; <<< forgotten separation
  requires \valid(l1) && \valid(l3) ;
  
  requires linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  requires dptr_separated_from_list(list, to_logic_list(*list, NULL)) ;

  ensures to_logic_list(*list, NULL) == 
          ([| l1 |] ^ to_logic_list{Pre}(\at(*list, Pre), NULL) ^ [| l3 |]) ;
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

  assigns *list,
          l3->next,
	  l1->next,
	  { l->next 
	    | struct list* l ; 
	      in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && \at(l->next, Pre) == NULL } ;
*/
void fail_push_add_on_single(list_t list, struct list *l1, struct list *l3)
{
  list_push(list, l1);

  /*@ assert
    { l->next 
    | struct list* l ; 
      in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && \at(l->next, Pre) == NULL } 
    ==
    { l->next 
      | struct list* l ; 
        in_list(l, to_logic_list(*list, NULL)) && l->next == NULL } ;
  */
  /*@ assert
    { l->next
    | struct list* l ;
      in_list(l, to_logic_list(*list, NULL)) && l->next == l3 }
    == {} ;
  */
  
  list_add(list, l3);
}

/*@
  requires \valid(list) ;
  requires \exists struct list* l2 ; to_logic_list(*list, NULL) == [| l2 |] &&
           \separated(l1, l2, l3) ;
  requires \separated(list, l1, l3) ;
  // requires \valid(l1) && \valid(l3) ; <<< forgotten validity
  
  requires linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  requires dptr_separated_from_list(list, to_logic_list(*list, NULL)) ;

  ensures to_logic_list(*list, NULL) == 
          ([| l1 |] ^ to_logic_list{Pre}(\at(*list, Pre), NULL) ^ [| l3 |]) ;
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  
  assigns *list,
          l3->next,
	  l1->next,
	  { l->next 
	    | struct list* l ; 
	      in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && \at(l->next, Pre) == NULL } ;
*/
void fail_add_push_on_single(list_t list, struct list *l1, struct list *l3)
{
  list_add(list, l3);
  list_push(list, l1);
}


/*@
  requires \valid(list) ;
  requires \exists struct list* l2 ; to_logic_list(*list, NULL) == [| l2 |] &&
           \separated(l1, l2) ;
  requires \separated(list, l1) ;
  requires \valid(l1);
  
  requires linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  // <<< forgotten handler separation
  // requires dptr_separated_from_list(list, to_logic_list(*list, NULL)) ; 

  ensures to_logic_list(*list, NULL) == [| l1 |] ;
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

  assigns *list, l1->next ;
*/
void fail_push_remove_on_single(list_t list, struct list *l1)
{
  struct list* root = *list ;
  
  list_push(list, l1);
  list_remove(list, root);
}


/*@
  requires \valid(list);
  requires \separated(l1, l2, l3, list);
  requires \valid(l1) && \valid(l2) && \valid(l3) ;

  ensures to_logic_list(*list, NULL) == [| l1, l2, l3 |] ; // <<< wrong list
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

  assigns *list, l1->next, l2->next, l3->next ;
*/
void fail_push_add_add_remove(list_t list, struct list *l1, struct list* l2, struct list *l3)
{
  list_init(list);
  list_push(list, l1);
  list_add(list, l2);
  //@  assert to_logic_list(*list, NULL) == [| l1, l2 |] ;
  
  list_add(list, l3);

  //@ assert to_logic_list(*list, NULL) == [| l1, l2, l3 |] ;
  //@ assert linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  //@ assert \nth(to_logic_list(*list, NULL), 0) == l1 ;
  //@ assert \nth(to_logic_list(*list, NULL), 1) == l2 ;
  //@ assert \nth(to_logic_list(*list, NULL), 0)->next == \nth(to_logic_list(*list, NULL), 1) ;
  //@ assert \nth(to_logic_list(*list, NULL), 2) == l3 ;
  //@ assert \nth(to_logic_list(*list, NULL), 1)->next == \nth(to_logic_list(*list, NULL), 2) ;
  //@ assert l2->next == l3 ;
  
  /*@ assert linked_ll(*list, NULL, to_logic_list(*list, NULL)) ==>
      in_list(l1->next, to_logic_list(*list, NULL)) ==>
      to_logic_list(*list, NULL) == (to_logic_list(l1, l1->next) ^ to_logic_list(l2, NULL));
  */
  //@ assert to_logic_list(*list, NULL) == (to_logic_list(l1, l1->next) ^ to_logic_list(l2, NULL)) ;
  /*@ assert linked_ll(l2, NULL, to_logic_list(l2, NULL)) ==>
      in_list(l2->next, to_logic_list(l2, NULL)) ==>
      to_logic_list(l2, NULL) == (to_logic_list(l2, l2->next) ^ to_logic_list(l3, NULL));
  */
  //@ assert to_logic_list(l2, NULL) == (to_logic_list(l2, l2->next) ^ to_logic_list(l3, NULL));
  //@ assert to_logic_list(l1, l2) == [| l1 |] ;
  //@ assert to_logic_list(l2, l2->next) == [| l2 |] ;
  //@ assert to_logic_list(l2->next, NULL) == [| l3 |] ;
  
  list_remove(list, l2);
}

/*@
  requires \valid(list);
  requires \separated(l1, l2, l3, list);
  requires \valid(l1) && \valid(l2) && \valid(l3) ;

  ensures to_logic_list(*list, NULL) == [| l1 , l2 |] ; // <<< wrong list
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

  assigns *list, l1->next, l2->next, l3->next ;
*/
void fail_push_add_remove_add(list_t list, struct list *l1, struct list* l2, struct list *l3)
{
  list_init(list);
  list_push(list, l1);
  list_add(list, l2);
  list_remove(list, l2);
  list_add(list, l3);
}

/*@
  requires \valid(list) ;
  requires \exists struct list* l2 ; to_logic_list(*list, NULL) == [| l2 |] &&
           \separated(l1, l2);
  requires \separated(list, l1) ;
  requires \valid(l1);
  
  // <<< Forgotten list linked_ll
  // requires linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  requires dptr_separated_from_list(list, to_logic_list(*list, NULL)) ;

  ensures to_logic_list(*list, NULL) == (to_logic_list{Pre}(\old(*list), NULL) ^ [| l1 |]) ;
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

  assigns *list,
          l1->next,
	  { l->next 
	    | struct list* l ; 
	      in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && \at(l->next, Pre) == NULL } ;
*/
void fail_push_add_same_single(list_t list, struct list *l1)
{
  list_push(list, l1);
  list_add(list, l1);
}

/*@
  requires \valid(list) ;
  requires \exists struct list* l2 ; to_logic_list(*list, NULL) == [| l2 |] &&
           \separated(l1, l2);
  requires \separated(list, l1) ;
  requires \valid(l1);
  
  requires linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;
  requires dptr_separated_from_list(list, to_logic_list(*list, NULL)) ;

  //                                                          Wrong label
  //                                                               v
  ensures to_logic_list(*list, NULL) == ([| l1 |] ^ to_logic_list{Here}(*list, NULL)) ;
  ensures linked_ll(*list, NULL, to_logic_list(*list, NULL)) ;

  assigns *list,
          l1->next,
	  { l->next 
	    | struct list* l ; 
	      in_list(l, to_logic_list{Pre}(\at(*list, Pre), NULL)) && \at(l->next, Pre) == NULL } ;
*/
void fail_add_push_same_single(list_t list, struct list *l1)
{
  list_add(list, l1);
  //@ assert to_logic_list(*list, NULL) == (to_logic_list{Pre}(\at(*list, Pre), NULL) ^ [| l1 |]) ;
  list_push(list, l1);
}
