#ifndef FILE_PUT_H_INCLUDED
#define FILE_PUT_H_INCLUDED

#include "../fileSpec.spec"
/*@

requires \valid(f) && Invariant(f);
requires choice == 1 || choice ==2 ;

behavior obj1_empty_or_emptyboth:
    assumes choice == 1;
    assumes Empty(f) || Empty1(f);
    assigns f->head1;
    assigns f->tail1;
    assigns f->obj1[f->tail1];
    assigns f->size1;
    ensures \valid(f) && Invariant(f);
    ensures Storage1(f) == Storage1{Old}(f);
	ensures f->head1 == \old(f->head1)+1 ;
	ensures f->tail1 == \old(f->tail1)+1;
    ensures Capacity(f) == Capacity{Old}(f);
    ensures \result == 1;

behavior obj1_emptyboth:
    assumes choice == 1;
    assumes !Full(f) && !Full1(f);
    assigns f->tail1;
    assigns f->obj1[f->tail1];
    assigns f->size1;
    ensures \valid(f) && Invariant(f);
    ensures Storage1(f) == Storage1{Old}(f);
	ensures f->tail1 != \old(f->tail1);
    ensures Capacity(f) == Capacity{Old}(f);
    ensures \result == 1;


behavior obj2_empty_or_emptyboth:
    assumes choice == 2;
    assumes Empty(f) || Empty2(f);
    assigns f->head2;
    assigns f->tail2;
    assigns f->obj2[f->tail2];
    assigns f->size2;
    ensures \valid(f) && Invariant(f);
    ensures Storage2(f) == Storage2{Old}(f);
	ensures f->head2 == \old(f->head2)+1 ;
	ensures f->tail2 == \old(f->tail2)+1;
    ensures Capacity(f) == Capacity{Old}(f);
    ensures \result == 1;

behavior obj2_emptyboth:
    assumes choice == 2;
    assumes !Full(f) && !Full2(f);
    assigns f->tail2;
    assigns f->obj2[f->tail2];
    assigns f->size2;
    ensures \valid(f) && Invariant(f);
    ensures Storage2(f) == Storage2{Old}(f);
	ensures f->tail2 != \old(f->tail2);
    ensures Capacity(f) == Capacity{Old}(f);
    ensures \result == 1;

behavior zero:
    assumes choice != 1 && choice != 2;
    ensures \result == 0 ;
behavior zero_bis:
        assumes choice == 1 || choice == 2;
        ensures \result == 0 <==> (choice == 1 || choice == 2) &&
         (f->size1 == f->capacity ) &&
         (f->size2 == f->capacity ) ;

complete behaviors;
disjoint behaviors;

*/
int file_put(File* f, int e, int choice); // Choice: permet de savoir si on insère dans le premier ou le deuxième tableau; 1 premier tableau 2 deuxieme

#endif // FILE_PUT_H_INCLUDED
