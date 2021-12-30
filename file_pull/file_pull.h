#ifndef FILE_PULL_H_INCLUDED
#define FILE_PULL_H_INCLUDED
#include "../fileSpec.spec"
/*
* Fonction qui supprime le première élément du tableau
* choice = 1 : récupère le premier élément du premier tableau et l'ajoute au deuxième tableau
* choice = 2 : supprime le premier élément du deuxième tableau
*/
/*@
requires \valid(f) && Invariant(f);
requires choice == 1 || choice == 2;
ensures \valid(f) && Invariant(f);

behavior obj1_then_size_empty:
    assumes !Empty1(f) && !Full2(f);
    assumes f->size1 == 0;
    assigns f->size1;
    assigns f->head1;
    assigns f->tail1;

    ensures f->head1 == -1;
    ensures f->tail1 == -1;

behavior obj1_then_size_notempty:
    assumes !Empty1(f) && !Full2(f);
    assumes f->size1 != 0;
    assigns f->size1;
    assigns f->head1;

    ensures f->head1 != \old(f->head1);

behavior obj2_then_size_empty:
    assumes !Empty2(f) ;
    assumes f->size2 == 0;
    assigns f->size2;
    assigns f->head2;
    assigns f->tail2;

    ensures f->head2 == -1;
    ensures f->tail2 == -1;

behavior obj2_then_size_notempty:
    assumes !Empty2(f);
    assumes f->size2 != 0;
    assigns f->size2;
    assigns f->head2;

    ensures f->head2 ==0 || f->head2 == \old(f->head2)+1;

complete behaviors;
disjoint behaviors;

*/
void file_pull(File* f, int choice);

#endif // FILE_PULL_H_INCLUDED
