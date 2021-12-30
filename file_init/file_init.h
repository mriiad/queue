#ifndef FILE_INIT_H_INCLUDED
#define FILE_INIT_H_INCLUDED

#include "../headers/file.h"
#include "../fileSpec.spec"
/*@

    requires \valid(f) && \valid(storage1) && \valid(storage2);
    requires capacity > 0;
    requires \valid(storage1 + (0..capacity-1));
    requires \valid(storage2 + (0..capacity-1));
    requires \separated(f, storage1 + (0..capacity-1));
    requires \separated(f, storage2 + (0..capacity-1));
    assigns *f, f->capacity;
    assigns f->obj1, f->size1, f->head1, f->tail1;
    assigns f->obj2, f->size2, f->head2, f->tail2;
    ensures \valid(f);
    ensures f->capacity == capacity;
    ensures f->obj1 == storage1;
    ensures f->obj2 == storage2;
    ensures capacity > 0;
    ensures \valid(storage1 + (0..capacity-1));
    ensures \valid(storage2 + (0..capacity-1));
    ensures \separated(f, storage1 + (0..capacity-1));
    ensures \separated(f, storage2 + (0..capacity-1));
    ensures f->size1 == 0;
    ensures f->size2 == 0;
*/
void file_init(File* f, value_type* storage1, value_type* storage2, size_type capacity);

#endif // FILE_INIT_H_INCLUDED
