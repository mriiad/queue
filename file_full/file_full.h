#ifndef FILE_FULL_H_INCLUDED
#define FILE_FULL_H_INCLUDED

#include "../fileSpec.spec"
/*@
    requires valid:    \valid_read(f) && Invariant(f);
    requires \valid_read(&f->capacity);
    requires \valid_read(&f->size1);
    requires \valid_read(&f->size2);
    assigns  \nothing;
    ensures  full:     \result == 2  <==>  Full(f);
    ensures  full_1: \result == 0  <==> Full1(f) && !Full2(f);
    ensures  full_2: \result == 1  <==> !Full1(f) && Full2(f);
    ensures  not_full: \result == -1  <==> !Full1(f) && !Full2(f);
*/
int file_full(const File* f);

#endif // FILE_FULL_H_INCLUDED
