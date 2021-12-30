#ifndef FILE_SIZE1_H_INCLUDED
#define FILE_SIZE1_H_INCLUDED
#include "../fileSpec.spec"
/*@
    requires valid: \valid_read(f) && Invariant(f);
    requires \valid_read(f);
    requires \valid_read(&f->size1);
    assigns \result;
    ensures \result == f->size1 ;
*/
size_type file_size1(const File* f);

#endif // FILE_SIZE1_H_INCLUDED
