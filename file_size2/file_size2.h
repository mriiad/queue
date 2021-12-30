#ifndef FILE_SIZE2_H_INCLUDED
#define FILE_SIZE2_H_INCLUDED
#include "../fileSpec.spec"
/*@
    requires valid: \valid_read(f) && Invariant(f);
    requires \valid_read(f);
    requires \valid_read(&f->size2);
    assigns \result;
    ensures \result == f->size2 ;
*/
size_type file_size2(const File* f);
#endif // FILE_SIZE2_H_INCLUDED
