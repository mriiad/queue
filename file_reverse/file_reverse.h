#ifndef FILE_REVERSE_H_INCLUDED
#define FILE_REVERSE_H_INCLUDED
#include "../fileSpec.spec"
/*@
requires valid:  \valid(f) && Invariant(f);
requires \valid_read(f);
behavior empty1 :
    assumes Empty2(f);
    ensures (\exists integer i ; 0 <= i<= ((f->size1)-1));
behavior else:
    assumes !Empty2(f);
    assigns \nothing;
complete behaviors;
disjoint behaviors;

*/
void file_reverse(File* f);

#endif // FILE_REVERSE_H_INCLUDED
