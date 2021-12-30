#ifndef FILE_EMPTY_H_INCLUDED
#define FILE_EMPTY_H_INCLUDED

#include "../fileSpec.spec"
/*@
    requires valid:    \valid_read(f);
    requires valid2:  Invariant(f);
    requires \valid_read(f);
    ensures all_empty: \result == 2  <==>   Empty(f);
    ensures empty_1: \result == 0  <==>   Empty1(f) && !Empty2(f);
    ensures empty_2: \result == 1  <==>  !Empty1(f) && Empty2(f);
    ensures not_empty: \result == -1  <==>  !Empty1(f) && !Empty2(f);
    assigns \nothing;
*/
int file_empty(const File* f);

#endif // FILE_EMPTY_H_INCLUDED
