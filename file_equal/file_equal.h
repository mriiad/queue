#ifndef FILE_EQUAL_H_INCLUDED
#define FILE_EQUAL_H_INCLUDED
#include "../fileSpec.spec"
/*@
    requires valid:     \valid(f1) && Invariant(f1);
    requires valid:     \valid(f2) && Invariant(f2);
    assigns             \nothing;
    ensures  equal:     \result == 1  <==>  Equal1{Here,Here}(f1, f2) && Equal2{Here,Here}(f1, f2);
    ensures  not_equal: \result == 0  <==> !Equal1{Here,Here}(f1, f2) && !Equal2{Here,Here}(f1, f2) ;
*/
int file_equal(const File* f1, const File* f2);

#endif // FILE_EQUAL_H_INCLUDED
