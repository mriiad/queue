#ifndef FILESPEC_SPEC_INCLUDED
#define FILESPEC_SPEC_INCLUDED
#include "headers/file.h"

/*@
    logic integer Capacity{L}(File* f) = f->capacity;
    logic integer Size1{L}(File* f) = f->size1;
    logic integer Size2{L}(File* f) = f->size2;
    logic value_type* Storage1{L}(File* f) = f->obj1;
    logic value_type* Storage2{L}(File* f) = f->obj2;


    predicate
     Separated1(File* f1, File* f2) =
       \separated(f1, f1->obj1 + (0..f1->capacity-1),
                  f1, f2->obj1 + (0..f2->capacity-1));
    predicate
     Separated2(File* f1, File* f2) =
       \separated(f1, f1->obj2 + (0..f1->capacity-1),
                  f1, f2->obj2 + (0..f2->capacity-1));

    predicate
        EqualRanges{K,L}(value_type* a, integer n, value_type* b) =
          \forall integer i; 0 <= i < n ==> \at(a[i],K) == \at(b[i],L);
    predicate
        EqualRanges{K,L}(value_type* a, integer m, integer n, value_type* b) =
          \forall integer i; m <= i < n ==> \at(a[i],K) == \at(b[i],L);
    predicate
        EqualRanges{K,L}(value_type* a, integer m, integer n,
                         value_type* b, integer p) =
          EqualRanges{K,L}(a+m, n-m, b+p);

    predicate
        EqualRanges{K,L}(value_type* a, integer m, integer n, integer p) =
          EqualRanges{K,L}(a, m, n, a, p);

    predicate
        Empty{L}(File* f) =  (Size1(f) == 0) && (Size2(f) == 0);
    predicate
        Empty1{L}(File* f) =  Size1(f) == 0;
    predicate
        Empty2{L}(File* f) =  Size2(f) == 0;
     predicate
        Full{L}(File* f)  =  (Size1(f) == Capacity(f)) && (Size2(f) == Capacity(f));
    predicate
        Full1{L}(File* f)  =  Size1(f) == Capacity(f);
     predicate
        Full2{L}(File* f)  =  Size2(f) == Capacity(f);
    predicate
         Equal1{F1,F2}(File* f1, File* f2) =
           Size1{F1}(f1) == Size1{F2}(f2) &&
           EqualRanges{F1,F2}(Storage1{F1}(f1), Size1{F1}(f1), Storage1{F2}(f2));
    predicate
         Equal2{F1,F2}(File* f1, File* f2) =
           Size2{F1}(f1) == Size2{F2}(f2) &&
           EqualRanges{F1,F2}(Storage2{F1}(f1), Size2{F1}(f1), Storage2{F2}(f2));
    predicate
        Invariant{L}(File* f) =
          0 < Capacity(f) &&
          0 <= Size1(f) <= Capacity(f) &&
          0 <= Size2(f) <= Capacity(f) &&
          \valid(Storage1(f) + (0..Capacity(f)-1)) &&
          \separated(f, Storage1(f) + (0..Capacity(f)-1))&&
          \valid(Storage2(f) + (0..Capacity(f)-1)) &&
          \separated(f, Storage2(f) + (0..Capacity(f)-1));

    predicate
        Unchanged{K,L}(value_type* a, integer m, integer n) =
          \forall integer i; m <= i < n ==> \at(a[i],K) == \at(a[i],L);
    predicate
        Unchanged{K,L}(value_type* a, integer n) =
          Unchanged{K,L}(a, 0, n);


*/

#endif /* FILESPEC_SPEC_INCLUDED */
