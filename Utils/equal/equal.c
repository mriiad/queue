#include "equal.h"
#include "../mismatch/mismatch.c"

int equal(const value_type* a, size_type n, const value_type* b)
{
    if(mismatch(a, n, b) == n){
        return 1;
    }
    return 0;
}
