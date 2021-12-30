#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "equal.c"

void equal_test()
{
    int n = 3;
    value_type tab1[n] = {10, 15, 3};
    value_type tab2[n] = {10, 15, 3};
    size_type result = equal(tab1, n, tab2);
    assert(result == n);
}
