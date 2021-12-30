#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "file_full.c"

void file_full_test()
{
    File f;
    size_type capacity = 10;
    value_type storage1[capacity];
    value_type storage2[capacity];
    file_init(&f, storage1, storage2, capacity);
    int result = file_full(&f);
    assert(result == -1); // the two arrays are empties
}
