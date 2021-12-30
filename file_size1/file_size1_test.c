#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "file_size1.c"

void file_size1_test()
{
    File f;
    size_type capacity = 10;
    value_type storage1[capacity];
    value_type storage2[capacity];
    file_init(&f, storage1, storage2, capacity);
    assert(file_size1(&f) == f.size1);
}
