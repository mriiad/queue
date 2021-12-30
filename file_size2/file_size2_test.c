#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "file_size2.c"
void file_size2_test()
{
    File f;
    size_type capacity = 10;
    value_type storage1[capacity];
    value_type storage2[capacity];
    file_init(&f, storage1, storage2, capacity);
    assert(file_size2(&f) == f.size2);
}
