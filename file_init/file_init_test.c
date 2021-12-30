#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "file_init.c"

void file_init_test()
{
    File f;
    size_type capacity = 10;
    value_type storage1[capacity];
    value_type storage2[capacity];
    file_init(&f, storage1, storage2, capacity);
    assert(f.capacity == capacity);
    assert(f.head1 == -1);
    assert(f.tail1 == -1);
    assert(f.size1 == 0);
    assert(f.head2 == -1);
    assert(f.tail2 == -1);
    assert(f.size2 == 0);
}
