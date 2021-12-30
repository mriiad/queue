#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "file_empty.c"

void file_empty_test()
{
    File f;
    size_type capacity = 10;
    value_type storage1[capacity];
    value_type storage2[capacity];
    file_init(&f, storage1, storage2, capacity);
    //@ assert \valid_read(f.obj1) ;
    //@ assert \valid_read(f.obj2) ;
    //@ assert f.capacity == capacity ;
    //@ assert f.size1 == 0 ;
    //@ assert f.size2 == 0 ;
    //@ assert f.head1 == -1 ;
    //@ assert f.head2 == -1 ;
    //@ assert f.tail1 == -1 ;
    //@ assert f.tail2 == -1 ;
    int result = file_empty(&f);
    //@ assert f.size1 == 0 ;
    //@ assert f.size2 == 0 ;
    assert(result == 2); // the two arrays are empties
}
