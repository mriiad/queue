#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "file_pull.c"

void file_pull_test()
{
    File f;
    size_type capacity = 3;
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
    file_put(&f, 1, 1);
    file_put(&f, 2, 1);
    assert(file_size1(&f) == 2);
    //@ assert f.size1 == 2;
    file_put(&f, 3, 2);
    file_put(&f, 4, 2);
    assert(file_size2(&f) == 2);
    //@ assert f.size2 == 2;
    file_pull(&f, 1);
    assert(file_size2(&f) == 3);
    //@ assert f.size2 == 3;
    //@ assert f.size1 == 1;
    file_pull(&f, 1); // Si le deuxi?me tableau est plein alors on ne supprime pas la valeur du premier tableau
    assert(file_size1(&f) == 1);
    //@ assert f.size1 == 1;
    //@ assert f.size2 == 3;
}
