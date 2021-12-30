#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "file_equal.c"

void file_equal_test()
{
    File f1;
    size_type capacity1 = 3;
    value_type storage1[capacity1];
    value_type storage2[capacity1];
    file_init(&f1, storage1, storage2, capacity1);
    file_put(&f1, 1, 1);
    file_put(&f1, 2, 1);
    file_put(&f1, 10, 2);
    File f2;
    size_type capacity2 = 3;
    value_type storage3[capacity2];
    value_type storage4[capacity2];
    file_init(&f2, storage3, storage4, capacity2);
    file_put(&f2, 1, 1);
    file_put(&f2, 2, 1);
    file_put(&f2, 10, 2);
    assert(file_equal(&f1, &f2) == 1);
}
