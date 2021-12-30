#include "file_equal.h"
#include "../Utils/equal/equal.c"
#include "../fileSpec.spec"
#include "../file_size1/file_size1.h"
#include "../file_size2/file_size2.h"
int file_equal(const File* f1, const File* f2)
{
    //size_type *tab1 = file_size(f1);
    //size_type *tab2 = file_size(f2);
    //if((file_size1(f1) == tab2[1]) && (tab1[1] == tab2[1]) && (equal(f1->obj1, tab1[0], f2->obj1) == 1) && (equal(f1->obj2, tab1[1], f2->obj2) == 1)){
    if((file_size1(f1) == file_size1(f2)) && (file_size2(f1) == file_size2(f2)) && (equal(f1->obj1, file_size1(f1), f2->obj1) == 1) && (equal(f1->obj2, file_size2(f1), f2->obj2) == 1)){
        return 1;
    }

    return 0;
}
