#ifndef FILE_H_INCLUDED
#define FILE_H_INCLUDED

#include "typedef.h"

struct File
{
    value_type* obj1;

    int head1;

    int tail1;

    size_type   size1;

    value_type* obj2;

    int head2;

    int tail2;

    size_type   size2;

    // La même pour les deux
    size_type capacity;
};
typedef struct File File;

#endif // FILE_H_INCLUDED
