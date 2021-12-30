#include "file_size1.h"
#include <stdlib.h>

extern  void*malloc(size_t);
size_type file_size1(const File* f)
{
    return f->size1;
}


