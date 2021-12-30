#include "file_size2.h"
#include <stdlib.h>

extern  void*malloc(size_t);
size_type file_size2(const File* f)
{
    return f->size2;
}

