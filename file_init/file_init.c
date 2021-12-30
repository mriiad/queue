#include "file_init.h"

void file_init(File* f, value_type* storage1, value_type* storage2, size_type capacity)
{
    f->obj1      = storage1;
    f->head1     = -1;
    f->tail1     = -1;
    f->size1     = 0u;
    f->obj2      = storage2;
    f->head2     = -1;
    f->tail2     = -1;
    f->size2     = 0u;
    f->capacity = capacity;
}
