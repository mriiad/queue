#include "file_reverse.h"
#include "../file_size1/file_size1.h"
#include "../file_size2/file_size2.h"
#include "../file_put/file_put.h"
void file_reverse(File* f)
{
    if(file_empty(f) == 1)  // Le deuxième tableau est vide => le premier n'est pas vide (car file_empty(f) != 2)
    {
        /*@
        loop invariant 0<= i<=((f->size1)-1)  ;
        loop assigns i ;
        loop variant 0+i;
        */
        for(int i = file_size1(f) - 1; i >= 0  ; i--)
        {
            file_put(f, f->obj1[i], 2);
        }
    }
}
