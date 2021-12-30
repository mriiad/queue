#include "file_put.h"
#include "../file_empty/file_empty.h"
#include "../file_full/file_full.h"

int file_put(File* f, int e, int choice)
{
    switch(choice)
    {
        case 1:
            if(file_empty(f) == 2 || file_empty(f) == 0){ // Les deux tableaux sont vides OU que le premier tableau est vide
                f->head1++;
                f->tail1++;
                f->obj1[f->tail1] = e;
                f->size1++;
                return 1;
            }else{
                if(file_full(f) != 2 && file_full(f) != 0){ // Les deux tableaux ne sont pas pleins OU que le premier tableau n'est pas plein
                    if(f->tail1 == (f->capacity - 1)){
                        f->tail1 = 0;
                    }else{
                        f->tail1++;
                    }
                    f->obj1[f->tail1] = e;
                    (f->size1)++;
                    return 1;
                }
                return 0;
            }
            break;
        case 2:
            if(file_empty(f) == 2 || file_empty(f) == 1){ // // Les deux tableaux sont vides OU que le 2e tableau est vide
                f->head2++;
                f->tail2++;
                f->obj2[f->tail2] = e;
                (f->size2)++;
                return 1;
            }else{
                if(file_full(f) != 2 && file_full(f) != 1){ // // Les deux tableaux ne sont pas pleins OU que le 2e tableau n'est pas plein
                    if(f->tail2 == (f->capacity - 1)){
                        f->tail2 = 0;
                    }else{
                        f->tail2++;
                    }
                    f->obj2[f->tail2] = e;
                    f->size2++;
                    return 1;
                }
                return 0;
            }
            break;
        default: // Dans le cas où choice != 1 et 2
            return 0;
    }
    return 0;
}
