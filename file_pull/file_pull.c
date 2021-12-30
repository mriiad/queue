#include "file_pull.h"
#include "../file_empty/file_empty.h"
#include "../file_full/file_full.h"
#include "../file_size1/file_size1.h"
#include "../file_size2/file_size2.h"
void file_pull(File* f, int choice)
{
    switch(choice)
    {
        case 1: // Supprimer du premier tableau
            if(file_empty(f) != 2 && file_empty(f) != 0 && file_full(f) != 2 && file_full(f) != 1){ // Le premier tableau n'est pas vide et le deuxième n'est pas plein -> on peut insérer
                int e = f->obj1[f->head1];
                f->size1--;
                //size_type *tab = file_size(f);
                if(file_size1(f) == 0)
                {
                    f->head1 = -1;
                    f->tail1 = -1;
                }else{
                    if(f->head1 == (f->capacity - 1)){
                        f->head1 = 0;
                    }else{
                        f->head1++;
                    }
                }
                file_put(f, e, 2);
            }
            break;
        case 2: // Supprimer du deuxième tableau
            if(file_empty(f) != 2 && file_empty(f) != 1){ // Le deuxième tableau n'est pas vide
                f->size2--;
                //size_type *tab = file_size(f);
                if(file_size2(f) == 0)
                {
                    f->head2 = -1;
                    f->tail2 = -1;
                }else{
                    if(f->head2 == (f->capacity - 1)){
                        f->head2 = 0;
                    }else{
                        f->head2++;
                    }
                }
            }
            break;
    }
}
