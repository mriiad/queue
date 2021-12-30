#include "file_empty.h"
#include "../file_size1/file_size1.h"
#include "../file_size2/file_size2.h"

int file_empty(const File* f)
{
    //size_type* f_size = file_size(f);
    if(f->size1 == 0 && f->size2 == 0){// Les deux tableaux sont vides
        return 2;
    }else if(f->size1 == 0){// Le premier tableau est vide
        return 0;
    }else if(f->size2 == 0){// Le deuxième tableau est vide
        return 1;
    }else{// Aucun des deux tableaux n'est vide
        return -1;
    }
}
