#include "file_full.h"
#include "../file_size1/file_size1.h"
#include "../file_size2/file_size2.h"
int file_full(const File* f)
{
    //size_type* f_size = file_size(f);
    if(file_size1(f) == f->capacity && file_size2(f) == f->capacity){// Les deux sont full
        return 2;
    }else if(file_size1(f) == f->capacity){// Le premier tableau est full
        return 0;
    }else if(file_size2(f) == f->capacity){// Le deuxième tableau est full
        return 1;
    }else{// Aucun des deux n'est full
        return -1;
    }
}


