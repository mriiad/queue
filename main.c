#include <stdio.h>
#include <stdlib.h>

#include "file_init/file_init_test.c"
#include "file_size1/file_size1_test.c"
#include "file_size2/file_size2_test.c"
#include "file_empty/file_empty_test.c"
#include "file_full/file_full_test.c"
#include "file_put/file_put_test.c"
#include "file_pull/file_pull_test.c"
#include "file_reverse/file_reverse_test.c"
#include "file_equal/file_equal_test.c"

int main()
{
    //file_init_test();
    file_size1_test();
    file_size2_test();
    //file_empty_test();
    //file_full_test();
    //file_put_test();
    file_pull_test();
    //file_reverse_test();
    //file_equal_test();
    return 0;
}
