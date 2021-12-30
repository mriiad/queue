#ifndef EQUAL_H_INCLUDED
#define EQUAL_H_INCLUDED
#include "../../fileSpec.spec"
/*@
  requires valid:  \valid_read(a + (0..n-1));
  requires valid:  \valid_read(b + (0..n-1));
  assigns          \nothing;
  ensures result:  \result <==> EqualRanges{Here,Here}(a, n, b);
*/

int equal(const value_type* a, size_type n, const value_type* b);

#endif // EQUAL_H_INCLUDED
