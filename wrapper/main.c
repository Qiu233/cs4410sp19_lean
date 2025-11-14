#include <stdio.h>

const int BOOL_TAG   = 0x00000001;
const int BOOL_TRUE  = 0x80000001; // These must be the same values
const int BOOL_FALSE = 0x00000001; // as chosen in compile.ml

int print(int val) {
  if ((val & BOOL_TAG) == 0) { // val is even ==> number
    printf("%d", val >> 1); // shift bits right to remove tag
  } else if (val == BOOL_TRUE) {
    printf("true");
  } else if (val == BOOL_FALSE) {
    printf("false");
  } else {
    printf("Unknown value: %#010x", val); // print unknown val in hex
  }
  return val;
}

extern int our_code_starts_here() asm("our_code_starts_here");

int main(int argc, char** argv) {
  int result = our_code_starts_here();
  print(result);
  return 0;
}
