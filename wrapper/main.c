#include <stdio.h>
#include <stdlib.h>

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
  } else if ((val & 0x00000007) == 0x00000001) {
    int *ptr = (int*)(((void*)val) - 1);
    int n = ptr[0];
    if (n == 0) {
      printf("()");
    } else {
      printf("(");
      print(ptr[1]);
      for (int i = 1; i < n; i++) {
        printf(", ");
        print(ptr[i + 1]);
      }
      printf(")");
    }
  } else {
    printf("Unknown value: %#010x", val); // print unknown val in hex
  }
  return val;
}

const int ERR_NOT_NUMBER = 1;
const int ERR_NOT_BOOLEAN = 2;
const int ERR_NOT_TUPLE = 3;
// other error codes here

void error(int errCode, int val) {
  if (errCode == ERR_NOT_NUMBER) {
    fprintf(stderr, "Expected number, but got %010x\n", val);
  } else if (errCode == ERR_NOT_BOOLEAN) {
    fprintf(stderr, "Expected boolean, but got %010x\n", val);
  } else if (errCode == ERR_NOT_TUPLE) {
    fprintf(stderr, "Expected tuple, but got %010x\n", val);
  }
  exit(errCode);
}

void error_tuple_size_mismatch(int expected, int actual) {
  fprintf(stderr, "Tuple size mismatched, expected %d, but got %d\n", expected, actual);
  exit(-1);
}

extern int our_code_starts_here() asm("our_code_starts_here");

int main() {
  int* HEAP = calloc(1024, sizeof(int)); // Allocate 4KB of memory for now
  int result = our_code_starts_here(HEAP);
  print(result);
  free(HEAP);
  return 0;
}
