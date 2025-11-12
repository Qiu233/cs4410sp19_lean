# cs4410sp19

## preparation

```bash
$ sudo apt install gcc-multilib nasm
```

```bash
cd wrapper
$ nasm -f elf32 -o our_code.o our_code.s
$ clang -g -m32 -o our_code main.c our_code.o
```

## run

```bash
$ lake exe cs4410sp19 ws/87.int > ws/87.s
$ nasm -f elf32 -o ws/87.o ws/87.s
$ clang -m32 -o ws/87.run wrapper/main.c ws/87.o
$ ./ws/87.run
```
