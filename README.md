# cs4410sp19

## preparation

```bash
$ sudo apt install gcc-multilib nasm
```

```bash
$ nasm -f elf32 -o our_code.o our_code.s
$ clang -g -m32 -o our_code main.c our_code.o
```

## run

```bash
$ lake exe cs4410sp19 87.int > 87.s
$ nasm -f elf32 -o 87.o 87.s
$ clang -m32 -o 87.run wrapper/main.c 87.o
$ ./87.run
```
