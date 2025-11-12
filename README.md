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
$ lake run
```

or

```bash
$ lake run .
```

or

```bash
$ lake run . main
```

where `main` can be replaced by another name as long as `name.int` exists in the folder `ws`.