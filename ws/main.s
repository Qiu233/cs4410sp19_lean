
section .text
extern error
global our_code_starts_here

error_non_number:
  push eax
  push 1
  call error
  add esp, 4 * 2

our_code_starts_here:
mov eax, 2
test eax, 1
jnz error_non_number
mov dword [esp + 4 * -1], eax
mov eax, dword [esp + 4 * -1]
test eax, 1
jnz error_non_number
mov eax, 0
sub eax, dword [esp + 4 * -1]
mov dword [esp + 4 * -1], eax
mov eax, 4
test eax, 1
jnz error_non_number
mov dword [esp + 4 * -2], eax
mov eax, dword [esp + 4 * -2]
test eax, 1
jnz error_non_number
mov eax, 0
sub eax, dword [esp + 4 * -2]
mov dword [esp + 4 * -2], eax
mov eax, dword [esp + 4 * -2]
test eax, 1
jnz error_non_number
mov eax, dword [esp + 4 * -1]
test eax, 1
jnz error_non_number
cmp eax, dword [esp + 4 * -2]
mov eax, 2147483649
jle label_less_eq_0
mov eax, 1
label_less_eq_0:
ret