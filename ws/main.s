section .text
extern error
extern print

error_non_number:
  push eax
  push 1
  call error
  add esp, 4 * 2


error_non_bool:
  push eax
  push 2
  call error
  add esp, 4 * 2

f:
push ebp
mov ebp, esp
sub esp, 12
mov eax, 0
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * 2]
test eax, 1
jnz error_non_number
cmp eax, 0
mov eax, 2147483649
je label_equal_0
mov eax, 1
label_equal_0:
mov dword [ebp + 4 * -1], eax
mov eax, dword [ebp + 4 * -1]
cmp eax, 1
je label_if_false_0
mov eax, 2
test eax, 1
jnz error_non_number
jmp label_done_0
label_if_false_0:
mov eax, 2
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * 2]
test eax, 1
jnz error_non_number
sub eax, 2
mov dword [ebp + 4 * -2], eax
mov eax, dword [ebp + 4 * -2]
push eax
call f
add esp, 4
mov dword [ebp + 4 * -3], eax
mov eax, dword [ebp + 4 * -3]
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * 2]
test eax, 1
jnz error_non_number
mul dword [ebp + 4 * -3]
sar eax, 1
label_done_0:
mov esp, ebp
pop ebp
ret

global our_code_starts_here
our_code_starts_here:
push ebp
mov ebp, esp
sub esp, 0
mov eax, 10
push eax
call f
add esp, 4
mov esp, ebp
pop ebp
ret