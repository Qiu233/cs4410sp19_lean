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

fact_v1:
push ebp
mov ebp, esp
sub esp, 12
mov eax, 2
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * 2]
test eax, 1
jnz error_non_number
cmp eax, 2
mov eax, 2147483649
jle label_less_eq_0
mov eax, 1
label_less_eq_0:
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
call fact_v1
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

fact_tail:
push ebp
mov ebp, esp
sub esp, 12
mov eax, 2
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * 2]
test eax, 1
jnz error_non_number
cmp eax, 2
mov eax, 2147483649
jle label_less_eq_1
mov eax, 1
label_less_eq_1:
mov dword [ebp + 4 * -1], eax
mov eax, dword [ebp + 4 * -1]
cmp eax, 1
je label_if_false_1
mov eax, dword [ebp + 4 * 3]
jmp label_done_1
label_if_false_1:
mov eax, 2
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * 2]
test eax, 1
jnz error_non_number
sub eax, 2
mov dword [ebp + 4 * -2], eax
mov eax, dword [ebp + 4 * 3]
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * 2]
test eax, 1
jnz error_non_number
mul dword [ebp + 4 * 3]
sar eax, 1
mov dword [ebp + 4 * -3], eax
mov eax, dword [ebp + 4 * -3]
push eax
mov eax, dword [ebp + 4 * -2]
push eax
call fact_tail
add esp, 8
label_done_1:
mov esp, ebp
pop ebp
ret

global our_code_starts_here
our_code_starts_here:
push ebp
mov ebp, esp
sub esp, 0
mov eax, 2
push eax
mov eax, 10
push eax
call fact_tail
add esp, 8
mov esp, ebp
pop ebp
ret