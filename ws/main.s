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
sub esp, 8
mov eax, dword [ebp + 4 * 2]
mov dword [ebp + 4 * -1], eax
mov eax, dword [ebp + 4 * 3]
mov dword [ebp + 4 * -2], eax
mov eax, dword [ebp + 4 * -2]
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * -1]
test eax, 1
jnz error_non_number
add eax, dword [ebp + 4 * -2]
mov dword [ebp + 4 * -1], eax
mov eax, dword [ebp + 4 * 4]
mov dword [ebp + 4 * -2], eax
mov eax, dword [ebp + 4 * -2]
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * -1]
test eax, 1
jnz error_non_number
sub eax, dword [ebp + 4 * -2]
mov esp, ebp
pop ebp
ret

global our_code_starts_here
our_code_starts_here:
push ebp
mov ebp, esp
sub esp, 16
mov eax, 2
test eax, 1
jnz error_non_number
mov dword [ebp + 4 * -1], eax
mov eax, 6
test eax, 1
jnz error_non_number
mov dword [ebp + 4 * -2], eax
mov eax, 4
test eax, 1
jnz error_non_number
mov dword [ebp + 4 * -3], eax
mov eax, dword [ebp + 4 * -3]
push eax
mov eax, dword [ebp + 4 * -2]
push eax
mov eax, dword [ebp + 4 * -1]
push eax
call f
add esp, 12
mov dword [ebp + 4 * -1], eax
mov eax, 6
test eax, 1
jnz error_non_number
mov dword [ebp + 4 * -2], eax
mov eax, 12
test eax, 1
jnz error_non_number
mov dword [ebp + 4 * -3], eax
mov eax, 4
test eax, 1
jnz error_non_number
mov dword [ebp + 4 * -4], eax
mov eax, dword [ebp + 4 * -4]
push eax
mov eax, dword [ebp + 4 * -3]
push eax
mov eax, dword [ebp + 4 * -2]
push eax
call f
add esp, 12
mov dword [ebp + 4 * -2], eax
mov eax, dword [ebp + 4 * -2]
test eax, 1
jnz error_non_number
mov eax, dword [ebp + 4 * -1]
test eax, 1
jnz error_non_number
add eax, dword [ebp + 4 * -2]
mov esp, ebp
pop ebp
ret