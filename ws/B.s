
section .text
global our_code_starts_here
our_code_starts_here:
mov eax, 10
mov [esp + 4 * -1], eax
mov eax, [esp + 4 * -1]
add eax, 1
mov [esp + 4 * -2], eax
mov eax, [esp + 4 * -2]
add eax, 1
mov [esp + 4 * -3], eax
mov eax, [esp + 4 * -3]
add eax, 1
ret
