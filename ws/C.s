
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
mov eax, [esp + 4 * -1]
mov [esp + 4 * -5], eax
mov eax, [esp + 4 * -2]
mov [esp + 4 * -6], eax
mov eax, [esp + 4 * -5]
add eax, [esp + 4 * -6]
mov [esp + 4 * -4], eax
mov eax, [esp + 4 * -3]
mov [esp + 4 * -5], eax
mov eax, [esp + 4 * -4]
sub eax, [esp + 4 * -5]
ret
