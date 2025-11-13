
section .text
global our_code_starts_here
our_code_starts_here:
mov eax, 0
mov dword [esp + 4 * -1], eax
mov eax, dword [esp + 4 * -1]
mov dword [esp + 4 * -2], eax
mov eax, 2
mov dword [esp + 4 * -3], eax
mov eax, dword [esp + 4 * -2]
add eax, dword [esp + 4 * -3]
mov dword [esp + 4 * -2], eax
mov eax, 1
mov dword [esp + 4 * -3], eax
mov eax, dword [esp + 4 * -2]
sub eax, dword [esp + 4 * -3]
mov dword [esp + 4 * -2], eax
mov eax, dword [esp + 4 * -2]
cmp eax, 0
je label_if_false_0
mov eax, 2
mov dword [esp + 4 * -3], eax
mov eax, 3
mov dword [esp + 4 * -4], eax
mov eax, dword [esp + 4 * -3]
mul dword [esp + 4 * -4]
jmp label_done_0
label_if_false_0:
mov eax, 0
label_done_0:
ret