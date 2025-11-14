
section .text
global our_code_starts_here
our_code_starts_here:
mov eax, dword [esp + 4 * 0]
mov dword [esp + 4 * -1], eax
mov eax, dword [esp + 4 * -1]
xor eax, 2147483648
ret