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

is_even:
	push ebp
	mov ebp, esp
	sub esp, 12
label_is_even_body_0:
	mov eax, dword [ebp + 4 * 2]
	cmp eax, 0
	mov eax, 2147483649
	je label_equal_0
	mov eax, 1
label_equal_0:
	mov dword [ebp + 4 * -1], eax
	mov eax, dword [ebp + 4 * -1]
	cmp eax, 1
	je label_if_false_0
	mov eax, 2147483649
	jmp label_done_0
label_if_false_0:
	mov eax, dword [ebp + 4 * 2]
	cmp eax, 2
	mov eax, 2147483649
	je label_equal_1
	mov eax, 1
label_equal_1:
	mov dword [ebp + 4 * -2], eax
	mov eax, dword [ebp + 4 * -2]
	cmp eax, 1
	je label_if_false_1
	mov eax, 1
	jmp label_done_1
label_if_false_1:
	mov eax, 2
	test eax, 1
	jnz error_non_number
	mov eax, dword [ebp + 4 * 2]
	test eax, 1
	jnz error_non_number
	sub eax, 2
	mov dword [ebp + 4 * -3], eax
	mov eax, dword [ebp + 4 * -3]
	push eax
	call is_odd
	add esp, 4
label_done_1:
label_done_0:
	mov esp, ebp
	pop ebp
	ret

is_odd:
	push ebp
	mov ebp, esp
	sub esp, 12
label_is_odd_body_0:
	mov eax, dword [ebp + 4 * 2]
	cmp eax, 2
	mov eax, 2147483649
	je label_equal_2
	mov eax, 1
label_equal_2:
	mov dword [ebp + 4 * -1], eax
	mov eax, dword [ebp + 4 * -1]
	cmp eax, 1
	je label_if_false_2
	mov eax, 2147483649
	jmp label_done_2
label_if_false_2:
	mov eax, dword [ebp + 4 * 2]
	cmp eax, 0
	mov eax, 2147483649
	je label_equal_3
	mov eax, 1
label_equal_3:
	mov dword [ebp + 4 * -2], eax
	mov eax, dword [ebp + 4 * -2]
	cmp eax, 1
	je label_if_false_3
	mov eax, 1
	jmp label_done_3
label_if_false_3:
	mov eax, 2
	test eax, 1
	jnz error_non_number
	mov eax, dword [ebp + 4 * 2]
	test eax, 1
	jnz error_non_number
	sub eax, 2
	mov dword [ebp + 4 * -3], eax
	mov eax, dword [ebp + 4 * -3]
	push eax
	call is_even
	add esp, 4
label_done_3:
label_done_2:
	mov esp, ebp
	pop ebp
	ret

f:
	push ebp
	mov ebp, esp
	sub esp, 0
label_f_body_0:
	mov eax, dword [ebp + 4 * 2]
	push eax
	call g
	add esp, 4
	mov esp, ebp
	pop ebp
	ret

g:
	push ebp
	mov ebp, esp
	sub esp, 0
label_g_body_0:
	mov eax, dword [ebp + 4 * 2]
	push eax
	call f
	add esp, 4
	mov esp, ebp
	pop ebp
	ret

h:
	push ebp
	mov ebp, esp
	sub esp, 0
label_h_body_0:
	mov eax, dword [ebp + 4 * 2]
	mov esp, ebp
	pop ebp
	ret

global our_code_starts_here
our_code_starts_here:
	push ebp
	mov ebp, esp
	sub esp, 0
	mov eax, 8
	push eax
	call is_even
	add esp, 4
	mov esp, ebp
	pop ebp
	ret