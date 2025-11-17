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

add:
	push ebp
	mov ebp, esp
	sub esp, 0
label_add_body_0:
	mov eax, dword [ebp + 4 * 3]
	test eax, 1
	jnz error_non_number
	mov eax, dword [ebp + 4 * 2]
	test eax, 1
	jnz error_non_number
	add eax, dword [ebp + 4 * 3]
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
	mov eax, 6
	push eax
	call add
	add esp, 8
	mov esp, ebp
	pop ebp
	ret