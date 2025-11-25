section .text
extern error
extern error_tuple_size_mismatch
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


error_non_tuple:
  push eax
  push 3
  call error
  add esp, 4 * 2

prod:
	push ebp
	mov ebp, esp
	sub esp, 4
label_prod_body.0:
	mov dword [esi + 4 * 0], 2
	mov eax, dword [ebp + 4 * 3]
	mov dword [esi + 4 * 1], eax
	mov eax, dword [ebp + 4 * 2]
	mov dword [esi + 4 * 2], eax
	mov eax, esi
	add eax, 1
	add esi, 16
	mov dword [ebp + 4 * -1], eax
	mov dword [esi + 4 * 0], 3
	mov eax, dword [ebp + 4 * 2]
	mov dword [esi + 4 * 1], eax
	mov eax, dword [ebp + 4 * 3]
	mov dword [esi + 4 * 2], eax
	mov eax, dword [ebp + 4 * -1]
	mov dword [esi + 4 * 3], eax
	mov eax, esi
	add eax, 1
	add esi, 16
	mov esp, ebp
	pop ebp
	ret

f:
	push ebp
	mov ebp, esp
	sub esp, 4
label_f_body.0:
	mov eax, 2
	push eax
	call print
	add esp, 4
	mov dword [ebp + 4 * -1], eax
	mov dword [esi + 4 * 0], 0
	mov eax, esi
	add eax, 1
	add esi, 8
	mov esp, ebp
	pop ebp
	ret

global our_code_starts_here
our_code_starts_here:
  mov esi, dword [esp + 4]
  add ESI, 7
  and ESI, 0xfffffff8
	push ebp
	mov ebp, esp
	sub esp, 8
	mov eax, 2147483649
	push eax
	mov eax, 2
	push eax
	call prod
	add esp, 8
	mov dword [ebp + 4 * -1], eax
	mov eax, dword [ebp + 4 * -1]
	and eax, 7
	cmp eax, 1
	mov eax, dword [ebp + 4 * -1]
	jnz error_non_tuple
	sub eax, 1
	cmp dword [eax + 4 * 0], 3
	jnz error_tuple_size_mismatch
	mov eax, dword [eax + 4 * 3]
	mov dword [ebp + 4 * -2], eax
	mov eax, dword [ebp + 4 * -2]
	and eax, 7
	cmp eax, 1
	mov eax, dword [ebp + 4 * -2]
	jnz error_non_tuple
	sub eax, 1
	cmp dword [eax + 4 * 0], 2
	jnz error_tuple_size_mismatch
	mov eax, dword [eax + 4 * 2]
	mov esp, ebp
	pop ebp
	ret