section .text
global our_code_starts_here


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



f:
.entry:
	push ebp
	mov ebp, esp
	sub esp, 20
	mov eax, dword [ebp + 8]
	mov eax, dword [ebp + 12]
	mov ebx, 10
	cmp ebx, 0
	mov dword [ebp + -4], 2147483649
	jz .skip.0
.side.0:
	mov dword [ebp + -4], 1
	jmp .skip.0
.skip.0:
	cmp dword [ebp + -4], 2147483649
	jz .split_.entry_.join.0_0.0
.skip.3:
	jmp .right.0
.right.0:
	mov ebx, 10
	cmp ebx, 2
	mov dword [ebp + -8], 2147483649
	jz .skip.1
.side.1:
	mov dword [ebp + -8], 1
	jmp .skip.1
.skip.1:
	cmp dword [ebp + -8], 2147483649
	jz .left.1
.skip.4:
	jmp .split_.right.0_.join.0_1.0
.left.1:
	mov ebx, 2
	add ebx, 8
	mov dword [ebp + -12], ebx
	jmp .join.0
.split_.entry_.join.0_0.0:
	mov dword [ebp + -12], 0
	jmp .join.0
.split_.right.0_.join.0_1.0:
	mov dword [ebp + -12], 4
	jmp .join.0
.join.0:
	mov ebx, dword [ebp + -12]
	cmp eax, 2
	mov dword [ebp + -16], 2147483649
	jz .skip.2
.side.2:
	mov dword [ebp + -16], 1
	jmp .skip.2
.skip.2:
	cmp dword [ebp + -16], 2147483649
	jz .split_.join.0_.join.2_0.0
.skip.5:
	jmp .split_.join.0_.join.2_1.0
.split_.join.0_.join.2_0.0:
	mov dword [ebp + -20], 4
	jmp .join.2
.split_.join.0_.join.2_1.0:
	mov dword [ebp + -20], 6
	jmp .join.2
.join.2:
	mov ecx, dword [ebp + -20]
	mov eax, ebx
	add eax, ecx
	mov ecx, eax
	add ecx, 10
	mov eax, ecx
	add eax, 14
	mov eax, eax
	mov esp, ebp
	pop ebp
	ret


our_code_starts_here:
  mov esi, dword [esp + 4]
  add ESI, 7
  and ESI, 0xfffffff8

.entry:
	push ebp
	mov ebp, esp
	push 2
	push 0
	call f
	mov edx, eax
	add esp, 4
	add esp, 4
	mov eax, edx
	mov esp, ebp
	pop ebp
	ret
