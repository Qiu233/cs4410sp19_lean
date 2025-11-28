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



g:
.entry:
  push ebp
  mov ebp, esp
  sub esp, 12
  mov eax, dword [ebp + 8]
  mov dword [ebp + -4], eax
  cmp dword [ebp + -4], 2
  mov dword [ebp + -12], 2147483649
  jle .skip.0
.side.0:
  mov dword [ebp + -12], 1
  jmp .skip.0
.skip.0:
  cmp dword [ebp + -12], 2147483649
  jz .split_.entry_.join.0_0.0
.skip.1:
  jmp .right.0
.right.0:
  mov eax, dword [ebp + -4]
  mov dword [ebp + -8], eax
  sub dword [ebp + -8], 2
  push dword [ebp + -8]
  call g
  mov dword [ebp + -8], eax
  add esp, 4
  mov eax, dword [ebp + -4]
  mov dword [ebp + -12], eax
  mov eax, dword [ebp + -12]
  imul eax, dword [ebp + -8]
  mov dword [ebp + -12], eax
  mov eax, dword [ebp + -12]
  sar eax, 1
  mov dword [ebp + -12], eax
  mov eax, dword [ebp + -12]
  mov dword [ebp + -12], eax
  jmp .join.0
.split_.entry_.join.0_0.0:
  mov dword [ebp + -12], 2
  jmp .join.0
.join.0:
  mov eax, dword [ebp + -12]
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
  sub esp, 4
  push 10
  call g
  mov dword [ebp + -4], eax
  add esp, 4
  mov eax, dword [ebp + -4]
  mov eax, eax
  mov esp, ebp
  pop ebp
  ret
