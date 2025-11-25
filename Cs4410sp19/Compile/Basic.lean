import Std
import Cs4410sp19.Basic

namespace Cs4410sp19

inductive StackSlot where
  /-- `ebp i` is `[ebp + i * 4]` -/
  | ebp : Int → StackSlot
  /-- `esp i` is `[esp + i * 4]` -/
  | esp : Int → StackSlot
deriving BEq, Inhabited, Repr

def StackSlot.to_arg : StackSlot → Arg
  | .esp i => .reg_offset .esp i
  | .ebp i => .reg_offset .ebp i

section

structure Env where
  functions : Std.HashSet String := {}

abbrev CompileM := ExceptT String <| StateT Env <| FreshM

def CompileM.run : CompileM α → Env → FreshM (Except String α × Env) := fun x env => x env

def gen_label [MonadNameGen m] (suggestedName : String) : m String :=
  gensym s!"label_{suggestedName}"

-- def find_global_constant? : String → CompileM (Option Constant) := fun s => do
--   let cs ← Env.global_consts <$> getThe Env
--   return cs.get? s

-- def register_global_constant : String → Constant → CompileM Unit := fun s c => do
--   let cs ← Env.global_consts <$> getThe Env
--   if cs.contains s then
--     throw s!"cannot register constant {s} because it already exists"
--   modify (fun x => { x with global_consts := x.global_consts.insert s c })

end

section

/-- context for sub-function compilation -/
structure Context where
  /-- (decl_name, decl_body_label) -/
  current_decl? : Option (String × String)
  arg_slots : List (String × StackSlot) := []
  var_slots : List (String × StackSlot) := []

/-- volatile state for sub-function compilation -/
structure State where
  max_stack_slots : Nat := 0
  used_constants : Std.HashSet String := {}

abbrev CompileFuncM := ReaderT Context <| StateT State CompileM

def CompileFuncM.run : CompileFuncM α → Context → State → CompileM (α × State) := fun x c s => (x c s)

end

def with_args (ids : Array String) (x : Array (String × StackSlot) → CompileFuncM α) : CompileFuncM α := do
  let new := ids.foldl (init := []) fun acc x => (x, StackSlot.ebp (acc.length + 2)) :: acc
  withReader (fun ctx => { ctx with arg_slots := new }) (x new.toArray)

def with_new_var (name : String) (x : StackSlot → CompileFuncM α) : CompileFuncM α := do
  let slots ← Context.var_slots <$> read
  let slot := .ebp (-(slots.length + 1))
  modify (fun s => {s with max_stack_slots := s.max_stack_slots.max (slots.length + 1)})
  withReader (fun ctx => { ctx with var_slots := (name, slot) :: ctx.var_slots }) (x slot)

def get_slot! (name : String) : CompileFuncM StackSlot := do
  let ctx ← read
  match ctx.var_slots.lookup name with -- search for variables first
  | none =>
    match ctx.arg_slots.lookup name with
    | none => throw s!"\"{name}\" is undefined"
    | some x => return x
  | some x => return x

def with_tmp_var (pref : String := "tmp") (x : String → StackSlot → CompileFuncM α) : CompileFuncM α := do
  let tmp ← gensym pref
  with_new_var tmp (x tmp)

def add_used_constants (name : String) : CompileFuncM Unit := do
  modify fun s => {s with used_constants := s.used_constants.insert name}

private def combine_insts [Monad m] : m (Array Instruction) → m (Array Instruction) → m (Array Instruction) :=
  fun x y => (· ++ ·) <$> x <*> y

def const_false : Arg := .const 0x00000001
def const_true : Arg := .const 0x80000001
