import Cs4410sp19.SSA.Basic

namespace Cs4410sp19
namespace SSA

structure Context where
  renaming' : Std.HashMap String VarName := {}

structure State where
  blocks : Array (Option (BasicBlock Unit String VarName Operand)) := {}

abbrev M := ReaderT Context <| StateT State FreshM

instance : MonadNameGen FreshM where
  gensym := FreshM.gensym

def new_block (name : String) (params : List VarName) (insts : Array (Inst Unit String VarName Operand)) : M Unit := do
  modifyThe State fun s => {s with blocks := s.blocks.push <| some ⟨name, params, insts⟩ }

def with_renamed (n : String) (x : VarName → M α) : M α := do
  let new ← genvar n
  withTheReader Context (fun c => {c with renaming' := c.renaming'.insert n new}) (x new)

def with_renamed_many (ns : List String) (x : List VarName → M α) : M α := do
  let new ← ns.mapM genvar
  withTheReader Context (fun c => {c with renaming' := c.renaming'.insertMany (ns.zip new)}) (x new)

def with_reserved_slot (name : String) (params : List VarName) (x : M (List (Inst Unit String VarName Operand))) : M Unit := do
  let i ← modifyGetThe State fun s => (s.blocks.size, {s with blocks := s.blocks.push none})
  let insts ← x
  modifyThe State fun s => {s with blocks := s.blocks.set! i (some ⟨name, params, insts.toArray⟩)}

mutual

private def goI (e : ImmExpr α) : ContT (List (Inst Unit String VarName Operand)) M Operand := do
  match e with
  | .num _ x =>
    let name ← genvar "c"
    fun k => do
      let r ← k (.var name)
      return Inst.assign () name (.const (ConstVal.int x)) :: r
  | .bool _ x =>
    let name ← genvar "c"
    fun k => do
      let r ← k (.var name)
      return Inst.assign () name (.const (ConstVal.bool x)) :: r
  | .id _ n => liftM (m := M) do
    let c ← readThe Context
    Operand.var <$> c.renaming'[n]?.getDM (return panic! "impossible: unbound variable name")

private def goC (e : CExpr α) : ContT (List (Inst Unit String VarName Operand)) M Operand := do
  match e with
  | .imm e => goI e
  | .ite _ cond bp bn =>
    let c ← goI cond
    let na ← gensym ".left"
    let nb ← gensym ".right"
    let join ← gensym ".join"
    liftM <| with_reserved_slot na [] do
      goA bp (fun n => pure [Inst.jmp () join [n]])
    liftM <| with_reserved_slot nb [] do
      goA bn (fun n => pure [Inst.jmp () join [n]])
    fun k => do
      let n ← genvar "a"
      with_reserved_slot join [n] (k (.param n))
      return [Inst.br () c na [] nb []]
  | .prim2 _ op x y =>
    let x' ← goI x
    let y' ← goI y
    let n ← genvar "r"
    fun k => do
      let r ← k (.var n)
      return Inst.prim2 () n op x' y' :: r
  | .prim1 _ op x =>
    let x' ← goI x
    let n ← genvar "r"
    fun k => do
      let r ← k (.var n)
      return Inst.prim1 () n op x' :: r
  | .call _ func xs =>
    let xs' ← xs.mapM goI
    let n ← genvar "r"
    fun k => do
      let r ← k (.var n)
      return Inst.call () n func xs' :: r
  | .tuple _ xs =>
    let xs' ← xs.mapM goI
    let n ← genvar "r"
    fun k => do
      let r ← k (.var n)
      return Inst.mk_tuple () n xs' :: r
  | .get_item _ v i n =>
    let v ← goI v
    let t ← genvar "r"
    fun k => do
      let r ← k (.var t)
      return Inst.get_item () t v i n :: r

private def goA (e : AExpr α) : ContT (List (Inst Unit String VarName Operand)) M Operand := do
  match e with
  | .let_in _ name value body =>
    let v ← goC value
    let _ ← fun k =>
      with_renamed name fun name' => do
        let r ← k ()
        return Inst.assign () name' v :: r
    goA body
  | .cexpr c => goC c

end


def cfg_of_function_def : AFuncDef α → FreshM (CFG Unit String VarName Operand) := fun e => do
  let {name, params, body} := e
  let go := with_renamed_many params fun ns => do
    let bargs ← ns.mapM fun _ => genvar "a"
    let assignments : List (Inst Unit String VarName Operand) := ns.zipWith (ys := bargs) fun n b => Inst.assign () n (Operand.param b)
    let go : ContT (List (Inst Unit String VarName Operand)) M Operand := do
      let _ ← fun k => do
        let r ← k ()
        return assignments ++ r
      goA body
    with_reserved_slot ".entry" bargs <| go (fun n => pure [Inst.ret () n])
  let (_, s) ← go.run {} |>.run {}
  let r := (s.blocks.map fun x => x.get!)
  return { name, blocks := r }
