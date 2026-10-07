import Cs4410sp19.SSA.Basic

namespace Cs4410sp19
namespace SSA

structure Context where
  renaming' : Std.HashMap String VarName := {}

structure State where
  blocks : Array (Option (BasicBlock Unit String VarName Operand)) := {}

abbrev M := ReaderT Context <| StateT State FreshM

def new_block (name : String) (params : List VarName) (insts : Array (Inst Unit String VarName Operand)) (terminal : Cs4410sp19.SSA.Terminal Unit String Operand) : M Unit := do
  modifyThe State fun s => {s with blocks := s.blocks.push <| some ⟨name, params, insts, terminal⟩ }

def with_renamed (n : String) (x : VarName → M α) : M α := do
  let new ← genvar n
  withTheReader Context (fun c => {c with renaming' := c.renaming'.insert n new}) (x new)

def with_renamed_many (ns : List String) (x : List VarName → M α) : M α := do
  let new ← ns.mapM genvar
  withTheReader Context (fun c => {c with renaming' := c.renaming'.insertMany (ns.zip new)}) (x new)

private abbrev IRInst := Inst Unit String VarName Operand
private abbrev IRTerm := Terminal Unit String Operand
private abbrev BlockCode := List IRInst × Option IRTerm
private abbrev Build := ContT BlockCode M

private def emit (inst : IRInst) : Build Unit :=
  fun k => do
    let (insts, term) ← k ()
    return (inst :: insts, term)

private def with_block (name : String) (params : List VarName)
    (body : Build BlockCode) : Build Unit := do
  let i ← liftM (m := M) <| modifyGetThe State fun s => (s.blocks.size, {s with blocks := s.blocks.push none})
  let (insts, termOpt) ← ContT.reset body
  let term := termOpt.getD (panic! "with_block: missing terminal")
  liftM (m := M) <| modifyThe State fun s => {s with blocks := s.blocks.set! i (some ⟨name, params, insts.toArray, term⟩)}

private def finish (term : IRTerm) : Build BlockCode :=
  pure ([], some term)

mutual

private def goI (e : ImmExpr α) : ContT BlockCode M Operand := do
  match e with
  | .num _ x =>
    let name ← genvar "c"
    emit <| Inst.assign () name (.const (ConstVal.int x))
    return .var name
  | .bool _ x =>
    let name ← genvar "c"
    emit <| Inst.assign () name (.const (ConstVal.bool x))
    return .var name
  | .id _ n => liftM (m := M) do
    let c ← readThe Context
    Operand.var <$> c.renaming'[n]?.getDM (return panic! "impossible: unbound variable name")

private def goC (e : CExpr α) : ContT BlockCode M Operand := do
  match e with
  | .imm e => goI e
  | .ite _ cond bp bn =>
    let c ← goI cond
    let na ← gensym ".left"
    let nb ← gensym ".right"
    let join ← gensym ".join"
    with_block na [] do
      let n ← goA bp
      finish <| .jmp () join [n]
    with_block nb [] do
      let n ← goA bn
      finish <| .jmp () join [n]
    ContT.shift fun k => do
      let n ← genvar "a"
      with_block join [n] do
        liftM <| k (Operand.param n)
      finish <| .br () c na [] nb []
  | .prim2 _ op x y =>
    let x' ← goI x
    let y' ← goI y
    let n ← genvar "r"
    emit <| Inst.prim2 () n op x' y'
    return .var n
  | .prim1 _ op x =>
    let x' ← goI x
    let n ← genvar "r"
    emit <| Inst.prim1 () n op x'
    return .var n
  | .call _ func xs =>
    let xs' ← xs.mapM goI
    let n ← genvar "r"
    emit <| Inst.call () n func xs'
    return .var n
  | .tuple _ xs =>
    let xs' ← xs.mapM goI
    let n ← genvar "r"
    emit <| Inst.mk_tuple () n xs'
    return .var n
  | .get_item _ v i n =>
    let v ← goI v
    let t ← genvar "r"
    emit <| Inst.get_item () t v i n
    return .var t

private def goA (e : AExpr α) : ContT BlockCode M Operand := do
  match e with
  | .let_in _ name value body =>
    let v ← goC value
    let _ ← fun k =>
      with_renamed name fun name' => do
        let r ← k ()
        return (Inst.assign () name' v :: r.1, r.2)
    goA body
  | .cexpr c => goC c

end


def cfg_of_function_def : AFuncDef α → FreshM (CFG Unit String VarName Operand) := fun e => do
  let {name, params, body} := e
  let go := with_renamed_many params fun ns => do
    let bargs ← ns.mapM fun _ => genvar "a"
    let assignments : List (Inst Unit String VarName Operand) := ns.zipWith (ys := bargs) fun n b => Inst.assign () n (Operand.param b)
    let go : ContT BlockCode M Unit := with_block ".entry" bargs do
      assignments.forM emit
      let n ← goA body
      finish <| .ret () n
    go.run fun _ => pure ([], none)
  let (_, s) ← go.run {} |>.run {}
  let r := (s.blocks.map fun x => x.get!)
  return { name, blocks := r }
