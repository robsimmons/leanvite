import Lean
import Lean.Syntax
import Std

open Std Singleton EmptyCollection

open Lean Elab Command Term Meta

private def mangleChar
 | '\'' => '_'
 | '.' => '_'
 | ch => ch

private def mangle (n : Name) := "lean." ++ String.map mangleChar (toString n)

inductive BinOp where
  | add : BinOp
  | sub : BinOp
  | mul : BinOp
  | div : BinOp
deriving Repr, Inhabited

inductive JS where
  | true : JS
  | false : JS
  | int : Int → JS
  | sci : Int → Int → JS
  | binop : BinOp → JS → JS → JS
  | neg : JS → JS
  | intToFloat : JS → JS
  | const : Name → JS
  | lam : Nat → JS → JS
  | var : Nat → JS
  | broken : String → JS
  | app : JS → JS → JS
  | prim : String → List JS → JS
deriving Repr, Inhabited

def binOpToString
  | BinOp.add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"

def jsToString
  | JS.true => "tt"
  | JS.false => "ff"
  | JS.int x => s!"{x}n"
  | JS.sci base exp => s!"{base}e{exp}"
  | JS.binop op x y => s!"({jsToString x} {binOpToString op} {jsToString y})"
  | JS.neg x => s!"(- {jsToString x})"
  | JS.lam n x => s!"(bvar_{n} => {jsToString x})"
  | JS.var n => s!"bvar_{n}"
  | JS.intToFloat x => s!"(Number({jsToString x}))"
  | JS.const name => mangle name
  | JS.app x y => s!"{jsToString x}({jsToString y})"
  | JS.broken str => s!"\"{str}\""
  | JS.prim f args => s!"leanprim.{f}({",".intercalate (args.map jsToString)})"

instance : ToString JS where
toString := jsToString

private partial def depsJS (env : Environment)
 | Expr.const name _uni =>
    match env.find? name with
    | none => singleton name
    | some (ConstantInfo.defnInfo defnInfo) =>
        HashSet.insert (depsJS env defnInfo.value) name
    | some _ => singleton name

 | Expr.bvar _n => emptyCollection
 | Expr.lam _binderName _binderType body _binderInfo => depsJS env body
 | Expr.letE _declName _type value body _nondep => HashSet.union (depsJS env value) (depsJS env body)
 | Expr.app fn arg => HashSet.union (depsJS env fn) (depsJS env arg)
 | Expr.lit _val => emptyCollection
 | Expr.fvar _fvarId => emptyCollection -- possible?
 | Expr.mvar _mvarId => emptyCollection -- possible?
 | Expr.mdata _data _expr => emptyCollection -- possible?
 | Expr.proj _typeName _idx struct => depsJS env struct
 | Expr.sort _u => emptyCollection -- possible?
 | Expr.forallE _binderName _binderType body _binderInfo => depsJS env body



private def exprJSStr ctx
 | Expr.const name _uni => mangle name
 | Expr.bvar n => s!"bv_{ctx - n - 1}"
 | Expr.lam _binderName _binderType body _binderInfo =>
      s!"(bv_{ctx}) => ({exprJSStr (ctx + 1) body})"
 | Expr.letE _declName _type value body _nondep =>
      s!"((bv_{ctx}) => ({exprJSStr (ctx + 1) body}))({exprJSStr ctx value})"
 | Expr.app fn arg => s!"({exprJSStr ctx fn})({exprJSStr ctx arg})"
 | Expr.lit (Literal.natVal val) => s!"{val}n"
 | Expr.lit (Literal.strVal val) => s!"'{val}'"
 | Expr.fvar fvarId => s!"((() => {"{"} throw new Error('Undefined fvar {fvarId.name}') {"}"})())"
 | Expr.mvar mvarId => s!"((() => {"{"} throw new Error('Undefined mvar {mvarId.name}') {"}"})())"
 | Expr.mdata data expr => s!"((() => {"{"} throw new Error('Undefined mdata {data} {expr}') {"}"})())"
 | Expr.proj typeName idx struct => s!"((() => {"{"} throw new Error('Undefined proj {typeName} {idx} {struct}') {"}"})())"
 | Expr.sort u => s!"((() => {"{"} throw new Error('Undefined sort {u}') {"}"})())"
 | Expr.forallE binderName binderType body _binderInfo =>
      s!"((() => {"{"} throw new Error('Undefined forallE {binderName} {binderType} {body}') {"}"})())"

def tNat := Expr.const (.str .anonymous "Nat") []
def tFloat := Expr.const (.str .anonymous "Float") []
def tTrue := Expr.const (.str (.str .anonymous "Bool") "true") []
def tFalse := Expr.const (.str (.str .anonymous "Bool") "false") []

def mkBinOp (exprJS : Nat → Expr → StateM (HashSet Name) JS) (name : String) (op : BinOp) (ctx : Nat) (args : List Expr) : StateM (HashSet Name) JS :=
  match args with
  | t1 :: t2 :: t3 :: rest =>
    if t1 == tNat && t2 == tNat && t3 == tNat || t1 == tFloat && t2 == tFloat && t3 == tFloat then
    match rest with
    | [_impl, x, y] => JS.binop op <$> (exprJS ctx x) <*> (exprJS ctx y)
    | _ => pure (.broken s!"unprepared for partial application of {name} {rest}")
    else pure (.broken s!"unprepared for {t1} {t2} {t3} instantiation of {name}")
  | _ => pure (.broken s!"insufficient type args for {name} {args}")

private def sek [Monad M] : List (M a) → M (List a)
| [] => pure []
| x :: xs => return (← x) :: (← sek xs)

private def mkKnownNames (exprJS : Nat → Expr → StateM (HashSet Name) JS) : HashMap Name (Nat → List Expr → StateM (HashSet Name) JS) :=
HashMap.ofList [
(.str (.str .anonymous "Bool") "false", λ _ _ => pure .false),
(.str (.str .anonymous "Bool") "true", λ _ _ => pure .true),
(.str (.str .anonymous "OfScientific") "ofScientific", λ _ctx args =>
match args with
| [type, _impl, Expr.lit (Literal.natVal base), isNeg, Expr.lit (Literal.natVal exp)] => pure (
  if type == tFloat && isNeg == tTrue
  then .sci base (- exp)
  else if type == tFloat && isNeg == tFalse
  then .sci base exp
  else .broken s!"unprepared for non-to-float or non-literal OfScientific.ofScientific {args}")
| _ => pure (.broken s!"unprepared for this instantiation of OfScientific.ofScientific {args}")),
(.str (.str .anonymous "Neg") "neg", λ ctx args =>
match args with
| [type, _impl, value] => do
  if type == tNat || type == tFloat
  then JS.neg <$> (exprJS ctx value)
  else return .broken s!"unprepared for non-nat or non-float Neg.neg {args}"
| _ => return .broken s!"unprepared for this instantiation of Neg.neg {args}"),
(.str (.str .anonymous "OfNat") "ofNat", λ _ args =>
match args with
| [type, Expr.lit (Literal.natVal const), _impl] =>
  if type == tNat then pure (JS.int const)
  else if type == tFloat
  then return JS.sci const 0
  else return .broken s!"unprepared for non-nat or non-const ofNat {args}"
| _ => return .broken s!"unprepared for this instantiation of ofNat"),
(.str (.str .anonymous "HSub") "hSub", mkBinOp exprJS "HSub.hSub" .sub),
(.str (.str .anonymous "HAdd") "hAdd", mkBinOp exprJS "HAdd.hAdd" .add),
(.str (.str .anonymous "HMul") "hMul", mkBinOp exprJS "HMul.hMul" .mul),
(.str (.str .anonymous "HDiv") "hDiv", mkBinOp exprJS "HDiv.hDiv" .div),
(.str (.str .anonymous "Splat") "stack", λ ctx args => .prim "stack" <$> (sek (args.map (exprJS ctx)))),
(.str (.str .anonymous "Splat") "func", λ ctx args => .prim "func" <$> (sek (args.map (exprJS ctx)))),
(.str (.str .anonymous "Splat") "line", λ ctx args => .prim "line" <$> (sek (args.map (exprJS ctx)))),
(.str (.str .anonymous "Splat") "circle", λ ctx args => .prim "circle" <$> (sek (args.map (exprJS ctx)))),
(.str (.str .anonymous "List") "toArray", λ ctx args => exprJS ctx args[1]!),
(.str (.str .anonymous "List") "cons", λ ctx args => .prim "cons" <$> (sek [exprJS ctx args[1]!, exprJS ctx args[2]!])),
(.str (.str .anonymous "List") "nil", λ ctx args => return .prim "nil" []),
(.str (.str .anonymous "Prod") "mk", λ ctx args => .prim "tuple" <$> (sek [exprJS ctx args[2]!, exprJS ctx args[3]!])),
]


mutual
  private partial def step (env : Environment) (name : Name) (e : Expr) : StateM (HashSet Name × List (Name × JS)) Unit := do
  let (js, deps) := (exprJS env 0 e) emptyCollection
  let (known, _) ← get
  for dep in deps do
    if name != dep && !known.contains dep
    then match env.find? dep with
    | some (ConstantInfo.defnInfo defnInfo) => do
      let () ← step env dep defnInfo.value
    | some _ =>
      modify (λ (known, signature) => (known.insert dep, (dep, .broken s!"unknown definition for {dep}") :: signature))
    | none =>
      modify (λ (known, signature) => (known.insert dep, (dep, .broken s!"no definition for {dep}") :: signature))
  modify (λ (known, signature) => (known.insert name, (name, js) :: signature))

  private partial def spine (env : Environment) (ctx : Nat) (sp : List Expr) : Expr → StateM (HashSet Name) JS
  | Expr.const name _uni =>
    match getKnownName env name with
    | some f => f ctx sp
    | none =>
      match env.find? name with
      | some (ConstantInfo.defnInfo _defnInfo) => do
        modify (λ s => s.insert name)
        return JS.const name
      | some _ => return JS.broken s!"unknown definition {name} {sp}"
      | none => return JS.broken s!"unknown constant {name} {sp}"
  | Expr.app fn arg => spine env ctx (arg :: sp) fn
  | Expr.bvar n =>
    if List.length sp != 1
    then return JS.broken s!"variable application with {List.length sp} args"
    else return .app (.var (ctx - n - 1)) (← exprJS env ctx (sp[0]!))
  | _ => return JS.broken s!"nonstandard application with !{List.length sp} args"

  private partial def exprJS (env : Environment) (ctx : Nat) (e : Expr) : StateM (HashSet Name) JS :=
  match e with
  | Expr.const _ _ => spine env ctx [] e
  | Expr.app _ _ => spine env ctx [] e
  | Expr.lam _binderName _binderType body _binderInfo => do
    return .lam ctx (← exprJS env (ctx + 1) body)
  | Expr.bvar n => return .var (ctx - n - 1)
  | Expr.letE _declName _type value body _nondep => do
    let value' ← exprJS env ctx value
    let body' ← exprJS env (ctx + 1) body
    return .app (.lam ctx body') value'
  | _ => pure (JS.broken s!"not ready")

  private partial def getKnownName (env : Environment) : Name → Option (Nat → List Expr → StateM (HashSet Name) JS) :=
  let knownNames := mkKnownNames (exprJS env)
  λ name => knownNames[name]?
end

private def exprJS' env := exprJS env 0

#check CommandElabM

elab "#splat" term:term : command => do
  let state : Command.State ← get
  let environment : Environment := state.env
  withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_mycommand1 do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := false)
    withRef term <| Meta.check e
    let e : Expr ← Term.levelMVarToParam (← instantiateMVars e)
    let _type ← inferType e
    if let Expr.bvar _ := e then
      logInfo s!"bvar {e}"
    /- if let Expr.const n _u := e then
      logInfo s!"const {e}"
      let q ← getEnv
      let c := q.constants
      if let ConstantInfo.defnInfo d := c.find! n then
        logInfo s!"defn {d.value}"
    else -/
    logInfo "doing"
    let name := (Std.HashSet.toArray (depsJS environment e))[0]!
    logInfo s!"{Std.HashSet.toArray (depsJS environment e)} {name}"
    if let some x := environment.find? name
    then logInfo s!"{x.isDefinition}"
    let (x, y) := (exprJS' environment e) emptyCollection
    logInfo s!"{x} {HashSet.toArray y}"
    let ((), (w, z)) := step environment .anonymous e (emptyCollection, [])
    logInfo s!"{HashSet.toArray w} {z}"

    /-
    IO.FS.writeFile "./src/generated-data-from-lean.js" ("import * as lean from './hacky-lean-runtime.js';\n\nexport const instructions = " ++ exprJS' e)
    logInfo s!"{exprJS' e}"
    logInfo "done"
    -/

inductive Splat where
  | line : Float × Float → Float × Float → Splat
  | func : (Float → Float) → Splat
  | stack : Array Splat → Splat
  | circle : Float × Float → Float → Splat
