import Lean
import Lean.Syntax
import Std.HashSet

open Lean Elab Command Term Meta

private def mangleChar
 | '\'' => '_'
 | '.' => '_'
 | ch => ch

private def mangle (n : Name) := "lean." ++ String.map mangleChar (toString n)

private def internalNames := Std.HashSet.ofArray #[

  ]

private def depsJS
 | Expr.const name _uni => Std.HashSet.singleton name
 | Expr.bvar n => Std.HashSet.empty
 | Expr.lam _binderName _binderType body _binderInfo => depsJS body
 | Expr.letE _annot?declName _type value body _nondep => Std.HashSet.union (depsJS value) (depsJS body)
 | Expr.app fn arg => Std.HashSet.union (depsJS fn) (depsJS arg)
 | Expr.lit (Literal.natVal val) => s!"{val}n"
 | Expr.lit (Literal.strVal val) => s!"'{val}'"
 | Expr.fvar fvarId => s!"((() => {"{"} throw new Error('Undefined fvar {fvarId.name}') {"}"})())"
 | Expr.mvar mvarId => s!"((() => {"{"} throw new Error('Undefined mvar {mvarId.name}') {"}"})())"
 | Expr.mdata data expr => s!"((() => {"{"} throw new Error('Undefined mdata {data} {expr}') {"}"})())"
 | Expr.proj typeName idx struct => s!"((() => {"{"} throw new Error('Undefined proj {typeName} {idx} {struct}') {"}"})())"
 | Expr.sort u => s!"((() => {"{"} throw new Error('Undefined sort {u}') {"}"})())"
 | Expr.forallE binderName binderType body _binderInfo =>
      s!"((() => {"{"} throw new Error('Undefined forallE {binderName} {binderType} {body}') {"}"})())"



private def exprJS ctx
 | Expr.const name _uni => mangle name
 | Expr.bvar n => s!"bv_{ctx - n - 1}"
 | Expr.lam _binderName _binderType body _binderInfo =>
      s!"(bv_{ctx}) => ({exprJS (ctx + 1) body})"
 | Expr.letE _annot?declName _type value body _nondep =>
      s!"((bv_{ctx}) => ({exprJS (ctx + 1) body}))({exprJS ctx value})"
 | Expr.app fn arg => s!"({exprJS ctx fn})({exprJS ctx arg})"
 | Expr.lit (Literal.natVal val) => s!"{val}n"
 | Expr.lit (Literal.strVal val) => s!"'{val}'"
 | Expr.fvar fvarId => s!"((() => {"{"} throw new Error('Undefined fvar {fvarId.name}') {"}"})())"
 | Expr.mvar mvarId => s!"((() => {"{"} throw new Error('Undefined mvar {mvarId.name}') {"}"})())"
 | Expr.mdata data expr => s!"((() => {"{"} throw new Error('Undefined mdata {data} {expr}') {"}"})())"
 | Expr.proj typeName idx struct => s!"((() => {"{"} throw new Error('Undefined proj {typeName} {idx} {struct}') {"}"})())"
 | Expr.sort u => s!"((() => {"{"} throw new Error('Undefined sort {u}') {"}"})())"
 | Expr.forallE binderName binderType body _binderInfo =>
      s!"((() => {"{"} throw new Error('Undefined forallE {binderName} {binderType} {body}') {"}"})())"

private def exprJS' := exprJS 0

#check CommandElabM

elab "#splat" term:term : command => do
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
    logInfo s!""
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
