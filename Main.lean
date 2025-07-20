import Lean
import Lean.Syntax
open Lean Elab Command Term Meta Widget

#check WidgetInstance

syntax (name := splat) "#splat" term : command -- declare the syntax

-- abbrev CommandElabM := ReaderT Context $ StateRefT State $ EIO Exception
-- abbrev CommandElab  := Syntax → CommandElabM Unit

def mangleChar
 | '\'' => '_'
 | '.' => '_'
 | ch => ch

def mangle (n : Name) := "lean." ++ String.map mangleChar (toString n)

def exprJS ctx
 | Expr.const name _uni => mangle name
 | Expr.bvar n => s!"bv_{ctx - n - 1}"
 | Expr.lam _binderName _binderType body _binderInfo =>
      s!"(bv_{ctx}) => ({exprJS (ctx + 1) body})"
 | Expr.letE _annot?declName _type value body _nondep =>
      s!"((bv_{ctx}) => ({exprJS (ctx + 1) body}))({exprJS ctx value})"
 | Expr.app fn arg => s!"({exprJS ctx fn})({exprJS ctx arg})"
 | Expr.lit (Literal.natVal val) => s!"{val}n"
 | Expr.lit (Literal.strVal val) => s!"'{val}'"
 | e => s!"((() => {"{"} throw new Error('Undefined {e}') {"}"})())"

def exprJS' := exprJS 0

@[command_elab splat]
def mySplat : CommandElab := fun stx : Syntax => do -- declare and register the elaborator
  if let `(#splat $term) := stx then
    withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_mycommand1 do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := false)
      withRef term <| Meta.check e
      let e : Expr ← Term.levelMVarToParam (← instantiateMVars e)
      let _type ← inferType e
      if let Expr.bvar _ := e then
        logInfo s!"bvar {e}"
      if let Expr.const n _u := e then
        logInfo s!"const {e}"
        let q ← getEnv
        let c := q.constants
        if let ConstantInfo.defnInfo d := c.find! n then
          logInfo s!"defn {d.value}"
      else
        IO.FS.writeFile "./src/generated-data-from-lean.js" ("import * as lean from './hacky-lean-runtime.js';\n\nexport const instructions = " ++ exprJS' e)
        -- logInfo "wrote src/generated-data-from-lean.js"
        -- logInfo (exprJS' e)
      -- logInfo s!"{e} : {type}"
      -- logInfo s!"{tk}"

inductive Splat where
  | line : Float × Float → Float × Float → Splat
  | func : (Float → Float) → Splat
  | stack : Array Splat → Splat
  | circle : Float × Float → Float → Splat


open Splat

#splat λ input =>
  let f := λ x => -0.03 * x * x + 2.7 * x + 10
  let slope := (f (input + 0.001) - f (input - 0.001)) / 0.002
  let yIntercept := f input - input * slope
  #[ line (0, 0) (0, 100)
   , line (0, 0) (100, 0)
   , func (λ x => yIntercept + slope * x)
   , circle (input, f input) 20
   , func f
  ] |> stack









/-
def f := λ input =>
  let f := λ x => -0.02 * x * x + 2.7 * x
  let f' := λ x => -0.04 * x + 2.7
  let inputY := f input
  let slope := f' input -- y = slope * x + int
  let yIntercept := inputY - slope * input
  #[ line (0, 0) (0, 100)
   , line (0, 0) (100, 0)
   , func (λ x => -0.02 * x * x + 2.7 * x)
   , func (λ x => slope * x + yIntercept)
  ] |> stack

#splat f
-/

/-

#splat λ input =>
  let f := λ x => -0.02 * x * x + 2.7 * x
  let f' := λ x => -0.04 * x + 2.7
  let inputY := f input
  let slope := (f (input + 0.0001) - f (input - 0.0001)) / 0.0002 -- y = slope * x + int
  let yIntercept := inputY - slope * input
  #[ line (0, 0) (0, 100)
   , line (0, 0) (100, 0)
   , func (λ x => -0.02 * x * x + 2.7 * x)
   , func (λ x => slope * x + yIntercept)
  ] |> stack

syntax (name := mycommand1) "#mycommand1" term : command -- declare the syntax

-- abbrev CommandElabM := ReaderT Context $ StateRefT State $ EIO Exception
-- abbrev CommandElab  := Syntax → CommandElabM Unit

@[command_elab mycommand1]
def mycommand1Impl : CommandElab := fun stx : Syntax => do -- declare and register the elaborator
  if let `(#mycommand1%$tk $term) := stx then
    withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_mycommand1 do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := false)
      withRef term <| Meta.check e
      let e : Expr ← Term.levelMVarToParam (← instantiateMVars e)
      let type ← inferType e
      logInfo s!"{e} : {type}"
      logInfo s!"{tk}"


#mycommand1 λ x => x + 2 -- Hello World

inductive Msg where
  | Increment : Msg
  | Decrement : Msg

#mycommand1 fun x : Msg => match x with
   | Msg.Increment => ()
   | Msg.Decrement => ()
-/
