import Splat
open Splat

def graph := λ input =>
  let f := λ x => -0.03 * x * x + 2.7 * x + 10
  let slope := (f (input + 0.001) - f (input - 0.001)) / 0.002
  let yIntercept := f input - input * slope
  #[ line (0, 0) (0, 100)
   , line (0, 0) (100, 0)
   , func (λ x => yIntercept + slope * x)
   , circle (input, f input) 20
   , func f
  ] |> stack

#splat graph

