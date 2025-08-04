import Std.Data.HashSet
open Std

def Output (ω : Type) [Hashable ω] [BEq ω] (α : Type) : Type :=
  (α × HashSet ω)

inductive Tree where
| node : String → Tree → Tree → Tree
| leaf : Tree

def height : Tree → StateM (HashSet String) Nat
| Tree.leaf => pure 0
| Tree.node str t1 t2 => do
  modify fun s => s.insert str
  max <$> height t1 <*> height t2
