-- Type alias : a PName is a Nat
import Mathlib
abbrev PName := Nat

inductive TransitionLabel : Type where
  | com (p q : PName)
syntax:10 (name := sclcom) term:10 " ⮕ " term:10 : term
@[macro sclcom] def sclcomImpl : Lean.Macro
  | `($t1:term ⮕ $t2:term) => `(TransitionLabel.com $t1 $t2)
  | _ => Lean.Macro.throwUnsupported

def TransitionLabel.pn : TransitionLabel → Finset PName
  | p ⮕ q => {p, q}
