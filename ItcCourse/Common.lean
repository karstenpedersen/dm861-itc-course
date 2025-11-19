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

abbrev TransitionLabels := List TransitionLabel

syntax:20 (name := sctlsnil) " ε " : term
@[macro sctlsnil] def sctlsnilImpl : Lean.Macro
  | `(ε) => `((List.nil : TransitionLabels))
  | _ => Lean.Macro.throwUnsupported

syntax:10 (name := sctls) term:10 " ∷ₜ " term:10 : term
@[macro sctls] def sctlsImpl : Lean.Macro
  | `($t1:term ∷ₜ $t2:term) => `( List.concat ($t1 : TransitionLabels) $t2)
  | _ => Lean.Macro.throwUnsupported

-- Some useful lemmas for manupulating lists
lemma eq_concat_nil :
  [p] = (ε ∷ₜ p) := by rfl

lemma cons_concat_eq:
  x :: (xs ∷ₜ y) = ((x :: xs) ∷ₜ y) := by rfl

lemma append_concat_eq :
  xs ++ (ys ∷ₜ y) = ((xs ++ ys) ∷ₜ y) := by simp

lemma cons_append_eq :
  [x , y] = [x] ++ [y] := by simp

lemma cons_append_assoc :
  x :: (ys ++ zs) = (x :: ys) ++ zs := by rfl
