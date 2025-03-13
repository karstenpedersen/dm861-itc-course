import Mathlib
import ItcCourse.Common

variable {buyer seller alice bob charlie: PName}

inductive SimpleProc : Type where
  | nil
  | send (p : PName) (pr : SimpleProc)
  | receive (p : PName) (pr : SimpleProc)

syntax:12 (name := spnil) "𝟎ₚ" : term
@[macro spnil] def spnilImpl : Lean.Macro
  | `(𝟎ₚ) => `(SimpleProc.nil)
  | _ => Lean.Macro.throwUnsupported

syntax:10 (name := spsend) term:10 "!" ";" term:10 : term
@[macro spsend] def spsendImpl : Lean.Macro
  | `($t1:term ! ; $t2:term) => `(SimpleProc.send $t1 $t2)
  | _ => Lean.Macro.throwUnsupported

syntax:10 (name := sprecv) term:10 "?" ";" term:10 : term
@[macro sprecv] def sprecvImpl : Lean.Macro
  | `($t1:term ? ; $t2:term) => `(SimpleProc.receive $t1 $t2)
  | _ => Lean.Macro.throwUnsupported

-- Example 3.1 and 3.2
-- Recall the choreography from Example 2.2

/- buyer ⮕ seller ; seller ⮕ buyer ; 𝟎 -/

-- To implement the choreography, we need two process programs,
-- one for the process buyer and one for the process seller.
-- For buyer, 1) send a message to seller, 2) receive a message from seller
example : SimpleProc := seller ! ; seller ? ; 𝟎ₚ
-- For seller, 1) receive a message from buyer, 2) send a message to buyer
example : SimpleProc := buyer ? ; buyer ! ; 𝟎ₚ

-- Exercise 3.1 Wirte a process term that formalises the following sequence of actions:
-- 1) Receive a message from Alice, 2) Send a message to Bob, 3) Send a message to Charlie
example : SimpleProc := sorry
-- try it :D

abbrev Network := PName → SimpleProc

def supp (n : Network) : Set PName :=
  { p | n p ≠ (𝟎ₚ) }

-- Terminated network
def Network.nil : Network := λ _ => (𝟎ₚ)
syntax:12 (name := nwnil) "𝟎ₙ" : term
@[macro nwnil] def nwnilImpl : Lean.Macro
  | `(𝟎ₙ) => `(Network.nil)
  | _ => Lean.Macro.throwUnsupported
#check 𝟎ₙ

-- Atomic network
def Network.atomic (p : PName) (pr : SimpleProc) : Network :=
  λ q => if p = q then pr else 𝟎ₚ
macro t1:term:10 "[" t2:term:11 "]" : term => `(Network.atomic $t1 $t2)
-- Example 3.3 The network with one running process, buyer, which behaves
-- as the defines in Example 3.2
example : Network := buyer [ (seller ! ; seller ? ; 𝟎ₚ) ]

-- Deciable equality for SimpleProc, this is need for encoding the parallel composition
instance (n : Network) : DecidablePred (fun p => n p = (𝟎ₚ)) := by
  intro p
  simp_all
  cases (n p)
  . apply isTrue
    simp_all
  . apply isFalse
    simp_all
  . apply isFalse
    simp_all
-- Don't worry too much about this (´・ω・｀)

-- Parallel composition of networks
-- note: n p ≠ (𝟎ₚ) -> p ∈ supp n, recall the definition of supp n
def Network.par (n m : Network): Network :=
  λ p => if n p ≠ (𝟎ₚ) then n p else m p
macro t1:term:10 " | " t2:term:11 : term => `(Network.par $t1 $t2)
-- note : we are implicitly assuming that supp n # supp m,
-- but we will explicitly need this to prove properties about the parallel composition.

-- Example 3.4 using the parallel composition to implement the bookstore scenario in example 3.1
example : Network := buyer [ (seller ! ; seller ? ; 𝟎ₚ) ] | seller [ (buyer ? ; buyer ! ; 𝟎ₚ) ]

-- Two networks are disjoint if they share no running processes
def Network.disjoint (n m : Network) : Prop :=
  ∀ p, n p = (𝟎ₚ) ∨ m p = (𝟎ₚ)

-- A property of disjoint networks
theorem Network.disjoint_symm (n m : Network) : n.disjoint m → m.disjoint n := by
  intro h
  intro p
  simp [Network.disjoint] at h
  cases (h p)
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

-- Proposition 3.2 and exercise 3.3
theorem Network.supp_union (n m : Network) {h : n.disjoint m} : supp (n | m) = supp n ∪ supp m := by
  sorry
  -- Try it :D
  -- Hint: use Set.ext

-- Let's check what this theorem does
#check Set.ext
-- In mathlib: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Defs.html#Set.ext

-- Equality of networks
-- Extensional equality in action (^w^)
-- Example 3.6
#check funext
-- In mathlib: https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#funext
theorem Network.nil_par_eq_nil: ((𝟎ₙ) | (𝟎ₙ)) = (𝟎ₙ) := by
  -- aesop
  apply funext
  intro p
  simp [Network.par]
-- Notes on aesop : Lean 4's proof search tactic.
-- https://github.com/leanprover-community/aesop

-- Properties of Parallel Composition
-- Proposition 3.4 partial commutative monoid
theorem Network.par_nil (n : Network) : (n | (𝟎ₙ)) = n := by
  funext p
  simp [Network.par]
  -- aesop -- simplifies the last three lines
  intro h
  simp [h]
  rfl

lemma Network.par_comm (n m : Network) {h : n.disjoint m} : (n | m) = (m | n) := by
  funext p
  simp [Network.par]
  simp [Network.disjoint] at h
  -- cases (h p) <;> aesop --cleverer way to do the same thing (^w^)
  cases (h p)
  . rename_i h₁
    simp [h₁]
    by_cases h₂ : m p = (𝟎ₚ)
    . simp [h₂]
    . simp [h₂]
  . rename_i h₁
    simp [h₁]
    by_cases h₂ : n p = (𝟎ₚ)
    . simp [h₂]
    . simp [h₂]

lemma Network.par_assoc (n1 n2 n3 : Network) : ((n1 | n2) | n3) = (n1 | (n2 | n3)) := by
  funext p
  simp [Network.par]
  -- Now I am lazy _(:3 」∠)_
  aesop

-- Propositional 3.5 and exercise 3.4
theorem Network.par_atomic_nil : (n | (p [𝟎ₚ])) = n := by
  sorry
  -- Try it :D
  -- Hint: use funext
