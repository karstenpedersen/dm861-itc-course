import Mathlib
import ItcCourse.Common

variable {buyer seller alice bob charlie: PName}

inductive SimpleProc : Type 0 where
  | nil
  | send (p : PName) (pr : SimpleProc)
  | receive (p : PName) (pr : SimpleProc)

-- Explaining Russell's paradox
inductive MyInductive0 : Type 0 where
  | oneCase

inductive MyInductive1 : Type 1 where
  | anotherCase

inductive AnotherInductive {α : Type u} {β : Type v} : Type (max u v) where
  | caseblah (x : α) (y : β)
-- end of explanation

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

-- Decidable equality for SimpleProc, this is need for encoding the parallel composition
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
macro t1:term:10 " |ₙ " t2:term:11 : term => `(Network.par $t1 $t2)
-- note : we are implicitly assuming that supp n # supp m,
-- but we will explicitly need this to prove properties about the parallel composition.

-- Example 3.4 using the parallel composition to implement the bookstore scenario in example 3.1
example : Network :=
  buyer [ (seller ! ; seller ? ; 𝟎ₚ) ] |ₙ seller [ (buyer ? ; buyer ! ; 𝟎ₚ) ]

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
theorem Network.supp_union (n m : Network) {h : n.disjoint m} : supp (n |ₙ m) = supp n ∪ supp m := by
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
theorem Network.nil_par_eq_nil:
  (𝟎ₙ |ₙ 𝟎ₙ) = (𝟎ₙ) := by
  rfl
  -- apply funext
  -- intro p
  -- simp [Network.par]
-- Notes on aesop : Lean 4's proof search tactic.
-- https://github.com/leanprover-community/aesop

-- Properties of Parallel Composition
-- Proposition 3.4 partial commutative monoid
theorem Network.par_nil (n : Network) : (n |ₙ 𝟎ₙ) = n := by
  -- apply funext
  -- intro p
  funext p
  simp [Network.par]
  aesop -- simplifies the last three lines
  -- intro h
  -- simp [h]
  -- rfl

lemma mylemma : ∀ (n m : Network), n.disjoint m → (n |ₙ m) = (m |ₙ n) := by
  intro n
  intro m
  intro h
  funext p
  simp [Network.par]
  simp [Network.disjoint] at h
  specialize (h p)
  cases h
  . rename_i h_n_p_nil
    simp [h_n_p_nil]
    by_cases h_m_p_nil : m p = SimpleProc.nil
    . simp only [h_m_p_nil]
      trivial
    . simp only [h_m_p_nil]
      trivial
  . sorry




#check mylemma

lemma Network.par_comm (n m : Network)
  {h : n.disjoint m} : (n |ₙ m) = (m |ₙ n) := by
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

lemma Network.par_assoc (n1 n2 n3 : Network) : ((n1 |ₙ n2) |ₙ n3) = (n1 |ₙ (n2 |ₙ n3)) := by
  funext p
  simp [Network.par]
  -- by_cases h₁ : n1 p = (𝟎ₚ)
  -- . simp [h₁]
  -- . simp [h₁]
  -- Now I am lazy _(:3 」∠)_
  aesop

-- Propositional 3.5 and exercise 3.4
theorem Network.par_atomic_nil : (n |ₙ (p [𝟎ₚ])) = n := by
  sorry
  -- Try it :D
  -- Hint: use funext

/- Semantics -/
inductive NLTS : Network → TransitionLabel → Network → Prop where
  | com :
    NLTS (p [ (q ! ; pr)] |ₙ q [ (p ? ; qr)]) (p ⮕ q) (p [pr] |ₙ q [qr])
  | par :
    NLTS n tl n' → NLTS (n |ₙ m) tl (n' |ₙ m)

syntax:30 (name := spNLTS) term:30 " -[ " term:30 " ]ₙ-> " term:30 : term
@[macro spNLTS] def spNLTSImpl : Lean.Macro
  | `($t1 -[ $t2 ]ₙ-> $t3) => `(NLTS $t1 $t2 $t3)
  | _ => Lean.Macro.throwUnsupported

-- Example 3.8
private axiom buyer_not_seller : buyer ≠ seller
example : (buyer [ (seller ! ; seller ? ; 𝟎ₚ) ] |ₙ seller [ (buyer ? ; buyer ! ; 𝟎ₚ) ]) -[(buyer ⮕ seller)]ₙ-> (buyer [ (seller ? ; 𝟎ₚ) ] |ₙ seller [ (buyer ! ; 𝟎ₚ) ]) := by
  exact NLTS.com

-- Example 3.9
lemma buyer_disjoint_seller : (buyer [ (seller ? ; 𝟎ₚ) ]).disjoint (seller [ (buyer ! ; 𝟎ₚ) ]) := by
  intro p
  simp [Network.atomic]
  by_cases h_p_buyer : p = buyer
  . simp [h_p_buyer]
    exact buyer_not_seller
  . apply Or.inl
    exact Ne.symm h_p_buyer

example : (buyer [ (seller ? ; 𝟎ₚ) ] |ₙ seller [ (buyer ! ; 𝟎ₚ) ]) -[(seller ⮕ buyer)]ₙ-> (seller [ 𝟎ₚ ] |ₙ buyer [ 𝟎ₚ ]) := by
  -- Parallel composition is commutative
  rw [@Network.par_comm (buyer [ (seller ? ; 𝟎ₚ) ]) (seller [ (buyer ! ; 𝟎ₚ) ]) buyer_disjoint_seller]
  exact NLTS.com

lemma atomic_nil_eq_network_nil (p : PName) : p [𝟎ₚ] = (𝟎ₙ) := by
  funext q
  simp [Network.atomic, Network.nil]

example : (seller [ 𝟎ₚ ] |ₙ buyer [ 𝟎ₚ ]) = (𝟎ₙ) := by
  rw [Network.par_atomic_nil] -- proposition 3.5
  rw [atomic_nil_eq_network_nil]

-- Example 3.10 Parallel execution
variable {client server gateway : PName}
example : (client [ (gateway ! ; 𝟎ₚ)] |ₙ (gateway [ (client ? ; server ! ; 𝟎ₚ ) ] |ₙ server [ (gateway ? ; 𝟎ₚ)]))
  -[(client ⮕ gateway)]ₙ-> ((client [ 𝟎ₚ ] |ₙ gateway [ (server ! ; 𝟎ₚ) ]) |ₙ server [ (gateway ? ; 𝟎ₚ) ]) := by
  rw [← Network.par_assoc] -- ← specifies the direction of the rewrite
  apply NLTS.par
  exact NLTS.com

/- Fundemental Property of the Semantics -/

-- Transition and process names
-- Proposition 3.7 : A transition never affacts the processes that are not involved in the transition
-- Proof by induction on the transition label
lemma Network.unaffected_process (n₁ n₂ : Network) (tl : TransitionLabel) (r : PName):
  n₁ -[tl]ₙ-> n₂ → r ∉ tl.pn → n₁ r = n₂ r := by
  intro hnlts hnotin
  induction hnlts
  case com p q pr qr =>
    simp [TransitionLabel.pn] at hnotin
    simp [Network.par]
    simp [Network.atomic]
    obtain ⟨ hrnotp , hrnotq ⟩ := hnotin
    simp [Ne.symm hrnotp]
    simp [Ne.symm hrnotq]
  case par m₁ tl m₂ m hnlts ih =>
    -- obtain equality from ih
    have heq := ih hnotin
    simp [Network.par]
    simp [heq]

-- Transition and process removal
def Network.rm (n : Network) (p : PName) : Network :=
  λ q => if p = q then 𝟎ₚ else n q
notation:50 n " \\ " p => Network.rm n p

-- Proposition 3.8 and Execrise 3.6
lemma Network.rm_not_in_supp (n : Network) (p : PName) : p ∉ supp n → (n \ p) = n := by
  -- Try it and have fun :D
  intro hpnotinsupp
  funext q
  simp [Network.rm]
  intro hpq
  cases hpq
  simp [supp] at hpnotinsupp
  exact hpnotinsupp.symm

-- Proposition 3.9 The order in which processes are removed does not matter
lemma Network.rm_comm (n : Network) (p q : PName) : ((n \ p) \ q) = ((n \ q) \ p):= by
  funext r
  simp [Network.rm]
  by_cases hqr : q = r
  . simp [hqr]
  . simp [hqr]

-- (Not in the book) A very good property to have, process removal is distributive over parallel composition
lemma Network.rm_par_dist (n m : Network) (p : PName) : ((n |ₙ m) \ p) = ((n \ p) |ₙ (m \ p)) := by
  funext r
  simp [Network.par, Network.rm]
  by_cases hpr : p = r
  . simp [hpr]
  . simp [hpr]

-- Lemma 3.10
lemma Network.rm_unaffected_process (n₁ n₂ : Network) (tl : TransitionLabel) (r : PName):
  n₁ -[tl]ₙ-> n₂ → r ∉ tl.pn → (n₁ \ r) -[tl]ₙ-> (n₂ \ r):= by
  intro hnlts hnotin
  induction hnlts
  case com p q pr qr =>
    simp [TransitionLabel.pn] at hnotin
    obtain ⟨ hrnotp , hrnotq ⟩ := hnotin
    -- Step 1 : introduce an assumption locally
    have hr_notin_supp₁ : r ∉ supp ((p [ (SimpleProc.send q pr)] ) |ₙ (q [(SimpleProc.receive p qr)])) := by
      simp [supp]
      simp [Network.par, Network.atomic]
      simp [Ne.symm hrnotp]
      simp [Ne.symm hrnotq]
    -- Step 2: using proposition 3.8 to construct an equality relation for the networks before the transition
    have heq₁ := rm_not_in_supp ((p [ (SimpleProc.send q pr)] ) |ₙ (q [(SimpleProc.receive p qr)])) r hr_notin_supp₁
    -- repeat the previous two steps for the networks after the transition
    have hr_notin_supp₂ : r ∉ supp ((p [pr]) |ₙ (q [qr])) := by
      simp [supp]
      simp [Network.par, Network.atomic]
      simp [Ne.symm hrnotp]
      simp [Ne.symm hrnotq]
    have heq₂ := rm_not_in_supp ((p [pr]) |ₙ (q [qr])) r hr_notin_supp₂
    rw [heq₁, heq₂]
    exact NLTS.com
  case par m₁ tl m₂ m hnlts ih =>
    -- This is simpler than the proof in the book
    rw [rm_par_dist m₁ m r] -- you can specify what to rewrite
    rw [rm_par_dist m₂ m r]
    have hpar := @NLTS.par (m₁ \ r) tl (m₂ \ r) (m \ r) (ih hnotin)
    exact hpar

-- A useful lemma that is not in the book
lemma Network.ne_rm_par_disjoint (n : Network) (p q : PName) (pr1 pr2 : SimpleProc):
  p ≠ q → ((n \ p) \ q).disjoint (p[pr1] |ₙ q[pr2]) := by
  intro hpnotq
  intro r
  by_cases hrp : r = p
  . simp [hrp]
    simp [Network.rm, Network.atomic]
  . by_cases hrq : r = q
    . simp [hrq]
      simp [Network.rm, Network.atomic]
    . simp [Network.rm, Network.atomic, Network.par, Ne.symm hrp, Ne.symm hrq]
