/- Examples and exercises from chapter 2 -/
import Mathlib
import ItcCourse.Common

-- here are some process names that are used in the exmaples and exercises
variable {buyer seller alice bob charlie: PName}

/- The syntax of simple choreographies -/
inductive SimpleChor : Type where
  | nil
  | com (p q : PName) (c : SimpleChor)

syntax:10 (name := sccom) term:10 " ⮕ " term:10 " ; " term:10 : term
@[macro sccom] def sccomImpl : Lean.Macro
  | `($t1:term ⮕ $t2:term ; $t3:term) => `(SimpleChor.com $t1 $t2 $t3)
  | _ => Lean.Macro.throwUnsupported

syntax:12 (name := scnil) "𝟎" : term
@[macro scnil] def scnilImpl : Lean.Macro
  | `(𝟎) => `(SimpleChor.nil)
  | _ => Lean.Macro.throwUnsupported

-- Example 2.2
example : SimpleChor :=
  buyer ⮕ seller;
  seller ⮕ buyer;
  𝟎

-- Exercise 2.1 Write a choregraphy for the following ring protocol among Alice, Bob, and Charlie
-- Alice communicates a message to Bob, Bob communicates a message to Charlie, and Charlie communicates a message to Alice.
example : SimpleChor := sorry
-- try it :D

-- Exercise 2.2 Write a choreography for the following scatter protocol where Alice communicates a message to Bob and Charlie.
-- Alice communicates a message to Bob and Alice communicates a message to Charlie.
example : SimpleChor := sorry
-- try it :D

syntax:10 (name := scpndisj) term:10 " # " term:10 : term
@[macro scpndisj] def pndisjImpl : Lean.Macro
  | `($t1:term # $t2:term) => `(Disjoint $t1 $t2)
  | _ => Lean.Macro.throwUnsupported

/- Semantics -/
inductive LTS : SimpleChor → TransitionLabel → SimpleChor → Prop where
  | com :
    LTS (p ⮕ q ; c) (p ⮕ q) c
  | delay :
    LTS c tl c' → ({p, q} # (tl.pn)) →
    ----------------------------------
    LTS (p ⮕ q ; c) tl (p ⮕ q ; c')

syntax:30 (name := scLTS) term:30 " -[ " term:30 " ]-> " term:30 : term
@[macro scLTS] def scLTSImpl : Lean.Macro
  | `($t1 -[ $t2 ]-> $t3) => `(LTS $t1 $t2 $t3)
  | _ => Lean.Macro.throwUnsupported

-- Example 2.3
example : (buyer ⮕ seller ; seller ⮕ buyer ; 𝟎) -[(buyer ⮕ seller)]-> (seller ⮕ buyer ; 𝟎) := by
  apply LTS.com
example : (seller ⮕ buyer ; 𝟎) -[(seller ⮕ buyer)]-> (𝟎) := by
  apply LTS.com

-- Exercise 2.3
-- The transition for the exercise 2.1
example : (alice ⮕ bob ; bob ⮕ charlie ; charlie ⮕ alice ; 𝟎) -[(alice ⮕ bob)]-> (bob ⮕ charlie ; charlie ⮕ alice ; 𝟎) := by
    apply LTS.com
  -- try it :D

example : (bob ⮕ charlie ; charlie ⮕ alice ; 𝟎) -[(bob ⮕ charlie)]-> (charlie ⮕ alice ; 𝟎) := by
  apply LTS.com
  -- try it :D

example : (charlie ⮕ alice ; 𝟎) -[(charlie ⮕ alice)]-> (𝟎) := by
  apply LTS.com
  -- try it :D

-- The transition for the exercise 2.2
example : (alice ⮕ bob ; alice ⮕ charlie ; 𝟎) -[(alice ⮕ bob)]-> (alice ⮕ charlie ; 𝟎) := by
  sorry
  -- try it :D
example : (alice ⮕ charlie ; 𝟎) -[(alice ⮕ charlie)]-> (𝟎) := by
  sorry
  -- try it :D

-- Example 2.4
variable {buyer₁ seller₁ buyer₂ seller₂ : PName}
axiom h : ({buyer₁, seller₁} : Finset PName) # {buyer₂, seller₂}

/- Side conditions: they express constraints on schematic variables -/
example : (buyer₁ ⮕ seller₁ ; buyer₂ ⮕ seller₂ ; 𝟎) -[(buyer₂ ⮕ seller₂)]-> (buyer₁ ⮕ seller₁ ; 𝟎) := by
  apply LTS.delay
  apply LTS.com
  -- Handling the side condition
  simp [TransitionLabel.pn, h.symm]

/- Tips :
  1. Use the `simp` tactic to simplify the goal
  2. Use the `symm` method to apply the symmetry of the hypothesis
  The symmetry of Disjoint is defined as follows:
  theorem Disjoint.symm {α : Type u_1}  [PartialOrder α]  [OrderBot α]  ⦃a b : α⦄ :
    Disjoint a b → Disjoint b a
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Disjoint.html#Disjoint.symm
-/

-- Example 2.5
variable {p₁ p₂ p₃ q₁ q₂ q₃ : PName}
-- Distinct process names
axiom h₁ : ({p₁, q₁} : Finset PName) # {p₂, q₂}
axiom h₂ : ({p₁, q₁} : Finset PName) # {p₃, q₃}
axiom h₃ : ({p₂, q₂} : Finset PName) # {p₃, q₃}

example : (p₁ ⮕ q₁ ; p₂ ⮕ q₂ ; p₃ ⮕ q₃ ; 𝟎) -[(p₃ ⮕ q₃)]-> (p₁ ⮕ q₁ ; p₂ ⮕ q₂ ; 𝟎) := by
  apply LTS.delay
  . apply LTS.delay
    . apply LTS.com
    . simp [TransitionLabel.pn, h₃.symm]
  . simp [TransitionLabel.pn, h₂.symm]

inductive MST : SimpleChor → TransitionLabels → SimpleChor → Prop where
  | refl :
    MST s (ε) s
  | stepR :
    MST s ps s'' → s'' -[p]-> s' →
    --------------------------------
        MST s (ps ∷ₜ p) s'

syntax:30 (name := scMST) term:30 " -[ " term:30 " ]->> " term:30 : term
@[macro scMST] def scMSTImpl : Lean.Macro
  | `($t1 -[ $t2 ]->> $t3) => `(MST $t1 $t2 $t3)
  | _ => Lean.Macro.throwUnsupported

-- Example 2.12 (Figure 2.5)
example : (buyer ⮕ seller ; seller ⮕ buyer ; 𝟎) -[([buyer ⮕ seller] ∷ₜ seller ⮕ buyer)]->> (𝟎) := by
  apply MST.stepR
  . rw [eq_concat_nil] -- this rewrite is definitely not necessary in the paper proof
    apply MST.stepR
    . apply MST.refl
    . apply LTS.com
  . apply LTS.com

-- Exercise 2.9
-- Rule StepL is admissible
theorem admissible_step_l :
    c -[tl]-> c'' → c'' -[tls]->> c' →
    c -[(tl :: tls)]->> c' := by
    intro h1 h2
    induction h2
    case refl =>
      rw [eq_concat_nil]
      apply MST.stepR
      . exact MST.refl
      . exact h1
    case stepR ps s₁  p s₂ h2 h3 ih  =>
      rw [cons_concat_eq]
      apply MST.stepR
      . exact ih
      . exact h3
  -- try it :D

-- Rule Comp is admissible
theorem admissible_comp : c -[tls]->> c'' → c'' -[tls']->> c' →
  c -[(tls ++ tls')]->> c' := by
  intro h1 h2
  induction h2
  case refl =>
    simp
    exact h1
  case stepR ps s'  p s'' _ h3 ih =>
    rw [append_concat_eq]
    apply MST.stepR
    . exact ih
    . exact h3
  -- try it :D

-- Exercise 2.10
-- Rule Single is derivable
theorem derivable_single : c -[tl]-> c' → c -[[tl]]->> c' := by
  rw [eq_concat_nil]
  apply MST.stepR
  exact MST.refl
  -- try it :D

-- Exercise 2.11
inductive MSTₗ : SimpleChor → TransitionLabels → SimpleChor → Prop where
  | refl :
    MSTₗ s (ε) s
  | stepL :
    s -[p]-> s'' → MSTₗ s'' ps s' →
    --------------------------------
        MSTₗ s (p :: ps) s'

syntax:30 (name := scMSTL) term:30 " -[ " term:30 " ]->>ₗ " term:30 : term
@[macro scMSTL] def scMSTLImpl : Lean.Macro
  | `($t1 -[ $t2 ]->>ₗ $t3) => `(MSTₗ $t1 $t2 $t3)
  | _ => Lean.Macro.throwUnsupported

-- Rule StepR is admissible
theorem admissible_l_step_r : c -[tls]->>ₗ c'' → c'' -[tl]-> c' →  c -[(tls ∷ₜ tl)]->>ₗ c' := by
  intro h1 h2
  induction h1
  case refl =>
    apply MSTₗ.stepL
    . exact h2
    . exact MSTₗ.refl
  case stepL s ps s' p s'' h1 h3 ih =>
    apply MSTₗ.stepL
    . exact h1
    . -- This is forward reasoning
      have goal := ih h2
      exact goal

      -- This is backward reasoning
      -- apply ih
      -- exact h2
      -- sorry
  -- try it :D

-- Rule Comp is admissible
theorem admissible_l_comp : c -[tls]->>ₗ c'' → c'' -[tls']->>ₗ c' → c -[(tls ++ tls')]->>ₗ c' := by
  intro h1 h2
  induction h1
  case refl =>
    simp
    exact h2
  case stepL s ps s' p s'' h1 h3 ih =>
    apply MSTₗ.stepL
    . exact h1
    -- . have goal := ih h2
    --   exact goal
    . apply ih
      exact h2
  -- try it :D

-- Rule Single is admissible
theorem admissible_l_single : c -[tl]-> c' →
  c -[[tl]]->>ₗ c' := by
  intro h1
  apply MSTₗ.stepL
  . exact h1
  . exact MSTₗ.refl
  -- try it :D

-- Exercise 2.12
inductive MSTAlt : SimpleChor → TransitionLabels → SimpleChor → Prop where
  | refl :
    MSTAlt s (ε) s
  | single :
    s -[tl]-> s' → MSTAlt s [tl] s'
  | comp :
    MSTAlt s ps s'' → MSTAlt s'' ps' s' →
    --------------------------------
        MSTAlt s (ps ++ ps') s'

syntax:30 (name := scMSTA) term:30 " -[ " term:30 " ]->>ₐ " term:30 : term
@[macro scMSTA] def scMSTAImpl : Lean.Macro
  | `($t1 -[ $t2 ]->>ₐ $t3) => `(MSTAlt $t1 $t2 $t3)
  | _ => Lean.Macro.throwUnsupported

theorem derivable_mst_alt : c -[tls]->> c' → c -[tls]->>ₐ c' := by
  sorry
  -- try it :D

-- Well-formedness
inductive SimpleChor.WF : SimpleChor → Prop where
  | nil : SimpleChor.WF (𝟎)
  | com : SimpleChor.WF c → p ≠ q
          → SimpleChor.WF (p ⮕ q ; c)

lemma SimpleChor.WF_com_inv (hwf : SimpleChor.WF (p ⮕ q ; c)):
  c.WF ∧ p ≠ q := by
  cases hwf
  case com hneq hwf' => exact ⟨hwf', hneq⟩
