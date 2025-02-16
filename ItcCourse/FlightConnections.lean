/- Chapter 1.1 -/
/- Let's start with defining a data type : City
   This is a simple inductive data type - a finite and enumerated list of elements. -/
inductive City : Type where
  | Odense : City
  | Rome : City
  | NewYork : City
  | Tokyo : City
  | Sydney : City

namespace FC
/- Axioms : flight connections between cities -/
inductive Conn : City → City → Prop where
  | OR : Conn .Odense .Rome
  | RS : Conn .Rome .Sydney
  | ST : Conn .Sydney .Tokyo
  | TN : Conn .Tokyo .NewYork
  | NR : Conn .NewYork .Rome

/- Schematic variables in expressing whether there exists a walk between two cities -/
inductive Walk : City → City → Prop where
  | dir : Conn A B →
        --------------
          Walk A B
  | comp : Walk A B → Walk B C →
        -------------------------
                Walk A C

/- Chapter 1.2 Derivations -/
/- Backward and forward reasoning -/
-- Backward reasoning: working backward from the goal to the premises
example : Walk .Odense .Rome := by
  apply Walk.dir
  apply Conn.OR

-- Forward reasoning: working forward from the premises to the goal
example : Walk .Odense .Rome := by
  have h : Conn .Odense .Rome := Conn.OR
  exact Walk.dir h

-- The derivation in (1.3)
example : Walk .Odense .Sydney := by
  apply Walk.comp
  apply Walk.dir
  apply Conn.OR
  apply Walk.dir
  apply Conn.RS

-- The derivation in (1.4)
example : Walk .NewYork .Tokyo := by
  apply Walk.dir
  -- Ooops, this does not work
  sorry

example : Walk .NewYork .Tokyo := by
  apply Walk.comp
  apply Walk.dir
  apply Conn.NR
  apply Walk.comp
  apply Walk.dir
  apply Conn.RS
  apply Walk.dir
  apply Conn.ST

-- Example 1.1 : let D_os be the derivation in (1.3)
theorem D_os : Walk .Odense .Sydney := by
  apply Walk.comp
  apply Walk.dir
  apply Conn.OR
  apply Walk.dir
  apply Conn.RS

#check D_os

-- Exercise 1.1 Derive walk(New York, Sydney)
theorem D_ns : Walk .NewYork .Sydney := by
  -- try it :D
  sorry

-- Exercise 1.2 Derive walk(Odense, New York)
theorem D_on : Walk .Odense .NewYork := by
  -- try it :D
  sorry

-- Exercise 1.3 Derive walk(New York, New York)
theorem D_nn : Walk .NewYork .NewYork := by
  -- try it :D
  sorry

-- Subderivations of Example 1.1 D_os
theorem E : Walk .Odense .Rome := by
  apply Walk.dir
  apply Conn.OR

theorem E' : Conn .Odense .Rome := by
  exact Conn.OR

theorem F : Walk .Rome .Sydney := by
  apply Walk.dir
  apply Conn.RS

theorem F' : Conn .Rome .Sydney := by
  exact Conn.RS

example : Walk .Odense .Sydney := by
  apply Walk.comp
  apply E
  apply Walk.dir
  apply Conn.RS

example : Walk .Odense .Sydney := by
  apply Walk.comp
  apply E
  apply F

example : Walk .Odense .Sydney := by
  apply Walk.comp
  apply Walk.dir
  apply E'
  apply Walk.dir
  apply Conn.RS

example : Walk .Odense .Sydney := by
  apply Walk.comp
  apply Walk.dir
  apply E'
  apply F

end FC

/- The system in figure 1.3 -/
namespace FCSym
/- Axioms : flight connections between cities -/
inductive Conn : City → City → Prop where
  | OR : Conn .Odense .Rome
  | RS : Conn .Rome .Sydney
  | ST : Conn .Sydney .Tokyo
  | TN : Conn .Tokyo .NewYork
  | NR : Conn .NewYork .Rome
  -- Symmetric connections
  | sym : Conn A B →
        --------------
          Conn B A

inductive Walk : City → City → Prop where
  | dir : Conn A B →
        --------------
          Walk A B
  | comp : Walk A B → Walk B C →
        -------------------------
                Walk A C

-- Exercise 1.4
theorem D_oo : Walk .Odense .Odense := by
  -- try it :D
  sorry

-- Exercise 1.5
theorem any_city_has_walk : ∀ a, Walk a a := by
  -- try it :D
  sorry
end FCSym

/- The system in figure 1.4 -/
namespace FCW
inductive Conn : City → City → Prop where
  | OR : Conn .Odense .Rome
  | RS : Conn .Rome .Sydney
  | ST : Conn .Sydney .Tokyo
  | TN : Conn .Tokyo .NewYork
  | NR : Conn .NewYork .Rome

inductive Walk : City → City → Nat → Prop where
  | dir : Conn A B →
        --------------
          Walk A B 1
  | comp : Walk A B n → Walk B C m →
        -------------------------
                Walk A C (n + m)

-- Example 1.2
example : Walk .Odense .Sydney 2 := by
  apply @Walk.comp .Odense .Rome 1 .Sydney 1
  apply Walk.dir
  apply Conn.OR
  apply Walk.dir
  apply Conn.RS
end FCW

namespace StructuralInduction
-- Proposition 1.3 (1)
theorem D_conn: FC.Conn a b → FCW.Conn a b := by
  intros h
  cases h
  case OR => exact FCW.Conn.OR
  case RS => exact FCW.Conn.RS
  case ST => exact FCW.Conn.ST
  case TN => exact FCW.Conn.TN
  case NR => exact FCW.Conn.NR

-- Proposition 1.3 (2)
theorem D_walk: FC.Walk a b → ∃ n, FCW.Walk a b n := by
  intros h
  induction h
  case dir a b h =>
    apply Exists.intro 1
    apply FCW.Walk.dir
    apply D_conn h
  case comp a c b h₁ h₂ ih₁ ih₂ =>
    obtain ⟨n, ih₁⟩ := ih₁
    obtain ⟨m, ih₂⟩ := ih₂
    apply Exists.intro (n + m)
    apply FCW.Walk.comp
    exact ih₁
    exact ih₂

end StructuralInduction
