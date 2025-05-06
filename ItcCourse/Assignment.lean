import ItcCourse.SimpleChoreographies
import ItcCourse.SimpleProcesses
import ItcCourse.Projection

variable {alice bob carol dave: PName}
private axiom alice_not_bob : alice ≠ bob
private axiom alice_not_carol : alice ≠ carol
private axiom bob_not_carol : bob ≠ carol
private axiom alice_not_dave : alice ≠ dave
private axiom bob_not_dave : bob ≠ dave
private axiom carol_not_dave : carol ≠ dave
-- Some useful lemmas for list operations can be found in the file ItcCourse/Common.lean

-- Prove that the choreography can perform the indicated transition.
theorem exercise_1 : (alice ⮕ bob ; alice ⮕ carol ; 𝟎) -[([alice ⮕ bob]∷ₜ alice ⮕ carol)]->> (𝟎) := by
  sorry

-- Prove that the choreography can perform the indicated transition.
theorem exercise_1_alt : (alice ⮕ bob ; bob ⮕ alice; carol ⮕ dave; 𝟎) -[(carol ⮕ dave)]-> (alice ⮕ bob ; bob ⮕ alice; 𝟎) := by
  sorry

-- Prove the following admissibility result.
-- Rule step-L is admissible in the system MSTAlt
theorem exercise_2 : c1 -[tl]-> c3 → c3 -[tls]->>ₐ c2 → c1 -[(tl :: tls)]->>ₐ c2 := by
  sorry

-- Prove that the network can perform the indicated transition.
theorem exercise_3 : (alice [(bob ! ; carol ! ; 𝟎ₚ)] |ₙ bob [ (alice ? ; 𝟎ₚ)] |ₙ (carol [(alice ? ; 𝟎ₚ)])) -[(alice ⮕ bob)]ₙ-> (alice [(carol ! ; 𝟎ₚ) ] |ₙ bob [ 𝟎ₚ ] |ₙ carol [ (alice ? ; 𝟎ₚ) ]) := by
  sorry

-- Prove the following admissibility result.
theorem exercise_4 : n1 -[tls1]ₙ->> n3 → n3 -[tls2]ₙ->> n2 → n1 -[(tls1 ++ tls2)]ₙ->> n2 := by
  sorry

-- Prove that the projection of the indicated choreography is indeed the indicated process.
theorem exercise_5 : ⟦ alice ⮕ bob ; alice ⮕ carol ; 𝟎 ⟧ = (alice [(bob ! ; carol ! ; 𝟎ₚ)] |ₙ bob [ (alice ? ; 𝟎ₚ)] |ₙ (carol [(alice ? ; 𝟎ₚ)])) := by
  sorry

-- Prove that, for the indicated choreography, its projection can simulate all its transitions.
theorem exercise_6 : (⟦ (alice ⮕ bob ; alice ⮕ carol ; 𝟎) ⟧  -[(alice ⮕ bob)]ₙ-> ⟦ (alice ⮕ carol ; 𝟎) ⟧) := by
  sorry


-- Good luck (^w^)
