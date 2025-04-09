import ItcCourse.SimpleChoreographies
import ItcCourse.SimpleProcesses

variable {buyer seller : PName}
private axiom buyer_not_seller : buyer ≠ seller

opaque myBuyer: PName := 1
opaque mySeller: PName := 2

def SimpChor.projection (c : SimpleChor) (r : PName) : SimpleProc :=
  match c with
  | SimpleChor.nil => SimpleProc.nil
  | SimpleChor.com p q c' =>
    if r = p then q ! ; (projection c' r)
    else if r = q then p ? ; (projection c' r)
    else projection c' r
macro "⟦" t1:term:10 "⟧" t2:term:10 : term => `(SimpChor.projection $t1 $t2)

-- Example 4.1
example : ( ⟦ buyer ⮕ seller ; seller ⮕ buyer ; 𝟎 ⟧ buyer) = (seller ! ; seller ? ; 𝟎ₚ) := by
  simp [SimpChor.projection]
  exact buyer_not_seller
  -- simp [SimpChor.projection]
  -- simp [buyer_not_seller]

example : ( ⟦ buyer ⮕ seller ; seller ⮕ buyer ; 𝟎 ⟧ seller) = (buyer ? ; buyer ! ; 𝟎ₚ) := by
  simp [SimpChor.projection]
  exact buyer_not_seller
  -- simp [SimpChor.projection]
  -- simp [buyer_not_seller]

#eval (⟦ myBuyer ⮕ mySeller ; mySeller ⮕ myBuyer ; 𝟎 ⟧ myBuyer)

#eval (⟦ myBuyer ⮕ mySeller ; mySeller ⮕ myBuyer ; 𝟎 ⟧ mySeller)

-- fun f  (c) : λ r → c r

def SimpChor.epp (c : SimpleChor) : Network :=
  λ r => ⟦c⟧ r
macro:max (priority := high) "⟦" t1:term:10 "⟧" : term => `(SimpChor.epp $t1)

-- Example 4.2
example :
  (⟦ buyer ⮕ seller ; seller ⮕ buyer ; 𝟎 ⟧) =
  (buyer [ (seller ! ; seller ? ; 𝟎ₚ) ] |ₙ seller [ (buyer ? ; buyer ! ; 𝟎ₚ) ]) := by
  funext r
  simp [SimpChor.epp, SimpChor.projection, buyer_not_seller, Network.par, Network.atomic]
  -- funext r
  -- simp [SimpChor.epp, SimpChor.projection, Network.par, Network.atomic, buyer_not_seller]

opaque procNotBuyerOrSeller : PName := 3

#eval (⟦ myBuyer ⮕ mySeller ; mySeller ⮕ myBuyer ; 𝟎 ⟧) myBuyer

#eval (⟦ myBuyer ⮕ mySeller ; mySeller ⮕ myBuyer ; 𝟎 ⟧) mySeller

#eval (⟦ myBuyer ⮕ mySeller ; mySeller ⮕ myBuyer ; 𝟎 ⟧) procNotBuyerOrSeller

-- Lemma 3.15+, a more detailed version of the lemma
-- A more general form would be N = N \ p \ q | p [ N p ] | q [ N q ]
lemma Choreography.epp_rm_par (c : SimpleChor) (p q : PName):
  (⟦ c ⟧) = ((⟦ c ⟧ \ p) \ q) |ₙ (p [(⟦ c ⟧p)] |ₙ q [(⟦ c ⟧ q)]) := by
  funext r
  simp [Network.par, Network.atomic, Network.rm]
  by_cases hpr : p = r
  . simp [hpr]
    simp [SimpChor.epp]
    by_cases hqr : q = r
    . simp [hqr]
    . simp [hqr]
      by_cases hprojnil : SimpChor.projection c r = SimpleProc.nil
      . simp [hprojnil]
      . simp [hprojnil]
  . simp [hpr]
    simp [SimpChor.epp]
    by_cases hqr : q = r
    . simp [hqr]
    . simp [hqr]
      by_cases hprojnil : SimpChor.projection c r = SimpleProc.nil
      . simp [hprojnil]
      . simp [hprojnil]

-- A more detailed version of the lemma 4.8
lemma Choreography.epp_com_rm_eq_epp_cont_rm (p q : PName) (c : SimpleChor): ((⟦ (SimpleChor.com p q c) ⟧ \ p) \ q) = ((⟦ c ⟧ \ p) \ q) := by
  funext r
  simp [Network.rm]
  by_cases hrp : r = p
  . simp [hrp]
  . simp [Ne.symm hrp]
    by_cases hrq : r = q
    . simp [hrq]
    . simp [Ne.symm hrq]
      simp [SimpChor.epp, SimpChor.projection]
      simp [hrp, hrq]

theorem epp_completeness (c c' : SimpleChor) (tl : TransitionLabel) (hwf : SimpleChor.WF c):
c -[tl]-> c' → (⟦ c ⟧ -[tl]ₙ-> ⟦c'⟧) := by
  intro hlts
  induction hlts
  case com p q c1 =>
    obtain ⟨ hwf', hneq⟩ := SimpleChor.WF_com_inv hwf
    have heq1 : (⟦ (SimpleChor.com p q c1) ⟧) = (((⟦ (SimpleChor.com p q c1)⟧ \ p) \ q) |ₙ (p [ (q ! ; ⟦ c1 ⟧ p) ] |ₙ q [ (p ? ;  ⟦ c1 ⟧ q) ])) := by
      have goal := Choreography.epp_rm_par (SimpleChor.com p q c1) p q -- by lemma 3.15+
      simp [SimpChor.projection] at goal -- by (4.3)
      simp [Ne.symm hneq] at goal -- by well-formedness
      exact goal
    have heq2 : (⟦ c1 ⟧) = ((⟦ c1 ⟧ \ p) \ q) |ₙ (p [(⟦ c1 ⟧p)] |ₙ q [(⟦ c1 ⟧ q)]) := by
      exact Choreography.epp_rm_par c1 p q -- by lemma 3.15+
    have heq3 := Choreography.epp_com_rm_eq_epp_cont_rm p q c1
    rw [heq3] at heq1
    -- commutativity of parallel composition
    have hcomm1 : (((⟦ c1⟧ \ p) \ q) |ₙ (p [ (q ! ; ⟦ c1 ⟧ p) ] |ₙ q [ (p ? ;  ⟦ c1 ⟧ q) ])) = (p [ (q ! ; ⟦ c1 ⟧ p) ] |ₙ q [ (p ? ;  ⟦ c1 ⟧ q) ]) |ₙ ((⟦ c1 ⟧ \ p) \ q) := by
      have hdisj := Network.ne_rm_par_disjoint (⟦  c1 ⟧) p q (q ! ; ⟦ c1 ⟧ p) (p ? ;  ⟦ c1 ⟧ q) hneq
      exact @Network.par_comm ((⟦ c1 ⟧ \ p) \ q) (p [ (q ! ; ⟦ c1 ⟧ p) ] |ₙ q [ (p ? ;  ⟦ c1 ⟧ q) ]) hdisj

    have hcomm2 : (((⟦ c1 ⟧ \ p) \ q) |ₙ (p [(⟦ c1 ⟧p)] |ₙ q [(⟦ c1 ⟧ q)])) = (p [(⟦ c1 ⟧p)] |ₙ q [(⟦ c1 ⟧ q)]) |ₙ ((⟦ c1 ⟧ \ p) \ q) := by
      have hdisj := Network.ne_rm_par_disjoint (⟦ c1 ⟧) p q (⟦ c1 ⟧ p) (⟦ c1 ⟧ q) hneq
      exact @Network.par_comm ((⟦ c1 ⟧ \ p) \ q) (p [(⟦ c1 ⟧p)] |ₙ q [(⟦ c1 ⟧ q)]) hdisj
    -- rewrite the goal to use network transition rules
    rw [hcomm1] at heq1
    rw [hcomm2] at heq2
    rw [heq1]
    nth_rewrite 2 [heq2]
    apply NLTS.par
    apply NLTS.com
  case delay c1 tl' c2 p q hlts hdisj ih =>
    obtain ⟨ hwf', hneq⟩ := SimpleChor.WF_com_inv hwf
    specialize ih hwf'
    have heq1 : (⟦ (SimpleChor.com p q c1) ⟧) = (((⟦ (SimpleChor.com p q c1)⟧ \ p) \ q) |ₙ (p [ (q ! ; ⟦ c1 ⟧ p) ] |ₙ q [ (p ? ;  ⟦ c1 ⟧ q) ])) := by
      have goal := Choreography.epp_rm_par (SimpleChor.com p q c1) p q -- by lemma 3.15+
      simp [SimpChor.projection] at goal -- by (4.3)
      simp [Ne.symm hneq] at goal -- by well-formedness
      exact goal
    have heq2 : (⟦ (SimpleChor.com p q c2) ⟧) = (((⟦ (SimpleChor.com p q c2)⟧ \ p) \ q) |ₙ (p [ (q ! ; ⟦ c2 ⟧ p) ] |ₙ q [ (p ? ;  ⟦ c2 ⟧ q) ])) := by
      have goal := Choreography.epp_rm_par (SimpleChor.com p q c2) p q -- by lemma 3.15+
      simp [SimpChor.projection] at goal -- by (4.3)
      simp [Ne.symm hneq] at goal -- by well-formedness
      exact goal
    have heq3 := Choreography.epp_com_rm_eq_epp_cont_rm p q c1
    have heq4 := Choreography.epp_com_rm_eq_epp_cont_rm p q c2
    rw [heq3] at heq1
    rw [heq4] at heq2

    -- We want to use Lemma 3.10
    have hpnotin : p ∉ tl'.pn := by
      have hpinpq : p ∈ ({p , q} : Finset PName) := by simp
      exact (@Finset.disjoint_left PName {p , q} tl'.pn).1 hdisj hpinpq
    have hqnotin : q ∉ tl'.pn := by
      have hqinpq : q ∈ ({p , q} : Finset PName) := by simp
      exact (@Finset.disjoint_left PName {p , q} tl'.pn).1 hdisj hqinpq
    have ihrmp : (⟦ c1 ⟧ \ p) -[tl']ₙ-> (⟦ c2 ⟧ \ p) := by
      exact Network.rm_unaffected_process (⟦ c1 ⟧) (⟦ c2 ⟧) tl' p ih hpnotin -- Lemma 3.10
    have ihqrm : ((⟦ c1 ⟧ \ p) \ q) -[tl']ₙ-> ((⟦ c2 ⟧ \ p) \ q) := by
      exact Network.rm_unaffected_process ((⟦ c1 ⟧ \ p)) ((⟦ c2 ⟧ \ p)) tl' q ihrmp hqnotin -- Lemma 3.10 again

    -- we want to use Proposition 3.7
    have heq5 : (⟦ c1 ⟧ p) = (⟦ c2 ⟧ p) := by
      have goal := Network.unaffected_process (⟦ c1 ⟧) (⟦ c2 ⟧) tl' p ih hpnotin -- Proposition 3.7
      simp [SimpChor.epp] at goal
      exact goal
    have heq6 : (⟦ c1 ⟧ q) = (⟦ c2 ⟧ q) := by
      have goal := Network.unaffected_process (⟦ c1 ⟧) (⟦ c2 ⟧) tl' q ih hqnotin -- Proposition 3.7
      simp [SimpChor.epp] at goal
      exact goal
    rw [heq1, heq2]
    rw [← heq5, ← heq6]
    apply NLTS.par
    exact ihqrm
