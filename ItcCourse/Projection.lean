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
