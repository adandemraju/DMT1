namespace DMT1.L00_reasoning

axiom P : Prop
axiom R : Prop
axiom Q : Prop
-- Use the #check command to check for yourself!
#check P            -- a proposition!
#check 5            -- a natural number!
#check "Hello!"     -- a string

def n : Nat := 5    -- n is a Nat, with 5 as a witness
#eval n             -- n evaluates to *5*
#reduce n           -- reduce works too
#eval n + 5         -- all kinds of expressions reduce

def PandQ : Prop := P ∧ Q
#check PandQ
#reduce (types := true) PandQ

axiom p : P
axiom q : Q
axiom r : R

-- All is as expected
#check P    -- a proposition
#check p    -- a proof of it


-- Construct proof of P ∧ Q using And.intro
def pq :    P ∧ Q    :=  And.intro p q
def pq' :   P ∧ Q    :=  ⟨ p, q ⟩

-- Construct nested proofs of nested propositions
def p_qr :  P ∧ (Q ∧ R)  :=  And.intro p (And.intro q r)
def p_qr' :  P ∧ (Q ∧ R)  :=  ⟨ p, ⟨ q, r ⟩ ⟩

-- Here with the nesting in the other order
def pq_r :  (P ∧ Q) ∧ R  :=  And.intro (And.intro p q) r
def pq_r' :  (P ∧ Q) ∧ R  :=  ⟨ ⟨ p, q ⟩, r ⟩

-- Just 6 applications of ∧ gets us 64 Ps!
#reduce (types := true)
  let C0 := P ∧ P
  let C1 := C0 ∧ C0
  let C2 := C1 ∧ C1
  let C3 := C2 ∧ C2
  let C4 := C3 ∧ C3
  let C5 := C4 ∧ C4
  C5

#check pq.left
#check pq.right
#check p_qr
#check pq_r
#check pq_r.right
#check pq_r.left
#check pq_r.left.left
#check pq_r.left.right

def andCommutes : Prop :=
  ∀ (P Q : Prop), -- for *all* propositions P,Q
    (P ∧ Q → Q ∧ P) ∧ -- if P ∧ Q is true then Q ∧ P is true
    (Q ∧ P → P ∧ Q) -- if Q ∧ P is true then P ∧ Q is true

theorem proofAndCommutes : andCommutes :=
  fun (P Q : Prop) =>
    And.intro
      -- left conjunct: P ∧ Q → Q ∧ P
      (fun h : P ∧ Q =>
        And.intro h.right h.left
      )
      -- right conjunct: Q ∧ P → P ∧ Q
      (fun h : Q ∧ P =>
        And.intro h.right h.left)

-- Here is the same proof using shorthand notation
theorem proofAndCommutes' :
  ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
    fun (P Q : Prop) =>
      fun (h : P ∧ Q) =>    -- assume we're given proof h
        ⟨ h.right, h.left ⟩ -- construct/return the result

theorem proofAndCommutes'' :
  ∀ (P Q : Prop),
    P ∧ Q → Q ∧ P :=
  by                      -- toggles to tactic mode
    intro P Q h           -- assume P, Q, h as arguments
                          -- self-test: what is h?
    let p := And.left h   -- from h extract (p : P)
    let q := And.right h  -- from h extract (q : Q)
    exact  ⟨ q, p ⟩       -- return ⟨ q, p ⟩ : Q ∧ P

def proofAndCommutes''' : ∀ (P Q : Prop),  P ∧ Q → Q ∧ P
| (P : Prop), (Q : Prop), ⟨ (p : P), (q : Q) ⟩ => ⟨ q, p ⟩

def proofAndCommutes'''' : ∀ (P Q : Prop),  P ∧ Q → Q ∧ P
| _, _, ⟨ p , q ⟩ => ⟨ q, p ⟩

def yay (P Q : Prop) : P ∧ Q → Q ∧ P
| ⟨ p , q ⟩ => ⟨ q, p ⟩

axiom DogRed : Prop
axiom KittyBlack : Prop
axiom dr : DogRed
axiom kb : KittyBlack
def DrAndKb : DogRed ∧ KittyBlack := ⟨ dr, kb ⟩
#check yay DogRed KittyBlack DrAndKb -- KittyBlack ∧ DogRed!

def yaySquared { P Q : Prop } : P ∧ Q → Q ∧ P
| ⟨ p , q ⟩ => ⟨ q, p ⟩

#check yaySquared DrAndKb  --  KittyBlack ∧ DogRed!

theorem proofAndAssoc : P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R :=
  -- to prove ↔, prove both directions
  Iff.intro
  -- forward: P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
  (
    fun
    (h : P ∧ (Q ∧ R)) =>
    by
      let p := h.left
      let q := h.right.left
      let r := h.right.right
      let pq := And.intro p q
      exact And.intro pq r
  )
  -- reverse: (P ∧ Q) ∧ R → P ∧ (Q ∧ R)
  (
    fun
    (h : (P ∧ Q) ∧ R) =>
    by
      let p : P := h.left.left
      let q : Q := h.left.right
      let r : R := h.right
      let qr : Q ∧ R := And.intro q r
      exact And.intro p qr
  )

def fiveIsTwoPlusThree : Prop := 5 = 2 + 3   -- a proposition
-- def p : fiveIsTwoPlusThree := rfl            -- a proof of it

def threeIsFiveMinusTwo : Prop := 3 = 5 - 2   -- another proposition
-- def q : threeIsFiveMinusTwo := rfl            -- a proof of it

def PimpQ : Prop := fiveIsTwoPlusThree → threeIsFiveMinusTwo  -- conjunction
-- def pimpq : PimpQ := fun pfP => q

axiom ifpq : P → Q
axiom ifqp : Q → P

#check Iff.intro ifpq ifqp  -- yay, let's label that

def piffq : P ↔ Q := Iff.intro ifpq ifqp

#check piffq.mp   -- expect P → Q
#check piffq.mpr  -- expect Q → P

end DMT1.L00_reasoning
