#check And
#check Prod

--(α : Type u) (β : Type v) : Type

/-
  Extract the left conjunct from a conjunction. `h : a ∧ b` then
  `h.left`, also notated as `h.1`, is a proof of `a`.
  left : a

  Extract the right conjunct from a conjunction. `h : a ∧ b` then
  `h.right`, also notated as `h.2`, is a proof of `b`.
  right : b
-/

namespace myAnd

structure And (a b : Prop) : Prop where
  intro :: --name of a value data constructure
  left : a
  right : b

axiom P : Prop
axiom Q : Prop

def aProof : And P Q := And.intro _ _
#check And.left aProof
#check And.right aProof
end myAnd

/-
structure creates data type and a and b are inputs
polymorphic
one constructor
ways to extract the two fields
-/

namespace MyProd

structure Prod(α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

def aProd : Prod Bool String := Prod.mk true "I Love this Stuff"
#eval aProd


#check (Prod)
#check Prod.mk

#eval Prod.fst aProd
#eval Prod.snd aProd

end MyProd

/-
Curry Howard Isomorphism
- Propositions ↔ Types: Every logical proposition corresponds to a type in programming.
- Proofs ↔ Programs: A proof of a proposition is like writing a program that has that type.
- Reasoning ↔ Computation: Doing logic (proving theorems) is the same as doing computation (running programs).
-/

namespace MyFuncs

def S : Type := String
def T : Type := Bool

#check S → T

def aFunc: String → Bool :=
  fun (s : String) => false

def aFunc2: String → Bool :=
  fun (s : String) => true

#check ∀ (s : S), T

def aFunc3 : ∀ (s : String), Bool := λ (s : String) => false

end MyFuncs

namespace myOr

#check Bool

inductive Bool : Type where
  | false : Bool
  | true : Bool

def b1 : Bool := Bool.true
def b2 : Bool := Bool.false

#check Or
axiom P : Prop
axiom Q : Prop
axiom p : P

#check Or P Q

theorem pfPorQ : P ∨ Q :=
  Or.inl p

axiom q : Q

theorem pfPorQ2 : P ∨ Q := Or.inr q

inductive Or (a b : Prop) : Prop where
  | inl (h:a) : Or a b
  | inr (h:b) : Or a b

end myOr

def zeroeqXero : 0 = 0 := rfl
theorem aThm : 0 = 0 ∨ 0 = 1 :=
  (
    let pfZeZ : 0 = 0 := rfl
    Or.inl (pfZeZ)
  )
