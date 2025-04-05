
import LoVe.LoVe06_InductivePredicates_Demo


-- # LoVe Demo 12: Logical Foundations of Mathematics

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


-- ## Universes

#check @And.intro
#check ∀ {a b : Prop}, a → b → a ∧ b
#check Prop
#check Type
#check Type 1

section

universe u
#check (a : Type u) → a  → a
#check (a : Prop) → a → a
#check ∀ x, x → x
#check ∀ p : Prop, p → p

end


theorem proof_irrel {a : Prop} (h₁ h₂ : a) :
  h₁ = h₂ := by
  rfl

#check False
#check True
#check True.intro

#check false
#check true
#check Bool


-- fails
-- def unsquare (i : ℤ) (hsq : ∃ j, i = j * j) : ℤ :=
--   match hsq with
--     | Exists.intro j _ => j

theorem thm₁ : ∃ j , j * j = (9 : ℤ)  :=
  Exists.intro 3 (by linarith)

theorem thm₂ : ∃ j , j * j = (9 : ℤ) :=
  Exists.intro (-3) (by linarith)

def Ok.extract (h : ∃ j, j * j = (9 : ℤ)) : True := by
  obtain ⟨j, hj⟩ := h
  trivial

def Bad.extract (h : ∃ j, j * j = (9 : ℤ)) : ℤ := by
  -- obtain ⟨j, hj⟩ := h -- error
  -- exact x
  sorry

opaque extract (h : ∃ j , j * j = (9 : ℤ)) : ℤ

axiom extract₁ : extract thm₁ = 3
axiom extract₂ : extract thm₂ = -3

example : False := by
  have irr : thm₁ = thm₂ := by rfl
  have : 3 = -3 := calc
    _ = extract thm₁ := by rw [extract₁]
    _ = extract thm₂ := by rw [irr]
    _ = -3 := by rw [extract₂]
  contradiction


#print Nonempty

theorem Nat.Nonempty : Nonempty ℕ :=
  Nonempty.intro 1

#check Classical.choice
#print axioms Classical.choice

#check Classical.choose
#check Classical.choose_spec
#check Classical.choose thm₁
#check Classical.choose_spec thm₁
#print axioms Classical.choose
#print axioms Classical.choose_spec

#check Classical.em
#print axioms Classical.em


-- ## Subtypes

def Finset α := {A : Set α // Set.Finite A}
#check Finset
#print Finset

-- ### FullTree

def FullTree (α : Type) : Type :=
  {t : Tree α // IsFull t}

def FullTree' (α : Type) : Type :=
  @Subtype (Tree α) IsFull

def nilFullTree : FullTree ℕ :=
  Subtype.mk Tree.nil IsFull.nil

def fullTree6 : FullTree ℕ :=
  Subtype.mk (.node 6 .nil .nil) ( by
    apply IsFull.node
    . apply IsFull.nil
    . apply IsFull.nil
    . rfl
  )

#reduce Subtype.val fullTree6
#reduce fullTree6.val
#check Subtype.property fullTree6


def FullTree.mirror {α : Type} (t : FullTree α) :
  FullTree α :=
  .mk (LoVe.mirror t.val) (by
    apply IsFull_mirror
    apply t.property
  )


theorem FullTree.mirror_mirror {α : Type} (t : FullTree α) :
  mirror (mirror t) = t := by
  apply Subtype.eq
  simp [mirror, LoVe.mirror_mirror]


-- ### Vectors

def Vector (α : Type) (n : ℕ) : Type :=
  {xs : List α // List.length xs = n}


def vector123 : Vector ℤ 3 :=
  .mk [1, 2, 3] (by rfl)

def Vector.neg {n : ℕ} (v : Vector ℤ n) : Vector ℤ n :=
  .mk (v.val.map (Int.neg)) (by
    rw [List.length_map]
    exact v.property
  )

theorem Vector.neg_neg (n : ℕ) (v : Vector ℤ n) :
  v.neg.neg = v := by
  apply Subtype.eq
  simp [neg]


-- ## Quotient Types

#print Setoid

#check Quotient.mk
#check Quotient.sound
#check Quotient.lift


-- ### Integers

instance Int.Setoid : Setoid (ℕ × ℕ) where
  r := fun pn₁ pn₂ : ℕ × ℕ ↦ pn₁.fst + pn₂.snd = pn₂.fst + pn₁.snd
  iseqv := {
    refl := by
      intro pn
      rfl
    symm := by
      intro pn₁ pn₂ h
      symm
      assumption
    trans := by
      intro pn₁ pn₂ pn₃ h₁₂ h₂₃
      linarith
  }

theorem Int.Setoid_Iff (pn₁ pn₂ : ℕ × ℕ) :
  pn₁ ≈ pn₂ ↔
  pn₁.fst + pn₂.snd = pn₂.fst + pn₁.snd
  := by rfl

def Int : Type := Quotient Int.Setoid

def Int.zero : Int := ⟦(0, 0)⟧

theorem Int.zero_Eq (m : ℕ) : Int.zero = ⟦(m, m)⟧ := by
  rw [Int.zero]
  apply Quotient.sound
  rw [Int.Setoid_Iff]
  simp

def Int.add : Int → Int → Int :=
  Quotient.lift₂
  (
    fun pn₁ pn₂ : ℕ × ℕ ↦
      ⟦(pn₁.fst + pn₂.fst, pn₁.snd + pn₂.snd)⟧
  )
  (by
    intro pn₁ pn₂ pn₁' pn₂' h₁ h₂
    apply Quotient.sound
    rw [Int.Setoid_Iff] at *
    linarith
  )

theorem Int.add_Eq (p₁ n₁ p₂ n₂ : ℕ) :
  Int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ = ⟦(p₁ + p₂, n₁ + n₂)⟧ := by
  rfl


theorem Int.add_zero (i : Int) :
  Int.add .zero i = i := by
  induction i using Quotient.inductionOn with
  | h pn =>
    cases pn with
    | mk p n => simp [Int.zero, Int.add]


end LoVe
