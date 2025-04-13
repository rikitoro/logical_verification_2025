
import LoVe.LoVe09_OperationalSemantics_Demo


-- # LoVe Demo 11: Denotational Semantics


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


-- ## Compositionality


namespace SorryDefs

def denote : Stmt → Set (State × State)
  | .skip             => Id
  | .assign x a       => {(s, t) | t = s [x ↦ a s]}
  | .seq S T          => denote S ◯ denote T
    -- r₁ ◯ r₂ = {(a, c) | ∃ b, (a, b) ∈ r₁ ∧ (b, c) ∈ r₂}
  | .ifThenElse B S T =>  (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
    -- r ⇃ P = {(a, b) | (a, b) ∈ r ∧ P a}
  | .whileDo B S      =>  sorry -- lfp (fun X ↦ ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun x ↦ ¬ B S)))

end SorryDefs
--#print lfp

/-
| .whileDo B S =>
  ((denote S ◯ denote (.whileDo B S)) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s))

X = ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s))
-/

-- ## Fixpoints

-- ## Monotone Functions

def Monotone {α β : Type} [PartialOrder α] [PartialOrder β] (f :α → β) : Prop :=
  ∀ a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

theorem Monotone_id {α : Type} [PartialOrder α] : Monotone (fun a : α ↦ a) := by
  intro a₁ a₂ ha
  simp
  exact ha

theorem Monotone_const {α β : Type} [PartialOrder α] [PartialOrder β] (b : β) :
  Monotone (fun _ : α ↦ b) := by
  intro a₁ a₂ h
  simp


theorem Monotone_union {α β : Type} [PartialOrder α]
  (f g : α → Set β) (hf : Monotone f) (hg : Monotone g) :
  Monotone (fun a ↦ f a ∪ g a) := by
  intro a₁ a₂ ha b hb
  simp at *
  cases hb with
  | inl h =>
    apply Or.inl
    apply hf
    apply ha
    apply h
  | inr h =>
    apply Or.inr
    apply hg
    apply ha
    apply h

-- ## Complete Lattices

#print CompleteLattice
#print Set.PartialOrder

class CompleteLattice (α : Type)
  extends PartialOrder α : Type where
  Inf     : Set α →α
  Inf_le  : ∀A b, b ∈ A → Inf A ≤ b
  le_Inf  : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A

instance Set.CompleteLattice {α : Type} : CompleteLattice (Set α) := {
  @Set.PartialOrder α with
  Inf       := fun X ↦ {a | ∀A, A ∈ X → a ∈ A}
  Inf_le    := by aesop
  le_Inf    := by aesop
}

-- ## Least Fixpoint

def lfp {α : Type} [CompleteLattice α] (f : α → α) : α :=
  CompleteLattice.Inf {a | f a ≤ a}


theorem lfp_le {α : Type} [CompleteLattice α]
  (f : α → α) (a : α) (h : f a ≤ a) :
  lfp f ≤ a := by
  apply CompleteLattice.Inf_le
  exact h

theorem le_lfp {α : Type} [CompleteLattice α]
  (f : α → α) (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
  a ≤ lfp f := by
  apply CompleteLattice.le_Inf
  simp
  exact h



end LoVe
