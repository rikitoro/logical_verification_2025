
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

theorem lfp_eq {α : Type} [CompleteLattice α] (f : α → α)
  (hf : Monotone f) :
  lfp f = f (lfp f) := by
  have h : f (lfp f) ≤ lfp f := by
    apply le_lfp
    intro a ha
    apply le_trans
    . apply hf
      apply lfp_le
      apply ha
    . apply ha
  apply le_antisymm
  . apply lfp_le
    apply hf
    apply h
  . apply h

-- ## A Relational Denotational Semantics, Continued

-- def denote : Stmt → Set (State × State)
--   | Stmt.skip             => Id
--   | Stmt.assign x a       =>
--     {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
--   | Stmt.seq S T          => denote S ◯ denote T
--   | Stmt.ifThenElse B S T =>
--     (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
--   | Stmt.whileDo B S      =>
--     lfp (fun X ↦ ((denote S ◯ X) ⇃ B)
--       ∪ (Id ⇃ (fun s ↦ ¬ B s)))

def denote : Stmt → Set (State × State)
  | .skip             => Id
  | .assign x a       => {(s, t) | t = s [x ↦ a s]}
  | .seq S T          => denote S ◯ denote T
    -- r₁ ◯ r₂ = {(a, c) | ∃ b, (a, b) ∈ r₁ ∧ (b, c) ∈ r₂}
  | .ifThenElse B S T =>  (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
    -- r ⇃ P = {(a, b) | (a, b) ∈ r ∧ P a}
  | .whileDo B S      =>
    lfp (fun X ↦ ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s)))

notation (priority := high) "⟦" S "⟧" => denote S



/- We will prove the following two theorems in the exercise. -/

namespace SorryTheorems

theorem Monotone_comp {α β : Type} [PartialOrder α]
      (f g : α → Set (β × β)) (hf : Monotone f)
      (hg : Monotone g) :
    Monotone (fun a ↦ f a ◯ g a) :=
  sorry

theorem Monotone_restrict {α β : Type} [PartialOrder α]
      (f : α → Set (β × β)) (P : β → Prop) (hf : Monotone f) :
    Monotone (fun a ↦ f a ⇃ P) :=
  sorry

end SorryTheorems

theorem Monotone_while_lfp_arg (S B) :
  Monotone (fun X ↦ ⟦S⟧ ◯ X ⇃ B ∪ Id ⇃ (fun s ↦ ¬ B s)) := by
  apply Monotone_union
  . apply SorryTheorems.Monotone_restrict
    apply SorryTheorems.Monotone_comp
    . apply Monotone_const
    . apply Monotone_id
  . apply SorryTheorems.Monotone_restrict
    apply Monotone_const

-- ## Application to Program Equivalence

def DenoteEquiv (S₁ S₂ : Stmt) : Prop :=
  ⟦S₁⟧ = ⟦S₂⟧

infix:50 (priority := high) " ~ " => DenoteEquiv

theorem DenoteEquiv.seq_congr {S₁ S₂ T₁ T₂ : Stmt}
  (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) : S₁; T₁ ~ S₂; T₂ := by
  simp [DenoteEquiv, denote] at *
  simp [hS, hT]

theorem DenoteEquiv.if_congr {B} {S₁ S₂ T₁ T₂ : Stmt}
  (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  .ifThenElse B S₁ T₁ ~ .ifThenElse B S₂ T₂ := by
  simp [DenoteEquiv, denote] at *
  simp [hS, hT]

theorem DenoteEquiv.while_congr {B} {S₁ S₂ : Stmt}
  (hS : S₁ ~ S₂) :
  .whileDo B S₁ ~ .whileDo B S₂ := by
  simp [DenoteEquiv, denote] at *
  simp [hS]

theorem DenoteEquiv.skip_assign_id {x} :
  .assign x (fun s ↦ s x) ~ .skip := by
  simp [DenoteEquiv, denote, Id]

theorem DenoteEquiv.seq_skip_left {S} :
  .skip; S ~ S := by
  simp [DenoteEquiv, denote, comp]

theorem DenoteEquiv.seq_skip_right {S} :
  S; .skip ~ S := by
  simp [DenoteEquiv, denote, comp]


theorem DenoteEquiv.if_seq_while {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip
    ~ Stmt.whileDo B S :=
      by
    simp [DenoteEquiv, denote]
    apply Eq.symm
    apply lfp_eq
    apply Monotone_while_lfp_arg


-- ## A Simpler Approach Based on an Inductive Predicate

inductive Awhile (B : State → Prop) (r : Set (State × State)) :
  State → State → Prop
  | true {s t u} (hcond : B s)
    (hbody : (s, t) ∈ r) (hrest : Awhile B r t u) :
    Awhile B r s u
  | false {s} (hcond : ¬ B s) :
    Awhile B r s s


def denoteAwhile : Stmt → Set (State × State)
  | .skip             => Id
  | .assign x a       =>
    {(s, t) | t = s [x ↦ a s]}
  | .seq S T          => denoteAwhile S ◯ denoteAwhile T
  | .ifThenElse B S T =>
    (denoteAwhile S ⇃ B) ∪ (denoteAwhile T ⇃ (fun s ↦ ¬ B s))
  | .whileDo B S      =>
    {(s, t) | Awhile B (denoteAwhile S) s t}


end LoVe
