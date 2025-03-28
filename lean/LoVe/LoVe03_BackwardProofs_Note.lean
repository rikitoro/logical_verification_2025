
import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Demo 3: Backward Proofs -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

/- ## Tactic Mode -/

theorem fst_of_two_props :
  ∀ a b : Prop, a → b → a := by
  intro a b
  intro ha hb
  apply ha

theorem fst_of_two_params (a b : Prop) (ha : a) (hb : b) : a := by
  apply ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
  a → c := by
  intro ha
  apply hbc
  apply hab ha

/- ## Basic Tactics -/

theorem α_example {α β : Type} (f : α → β) :
  (fun x ↦ f x) = (fun y ↦ f y) := by rfl

theorem β_example {α β : Type} (f : α → β) (a : α):
  (fun x ↦ f x) a = f a := by rfl

def double (n : ℕ) : ℕ := n + n

theorem δ_example : double 5 = 5 + 5 := by rfl

theorem ζ_example : (
  let n : ℕ := 2
  n + n
  ) = 4 := by rfl

theorem η_example {α β : Type} (f : α → β) :
  (fun x ↦ f x) = f := by rfl

theorem ι_example {α β : Type} (a : α) (b : β) :
  Prod.fst (a, b) = a := by rfl


/- ## Reasoning about Connectives and Quantifiers -/

theorem And_swap (a b : Prop) :
  a ∧ b → b ∧ a := by
  intro hab
  apply And.intro
  . apply And.right hab
  . apply And.left hab

opaque f : ℕ → ℕ

theorem f5_if (h : ∀ n : ℕ, f n = n) :
  f 5 = 5 := by
  exact h 5

theorem Exists_double_iden :
  ∃ n : ℕ, double n = n := by
  apply Exists.intro 0
  rfl


end LoVe
