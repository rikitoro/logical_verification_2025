/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a _ ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun f b a ↦ f a b

def projFst : α → α → α :=
  fun a _ ↦ a

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun _ a ↦ a

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun _ a g _ ↦ g a


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. You might find the characters `–` (to draw horizontal
bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper

/-

––––––––––––––––––––– VAR –––––––––––– VAR
C ⊢ f : α → β → γ       C ⊢ a : α
––––––––––––––––––––––––––––––––––––– APP    –––––––––––– VAR
C ⊢ f a : β → γ                             C ⊢ b : β       (where, C := f : α → β → γ, b : β, a : α)
–––––––––––––––––––––––––––––––––––––––––––––––––––––––– APP
f : α → β → γ, b : β, a : α ⊢ f a b : γ
–––––––––––––––––––––––––––––––––––––––––––––––––––– FUN
f : α → β → γ, b : β  ⊢ fun a ↦ f a b : α → γ
–––––––––––––––––––––––––––––––––––––––––––––––––––– FUN
f : α → β → γ ⊢ fun b a ↦ f a b : β → α → γ
–––––––––––––––––––––––––––––––––––––––––––––––––––– FUN
⊢ fun f b a ↦ f a b : (α → β → γ) → β → α → γ

何故か ⊢ が左右反転してる？？
-/



end LoVe
