/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 6 (10 points): Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): A Type of Terms

Recall the type of terms from question 3 of exercise 5: -/

inductive Term : Type
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 1.1 (2 points). Define an inductive predicate `IsLam` that returns `True` if
its argument is of the form `Term.lam …` and that returns `False` otherwise. -/

-- enter your definition here
inductive IsLam : Term → Prop
  | lam (s : String) (t : Term) : IsLam (.lam s t)

/- 1.2 (2 points). Validate your answer to question 1.1 by proving the following
theorems: -/

theorem IsLam_lam (s : String) (t : Term) :
    IsLam (Term.lam s t) := by
  apply IsLam.lam

theorem not_IsLamVar (s : String) :
    ¬ IsLam (Term.var s) := by
  intro h
  cases h

theorem not_IsLam_app (t u : Term) :
    ¬ IsLam (Term.app t u) := by
  intro h
  cases h

/- ## Question 2 (6 points): Transitive Closure

In mathematics, the transitive closure `R⁺` of a binary relation `R` over a
set `A` can be defined as the smallest solution satisfying the following rules:

    (base) for all `a, b ∈ A`, if `a R b`, then `a R⁺ b`;
    (step) for all `a, b, c ∈ A`, if `a R b` and `b R⁺ c`, then `a R⁺ c`.

In Lean, we can define this notion as follows, by identifying the set `A` with
the type `α`: -/

inductive TCV1 {α : Type} (R : α → α → Prop) : α → α → Prop
  | base (a b : α)   : R a b → TCV1 R a b
  | step (a b c : α) : R a b → TCV1 R b c → TCV1 R a c

/- 2.1 (2 points). Rule `(step)` makes it convenient to extend transitive chains
by adding links to the left. Another way to define the transitive closure `R⁺`
would use replace `(step)` with the following right-leaning rule:

    (pets) for all `a, b, c ∈ A`, if `a R⁺ b` and `b R c`, then `a R⁺ c`.

Define a predicate `TCV2` that embodies this alternative definition. -/

-- enter your definition here

/- 2.2 (2 points). Yet another definition of the transitive closure `R⁺` would
use the following symmetric rule instead of `(step)` or `(pets)`:

    (trans) for all `a, b, c ∈ A`, if `a R⁺ b` and `b R⁺ c`, then `a R⁺ c`.

Define a predicate `TCV3` that embodies this alternative definition. -/

-- enter your definition here

/- 2.3 (1 point). Prove that `(step)` also holds as a theorem about `TCV3`. -/

theorem TCV3_step {α : Type} (R : α → α → Prop) (a b c : α) (rab : R a b)
      (tbc : TCV3 R b c) :
    TCV3 R a c :=
  sorry

/- 2.4 (1 point). Prove the following theorem by rule induction: -/

theorem TCV1_pets {α : Type} (R : α → α → Prop) (c : α) :
    ∀a b, TCV1 R a b → R b c → TCV1 R a c :=
  sorry

end LoVe
