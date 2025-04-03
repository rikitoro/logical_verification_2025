/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
    Odd 1 := by
  intro h
  cases h

/- 1.2. Prove that 3 and 5 are odd. -/

-- enter your answer here
theorem Odd_3 : Odd 3 := by
  intro h
  cases h with
  | add_two _ h1 =>
    simp at *
    cases h1

theorem Odd_5 : Odd 5 := by
  intro h5
  cases h5 with
  | add_two _ h3 =>
    cases h3 with
    | add_two _ h1 =>
      simp at *
      cases h1


/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_times :
    ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 => by
    apply Even.add_two
    . simp [Even_two_times]

/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop
  | vs        : ∀ m n, m > n → ServAhead (m–n)
  | advServ   : ServAhead .advServ
  | gameServ  : ServAhead .gameServ

  -- enter the missing cases here

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
    ServAhead (Score.vs m n) := by
  apply ServAhead.vs _ _ hgt


theorem ServAhead_advServ :
    ServAhead Score.advServ := by
  apply ServAhead.advServ

theorem not_ServAhead_advRecv :
    ¬ ServAhead Score.advRecv := by
  intro h
  cases h

theorem ServAhead_gameServ :
    ServAhead Score.gameServ := by
  apply ServAhead.gameServ

theorem not_ServAhead_gameRecv :
    ¬ ServAhead Score.gameRecv := by
  intro h
  cases h

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

-- enter your answer here


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
    ∀t : Tree α, IsFull (mirror t) → IsFull t := by
  intro t h
  rw [← mirror_mirror t]
  apply IsFull_mirror
  exact h

/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/
#print Tree

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | .nil =>
    .nil
  | .node a l r =>
    .node (f a) (map f l) (map f r)

/- 3.3. Prove the following theorem by case distinction. -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
    ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil
  | .nil => by
    simp [map]
  | .node a l r => by
    simp [map]


/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

#print IsFull

theorem map_mirror {α β : Type} (f : α → β) :
    ∀t : Tree α, IsFull t → IsFull (Tree.map f t) := by
  intro t h
  induction h with
  | nil =>
    simp [Tree.map]
    apply IsFull.nil
  | node a l r hl hr hiff ihl ihr =>
    simp [Tree.map]
    apply IsFull.node
    . apply ihl
    . apply ihr
    . apply Iff.intro
      . intro h
        simp [Tree.map_eq_empty_iff, hiff] at *
        exact h
      . intro h
        simp [Tree.map_eq_empty_iff, hiff] at *
        exact h





end LoVe
