import LoVe.LoVe04_ForwardProofs_Demo
import LoVe.LoVe05_FunctionalProgramming_Demo

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

-- ## Introductory Example

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀ k : ℕ, Even k → Even (k + 2)

theorem Even_4 : Even 4 :=
  have Even_0 : Even 0 :=
    Even.zero
  have Even_2 : Even 2 :=
    Even.add_two _ Even_0
  show Even 4 from
    Even.add_two _ Even_2

inductive Score : Type where
  | vs        : ℕ → ℕ → Score
  | advServ   : Score
  | advRecv   : Score
  | gameServ  : Score
  | gameRecv  : Score

infixr:50 " – " => Score.vs

inductive Step : Score → Score → Prop
  | serv_0_15       : ∀ n, Step (0–n) (15–n)
  | serv_15_30      : ∀ n, Step (15–n) (30–n)
  | serv_30_40      : ∀ n, Step (30–n) (40–n)
  | serv_40_game    : ∀ n, n < 40 → Step (40–n) .gameServ
  | serv_40_adv     : Step (40–40) .advServ
  | serve_adv_40    : Step .advServ (40–40)
  | serve_adv_game  : Step .advServ .gameServ
  | recv_0_15       : ∀ n, Step (n–0) (n–15)
  | recv_15_30      : ∀ n, Step (n–15) (n–30)
  | recv_30_40      : ∀ n, Step (n–30) (n–40)
  | recv_40_game    : ∀ n, n < 40 → Step (n–40) .gameRecv
  | recv_40_adv     : Step (40–40) .advRecv
  | recv_adv_40     : Step .advRecv (40–40)
  | recv_adv_game   : Step .advRecv .gameRecv

infixr:45 " ↝ " => Step

theorem no_Step_to_0_0 (s : Score) :
  ¬ s ↝ 0–0 := by
  intro h
  cases h

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | base (a b : α)      : R a b → Star R a b
  | refl (a : α)        : Star R a a
  | trans (a b c : α)   : Star R a b → Star R b c → Star R a c


-- fails
-- inductive Illegal : Prop where
--   | intro : ¬ Illegal → Illegal

-- ## Logical Symbols
namespace TempLogicalSymbols

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Type} (P : α → Prop) : Prop where
  | intro : ∀ a : α, P a → Exists P

inductive True : Prop where
  | intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀ a : α, Eq a a

end TempLogicalSymbols

-- ## Rule Induction

theorem mod_two_Eq_zero_of_Even (n : ℕ) (h : Even n) :
  n % 2 = 0 := by
  induction h with
  | zero => rfl
  | add_two k hk ih => simp [ih]


theorem Star_Star_Iff_Star {α : Type} (R : α → α → Prop) (a b : α) :
  Star (Star R) a b ↔ Star R a b := by
  apply Iff.intro
  . intro h
    induction h with
    | base a' b' hab =>
      exact hab
    | refl a' =>
      apply Star.refl
    | trans a b c hab hbc ihab ihbc =>
      apply Star.trans a b
      . exact ihab
      . exact ihbc
  . intro h
    apply Star.base
    exact h

@[simp]
theorem Star_Star_Eq_Star {α : Type} (R : α → α → Prop) :
  Star (Star R) = Star R := by
  apply funext
  intro a
  apply funext
  intro b
  apply propext
  apply Star_Star_Iff_Star


-- ## Elimination

theorem Even_Iff (n : ℕ) :
  Even n ↔ n = 0 ∨ (∃ m : ℕ, n = m + 2 ∧ Even m) := by
  apply Iff.intro
  . intro hn
    cases hn with
    | zero => simp
    | add_two k hk =>
      apply Or.inr
      apply Exists.intro k
      simp [hk]
  . intro hor
    cases hor with
    | inl heq => simp [heq, Even.zero]
    | inr hex =>
      cases hex with
      | intro k hand =>
        cases hand with
        | intro heq hk =>
          simp [heq, Even.add_two, hk]

theorem Even_Iff_struct (n : ℕ) :
  Even n ↔ n = 0 ∨ (∃ m : ℕ, n = m + 2 ∧ Even m) :=
  Iff.intro
  (
    assume hn : Even n
    match n, hn with
    | _, .zero =>
      show 0 = 0 ∨ _ from by
        simp
    | _, .add_two k hk =>
      show _ ∨ (∃ m, k + 2 = m + 2 ∧ Even m) from
        Or.inr (Exists.intro k (by simp [hk]))
  )
  (
    assume hor : n = 0 ∨ (∃ m, n = m + 2 ∧ Even m)
    match hor with
    | .inl heq =>
      show Even n from
        by simp [heq, Even.zero]
    | .inr hex =>
      match hex with
      | Exists.intro m hand =>
        match hand with
        | And.intro heq hm =>
          show Even n from by
            simp [heq, hm, Even.add_two]
  )

-- ## Further Examples

inductive Sorted : List ℕ → Prop where
  | nil : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ} (hle : x ≤ y) (hsorted : Sorted (y :: zs)) :
    Sorted (x :: y :: zs)

theorem Sorted_3_5 : Sorted [3, 5] := by
  apply Sorted.two_or_more
  . simp
  . exact .single _

theorem Sorted_3_5_raw : Sorted [3, 5] :=
  Sorted.two_or_more _ _ (by simp) (.single _)

theorem Sorted_7_9_9_11 : Sorted [7, 9, 9, 11] :=
  Sorted.two_or_more _ _ (by simp) (
    .two_or_more _ _ (by simp) (
      .two_or_more _ _ (by simp) (
        .single _)))

theorem Not_Sorted_17_13 : ¬ Sorted [17, 13] := by
  intro h
  cases h with
  | two_or_more _ _ hlt hsorted => simp at hlt


inductive Palindrome {α : Type} : List α → Prop where
  | nil : Palindrome []
  | single (x : α) : Palindrome [x]
  | sandwich (x : α) (xs : List α) (hxs : Palindrome xs) :
    Palindrome ([x] ++ xs ++ [x])

theorem Palindrome_reverse {α : Type} (xs : List α) (hxs : Palindrome xs) :
  Palindrome (reverse xs) := by
  induction hxs with
  | nil => exact .nil
  | single x => exact .single x
  | sandwich x xs hxs ih =>
    simp [reverse, reverse_append]
    exact .sandwich _ _ ih


inductive IsFull {α : Type} : Tree α → Prop where
  | nil : IsFull Tree.nil
  | node (a : α) (l r : Tree α) (hl : IsFull l) (hr : IsFull r)
      (hiff : l = .nil ↔ r = .nil) :
    IsFull (.node a l r)


theorem IsFull_singleton {α : Type} (a : α) :
  IsFull (.node a .nil .nil) := by
  apply IsFull.node
  . apply IsFull.nil
  . apply IsFull.nil
  . rfl

theorem IsFull_mirror {α : Type} (t : Tree α) (ht : IsFull t) :
  IsFull (mirror t) := by
  induction ht with
  | nil =>
    simp [mirror, IsFull.nil]
  | node a l r hl hr hiff ih_l ih_r =>
    simp [mirror]
    apply IsFull.node
    . exact ih_r
    . exact ih_l
    . simp [mirror_Eq_nil_Iff, *]

theorem IsFull_mirror_strict_induct {α : Type} (t : Tree α) :
  IsFull t → IsFull (mirror t) := by
  induction t with
  | nil =>
    intro ht
    simp [mirror, ht]
  | node a l r ih_l ih_r =>
    intro ht
    cases ht with
    | node _ _ _ hl hr hiff =>
      simp [mirror]
      apply IsFull.node
      . apply ih_r hr
      . apply ih_l hl
      . simp [mirror_Eq_nil_Iff, hiff]


inductive Term (α β : Type) : Type where
  | var : β → Term α β
  | fn  : α → List (Term α β) → Term α β

inductive WellFormed {α β : Type} (arity : α → ℕ) :
  Term α β → Prop where
  | var (x : β) : WellFormed arity (.var x)
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀ t ∈ ts, WellFormed arity t)
      (hlen : length ts = arity f) :
    WellFormed arity (.fn f ts)

inductive VariableFree {α β : Type} : Term α β → Prop where
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀ t ∈ ts, VariableFree t) :
    VariableFree (Term.fn f ts)

-- ## Induction Pitfalls

theorem Not_Even_two_mul_add_one (m n : ℕ) (hm : m = 2 * n + 1) : ¬ Even m := by
  intro h
  induction h generalizing n with
  | zero => linarith
  | add_two k hk ih =>
    apply ih (n - 1)
    cases n with
    | zero => linarith
    | succ n =>
      simp [Nat.succ_eq_add_one] at *
      linarith



end LoVe
