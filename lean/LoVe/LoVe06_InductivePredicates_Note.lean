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

end LoVe
