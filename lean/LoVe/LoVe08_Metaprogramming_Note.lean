
import LoVe.LoVe06_InductivePredicates_Demo

set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe

/- ## 8.1 Tactic Combinators -/


theorem repeat_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro    --  なぜか repeat' hoge とした段階で Lean がハングしてしまう
  repeat' apply Even.add_two
  repeat' sorry

theorem repeat_first_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  repeat'
    first
    | apply Even.add_two
    | apply Even.zero
  . show Even 1
    sorry
  . show Even 1
    sorry

theorem all_goals_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  -- all_goals apply Even.add_two -- fails
  repeat' sorry

theorem all_goals_try_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  all_goals try apply Even.add_two -- always succeeds
  . show Even 2
    sorry
  . show Even 5
    sorry
  . show Even 1
    sorry
  . show Even 0
    sorry

theorem any_goals_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  any_goals apply Even.add_two -- can fail
  . show Even 2
    sorry
  . show Even 5
    sorry
  . show Even 1
    sorry
  . show Even 0
    sorry




/- ## 8.2 Macros -/

macro "intro_and_even" : tactic =>
  `(tactic|
    (
      repeat' apply And.intro
      any_goals
        solve
        | repeat'
          first
          | apply Even.add_two
          | apply Even.zero
    )
  )

theorem intro_and_even_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  intro_and_even
  . show Even 7
    sorry
  . show Even 3
    sorry


/- ## 8.3 The Metaprogramming Monads -/
