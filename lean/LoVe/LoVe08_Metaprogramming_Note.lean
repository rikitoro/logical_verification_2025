
import LoVe.LoVe06_InductivePredicates_Demo

-- # LoVe Demo 8: Metaprogramming

set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe

-- ## Tactic Combinators

theorem repeat'_example :
  Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by
  repeat' apply And.intro
  repeat'
    first
    | apply Even.add_two
    | apply Even.zero
  . sorry
  . sorry









end LoVe
