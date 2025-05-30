/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 8 (10 points + 2 bonus points): Metaprogramming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Question 1 (10 points): A `safe` Tactic

You will develop a tactic that applies all safe introduction and elimination
rules for the connectives and quantifiers exhaustively. A rule is said to be
__safe__ if, given a provable goal, it always gives rise to provable subgoals.
In addition, we will require that safe rules do not introduce metavariables
(since these can easily be instantiated accidentally with the wrong terms).

You will proceed in three steps.

1.1 (4 points). Develop a `safe_intros` tactic that repeatedly applies the
introduction rules for `True`, `∧`, and `↔` and that invokes `intro _` for
`→`/`∀`. The tactic generalizes `intro_and` from the exercise. -/

macro "safe_intros" : tactic => `(tactic | (
  repeat'
    first
    | apply True.intro
    | apply And.intro
    | apply Iff.intro
    | intro
))

theorem abcd (a b c d : Prop) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe_intros
    /- The proof state should be roughly as follows:

        case left
        a b c d : Prop
        a_1 : a
        a_2 : b
        ⊢ False

        case right.mp
        a b c d : Prop
        a_1 : a
        a_2 : c
        ⊢ d

        case right.mpr
        a b c d : Prop
        a_1 : a
        a_2 : d
        ⊢ c -/
    repeat' sorry

/- 1.2 (4 points). Develop a `safe_cases` tactic that performs case
distinctions on `False`, `∧` (`And`), and `∃` (`Exists`). The tactic generalizes
`cases_and` from the exercise.

Hints:

* The last argument of `Expr.isAppOfArity` is the number of arguments expected
  by the logical symbol. For example, the arity of `∧` is 2.

* The "or" connective on `Bool` is called `||`.

Hint: When iterating over the declarations in the local context, make sure to
skip any declaration that is an implementation detail. -/

#check @False
#check @And
#check @Exists

partial def safeCases : TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    for ldecl in lctx do
      if ! ldecl.isImplementationDetail then
        let ty := ldecl.type
        if ty.isAppOfArity ``False 0 || ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then
          cases ldecl.fvarId
          safeCases
          return


elab "safe_cases" : tactic =>
  safeCases

theorem abcdef (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    False :=
  by
    safe_cases
  /- The proof state should be roughly as follows:

      case intro.intro.intro
      a b c d e f : Prop
      P : ℕ → Prop
      hneg : ¬a
      hor : c ∨ d
      himp : b → e
      hiff : e ↔ f
      left : a
      w : ℕ
      h : P w
      left_1 : b
      right : c
      ⊢ False -/
    sorry

/- 1.3 (2 points). Implement a `safe` tactic that first invokes `safe_intros`
on all goals, then `safe_cases` on all emerging subgoals, before it tries
`assumption` on all emerging subsubgoals. -/

macro "safe" : tactic => `(tactic|(
  safe_intros <;>
  safe_cases <;>
  try assumption
))

theorem abcdef_abcd (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe
    /- The proof state should be roughly as follows:

        case left.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : b
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ False

        case right.mp.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : c
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ d -/
    repeat' sorry


/- ## Question 2 (2 bonus points): An `aesop`-Like Tactic

2.1 (1 bonus point). Develop a simple `aesop`-like tactic.

This tactic should apply all safe introduction and elimination rules. In
addition, it should try potentially unsafe rules (such as `Or.inl` and
`False.elim`) but backtrack at some point (or try several possibilities in
parallel). Iterative deepening may be a valid approach, or best-first search, or
breadth-first search. The tactic should also try to apply assumptions whose
conclusion matches the goal, but backtrack if necessary.

Hint: The `MonadBacktrack` monad class might be useful.

2.2 (1 bonus point). Test your tactic on some benchmarks.

You can try your tactic on logic puzzles of the kinds we proved in exercise and
homework 3. Please include these below. -/

end LoVe
