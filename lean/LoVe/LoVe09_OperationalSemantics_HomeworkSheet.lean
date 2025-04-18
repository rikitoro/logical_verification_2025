/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 9 (10 points + 1 bonus point): Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (5 points): Arithmetic Expressions

Recall the type of arithmetic expressions from lecture 1 and its evaluation
function: -/

#check AExp
#check eval

#print AExp
#print eval

/- Let us introduce the following abbreviation for an environment that maps
variable names to values: -/

def Envir : Type :=
  String → ℤ

/- 1.1 (2 points). Complete the following Lean definition of a big-step-style
semantics for arithmetic expressions. The predicate `BigStep` (`⟹`) relates
an arithmetic expression, an environment, and the value to which the expression
evaluates in the given environment: -/

inductive BigStep : AExp × Envir → ℤ → Prop
  -- LoVe.AExp.num : ℤ → AExp
  | num (i env) : BigStep (AExp.num i, env) i
  -- AExp.var : String → AExp
  | var x env     : BigStep (.var x, env) (env x)
  -- LoVe.AExp.add : AExp → AExp → AExp
  | add e₁ e₂ env : BigStep (.add e₁ e₂, env) (eval env e₁ + eval env e₂)
  -- LoVe.AExp.sub : AExp → AExp → AExp
  | sub e₁ e₂ env : BigStep (.sub e₁ e₂, env) (eval env e₁ - eval env e₂)
  -- LoVe.AExp.mul : AExp → AExp → AExp
  | mul e₁ e₂ env : BigStep (.mul e₁ e₂, env) (eval env e₁ * eval env e₂)
  -- LoVe.AExp.div : AExp → AExp → AExp
  | div e₁ e₂ env : BigStep (.div e₁ e₂, env) (eval env e₁ / eval env e₂)



infix:60 " ⟹ " => BigStep

/- 1.2 (1 point). Prove the following theorem to validate your definition
above.

Hint: It may help to first prove
`(AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 2 + 2`. -/

theorem BigStep_add_two_two (env : Envir) :
    (AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 4 := by
  apply BigStep.add

/- 1.3 (2 points). Prove that the big-step semantics is sound with respect to
the `eval` function: -/

theorem BigStep_sound (aenv : AExp × Envir) (i : ℤ) (hstep : aenv ⟹ i) :
    eval (Prod.snd aenv) (Prod.fst aenv) = i := by
  cases hstep with
  | num => rfl
  | var => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl
  | div => rfl


/- ## Question 2 (5 points + 1 bonus point): Semantics of Regular Expressions

Regular expressions are a very popular tool for software development. Often,
when textual input needs to be analyzed it is matched against a regular
expression. In this question, we define the syntax of regular expressions and
what it means for a regular expression to match a string.

We define `Regex` to represent the following grammar:

    R  ::=  ∅       -- `nothing`: matches nothing
         |  ε       -- `empty`: matches the empty string
         |  a       -- `atom`: matches the atom `a`
         |  R ⬝ R    -- `concat`: matches the concatenation of two regexes
         |  R + R   -- `alt`: matches either of two regexes
         |  R*      -- `star`: matches arbitrary many repetitions of a Regex

Notice the rough correspondence with a WHILE language:

    `empty`  ~ `skip`
    `atom`   ~ assignment
    `concat` ~ sequential composition
    `alt`    ~ conditional statement
    `star`   ~ while loop -/

inductive Regex (α : Type) : Type
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- The `Matches r s` predicate indicates that the regular expression `r` matches
the string `s` (where the string is a sequence of atoms). -/

inductive Matches {α : Type} : Regex α → List α → Prop
| empty :
  Matches Regex.empty []
| atom (a : α) :
  Matches (Regex.atom a) [a]
| concat (r₁ r₂ : Regex α) (s₁ s₂ : List α) (h₁ : Matches r₁ s₁)
    (h₂ : Matches r₂ s₂) :
  Matches (Regex.concat r₁ r₂) (s₁ ++ s₂)
| alt_left (r₁ r₂ : Regex α) (s : List α) (h : Matches r₁ s) :
  Matches (Regex.alt r₁ r₂) s
| alt_right (r₁ r₂ : Regex α) (s : List α) (h : Matches r₂ s) :
  Matches (Regex.alt r₁ r₂) s
| star_base (r : Regex α) :
  Matches (Regex.star r) []
| star_step (r : Regex α) (s s' : List α) (h₁ : Matches r s)
    (h₂ : Matches (Regex.star r) s') :
  Matches (Regex.star r) (s ++ s')

/- The introduction rules correspond to the following cases:

* match the empty string
* match one atom (e.g., character)
* match two concatenated regexes
* match the left option
* match the right option
* match the empty string (the base case of `R*`)
* match `R` followed again by `R*` (the induction step of `R*`)

2.1 (1 point). Explain why there is no rule for `nothing`. -/

-- enter your answer here

/- 2.2 (4 points). Prove the following inversion rules. -/

@[simp] theorem Matches_atom {α : Type} {s : List α} {a : α} :
    Matches (Regex.atom a) s ↔ s = [a] := by
  apply Iff.intro
  . intro h
    cases h with
    | atom => rfl
  . intro h
    rw [h]
    apply Matches.atom


@[simp] theorem Matches_nothing {α : Type} {s : List α} :
    ¬ Matches Regex.nothing s := by
  intro h
  cases h

@[simp] theorem Matches_empty {α : Type} {s : List α} :
    Matches Regex.empty s ↔ s = [] := by
  apply Iff.intro
  . intro h
    cases h with
    | empty => rfl
  . intro h
    rw [h]
    apply Matches.empty

@[simp] theorem Matches_concat {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.concat r₁ r₂) s
    ↔ (∃s₁ s₂, Matches r₁ s₁ ∧ Matches r₂ s₂ ∧ s = s₁ ++ s₂) := by
  apply Iff.intro
  . intro h
    cases h with
    | concat =>
      apply Exists.intro s₁
      apply Exists.intro s₂
      aesop
  . intro h
    cases h with
    | intro s₁ h =>
      cases h with
      | intro s₂ h =>
        rw [h.right.right]
        apply Matches.concat
        . apply h.left
        . apply h.right.left

@[simp] theorem Matches_alt {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.alt r₁ r₂) s ↔ (Matches r₁ s ∨ Matches r₂ s) := by
  apply Iff.intro
  . intro h
    cases h with
    | alt_left =>
      left
      exact h_1
    | alt_right =>
      right
      exact h_1
  . intro h
    cases h with
    | inl =>
      apply Matches.alt_left
      exact h_1
    | inr =>
      apply Matches.alt_right
      exact h_1

/- 2.3 (1 bonus point). Prove the following inversion rule. -/

theorem Matches_star {α : Type} {s : List α} {r : Regex α} :
    Matches (Regex.star r) s ↔
    s = []
    ∨ (∃s₁ s₂, Matches r s₁ ∧ Matches (Regex.star r) s₂ ∧ s = s₁ ++ s₂) := by
  apply Iff.intro
  . intro h
    cases h with
    | star_base =>
      apply Or.inl
      rfl
    | star_step =>
      apply Or.inr
      apply Exists.intro s_1
      apply Exists.intro s'
      aesop
  . intro h
    cases h with
    | inl =>
      rw [h_1]
      apply Matches.star_base
    | inr =>
      cases h_1  with
      | intro s₁ h =>
        cases h with
        | intro s₂ h =>
          rw [h.right.right]
          apply Matches.star_step
          . apply h.left
          . apply h.right.left

end LoVe
