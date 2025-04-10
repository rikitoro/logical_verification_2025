/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe Exercise 9: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Guarded Command Language

In 1976, E. W. Dijkstra introduced the guarded command language (GCL), a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert B     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert B` aborts if `B` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace GCL

inductive Stmt : Type
  | assign : String → (State → ℕ) → Stmt
  | assert : (State → Prop) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | choice : List Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. Complete the following big-step semantics, based on the informal
specification of GCL above. -/

inductive BigStep : (Stmt × State) → State → Prop
  -- enter the missing `assign` rule here
  | assign x a s :
    BigStep (.assign x a, s) (s[x ↦ a s])
  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  -- enter the missing `seq` rule here
  | seq S T s t u (hS : BigStep (S, s) t) (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  -- below, `Ss[i]'hless` returns element `i` of `Ss`, which exists thanks to
  -- condition `hless`
  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  -- enter the missing `loop` rules here
  | loop S s t u (hbody : BigStep (S, s) t) (hrest : BigStep (.loop S, t) u):
    BigStep (.loop S, s) u
  | loop_skip S s :
    BigStep (.loop S, s) s

infixl:110 " ⟹ " => BigStep

/- 1.2. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] theorem BigStep_assign_iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] := by
  apply Iff.intro
  . intro h
    cases h with
    | assign => rfl
  . intro h
    rw [h]
    apply BigStep.assign

@[simp] theorem BigStep_assert {B s t} :
    (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s := by
  apply Iff.intro
  . intro h
    cases h with
    | assert =>
      apply And.intro rfl hB
  . intro h
    cases h with
    | intro hts hBs =>
      rw [hts]
      apply BigStep.assert
      apply hBs

@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
    (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) := by
  apply Iff.intro
  . intro h
    cases h with
    | seq _ _ _ t' _ =>
      apply Exists.intro t'
      apply And.intro hS hT
  . intro h
    cases h with
    | intro s' hs' =>
      cases hs' with
      | intro hss' hs't =>
        apply BigStep.seq
        . apply hss'
        . apply hs't

theorem BigStep_loop {S s u} :
    (Stmt.loop S, s) ⟹ u ↔
    (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) := by
  apply Iff.intro
  . intro h
    cases h with
    | loop _ _ _ _ hb hr =>
      apply Or.inr
      apply Exists.intro t
      apply And.intro hb hr
    | loop_skip _ _ =>
      apply Or.inl
      rfl
  . intro h
    cases h with
    | inl h =>
      rw [h]
      apply BigStep.loop_skip
    | inr h =>
      cases h with
      | intro t ht =>
        cases ht with
        | intro hst htu =>
          apply BigStep.loop
          . apply hst
          . apply htu

/- This one is more difficult: -/

@[simp] theorem BigStep_choice {Ss s t} :
    (Stmt.choice Ss, s) ⟹ t ↔
    (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) := by
  apply Iff.intro
  . intro h
    cases h with
    | choice =>
      apply Exists.intro i
      apply Exists.intro hless
      apply hbody
  . intro h
    cases h with
    | intro i hi =>
      cases hi with
      | intro hless h' =>
        apply BigStep.choice _ _ _ i hless
        apply h'

end GCL

/- 1.3. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a =>
    .assign x a
  | S; T =>
    .seq (gcl_of S) (gcl_of T)
  | Stmt.ifThenElse B S T  =>
    .choice [.assert B; gcl_of S, .assert (fun s ↦ ¬ B s); gcl_of T]
  | Stmt.whileDo B S =>
    .loop (.assert B; (gcl_of S)); .assert (fun s ↦ ¬ B s)

/- 1.4. In the definition of `gcl_of` above, `skip` is translated to
`assert (fun _ ↦ True)`. Looking at the big-step semantics of both constructs,
we can convince ourselves that it makes sense. Can you think of other correct
ways to define the `skip` case? -/

-- enter your answer here


/- ## Question 2: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ~ S₂`. -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- Program equivalence is an equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

theorem BigStepEquiv.refl {S} :
    S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
    S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
    S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. Prove the following program equivalences. -/

theorem BigStepEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip := by
  intro s t
  apply Iff.intro
  . intro h
    cases h with
    | assign =>
      simp only [update_id, BigStep_skip_Iff]
  . intro h
    cases h with
    | skip =>
      simp only [BigStep_assign_Iff, update_id]

theorem BigStepEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S := by
  intro s t
  apply Iff.intro
  . intro h
    cases h with
    | seq _ _ _ t' _ hS hT =>
      cases hS with
      | skip =>
        exact hT
  . intro h
    apply BigStep.seq _ _ _ s
    . apply BigStep.skip
    exact h

theorem BigStepEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S := by
  intro s t
  apply Iff.intro
  . intro h
    cases h with
    | seq _ _ _ t' _ hS hT =>
      cases hT with
      | skip =>
        exact hS
  . intro h
    apply BigStep.seq _ _ s t
    . apply h
    . apply BigStep.skip

theorem BigStepEquiv.if_seq_while_skip {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S := by
  intro s t
  apply Iff.intro
  . intro h
    cases h with
    | if_true =>
      cases hbody with
      | seq =>
        apply BigStep.while_true
        apply hcond
        apply hS
        apply hT
    | if_false =>
      cases hbody with
      | skip =>
        apply BigStep.while_false
        apply hcond
  . intro h
    cases h with
    | while_true =>
      apply BigStep.if_true
      apply hcond
      apply BigStep.seq
      apply hbody
      apply hrest
    | while_false =>
      apply BigStep.if_false
      apply hcond
      simp

/- 2.2 (**optional**). Program equivalence can be used to replace subprograms
by other subprograms with the same semantics. Prove the following so-called
congruence rules that facilitate such replacement: -/

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
      (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ := by
  rw [BigStepEquiv] at *
  -- aesop
  intro s t
  apply Iff.intro
  . intro h
    cases h with
    | seq =>
      apply BigStep.seq
      rw [← hS]
      apply hS_1
      rw [← hT]
      apply hT_1
  . intro h
    cases h with
    | seq =>
      apply BigStep.seq
      rw [hS]
      apply hS_1
      rw [hT]
      apply hT_1

theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ := by
  rw [BigStepEquiv] at *
  aesop

end LoVe
