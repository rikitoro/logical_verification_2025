/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (2 points). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem about_Impl_term :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fun _ _ hor ha =>
    Or.elim hor
      (
        fun hna =>
          False.elim
          (
            hna ha
          )
      )
      (
        fun hb => hb
      )

/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a b : Prop
  assume hor : ¬ a ∨ b
  assume ha : a
  show b from
    Or.elim hor
    (
      show ¬ a → b from
        assume hna : ¬ a
        show b from
          False.elim <| hna ha
    )
    (
      show b → b from
        assume hb : b
        show b from hb
    )



/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  show (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) from
    Iff.intro
    (
      show (∀x, p x ∨ q x) → (∀x, q x ∨ p x) from
        assume h : ∀x, p x ∨ q x
        fix x : α
        have hpxqx : p x ∨ q x := h x
        Or.elim hpxqx
        (
          assume hpx : p x
          show q x ∨ p x from
            Or.inr hpx
        )
        (
          assume hqx : q x
          show q x ∨ p x from
            Or.inl hqx
        )
    )
    (
      show (∀x, q x ∨ p x) → (∀x, p x ∨ q x) from
      assume h : ∀ (x : α), q x ∨ p x
      fix x : α
      Or.elim (h x)
      (
        assume hqx : q x
        Or.inr hqx
      )
      (
        assume hpx : p x
        Or.inl hpx
      )
    )

/- 2.2 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  assume hdn : DoubleNegation
  have hex := SorryTheorems.EM_of_DN hdn
  have hpe := Peirce_of_EM hex
  show Peirce from hpe

theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  assume hpe : Peirce
  have hdn := DN_of_Peirce hpe
  have hem := SorryTheorems.EM_of_DN hdn
  show ExcludedMiddle from hem

theorem dn_of_em :
    ExcludedMiddle → DoubleNegation :=
  assume hem : ExcludedMiddle
  have hpe : Peirce := Peirce_of_EM hem
  have hde : DoubleNegation := DN_of_Peirce hpe
  show DoubleNegation from hde

end BackwardProofs

end LoVe
