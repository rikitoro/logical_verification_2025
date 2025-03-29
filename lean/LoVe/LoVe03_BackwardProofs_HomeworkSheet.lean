/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 3 (10 points): Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1 (5 points): Connectives and Quantifiers

1.1 (4 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem B (a b c : Prop) :
    (a → b) → (c → a) → c → b := by
  intro hab hca hc
  apply hab
  apply hca hc

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c := by
  intro habc hab ha
  apply habc ha
  apply hab ha

theorem more_nonsense (a b c d : Prop) :
    ((a → b) → c → d) → c → b → d := by
  intro h hc hb
  apply h
  intro ha
  apply hb
  apply hc


theorem even_more_nonsense (a b c : Prop) :
    (a → b) → (a → c) → a → b → c := by
  intro hab hac ha hb
  apply hac ha


/- 1.2 (1 point). Prove the following theorem using basic tactics. -/

theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b := by
  intro h
  apply h
  intro h'
  apply h'
  intro ha
  apply h
  intro h''
  apply ha



/- ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about double negation using basic
tactics.

Hints:

* Keep in mind that `¬ a` is defined as `a → False`. You can start by invoking
  `simp [Not]` if this helps you.

* You will need to apply the elimination rule for `False` at a key point in the
  proof. -/

theorem herman (a : Prop) :
    ¬¬ (¬¬ a → a) := by
  intro h
  apply h
  intro nna
  apply False.elim
  apply nna
  intro ha
  apply h
  intro nna
  apply ha


/- 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* One way to find the definitions of `DoubleNegation` and `ExcludedMiddle`
  quickly is to

  1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
  2. move the cursor to the identifier `DoubleNegation` or `ExcludedMiddle`;
  3. click the identifier.

* You can use `rw DoubleNegation` to unfold the definition of
  `DoubleNegation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check DoubleNegation
#check ExcludedMiddle

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle := by
  rw [DoubleNegation, ExcludedMiddle]
  intro hdn
  intro a
  apply hdn
  intro h
  apply h
  apply Or.inr
  intro ha
  apply h
  apply Or.inl ha

/- 2.3 (2 points). We have proved three of the six possible implications
between `ExcludedMiddle`, `Peirce`, and `DoubleNegation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check Peirce_of_EM
#check DN_of_Peirce
#check EM_of_DN

-- enter your solution here
theorem EM_of_Peirce :
  Peirce → ExcludedMiddle := by
  intro h
  apply EM_of_DN
  apply DN_of_Peirce h

theorem Peirce_of_DN :
  DoubleNegation → Peirce := by
  intro h
  apply Peirce_of_EM
  apply EM_of_DN h

theorem DN_of_EM :
  ExcludedMiddle → DoubleNegation := by
  intro h
  apply DN_of_Peirce
  apply Peirce_of_EM h


end BackwardProofs

end LoVe
