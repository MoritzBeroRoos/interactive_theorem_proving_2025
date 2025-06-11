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
  exact hab (hca hc)

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c := by
  intro habc hab ha
  apply habc
  · exact ha
  · exact hab ha

theorem more_nonsense (a b c d : Prop) :
    ((a → b) → c → d) → c → b → d := by
  intro p hc hb
  apply p
  · intro ha
    exact hb
  · exact hc

theorem even_more_nonsense (a b c : Prop) :
    (a → b) → (a → c) → a → b → c := by
  intro hab hac ha hb
  exact hac ha

/- 1.2 (1 point). Prove the following theorem using basic tactics. -/

theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b := by
  intro h1
  apply h1
  intro h2
  apply h2
  intro ha
  apply h1
  intro
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
  intro h                     -- h : (¬¬a → a) → False
  apply h                     -- it suffices to build g : ¬¬a → a
  intro hna                   -- hna : ¬a → False   (i.e. ¬¬a)
  -- construct na : ¬a, using h
  have na : ¬ a := by
    intro ha                  -- ha : a
    exact h (by               -- constant function λ _ : ¬¬a, ha
      intro _; exact ha)
  -- hna na : False, so derive a from False
  exact (hna na).elim



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

theorem helper {a}:
    DoubleNegation → ((¬¬a ∨ ¬a) → (a ∨ ¬a)) := by
  intro hdn h
  apply Or.elim h
  · intro hnna
    apply Or.intro_left
    apply hdn /-Why does hnna not work here as function argument for hdn?-/
    exact hnna
  · intro na
    apply Or.intro_right
    exact na

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle := by
  intro DN a
  apply helper DN
  apply Iff.mp not_and_or
  intro p
  apply And.left p (And.right p)

/- 2.3 (2 points). We have proved three of the six possible implications
between `ExcludedMiddle`, `Peirce`, and `DoubleNegation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/
--
#check Peirce_of_EM
#check DN_of_Peirce
#check EM_of_DN

-- enter your solution here

theorem EM_of_Peirce: Peirce → ExcludedMiddle := by
  intro
  apply EM_of_DN
  apply DN_of_Peirce
  assumption

theorem Peirce_of_DN: DoubleNegation → Peirce := by
  intro
  apply Peirce_of_EM
  apply EM_of_DN
  assumption

theorem DN_of_EM: ExcludedMiddle → DoubleNegation := by
  intro
  apply DN_of_Peirce
  apply Peirce_of_EM
  assumption



end BackwardProofs

end LoVe
