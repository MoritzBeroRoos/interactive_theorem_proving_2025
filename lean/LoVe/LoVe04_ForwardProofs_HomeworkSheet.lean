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
    fun a ↦ (
      fun b ↦ (
        fun hnab ↦ (
          fun ha ↦ (
            Or.elim hnab
              (fun na ↦ False.elim (na ha))
              (fun hb ↦ hb)
          )
        )
      )
    )

/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
      assume a: Prop
      assume b: Prop
      assume hnab: ¬a ∨ b
      assume ha: a
      show b from
        Or.elim hnab
        (
          assume na: ¬a
          show b from False.elim (na ha)
        )
        (
          assume hb:b
          show b from hb
        )


/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
      Iff.intro
        (
          assume h: (∀x, p x ∨ q x)
          assume x: α
          Or.elim (h x)
          (
            assume hp: p x
            show q x ∨ p x from Or.inr hp
          )
          (
            assume hq: q x
            show q x ∨ p x from Or.inl hq
          )
        )
        (
          assume h: (∀x, q x ∨ p x)
          assume x : α
          Or.elim (h x) (
            assume hq: q x
            show p x ∨ q x from Or.inr hq
          )
          (
            assume hp: p x
            show p x ∨ q x from Or.inl hp
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
  assume DN: DoubleNegation
  show Peirce from Peirce_of_EM (SorryTheorems.EM_of_DN DN)

theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  assume p: Peirce
  show ExcludedMiddle from SorryTheorems.EM_of_DN (DN_of_Peirce p)

theorem dn_of_em :
    ExcludedMiddle → DoubleNegation :=
  assume em: ExcludedMiddle
  show DoubleNegation from DN_of_Peirce (Peirce_of_EM em)

end BackwardProofs

end LoVe
