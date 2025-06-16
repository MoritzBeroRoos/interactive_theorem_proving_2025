/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Connectives and Quantifiers

1.1 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  assume h : DoubleNegation
  show Peirce from
    Peirce_of_EM (SorryTheorems.EM_of_DN h)

theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  assume h : Peirce
  show ExcludedMiddle from
    SorryTheorems.EM_of_DN (DN_of_Peirce h)

theorem dn_of_em :
    ExcludedMiddle → DoubleNegation :=
  assume h : ExcludedMiddle
  show DoubleNegation from
    DN_of_Peirce (Peirce_of_EM h)

end BackwardProofs

/- 1.2 (3 points). Supply a structured proof of the commutativity of `∧` under
an `∃` quantifier, using no other theorems than the introduction and elimination
rules for `∃`, `∧`, and `↔`. -/

theorem And_comm_under_Exists {α : Type} (p q : α → Prop) :
    (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
  Iff.intro
    (assume hex : ∃x, p x ∧ q x
     show ∃x, q x ∧ p x from
       Exists.elim hex
         (fix a : α
          assume hpq : p a ∧ q a
          have hp : p a :=
            And.left hpq
          have hq : q a :=
            And.right hpq
          show ∃x, q x ∧ p x from
            Exists.intro a (And.intro hq hp)))
    (assume hex : ∃x, q x ∧ p x
     show ∃x, p x ∧ q x from
       Exists.elim hex
         (fix a : α
          assume hqp : q a ∧ p a
          have hq : q a :=
            And.left hqp
          have hp : p a :=
            And.right hqp
          show ∃x, p x ∧ q x from
            Exists.intro a (And.intro hp hq)))


/- ## Question 2 (4 points): Logic Puzzles

Recall the following tactical proof: -/

theorem weak_peirce :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  by
    intro a b habaab
    apply habaab
    intro habaa
    apply habaa
    intro ha
    apply habaab
    intro haba
    apply ha

/- 2.1 (2 points). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem weak_peirce_term :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  fun (a b : Prop) (habaab : (((a → b) → a) → a) → b) ↦
    habaab (fun habaa : (a → b) → a ↦
      habaa (fun ha : a ↦
        habaab (fun haba : (a → b) → a ↦
          ha)))

/- There are in fact three easy ways:

* Copy-paste the result of `#print weak_peirce`.

* Simply enter `weak_peirce` as the proof term for `weak_peirce_term`.

* Reuse the answer to question 1.2 of homework 1. -/

/- 2.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem weak_peirce_struct :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  fix a b : Prop
  assume habaab : (((a → b) → a) → a) → b
  show b from
    habaab
      (assume habaa : (a → b) → a
       show a from
         habaa
           (assume ha : a
            show b from
              habaab
                (assume haba : (a → b) → a
                  show a from
                    ha)))

end LoVe
