/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
    a → a :=
  assume ha: a
  show a from ha

theorem K (a b : Prop) :
    a → b → b :=
  assume ha: a
  assume hb: b
  show b from hb



theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  assume habc : (a → b → c)
  assume hb: b
  assume ha: a
  show c from habc ha hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  assume ha:a
  assume ha2:a
  show a from ha

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  assume ha: a
  assume ha2: a
  show a from ha2

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  assume habc: a → b → c
  assume ha: a
  assume hac: a → c
  assume hb: b
  show c from hac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  assume hab: a → b
  assume nb: ¬b
  assume ha: a
  show False from
    nb (hab ha)

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (
      assume h1: (∀ (x : α), p x ∧ q x)
      show (∀ (x : α), p x) ∧ ∀ (x : α), q x from
      And.intro
      (
        fix x: α
        show p x from (h1 x).left
      )
      (
        fix x: α
        show q x from (h1 x).right
      )
    )
    (
      assume h1: (∀ (x : α), p x) ∧ ∀ (x : α), q x
      show ∀ (x : α), p x ∧ q x from
        assume x : α
        show p x ∧ q x from
          And.intro (h1.left x) (h1.right x)
    )

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/
#check Exists.elim

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume he: (∃x, ∀y, p x y)
  show (∀y, ∃x, p x y) from
    assume  y: α

    Exists.elim he (
      assume a : α
      show (∀ (y : α), p a y) → ∃ x, p x y from
        assume pp: ∀(y : α), p a y
        Exists.intro a (pp y)

    )




/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/
#check two_mul
theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
  (a + b) * (a + b) = a * (a + b) + b * (a + b) := by simp[add_mul]
  _ = a * a + a * b + b * a + b * b := by simp[mul_add, add_assoc]
  _ = a * a + a * b + a * b + b * b := by simp[mul_comm]
  _ = a * a + 2 * a * b + b * b := by simp[Nat.two_mul, add_mul, add_assoc]
/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  sorry


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

def R : Nat → Prop :=
  fun x ↦ x = 0

theorem All.proof_of_False :
    False :=
    have hR: R 0 := by rfl
    have hall: (∀x : Nat, x = 0 ∧ R x) := Iff.mpr (All.one_point_wrong 0 R) hR
    have incon: 1 = 0 := (hall 1).left
    have bla: (1 = 0) → False := sorry
    show False from bla incon





/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
    False :=
  sorry

end LoVe
