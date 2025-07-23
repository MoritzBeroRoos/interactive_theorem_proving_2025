/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo
import LoVe.LoVe14_RationalAndRealNumbers_Demo


/- # LoVe Exercise 14: Rational and Real Numbers

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Rationals

1.1. Prove the following theorem.

Hints:

* Start with case distinctions on `a` and `b`.

* When the goal starts getting complicated, use `simp at *` to clean it up. -/

theorem Fraction.ext (a b : Fraction) (hnum : Fraction.num a = Fraction.num b)
      (hdenom : Fraction.denom a = Fraction.denom b) :
    a = b := by
    cases a
    cases b
    aesop

/- 1.2. Extending the `Fraction.Mul` instance from the lecture, declare
`Fraction` as an instance of `Semigroup`.

Hint: Use the theorem `Fraction.ext` above, and possibly `Fraction.mul_num` and
`Fraction.mul_denom`. -/

#check Fraction.ext
#check Fraction.mul_num
#check Fraction.mul_denom

instance Fraction.Semigroup : Semigroup Fraction :=
  { Fraction.Mul with
    mul_assoc := by
      intro a b c
      apply Fraction.ext
      simp
      · simp [mul_assoc]
      · simp [mul_assoc]
  }

/- 1.3. Extending the `Rat.Mul` instance from the lecture, declare `Rat` as an
instance of `Semigroup`. -/
@[simp]
theorem mul_def {a b : Fraction}:  (LoVe.Rat.mk a) *  (Rat.mk b) = ⟦a * b⟧ := by rfl

@[simp]
theorem mul_def2 {a b : Fraction}:  ⟦a⟧ *  ⟦b⟧ = ⟦a * b⟧ := by rfl

@[simp]
theorem mul_def3 {a b : Fraction} :
  @HMul.hMul (Rat) (Rat) _ _ ⟦a⟧ ⟦b⟧ = ⟦a * b⟧ := by rfl

#check mul_def3
#check @HMul.hMul
variable (a_1: Fraction)
#check @Quotient.mk Fraction Fraction.Setoid a_1
#check LoVe.Rat.mk a_1


instance Rat.Semigroup : Semigroup Rat :=
  { Rat.Mul with
    mul_assoc := by
      intro a b c
      induction a using Quotient.ind
      induction b using Quotient.ind
      induction c using Quotient.ind
      
      have h1: (LoVe.Rat.mk a_1) * (LoVe.Rat.mk a) * (LoVe.Rat.mk a_2) = ⟦a_1 * a * a_2⟧ := by rfl
      have h2: (LoVe.Rat.mk a_1) * ((LoVe.Rat.mk a) * (LoVe.Rat.mk a_2)) = ⟦a_1 * (a * a_2)⟧ := by rfl
      rw [h1]
      unfold mul_def
      simp[mul_def]
  }

end LoVe
