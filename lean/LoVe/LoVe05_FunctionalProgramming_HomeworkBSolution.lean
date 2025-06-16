/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe Homework 5 (10 points + 2 bonus points): Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Reverse of a List

Recall the `reverse` operation from lecture 2 and the `reverse_append` and
`reverse_reverse` theorems from the demo of lecture 4. -/

#check reverse
#check reverse_append
#check reverse_append_tactical
#check reverse_reverse

/- 1.1 (3 points). Prove `reverse_append` again, this time using the
calculational style for the induction step. -/

theorem reverse_append_calc {α : Type} :
    ∀xs ys : List α, reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [],      ys => by simp [reverse]
  | x :: xs, ys =>
    calc
      reverse (x :: xs ++ ys) = reverse (xs ++ ys) ++ [x] :=
        by rfl
      _ = reverse ys ++ reverse xs ++ [x] :=
        by simp [reverse_append_calc]
      _ = reverse ys ++ reverse (x :: xs) :=
        by simp [reverse]

/- 1.2 (3 points). Prove the induction step in the proof below using the
calculational style, following this proof sketch:

      reverse (reverse (x :: xs))
    =     { by definition of `reverse` }
      reverse (reverse xs ++ [x])
    =     { using the theorem `reverse_append` }
      reverse [x] ++ reverse (reverse xs)
    =     { by the induction hypothesis }
      reverse [x] ++ xs
    =     { by definition of `++` and `reverse` }
      [x] ++ xs
    =     { by computation }
      x :: xs -/

theorem reverse_reverse_calc {α : Type} :
    ∀xs : List α, reverse (reverse xs) = xs
  | []      => by rfl
  | x :: xs =>
    calc
      reverse (reverse (x :: xs)) = reverse (reverse xs ++ [x]) :=
        by rw [reverse]
      _ = reverse [x] ++ reverse (reverse xs) :=
        by rw [reverse_append]
      _ = reverse [x] ++ xs :=
        by rw [reverse_reverse_calc xs]
      _ = [x] ++ xs :=
        by simp [reverse]
      _ = x :: xs :=
        by rfl


/- ## Question 2 (4 points + 2 bonus points): Gauss's Summation Formula

`sumUpToOfFun f n = f 0 + f 1 + ⋯ + f n`: -/

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

/- 2.1 (2 points). Prove the following theorem, discovered by Carl Friedrich
Gauss as a pupil.

Hints:

* The `mul_add` and `add_mul` theorems might be useful to reason about
  multiplication.

* The `linarith` tactic introduced in lecture 6 might be useful to reason about
  addition. -/

#check mul_add
#check add_mul

theorem sumUpToOfFun_eq :
    ∀m : ℕ, 2 * sumUpToOfFun (fun i ↦ i) m = m * (m + 1)
  | 0     => by rfl
  | m + 1 =>
    by
      simp [sumUpToOfFun, sumUpToOfFun_eq m, add_mul, mul_add]
      linarith

/- 2.2 (2 points). Prove the following property of `sumUpToOfFun`. -/

theorem sumUpToOfFun_mul (f g : ℕ → ℕ) :
    ∀n : ℕ, sumUpToOfFun (fun i ↦ f i + g i) n =
      sumUpToOfFun f n + sumUpToOfFun g n
  | 0     => by rfl
  | n + 1 =>
    by
      simp [sumUpToOfFun, sumUpToOfFun_mul _ _ n]
      ac_rfl

/- 2.3 (2 bonus points). Prove `sumUpToOfFun_mul` again as a "paper" proof.
Follow the guidelines given in question 1.4 of the exercise. -/

/- We perform the proof by structural induction on `n`.

Case 0: The goal is `sumUpToOfFun (fun i ↦ f i + g i) 0 =`
`sumUpToOfFun f 0 + sumUpToOfFun g 0`. The left-hand side equals `0` by
definition of `sumUpToOfFun`. Similarly, the right-hand side equals `0 + 0`,
i.e., `0`.

Case `n' + 1`. The goal is `sumUpToOfFun (fun i ↦ f i + g i) (n' + 1) =`
`sumUpToOfFun f (n' + 1) + sumUpToOfFun g (n' + 1)`. The induction hypothesis is
`sumUpToOfFun (fun i ↦ f i + g i) n' =` `sumUpToOfFun f n' + sumUpToOfFun g n'`.

Let us simplify the goal's left-hand side:

      sumUpToOfFun (fun i ↦ f i + g i) (n' + 1)
    = sumUpToOfFun (fun i ↦ f i + g i) n' + (f (n' + 1) + g (n' + 1))
      -- by definition of `sumUpToOfFun`
    = sumUpToOfFun f n' + sumUpToOfFun g n' + (f (n' + 1) + g (n' + 1))
      -- by the induction hypothesis

Now let us massage the right-hand side so that it matches the simplified
left-hand side:

      sumUpToOfFun f (n' + 1) + sumUpToOfFun g (n' + 1)
    = (sumUpToOfFun f n' + f (n' + 1)) + (sumUpToOfFun g n' + g (n' + 1))
      -- by definition of `sumUpToOfFun` (twice)
    = sumUpToOfFun f n' + sumUpToOfFun g n' + (f (n' + 1) + g (n' + 1))
      -- by associativity and commutativity of `+`

The two sides are equal. QED -/

end LoVe
