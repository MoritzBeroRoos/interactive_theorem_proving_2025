/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe Exercise 5: Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Reverse of a List

We define an accumulator-based variant of `reverse`. The first argument, `as`,
serves as the accumulator. This definition is __tail-recursive__, meaning that
compilers and interpreters can easily optimize the recursion away, resulting in
more efficient code. -/

def reverseAccu {α : Type} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu (x :: as) xs

/- 1.1. Our intention is that `reverseAccu [] xs` should be equal to
`reverse xs`. But if we start an induction, we quickly see that the induction
hypothesis is not strong enough. Start by proving the following generalization
(using the `induction` tactic or pattern matching): -/

/-

∀m ∈ ℕ: ∀n ∈ ℕ: P(n,m)
------------
Beweis:
Sei m ∈ ℕ beliebig. Zeige: ∀n ∈ ℕ: P(n,m)
Induktion über n:
Zeige P(0,m).

IS: Angenommen (IV): P(n,m). Zeige dann P(n+1,m).

----------------------------
Bweis2 (besser):
Beweise stattdessen
∀n ∈ ℕ: ∀m ∈ ℕ: P(n,m).
Induktion über n:
Zeige ∀m ∈ ℕ: P(0,m).

IS: Angenommen (IV) ∀m ∈ ℕ: P(n,m). Zeige dann ∀m ∈ ℕ: P(n+1,m)


-/


theorem reverseAccu_Eq_reverse_append {α : Type} :
    ∀as xs : List α, reverseAccu as xs = reverse xs ++ as := by
  intro as xs
  induction xs generalizing as with
  | nil => rfl
  | cons => simp [reverseAccu, tail_ih]; simp [reverse]

/- 1.2. Derive the desired equation. -/

theorem reverseAccu_eq_reverse {α : Type} (xs : List α) :
    reverseAccu [] xs = reverse xs := by
    have h: reverseAccu [] xs = reverse xs ++ [] := reverseAccu_Eq_reverse_append [] xs
    simp[List.append] at h
    exact h



/- 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

theorem reverseAccu_reverseAccu {α : Type} (xs : List α) :
    reverseAccu [] (reverseAccu [] xs) = xs :=
  by simp [reverseAccu_eq_reverse, reverse_reverse]

/- 1.4. Prove the following theorem by structural induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how
structural induction works (and is good practice for the final exam).

    theorem reverseAccu_Eq_reverse_append {α : Type} :
      ∀as xs : list α, reverseAccu as xs = reverse xs ++ as

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the induction hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `rfl` or `simp` need not be
justified if you think they are obvious (to humans), but you should say which
key theorems they depend on. You should be explicit whenever you use a function
definition. -/

-- enter your paper proof here


/- ## Question 2: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/
def drop {α : Type} : ℕ → List α → List α
  | 0,     xs      => xs
  | _ + 1, []      => []
  | m + 1, _ :: xs => drop m xs
/-whatsnew_in-/
/- 2.1. Define the `take` function, which returns a list consisting of the first
`n` elements at the front of a list.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → List α → List α
  | 0, _ => []
  | _+1, [] => []
  | n+1, (x::xs) => (x :: take n xs)

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 2.2. Prove the following theorems, using `induction` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] theorem drop_nil {α : Type} :
    ∀n : ℕ, drop n ([] : List α) = []
  | 0 => rfl
  | _+1 => rfl


@[simp] theorem take_nil {α : Type} :
    ∀n : ℕ, take n ([] : List α) = []
    | 0 => rfl
    | _+1 => rfl

/- 2.3. Follow the recursion pattern of `drop` and `take` to prove the
following theorems. In other words, for each theorem, there should be three
cases, and the third case will need to invoke the induction hypothesis.

Hint: Note that there are three variables in the `drop_drop` theorem (but only
two arguments to `drop`). For the third case, `← add_assoc` might be useful. -/

theorem drop_drop {α : Type} :
    ∀(m n : ℕ) (xs : List α), drop n (drop m xs) = drop (n + m) xs
  | 0,     n, xs      => by rfl
  | n+1, m, [] => by simp
  | n+1, m, x::xs => by simp[drop, drop_drop]
  -- supply the two missing cases here

theorem take_take {α : Type} :
    ∀(m : ℕ) (xs : List α), take m (take m xs) = take m xs
  | 0, xs => rfl
  | n+1, [] => by simp
  | n+1, x::xs => by simp[take, take_take]

theorem take_drop {α : Type} :
    ∀(n : ℕ) (xs : List α), take n xs ++ drop n xs = xs
  | 0, xs => rfl
  | n+1, [] => by simp
  | n+1, x::xs => by simp[take, drop, take_drop]


/- ## Question 3: A Type of Terms

3.1. Define an inductive type corresponding to the terms of the untyped
λ-calculus, as given by the following grammar:

    Term  ::=  `var` String        -- variable (e.g., `x`)
            |  `lam` String Term   -- λ-expression (e.g., `λx. t`)
            |  `app` Term Term     -- application (e.g., `t u`) -/

-- enter your definition here
inductive Term where
  | var: String → Term
  | lam: String → Term → Term
  | app: Term → Term → Term


/- 3.2 (**optional**). Register a textual representation of the type `Term` as
an instance of the `Repr` type class. Make sure to supply enough parentheses to
guarantee that the output is unambiguous. -/

def Term.repr : Term → String := sorry
-- enter your answer here

instance Term.Repr : Repr Term :=
  { reprPrec := fun t prec ↦ Term.repr t }

/- 3.3 (**optional**). Test your textual representation. The following command
should print something like `(λx. ((y x) x))`. -/
/-
#eval (Term.lam "x" (Term.app (Term.app (Term.var "y") (Term.var "x"))
    (Term.var "x")))
-/
end LoVe
