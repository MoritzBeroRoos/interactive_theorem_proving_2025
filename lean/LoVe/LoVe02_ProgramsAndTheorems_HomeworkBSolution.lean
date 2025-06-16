/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 2 (10 points): Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Minus 2

1.1 (3 points). Define the function `minusTwo` that subtracts two from its 
argument.

Hint: There should be three cases. -/

def minusTwo : ℕ → ℕ
  | 0     => 0
  | 1     => 0
  | n + 2 => n

/- 1.2 (1 point). Convince yourself that your definition of `minusTwo` works by
testing it on a few examples. -/

#eval minusTwo 0   -- expected: 0
#eval minusTwo 1   -- expected: 0
#eval minusTwo 2   -- expected: 0
#eval minusTwo 3   -- expected: 1
#eval minusTwo 4   -- expected: 2
#eval minusTwo 5   -- expected: 3


/- ## Question 2 (6 points): Lists

Consider the type `List` described in the lecture and the `append` and `reverse`
functions from the lecture's demo. The `List` type is part of Lean's
core libraries. You will find the definition of `append` and `reverse` in
`LoVe02_ProgramsAndTheorems_Demo.lean`. One way to find them quickly is
to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `List`, `append`, or `reverse`;
3. click the identifier. -/

#print List
#check append
#check reverse

/- 2.1 (2 points). Test that `reverse` behaves as expected on a few examples.

In the first example, the type annotation `: List ℕ` is needed to guide Lean's
type inference. -/

#eval reverse ([] : List ℕ)   -- expected: []
#eval reverse [1, 3, 5]       -- expected: [5, 3, 1]
#eval reverse [3]             -- expected: [3]
#eval reverse [3, 2]          -- expected: [2, 3]
#eval reverse [3, 2, 5]       -- expected: [5, 2, 3]
#eval reverse [7, 2, 9, 8]    -- expected: [8, 9, 2, 7]
#eval reverse ["b", "c"]      -- expected: ["c, "b"]

/- 2.2 (4 points). State (without proving them) the following properties of
`append` and `reverse`. Schematically:

    `append _ (append _ xs ys) zs = append _ xs (append _ ys zs)`
    `reverse (append _ xs ys) = append _ (reverse ys) (reverse xs)`

for all lists `xs`, `ys`, `zs`. Try to give meaningful names to your theorems.

Hint: Take a look at `reverse_reverse` from the demonstration file. -/

#check SorryTheorems.reverse_reverse

theorem append_assoc {α : Type} (xs ys zs : List α) :
    append _ (append _ xs ys) zs = append _ xs (append _ ys zs) :=
  sorry

theorem reverse_append {α : Type} (xs ys : List α) :
    reverse (append _ xs ys) = append _ (reverse ys) (reverse xs) :=
  sorry

end LoVe
