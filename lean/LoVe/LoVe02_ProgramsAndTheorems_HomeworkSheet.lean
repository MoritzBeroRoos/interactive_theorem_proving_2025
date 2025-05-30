/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 2 (10 points): Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Snoc

1.1 (3 points). Define the function `snoc` that appends a single element to the
end of a list. Your function should be defined by recursion and not using `++`
(`List.append`). -/

def snoc {α : Type} : List α → α → List α
  | [], a => [a]
  |  x::xs, a => x::(snoc xs a)


/- 1.2 (1 point). Convince yourself that your definition of `snoc` works by
testing it on a few examples. -/

#eval snoc [1] 2
-- invoke `#eval` or `#reduce` here


/- ## Question 2 (6 points): Sum

2.1 (3 points). Define a `sum` function that computes the sum of all the numbers
in a list. -/

def sum : List ℕ → ℕ
  | [] => 0
  | x::xs => x + sum xs

#eval sum [1, 12, 3]   -- expected: 16

/- 2.2 (3 points). State (without proving them) the following properties of
`sum` as theorems. Schematically:

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

Try to give meaningful names to your theorems. Use `sorry` as the proof. -/

-- enter your theorem statements here
theorem sum_snoc (ms n): sum (snoc ms n) = n + sum ms := sorry

theorem sum_append (ms ns): sum (ms ++ ns) = sum ms + sum ns := sorry

theorem sum_reverse (ns) : sum (reverse ns) = sum ns := sorry

end LoVe
