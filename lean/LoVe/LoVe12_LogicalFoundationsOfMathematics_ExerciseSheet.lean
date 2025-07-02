/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe12_LogicalFoundationsOfMathematics_Demo


/- # LoVe Exercise 12: Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Vectors as Subtypes

Recall the definition of vectors from the demo: -/

#check Vector

/- The following function adds two lists of integers elementwise. If one
function is longer than the other, the tail of the longer list is ignored. -/

def List.add : List ℤ → List ℤ → List ℤ
  | [],      []      => []
  | x :: xs, y :: ys => (x + y) :: List.add xs ys
  | [],      y :: ys => []
  | x :: xs, []      => []

/- 1.1. Show that if the lists have the same length, the resulting list also
has that length. -/

theorem List.length_add :
    ∀xs ys, List.length xs = List.length ys →
      List.length (List.add xs ys) = List.length xs
  | [], [] =>
    by simp [add]
  | x :: xs, y :: ys =>
    by
      simp [add, length_add xs ys]
      apply length_add xs ys
  | [], y :: ys => by
    simp
  | x :: xs, [] => by
    simp

/- 1.2. Define componentwise addition on vectors using `List.add` and
`List.length_add`. -/
#check Vector
def Vector.add {n : ℕ} : Vector ℤ n → Vector ℤ n → Vector ℤ n :=
 fun a b ↦ Subtype.mk (List.add a.val b.val) (by
  have :  (a.val).length = n := by exact a.property
  simp [←this] --wWTF warum nicht rw?
  apply List.length_add
  simp [a.property, b.property]
  )

/- 1.3. Show that `List.add` and `Vector.add` are commutative. -/
@[simp]
theorem List.add_left (xs: List ℤ):
List.add [] xs = [] := by
  cases xs
  simp[add]
  simp[add]

@[simp]
theorem List.add_right (xs: List ℤ):
List.add xs [] = [] := by
  cases xs
  simp[add]
  simp[add]


theorem List.add.comm :
    ∀xs ys, List.add xs ys = List.add ys xs := by
    intro xs ys
    induction xs with
    | nil => simp
    | cons head tail ih =>
      cases ys with
      | nil => simp
      | cons head' tail' =>
        simp [add]
        apply And.intro
        · ring
        · apply List.add.comm


theorem Vector.add.comm {n : ℕ} (u v : Vector ℤ n) :
    Vector.add u v = Vector.add v u := by
    apply Subtype.eq
    unfold add --why is this step not needed?
    apply List.add.comm



/- ## Question 2: Integers as Quotients

Recall the construction of integers from the lecture, not to be confused with
Lean's predefined type `Int` (= `ℤ`): -/

#check Int.Setoid
#check Int.Setoid_Iff
#check Int

/- 2.1. Define negation on these integers. Observe that if `(p, n)` represents
an integer, then `(n, p)` represents its negation. -/




def Int.neg : Int → Int :=
 Quotient.lift (fun np ↦ ⟦(np.2, np.1)⟧) ( by
 intro np1 np2 h
 simp
 apply Quotient.sound
 simp [Setoid_Iff] at *
 linarith
 )


/- 2.2. Prove the following theorems about negation. -/

theorem Int.neg_eq (p n : ℕ) :
    Int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
  by rfl


#check Quotient.ind
theorem int.neg_neg (a : Int) :
    Int.neg (Int.neg a) = a := by
    induction a using Quotient.ind
    constructor--dafuq? this works?








end LoVe
