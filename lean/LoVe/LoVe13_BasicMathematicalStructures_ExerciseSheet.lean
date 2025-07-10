/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe13_BasicMathematicalStructures_Demo


/- # LoVe Exercise 13: Basic Mathematical Structures

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Type Classes

Recall the inductive type `Tree` we introduced in lecture 5: -/

#check Tree

/- The following function takes two trees and attaches copies of the second
tree to each leaf of the first tree. -/

def Tree.graft {α : Type} : Tree α → Tree α → Tree α
  | Tree.nil,        u => u
  | Tree.node a l r, u =>
    Tree.node a (Tree.graft l u) (Tree.graft r u)

#reduce Tree.graft (Tree.node 1 Tree.nil Tree.nil)
  (Tree.node 2 Tree.nil Tree.nil)

/- 1.1. Prove the following two theorems by structural induction on `t`. -/

theorem Tree.graft_assoc {α : Type} (t u v : Tree α) :
    Tree.graft (Tree.graft t u) v = Tree.graft t (Tree.graft u v) := by
    induction t with
    | nil => rfl
    | node _ t1 t2 _ _ =>
      simp [graft]
      aesop


theorem Tree.graft_nil {α : Type} (t : Tree α) :
    Tree.graft t Tree.nil = t := by
    induction t <;>
    simp [graft]
    aesop

theorem Tree.nil_graft {α : Type} (t : Tree α) :
    Tree.graft Tree.nil t = t := by rfl

/- 1.2. Declare `Tree` an instance of `AddMonoid` using `graft` as the
addition operator. -/

#print AddMonoid

instance Tree.AddMonoid {α : Type} : AddMonoid (Tree α) :=
  { add       := Tree.graft
    add_assoc := Tree.graft_assoc
    zero      := Tree.nil
    add_zero  := Tree.graft_nil
    zero_add  := Tree.nil_graft
    nsmul     := @nsmulRec (Tree α) (Zero.mk Tree.nil) (Add.mk Tree.graft)
  }

/- 1.3 (**optional**). Explain why `Tree` with `graft` as addition cannot be
declared an instance of `AddGroup`. There is no inverse Element, since Trees only become bigger with our Add_def -/

#print AddGroup

-- enter your explanation here

/- 1.4 (**optional**). Prove the following theorem illustrating why `Tree`
with `graft` as addition does not constitute an `AddGroup`. -/

theorem Tree.add_left_neg_counterexample :
    ∃x : Tree ℕ, ∀y : Tree ℕ, Tree.graft y x ≠ Tree.nil := by
    use (Tree.node 0 Tree.nil Tree.nil)
    intro y
    cases y
    · simp [graft]
    · simp [graft]


/- ## Question 2: Multisets and Finsets

Recall the following definitions from the lecture: -/

#check Finset.elems
#check List.elems

/- 2.1. Prove that the finite set of nodes does not change when mirroring a
tree. -/

theorem Finset.elems_mirror (t : Tree ℕ) :
    Finset.elems (mirror t) = Finset.elems t := by
    induction t with
    | nil => rfl
    | node a t1 t2 ih1 ih2 => simp [mirror, elems, ih1, ih2]; ac_rfl

/- 2.2. Show that this does not hold for the list of nodes by providing a
tree `t` for which `List.elems t ≠ List.elems (mirror t)`.

If you define a suitable counterexample, the proof below will succeed. -/

def rottenTree : Tree ℕ := Tree.node 0 (Tree.node 0 .nil .nil) (.node 1 .nil .nil)

#eval List.elems rottenTree
#eval List.elems (mirror rottenTree)

theorem List.elems_mirror_counterexample :
    ∃t : Tree ℕ, List.elems t ≠ List.elems (mirror t) :=
  by
    apply Exists.intro rottenTree
    simp [List.elems]

end LoVe
