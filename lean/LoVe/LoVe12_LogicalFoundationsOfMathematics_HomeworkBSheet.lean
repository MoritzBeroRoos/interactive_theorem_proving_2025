/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 12 (10 points + 2 bonus points):
# Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (10 points): Multisets as a Quotient Type

A multiset (or bag) is a collection of elements that allows for multiple
(but finitely many) occurrences of its elements. For example, the multiset
`{2, 7}` is equal to the multiset `{7, 2}` but different from `{2, 7, 7}`.

Finite multisets can be defined as a quotient over lists. We start with the
type `List α` of finite lists and consider only the number of occurrences of
elements in the lists, ignoring the order in which elements occur. Following
this scheme, `[2, 7, 7]`, `[7, 2, 7]`, and `[7, 7, 2]` would be three equally
valid representations of the multiset `{2, 7, 7}`.

The `List.count` function returns the number of occurrences of an element in a
list. Since it uses equality on elements of type `α`, it requires `α` to belong
to the `BEq` (Boolean equality) type class. For this reason, the definitions and
theorems below all take `[BEq α]` as type class argument.

1.1 (2 points). Provide the missing proof below. -/

instance Multiset.Setoid (α : Type) [BEq α] : Setoid (List α) :=
{ r     := fun as bs ↦ ∀x, List.count x as = List.count x bs
  iseqv :=
    { refl  := by aesop
      symm  := by aesop;
      trans := by aesop
    } }

/- 1.2 (1 point). Define the type of multisets as the quotient over the
relation `Multiset.Setoid`. -/

def Multiset (α : Type) [BEq α] : Type := Quotient (Multiset.Setoid α)


/- 1.3 (3 points). Now we have a type `Multiset α` but no operations on it.
Basic operations on multisets include the empty multiset (`∅`), the singleton
multiset (`{x} `for any element `x`), and the sum of two multisets (`A ⊎ B` for
any multisets `A` and `B`). The sum should be defined so that the multiplicities
of elements are added; thus, `{2} ⊎ {2, 2} = {2, 2, 2}`.

Fill in the `sorry` placeholders below to implement the basic multiset
operations. -/

def Multiset.equiv_iff {α : Type} [BEq α] {as bs : List α}:
  as ≈ bs ↔ ∀x, List.count x as = List.count x bs := by rfl

def Multiset.mk {α : Type} [BEq α] : List α → Multiset α :=
  Quotient.mk (Multiset.Setoid α)

def Multiset.empty {α : Type} [BEq α] : Multiset α := ⟦[]⟧

def Multiset.singleton {α : Type} [BEq α] (a : α) : Multiset α := ⟦[a]⟧

def Multiset.union {α : Type} [BEq α] : Multiset α → Multiset α → Multiset α :=
  Quotient.lift₂
  fun
  | l1, l2 => ⟦l1++l2⟧
  (by
  intro a1 b1 a2 b2 h1 h2
  apply Quotient.sound
  aesop (add norm Multiset.equiv_iff)
  )

/- 1.4 (4 points). Prove that `Multiset.union` is commutative and associative
and has `Multiset.empty` as identity element. -/

theorem Multiset.union_comm {α : Type} [BEq α] (A B : Multiset α) :
    Multiset.union A B = Multiset.union B A := by
    cases A using Quotient.ind
    cases B using Quotient.ind
    simp [union]
    apply Quotient.sound
    aesop (add norm Multiset.equiv_iff, unsafe add_comm)

theorem Multiset.union_assoc {α : Type} [BEq α] (A B C : Multiset α) :
    Multiset.union (Multiset.union A B) C =
    Multiset.union A (Multiset.union B C) := by
    cases A using Quotient.ind
    cases B using Quotient.ind
    cases C using Quotient.ind
    simp [union]

theorem Multiset.union_iden_left {α : Type} [BEq α] (A : Multiset α) :
    Multiset.union Multiset.empty A = A := by
    cases A using Quotient.ind
    simp [empty, union]

theorem Multiset.union_iden_right {α : Type} [BEq α] (A : Multiset α) :
    Multiset.union A Multiset.empty = A := by
    cases A using Quotient.ind
    simp [empty, union]


/- ## Question 2 (2 bonus points): Nonempty Types

In the lecture, we saw the inductive predicate `Nonempty` that states that a
type has at least one element: -/

#print Nonempty

/- The purpose of this question is to think about what would happen if all
types had at least one element. To investigate this, we introduce this fact as
an axiom as follows. Introducing axioms should be generally avoided or done
with great care, since they can easily lead to contradictions, as we will
see. -/

axiom Sort_Nonempty (α : Sort _) :
    Nonempty α

/- This axiom gives us a theorem `Sort_Nonempty` admitted with no proof. It
resembles a theorem proved by `sorry`, but without the warning. -/

#check Sort_Nonempty

/- 2.1 (1 bonus point). Prove that this axiom leads to a contradiction, i.e.,
lets us derive `False`. -/

theorem proof_of_False :
    False := by
    have a : Nonempty False := Sort_Nonempty False
    cases a
    assumption


/- 2.2 (1 bonus point). Prove that even the following weaker axiom leads to a
contradiction. Of course, you may not use the axiom or the theorem from 3.1.

Hint: Subtypes can help. -/

axiom Type_Nonempty (α : Type _) :
    Nonempty α

theorem another_proof_of_False :
    False := by
  have nonempty : Nonempty {a : Nat // False} := Type_Nonempty {a : Nat // False}
  cases nonempty with
  | intro val => exact val.property
  
end LoVe
