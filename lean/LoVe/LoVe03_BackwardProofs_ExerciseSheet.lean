/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics such as `intro`,
`apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
    a → a :=
  by
    intro ha
    exact ha

theorem K (a b : Prop) :
    a → b → b := by
    intro ha hb
    exact hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c := by
    intro f hb ha
    apply f ha hb


theorem proj_fst (a : Prop) :
    a → a → a :=
    by
      intro ha1 ha2
      exact ha1

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  by
    intro ha1 ha2
    apply ha2

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by
    intro f ha hac hb
    apply hac ha

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by
    intro hab nb
    intro ha
    apply nb
    apply hab
    exact ha

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) := by
    apply Iff.intro
    {
      intro pq
      apply And.intro
      {
        intro x
        apply And.left (pq x)
      }
      {
        intro x
        apply And.right (pq x)
      }
    }
    {
      intro pq
      intro x
      apply And.intro (And.left pq x) (And.right pq x)
    }
/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [mul, ih, add]

#check add_succ

theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [mul, ih, add_succ, add_assoc, add]

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m := by
  induction n with
  | zero => simp [mul_zero, mul]
  | succ n ih => simp [mul_succ, mul, add_comm, ih]



/-
ih: (l*m)*n = l* (m * n)

(l*m)*(n+1) =zz l * (m * (n+1)) =def  l * (m + m*n) =mul_add  l * m + l * (m*n)


(l*m)*(n+1) =def (l*m) + (l*m)*n
            =ih  (l*m) + l*(m*n)
-/
theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) := by
  induction n with
  | zero => rfl
  |succ n ih => simp [mul, ih, mul_add]

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

/--
have: l * (m+n) = l*m + l*n

zz: (l+m) * n = l*m + l*n


-/

theorem add_mul (l m n : ℕ) :
    mul (add l m) n = add (mul n l) (mul n m) := by
  rw [mul_comm ]
  rw [mul_add]



/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/


/-
Es gelte (a->b) -> a. zz. a
Fall1. a, dann fertig
Fall2. ¬a, d.h. (a->False). Dann gilt (a->b), also a.
-/
theorem Peirce_of_EM :
    ExcludedMiddle → Peirce := by
  intro hem a b hab
  apply Or.elim (hem a)
  · intro ha
    exact ha
  · intro hna
    apply hab
    intro ha
    exact False.elim (hna ha)

/- 3.2 (**optional**). Prove the following implication using tactics. -/


/-
Peirce: ((a → b) → a) → a
Peirce für b:=False: ((a → False) → a) → a

Es gelte Peirce. ZZ. ¬¬a -> a
Dazu gelte ¬¬a (d.h. ¬a -> False) Zeige nun a.

Peirce sagt es reicht zu zeigen, dass ((a → False) → a).
Dazu gelte a->False bzw. ¬a. Dann habe False von ¬¬a, also folgt a, also fertig.

-/

theorem DN_of_Peirce :
    Peirce → DoubleNegation := by
  intro p a naa
  apply (p a False)
  intro a_na
  apply False.elim
  exact naa a_na

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

/-
Es gelte ¬¬a -> a
ZZ. a ∨ ¬a.
mit helper r.z.. ¬¬a ∨ ¬a
r.zz. ¬(¬a ∧ a), bzw. ((a->False) ∧ a) -> False mit not_and_or
wobei ¬(¬a ∧ a) quasi trivial.

-/

theorem helper {a}:
    DoubleNegation → ((¬¬a ∨ ¬a) → (a ∨ ¬a)) := by
  intro hdn h
  apply Or.elim h
  · intro hnna
    apply Or.intro_left
    apply hdn /-Why does hnna not work here as function argument for hdn?-/
    exact hnna
  · intro na
    apply Or.intro_right
    exact na

#check not_and_or

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle := by
  intro DN a
  apply helper DN
  apply Iff.mp not_and_or
  intro p
  apply And.left p (And.right p)
end SorryTheorems

end BackwardProofs

end LoVe
