/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 9 (10 points + 1 bonus point): Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (7 points + 1 bonus point): Semantics of the REPEAT Language

We introduce REPEAT, a programming language that resembles the WHILE language
but whose defining feature is a `repeat` loop.

The Lean definition of its abstract syntax tree follows: -/

inductive Stmt : Type
  | skip     : Stmt
  | assign   : String → (State → ℕ) → Stmt
  | seq      : Stmt → Stmt → Stmt
  | unlessDo : (State → Prop) → Stmt → Stmt
  | repeat   : ℕ → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- The `skip`, `assign`, and `S; T` statements have the same syntax and
semantics as in the WHILE language.

The `unless b do S` statement executes `S` unless `b` is true—i.e., it executes
`S` if `b` is false. Otherwise, `unless b do S` does nothing. This construct is
inspired by the Perl language.

The `repeat n S` statement executes `S` exactly `n` times. Thus, `repeat 5 S`
has the same effect as `S; S; S; S; S` (as far as the big-step semantics is
concerned), and `repeat 0 S` has the same effect as `skip`.

1.1 (2 points). Complete the following definition of a big-step semantics: -/

inductive BigStep : Stmt × State → State → Prop
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hs : BigStep (S, s) t) (ht : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | unless_false (B S s t) (hcond : ¬ B s) (hbody : BigStep (S, s) t) :
    BigStep (Stmt.unlessDo B S, s) t
  | unless_true (B S s) (hcond : B s) :
    BigStep (Stmt.unlessDo B S, s) s
  | repeat_zero (S s) : BigStep (Stmt.repeat 0 S, s) s
  | repeat_succ (n S s t u) (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.repeat n S, t) u) :
    BigStep (Stmt.repeat (n + 1) S, s) u

infix:110 " ⟹ " => BigStep

/- 1.2 (2 points). Complete the following definition of a small-step
semantics: -/

inductive SmallStep : Stmt × State → Stmt × State → Prop
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
  | seq_step (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seq_skip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | unless_false (B S s) (hcond : ¬ B s) :
    SmallStep (Stmt.unlessDo B S, s) (S, s)
  | unless_true (B S s) (hcond : B s) :
    SmallStep (Stmt.unlessDo B S, s) (Stmt.skip, s)
  | repeat_zero {S s} :
    SmallStep (Stmt.repeat 0 S, s) (Stmt.skip, s)
  | repeat_succ {n S s} :
    SmallStep (Stmt.repeat (n + 1) S, s) (S; Stmt.repeat n S, s)

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

/- 1.3 (3 points). We will now attempt to prove termination of the REPEAT
language. More precisely, we will show that there cannot be infinite chains of
the form

    `(S₀, s₀) ⇒ (S₁, s₁) ⇒ (S₂, s₂) ⇒ ⋯`

Towards this goal, you are asked to define a __measure__ function: a function
`mess` that takes a statement `S` and that returns a natural number indicating
how "big" the statement is. The measure should be defined so that it strictly
decreases with each small-step transition. -/

def mess : Stmt → ℕ
  | Stmt.skip         => 0
  | Stmt.assign _ _   => 1
  | S; T              => mess S + mess T + 1
  | Stmt.unlessDo _ S => mess S + 1
  | Stmt.repeat n S   => n * (mess S + 2) + 1

/- You can validate your answer as follows. Consider the following program
`S₀`: -/

def incr (x : String) : Stmt :=
  Stmt.assign x (fun s ↦ s x + 1)

def S₀ : Stmt :=
  Stmt.repeat 1 (incr "m"; incr "n")

/- Check that `mess` strictly decreases with each step of its small-step
evaluation: -/

def S₁ : Stmt :=
  (incr "m"; incr "n"); Stmt.repeat 0 (incr "m"; incr "n")

def S₂ : Stmt :=
  (Stmt.skip; incr "n"); Stmt.repeat 0 (incr "m"; incr "n")

def S₃ : Stmt :=
  incr "n"; Stmt.repeat 0 (incr "m"; incr "n")

def S₄ : Stmt :=
  Stmt.skip; Stmt.repeat 0 (incr "m"; incr "n")

def S₅ : Stmt :=
  Stmt.repeat 0 (incr "m"; incr "n")

def S₆ : Stmt :=
  Stmt.skip

#eval mess S₀   -- result: e.g., 6
#eval mess S₁   -- result: e.g., 5
#eval mess S₂   -- result: e.g., 4
#eval mess S₃   -- result: e.g., 3
#eval mess S₄   -- result: e.g., 2
#eval mess S₅   -- result: e.g., 1
#eval mess S₆   -- result: e.g., 0

/- 1.4 (1 bonus point). Prove that the measure decreases with each small-step
transition. If necessary, revise your answer to question 1.3. -/

theorem SmallStep_mess_decreases {Ss Tt : Stmt × State} (h : Ss ⇒ Tt) :
    mess (Prod.fst Ss) > mess (Prod.fst Tt) :=
  by
    induction h <;>
      simp [mess, mul_add, add_mul] at * <;>
      linarith


/- ## Question 2 (3 points): Inversion Rules

2.1 (1 point). Prove the following inversion rule for the big-step semantics
of `unless`. -/

theorem BigStep_ite_iff {B S s t} :
    (Stmt.unlessDo B S, s) ⟹ t ↔ (B s ∧ s = t) ∨ (¬ B s ∧ (S, s) ⟹ t) :=
  by
    apply Iff.intro
    { intro hu
      cases hu <;>
        aesop }
    { intro hor
      cases hor with
      | inl hand =>
        cases hand with
        | intro hB hst =>
          cases hst
          apply BigStep.unless_true
          assumption
      | inr hand =>
        apply BigStep.unless_false <;>
          aesop }

/- 2.2 (2 points). Prove the following inversion rule for the big-step
semantics of `repeat`. -/

theorem BigStep_repeat_iff {n S s u} :
    (Stmt.repeat n S, s) ⟹ u ↔
    (n = 0 ∧ u = s)
    ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (Stmt.repeat m S, t) ⟹ u) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | repeat_zero =>
        apply Or.intro_left
        apply And.intro <;>
          rfl
      | repeat_succ m S t' t u hS hr =>
        apply Or.intro_right
        apply Exists.intro m
        apply Exists.intro t
        aesop }
    { intro h
      cases h with
      | inl hand =>
        cases hand with
        | intro hn hu =>
          cases hn
          cases hu
          apply BigStep.repeat_zero
      | inr hex =>
        cases hex with
        | intro m hex' =>
          cases hex' with
          | intro t hand =>
            cases hand with
            | intro hn hand' =>
              cases hand' with
              | intro hS hr =>
                rw [hn]
                rw [← Nat.succ_eq_add_one]
                apply BigStep.repeat_succ <;>
                  assumption }

end LoVe
