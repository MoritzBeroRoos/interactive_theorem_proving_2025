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
  | skip {s} : BigStep (Stmt.skip, s) s
  | assign {x a s} : BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq {S1 S2 s s' s''} (hS1: BigStep (S1, s) s') (hS23: BigStep (S2,s') s''):  BigStep (Stmt.seq S1 S2, s) s''
  | unlessDoTrue {S b s} (hb: b s) : BigStep (Stmt.unlessDo b S, s) s
  | unlessDoFalse {S b s s'} (nhb: ¬(b s)) (hS: BigStep (S, s) s'): BigStep (Stmt.unlessDo b S, s) s'
  | repeat0 {S s} : BigStep (Stmt.repeat 0 S, s) s
  | repeat_succ_n {S s s' s'' n} (h1: BigStep (S,s) s') (hn: BigStep (Stmt.repeat n S, s') s'') : BigStep (Stmt.repeat (n+1) S, s) s''
-- enter the missing cases here

infix:110 " ⟹ " => BigStep

/- 1.2 (2 points). Complete the following definition of a small-step
semantics: -/

inductive SmallStep : Stmt × State → Stmt × State → Prop
  | assign {x a s} : SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
  | seq {S1 S2 S1' s s'} (hS1: SmallStep (S1,s) (S1', s')): SmallStep (S1; S2, s) (S1'; S2, s')
  | seq_skip {S s} : SmallStep (Stmt.skip; S, s) (S,s)
  | unlessDoTrue {b S s} (hb: (b s)): SmallStep (Stmt.unlessDo b S, s) (Stmt.skip, s)
  | unlessDoFalse {b S s} (nhb: ¬(b s)) : SmallStep (Stmt.unlessDo b S, s) (S, s)
  | repeat0 {S s}:  SmallStep (Stmt.repeat 0 S, s) (Stmt.skip, s)
  | repeat_succ_n {n S s}: SmallStep (Stmt.repeat (n+1) S, s) (S;Stmt.repeat n S, s)
-- enter the missing cases here

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

def mess : Stmt → ℕ := fun
  | .skip => 0
  | .assign _ _ => 1
  | .seq S1 S2 => mess S1 + mess S2 + 1
  | .unlessDo _ S => mess S + 1
  | .repeat 0 _ => 1
  | .repeat (n+1) S => 2 + mess S + mess (Stmt.repeat n S) --+1 for the application of the repeat_succ rule, +1 for the sequence we build on top of the repeat-rest.

-- enter the missing cases here

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
    mess (Prod.fst Ss) > mess (Prod.fst Tt) := by
  induction h with
  | assign => simp [mess]
  | seq hS1 ih => simp [mess, ih]
  | seq_skip => simp [mess]
  | unlessDoTrue hb => simp [mess]
  | unlessDoFalse nhb => simp [mess]
  | repeat0 => simp [mess]
  | repeat_succ_n => simp [mess];linarith


/- ## Question 2 (3 points): Inversion Rules

2.1 (1 point). Prove the following inversion rule for the big-step semantics
of `unless`. -/

theorem BigStep_ite_iff {B S s t} :
    (Stmt.unlessDo B S, s) ⟹ t ↔ (B s ∧ s = t) ∨ (¬ B s ∧ (S, s) ⟹ t) := by
    cases em (B s)
    <;> aesop (add norm BigStep.unlessDoTrue, norm BigStep.unlessDoFalse, safe cases BigStep)

/- 2.2 (2 points). Prove the following inversion rule for the big-step
semantics of `repeat`. -/

theorem BigStep_repeat_iff {n S s u} :
    (Stmt.repeat n S, s) ⟹ u ↔
    (n = 0 ∧ u = s)
    ∨ (∃m t, n = m + 1 ∧ (S, s) ⟹ t ∧ (Stmt.repeat m S, t) ⟹ u) := by
    apply Iff.intro
    · intro repeatS
      cases repeatS
      <;> aesop
    · aesop (add safe BigStep.repeat0, safe BigStep.repeat_succ_n, unsafe cases BigStep)

end LoVe
