/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe Exercise 10: Hoare Logic

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Program Verification

1.1. The following WHILE program takes two numbers `a` and `b` and increments
`b` until it reaches `a`: -/

def COUNT_UP : Stmt :=
  Stmt.whileDo (fun s ↦ s "b" ≠ s "a")
    (Stmt.assign "b" (fun s ↦ s "b" + 1))

/- Prove the following Hoare triple. The main difficulty is to figure out which
invariant to use for the while loop. The invariant should capture both the work
that has been done already (the intermediate result) and the work that remains
to be done. Use a `show` command to annotate the program with a loop invariant.

Hint: If a variable `x` does not change in a program, it might be useful to
record this in the invariant, by adding a conjunct `s "x" = x₀`. -/

theorem COUNT_UP_correct (a₀ : ℕ) :
    {* fun s ↦ s "a" = a₀ *} (COUNT_UP) {* fun s ↦ s "a" = a₀ ∧ s "b" = a₀ *} :=
    show  {* fun s ↦ s "a" = a₀ *}
      (Stmt.invWhileDo (fun s ↦ s "a" = a₀) (fun s ↦ s "b" ≠ s "a")
        (Stmt.assign "b" (fun s ↦ s "b" + 1)))
      {* fun s ↦ s "a" = a₀ ∧ s "b" = a₀ *} from by
      vcg <;>
      aesop

/- 1.2. What happens if the program is run with `b > a`? How is this captured
by the Hoare triple? -/

-- enter your solution here
-- hoare triple doesnt tell us anything in case of nontermination

/- 1.3. The following WHILE program is intended to compute the Gaussian sum up
to `n`, leaving the result in `r`. -/

def GAUSS (N : ℕ) : Stmt :=
  Stmt.assign "r" (fun s ↦ 0);
  Stmt.assign "n" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ N)
    (Stmt.assign "n" (fun s ↦ s "n" + 1);
     Stmt.assign "r" (fun s ↦ s "r" + s "n"))

/- Here is a functional implementation of the same function: -/

def sumUpTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => n + 1 + sumUpTo n

/- Invoke `vcg` on `GAUSS` using a suitable loop invariant and prove the
emerging verification conditions. -/



theorem GAUSS_correct (N : ℕ) :
    {* fun s ↦ True *} (GAUSS N) {* fun s ↦ s "r" = sumUpTo N *} :=
    show {* fun s ↦ True *} (  Stmt.assign "r" (fun s ↦ 0);
  Stmt.assign "n" (fun s ↦ 0);
  Stmt.invWhileDo (fun s ↦ s "r" = sumUpTo (s "n")) (fun s ↦ s "n" ≠ N)
    (Stmt.assign "n" (fun s ↦ s "n" + 1);
     Stmt.assign "r" (fun s ↦ s "r" + s "n")))
     {* fun s ↦ s "r" = sumUpTo N *} from by
     vcg <;>
     aesop (add norm sumUpTo); ac_rfl

/- 1.4 (**optional**). The following program `MUL` is intended to compute the
product of `n` and `m`, leaving the result in `r`. Invoke `vcg` on `MUL` using a
suitable loop invariant and prove the emerging verification conditions. -/

def MUL : Stmt :=
  Stmt.assign "r" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "r" (fun s ↦ s "r" + s "m");
     Stmt.assign "n" (fun s ↦ s "n" - 1))





theorem bla (r m n : ℤ): r + m + (n * m - m) = r + n * m := by linarith

theorem MUL_correct (n₀ m₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *} (MUL) {* fun s ↦ s "r" = n₀ * m₀ *} :=
  show {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
    (  Stmt.assign "r" (fun s ↦ 0);
  Stmt.invWhileDo (fun s ↦ (s "m" = m₀ ∧ s "r" + s "n" * s "m" = n₀ * s "m")) (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "r" (fun s ↦ s "r" + s "m");
     Stmt.assign "n" (fun s ↦ s "n" - 1)))
    {* fun s ↦ s "r" = n₀ * m₀ *} from by
    vcg
    ·
      intro s a
      simp_all only [ne_eq, String.reduceEq, not_false_eq_true, update_apply_neq, update_apply, true_and]
      obtain ⟨left, right⟩ := a
      obtain ⟨left, right_1⟩ := left
      subst left
      --haev ( a b c: ℕ) (hc: c ≠ 0): a + b + (c-1) * b = a + c * ... := by cases c with
      generalize s "m" = m, s "n" = n at *
      simp [<-right_1]
      clear right_1
      suffices m + (n - 1) * m = n * m by omega
      cases n with
      | zero => simp at *
      | succ n =>
        suffices  (n) * m+ m = (n + 1) * m by rw [Nat.add_succ_sub_one]; linarith
        linarith

    · intro s a a_1
      simp_all only [ne_eq, Decidable.not_not, zero_mul, add_zero]
    · intro s a
      simp_all only [ne_eq, String.reduceEq, not_false_eq_true, update_apply_neq, update_apply, zero_add, and_self]








/- ## Question 2: Hoare Triples for Total Correctness

The following definition captures Hoare triples for total correctness for
deterministic languages: -/

def TotalHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s, P s → ∃t, (S, s) ⟹ t ∧ Q t

macro "[*" P:term " *] " "(" S:term ")" " [* " Q:term " *]" : term =>
  `(TotalHoare $P $S $Q)

namespace TotalHoare

/- 2.1. Prove the consequence rule. -/

theorem consequence {P P' Q Q' S}
      (hS : [* P *] (S) [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) :
    [* P' *] (S) [* Q' *] := by
    intro s hP's
    have hPs: P s := by apply hP s hP's
    have ex_t : ∃ t, (S, s) ⟹ t ∧ Q t := by aesop
    obtain ⟨t, ht⟩ := ex_t
    use t
    aesop


/- 2.2. Prove the rule for `skip`. -/

theorem skip_intro {P} :
    [* P *] (Stmt.skip) [* P *] :=
  by aesop (add norm TotalHoare)

/- 2.3. Prove the rule for `assign`. -/

theorem assign_intro {P x a} :
    [* fun s ↦ P (s[x ↦ a s]) *] (Stmt.assign x a) [* P *] := by
    aesop (add norm TotalHoare)

/- 2.4. Prove the rule for `seq`. -/

theorem seq_intro {P Q R S T} (hS : [* P *] (S) [* Q *])
      (hT : [* Q *] (T) [* R *]) :
    [* P *] (S; T) [* R *] := by
    aesop (add norm TotalHoare) (add safe destruct hS) (add safe destruct hT)


/- 2.5. Complete the proof of the rule for `if`–`then`–`else`.

Hint: The proof requires a case distinction on the truth value of `B s`. -/

theorem if_intro {B P Q S T}
      (hS : [* fun s ↦ P s ∧ B s *] (S) [* Q *])
      (hT : [* fun s ↦ P s ∧ ¬ B s *] (T) [* Q *]) :
    [* P *] (Stmt.ifThenElse B S T) [* Q *] := by
    intro s Ps
    cases (em (B s))
    <;> aesop (add norm TotalHoare, safe destruct hS, safe destruct hT)

/- 2.6 (**optional**). Try to prove the rule for `while`.

The rule is parameterized by a loop invariant `I` and by a variant `V` that
decreases with each iteration of the loop body.

Before we prove the desired theorem, we introduce an auxiliary theorem. Its
proof requires induction by pattern matching and recursion. When using
`var_while_intro_aux` as induction hypothesis we recommend to do it directly
after proving that the argument is less than `v₀`:

    have ih : ∃u, (Stmt.whileDo B S, t) ⟹ u ∧ I u ∧ ¬ B u :=
      have _ : V t < v₀ :=
        …
      var_while_intro_aux I V h_inv (V t) …

Similarly to `if`--`then`--`else`, the proof requires a case distinction on the
truth value of `B s`. -/

theorem var_while_intro_aux {B} (I : State → Prop) (V : State → ℕ) {S}
    (h_inv : ∀v₀,
       [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
    ∀v₀ s, V s = v₀ → I s → ∃t, (Stmt.whileDo B S, s) ⟹ t ∧ I t ∧ ¬ B t := by
  intro v₀ s V_eq hs
  cases (em (B s))
  · have : ∃ t, (S, s) ⟹ t ∧ I t ∧ V t < v₀ := by
      aesop
    obtain ⟨t, ht⟩ := this
    have : ∃ t_1, (Stmt.whileDo B S, t) ⟹ t_1 ∧ I t_1 ∧ ¬B t_1 := by aesop (add unsafe var_while_intro_aux)
    obtain ⟨t_1, ht_1⟩ := this
    use t_1
    aesop
  · use s
    aesop

theorem var_while_intro {B} (I : State → Prop) (V : State → ℕ) {S}
    (hinv : ∀v₀,
       [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
    [* I *] (Stmt.whileDo B S) [* fun s ↦ I s ∧ ¬ B s *] := by
    intro s hs
    have : _ := (var_while_intro_aux I V hinv (V s) s rfl hs)
    exact this

end TotalHoare

end LoVe
