/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe Exercise 9: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Guarded Command Language

In 1976, E. W. Dijkstra introduced the guarded command language (GCL), a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert B     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert B` aborts if `B` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace GCL

inductive Stmt : Type
  | assign : String → (State → ℕ) → Stmt
  | assert : (State → Prop) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | choice : List Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. Complete the following big-step semantics, based on the informal
specification of GCL above. -/

inductive BigStep : (Stmt × State) → State → Prop
  -- enter the missing `assign` rule here
  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  | seq (C C' s s' s'') : BigStep (C, s) s' → BigStep (C', s') s'' → BigStep (C;C', s) s''
  | assign (x a s): BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  -- enter the missing `seq` rule here
  -- below, `Ss[i]'hless` returns element `i` of `Ss`, which exists thanks to
  -- condition `hless`
  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  | loop0 (S s): BigStep (Stmt.loop S, s) s
  | loop (S s t u): BigStep (S, s) t → BigStep (Stmt.loop S, t) u → BigStep (Stmt.loop S, s) u
  -- enter the missing `loop` rules here

infixl:110 " ⟹ " => BigStep

/- 1.2. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/

@[simp] theorem BigStep_assign_iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] := by
      apply Iff.intro
      · intro h
        cases h
        rfl
      · intro h
        simp [h, BigStep.assign]

@[simp] theorem BigStep_assert {B s t} :
    (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s := by
    apply Iff.intro
    · intro h
      cases h
      simp [hB]
    · intro h
      simp [BigStep.assert B s h.right, h.left]

@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
    (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) := by
    apply Iff.intro
    · intro h
      cases h
      use s'
    · intro h
      obtain ⟨u', hh⟩ := h
      aesop (add 100% BigStep.seq)



theorem BigStep_loop {S s u} :
    (Stmt.loop S, s) ⟹ u ↔
    (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) := by
      apply Iff.intro
      · intro h
        cases h
        · aesop
        · aesop
      · intro h
        cases h
        · aesop (add 100% BigStep.loop0)
        · cases h_1
          aesop (add 50% BigStep.loop)

/- This one is more difficult: -/

@[simp] theorem BigStep_choice {Ss s t} :
    (Stmt.choice Ss, s) ⟹ t ↔
    (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) := by
    apply Iff.intro
    · intro h
      cases h
      use i, hless
    · intro h
      cases h
      cases h_1
      aesop (add safe BigStep.choice)

end GCL

/- 1.3. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a => GCL.Stmt.assign x a
  | S; T => gcl_of S; gcl_of T
  | Stmt.ifThenElse B S T  => GCL.Stmt.choice [GCL.Stmt.assert B; gcl_of S, GCL.Stmt.assert (fun x ↦ ¬(B x)); gcl_of T ] -- choice [assert B; S, assert ¬B, T]
  | Stmt.whileDo B S => GCL.Stmt.loop (GCL.Stmt.choice [GCL.Stmt.assert B; gcl_of S, GCL.Stmt.assert (fun x ↦ ¬(B x))])
  --     loop (choice [(Assert B; S), Assert ¬B])

/- 1.4. In the definition of `gcl_of` above, `skip` is translated to
`assert (fun _ ↦ True)`. Looking at the big-step semantics of both constructs,
we can convince ourselves that it makes sense. Can you think of other correct
ways to define the `skip` case? -/

-- enter your answer here


/- ## Question 2: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ~ S₂`. -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- Program equivalence is an equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

theorem BigStepEquiv.refl {S} :
    S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
    S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
    S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. Prove the following program equivalences. -/
#check BigStepEquiv
theorem BigStepEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip := by
    simp [BigStepEquiv]

theorem BigStepEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S := by
  simp [BigStepEquiv]

theorem BigStepEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S := by
  simp [BigStepEquiv]

theorem BigStepEquiv.if_seq_while_skip {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S := by
  simp only [BigStepEquiv, BigStep_if_Iff, BigStep_seq_Iff, BigStep_skip_Iff]
  intro s t
  constructor
  · intro h
    cases h
    · aesop
    · aesop
  · intro h
    cases h
    · aesop
    · aesop

/- 2.2 (**optional**). Program equivalence can be used to replace subprograms
by other subprograms with the same semantics. Prove the following so-called
congruence rules that facilitate such replacement: -/

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
      (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ := by
      unfold BigStepEquiv
      intro s t
      apply Iff.intro
      · intro h
        cases h
        have : (S₂, s) ⟹ t_1 := (hS s t_1).mp hS_1
        have : (T₂, t_1) ⟹ t := (hT t_1 t).mp hT_1
        aesop
      · intro h
        cases h
        have : (S₁, s) ⟹ t_1 := (hS s t_1).mpr hS_1
        have : (T₁, t_1) ⟹ t := (hT t_1 t).mpr hT_1
        aesop


theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ := by
    unfold BigStepEquiv
    intro s t
    apply Iff.intro
    · intro h
      cases h
      · simp [hcond, hS]
        apply (hS s t).mp
        assumption
      · simp [hcond]
        apply (hT s t).mp
        assumption
    · intro h
      cases h
      · simp [hcond]
        --how to do this with aesop without instantiating everyhting?
        simp [(hS s t).mpr hbody]
      · simp [hcond, (hT s t).mpr hbody]
end LoVe
