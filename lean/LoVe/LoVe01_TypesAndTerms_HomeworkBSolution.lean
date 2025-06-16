/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 1 (10 points): Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Terms

We start by declaring three new opaque types. -/

opaque α : Type
opaque β : Type
opaque γ : Type

/- 1.1 (4 points). Complete the following definitions, by replacing the `sorry`
placeholders by terms of the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.4 of the
Hitchhiker's Guide. As explained there, you can use `_` as a placeholder while
constructing a term. By hovering over `_`, you will see the current logical
context. -/

def B : (α → β) → (γ → α) → γ → β :=
  fun g f c ↦ g (f c)

def S : (α → β → γ) → (α → β) → α → γ :=
  fun g f a ↦ g a (f a)

def moreNonsense : (γ → (α → β) → α) → γ → β → α :=
  fun h c b ↦ h c (fun a ↦ b)

def evenMoreNonsense : (α → α → β) → (β → γ) → α → β → γ :=
  fun f g a b ↦ g (f a a)

/- 1.2 (2 points). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  fun f ↦ f (fun g ↦ g (fun a ↦ f (fun h ↦ a)))


/- ## Question 2 (4 points): Typing Derivation

Show the typing derivation for your definition of `S` above, using ASCII or
Unicode art. Start with an empty context. You might find the characters `–` (to
draw horizontal bars) and `⊢` useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

/- Let `C` := `g : α → β → γ, f : α → β, a : α`. We have

    –––––––––––––– Var  –––––––––– Var  –––––––––––––– Var  –––––––––– Var
    C ⊢ g : α → β       C ⊢ a : α       C ⊢ f : α → β       C ⊢ a : α
    –––––––––––––––––––––––––––––– App  –––––––––––––––––––––––––––––– App
    C ⊢ g a : β → γ                     C ⊢ f a : β
    –––––––––––––––––––––––––––––––––––––––––––––––– App
    C ⊢ g a (f a) : γ
    –––––––––––––––––––––––––––––––––––––––––––––––––––––– Fun
    g : α → β → γ, f : α → β ⊢ (fun a ↦ g a (f a)) : α → γ
    ––––––––––––––––––––––––––––––––––––––––––––––––––––––– Fun
    g : α → β → γ ⊢ (fun f a ↦ g a (f a)) : (α → β) → α → γ
    ––––––––––––––––––––––––––––––––––––––––––––––––––––––––– Fun
    ⊢ (fun g f a ↦ g a (f a)) ⊢ (α → β → γ) → (α → β) → α → γ -/

end LoVe
