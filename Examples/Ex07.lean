import Mathlib
/-

# Rewriting

The [rw tactic][rw] is based on properties of equality together with the [propext][propext] axiom.

[rw]: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-rw
[propext]: https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/#propext

Consider
-/
lemma rw_example1 (α β : Type) (a b : α) (f : α → β)
  (h : a = b)
  : f a = f b
:= by
  rw [h]

#print rw_example1
/-
Apart from `Eq.mpr`, we have seen the concepts appearing in the proof of `rw_example1`.

Write `@Eq.mpr` in terms of `Eq.rec`.
-/
set_option pp.proofs true in
set_option pp.notation false in
#print Eq.mpr

#check Eq.mpr

example (α β : Sort u)
  : @Eq.mpr α β = λ h b ↦ Eq.rec b (Eq.symm h)
:= rfl
/-

Lean provides three mathematical axioms postulating principles that cannot be established otherwise. For the moment, we restrict our attention to propositional extensionality
-/
#print propext

example : ∀ a b : Prop, (a ↔ b) → a = b := @propext
/-

Proposition extensionality is postulated since

* It is used in the proof function extensionality
* It is used to pass from constructive to classical logic
* It makes rewriting more convenient

Consider
-/
lemma rw_example2 (p q : Prop)
  (hp : p) (hqp : q ↔ p)
  : q
:= by
  rw [hqp]
  exact hp

#print rw_example2
/-
We see that the proof of `rw_example2` boils down to using `Eq.rec` and `propext`. Latter enables treating equivalence and equality in a unified manner.


# Simplification

The [simp tactic][simp] is similar to `rw` but more powerful.

[simp]: https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#simp-tactics

Consider
-/
lemma simp_example (α β : Type) (a b : α) (f : α → β)
  (h : a = b)
  : f a = f b
:= by
  simp [h]

#print simp_example
/-
Apart from `of_eq_true` and `eq_self`, we have seen the concepts appearing in the proof of `simp_example` (`congrFun'` is a non-dependent variant of `congrFun`).

Write `@of_eq_true` in terms of `Eq.rec`.
-/
-- __Solution__
set_option pp.notation false in
#print of_eq_true
#check of_eq_true

example (p : Prop)
  : @of_eq_true p = λ h ↦ Eq.rec trivial (Eq.symm h)
:= rfl
/-

Write `eq_self` in terms of `propext`.
-/
-- __Solution__
example (α : Sort u)
  : @eq_self α = λ a ↦ eq_true rfl := rfl

#print eq_true
#check eq_true

example (p : Prop)
  : @eq_true p
    = λ h ↦ propext {mp := λ _ ↦ trivial, mpr := λ _ ↦ h}
:= rfl

-- __Solution__ constructing equivalence separately
example (p : Prop)
  : @eq_true p
    =
    λ h ↦
      have : p ↔ True := ⟨λ _ ↦ trivial, λ _ ↦ h⟩
      propext this
:= rfl
/-

Lean keeps track of axioms used in proofs.
-/
#print axioms simp_example

#print axioms rw_example1
/-


# Congruence

Function extensionality can be formulated as an equivalence.
-/
example (α β : Type) (f g : α → β)
  : f = g ↔ ∀ x : α, f x = g x
:= by
  constructor
  · intro h x
    exact congrFun h x
  · intro h
    funext x
    exact h x
/-

Show the mixed congruence.
-/
example (α : Sort u) (β : Sort v) (a b : α) (f g : α → β)
  (h1 : f = g) (h2 : a = b)
  : f a = g b
:= by
  -- __Solution__
  calc
    f a
    _ = f b := by exact congrArg f h2
    _ = g b := by exact congrFun h1 b
/-


# Free generation of Prod and Sum

Injectivity of product.
-/
example (α β : Type) (a a' : α) (b b' : β)
  (h : (a, b) = (a', b'))
  : a = a' ∧ b = b'
:= by
  injection h with ha hb
  exact ⟨ha, hb⟩

example (α β : Type) (a a' : α) (b b' : β)
  (h : a ≠ a' ∨ b ≠ b')
  : (a, b) ≠ (a', b')
:= by
  by_contra
  injection this with ha hb
  obtain (_ | _) := h <;> contradiction
/-

Injectivity of `inl`.
-/
example (α β : Type) (a a' : α)
  (h : Sum.inl (β := β) a = Sum.inl a')
  : a = a'
:= by
  -- __Solution__
  injection h

example (α β : Type) (a a' : α)
  (h : a ≠ a')
  : Sum.inl (β := β) a ≠ Sum.inl a'
:= by
  -- __Solution__
  by_contra
  injection this
  contradiction
/-

Injectivity of `inr`.
-/
example (α β : Type) (b b' : β)
  (h : b ≠ b')
  : Sum.inr (α := α) b ≠ Sum.inr b'
:= by
  -- __Solution__
  grind
/-

Distinctness of `inl` and `inr`.
-/
example (α β : Type) (a : α) (b : β)
  : Sum.inl a ≠ Sum.inr b
:= by
  -- __Solution__
  nofun

-- __Solution__ by grind
example (α β : Type) (a : α) (b : β)
  : Sum.inl a ≠ Sum.inr b
:= by grind
/-


# Injectivity of morphisms in Prod and Sum categories

Show that a morphism in the symmetric monoidal category of products is injective if both its components are.
-/
open Function in
example (α β γ δ : Type) (f : α → γ) (g : β → δ)
  (hf : Injective f) (hg : Injective g)
  : Injective (λ p : α × β ↦ (f p.1, g p.2))
:= by
  intro ⟨a, b⟩ ⟨a', b'⟩ h
  injection h
  congr <;>
  (first | apply hf | apply hg) <;>
  assumption
/-

Show that a morphism in the symmetric monoidal category of coproducts is injective if both its components are.
-/
open Function in
example (α β γ δ : Type) (f : α → γ) (g : β → δ)
  (hf : Injective f) (hg : Injective g)
  : Injective (λ s : α ⊕ β ↦
      match s with
      | Sum.inl a => Sum.inl (f a)
      | Sum.inr b => Sum.inr (g b)
    )
:= by
  -- __Solution__
  intro x y h
  obtain a | b := x <;> obtain a' | b' := y <;>
  injection h <;>
  congr <;>
  (first | apply hf | apply hg) <;>
  assumption
