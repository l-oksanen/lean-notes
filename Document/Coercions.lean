/-
Coercions and embeddings
%%%
tag := "sec-coercions"
%%%
-/
import Document.Type_classes
import Document.Quotient_types
/-
When Lean's elaborator encounters an expression with unexpected type, it attempts to automatically insert a coercion, that is, a function from the unexpected type to the expected type. The search of a suitable function is based on instance synthesis.

As an illustration, consider our versions of natural numbers `Nat'`, with the abbreviation `N`, and integers `Z`.{margin}[We have imported our earlier definitions.]

The following invalid example triggers the coercion mechanism, but instance synthesis fails to find a coercion. The same example becomes valid once a suitable coercion is in place.
```lean +error
example (x : Z) (y : N) : Z := x + y
```

A coercion from `N` to `Z` is defined using the type class `Coe`.
-/
#print Coe

instance : Coe N Z where
  coe := λ n ↦ ⟦(n, 0)⟧
/-

Let us now return to the example triggering the coercion.
-/
example (x : Z) (y : N) : Z := x + y
/-

As a more concrete example, we formulate `1 - 1 = 0` using coercion.
-/
example : (1 : N) + (⟦(0, 1)⟧ : Z) = (0 : N)
:= Quotient.sound rfl
/-

The instance of `Coe N Z` encodes the natural embedding of `N` into `Z`. In what follows, we describe two general techniques to encode embeddings: subtypes and substructures. Substructures build on subsets together with two type classes called `SetLike` and `CoeSort`.


# Subtypes

`Subtype` is a structure taking a predicate as a parameter.
-/
#print Subtype
/-

The following syntactic sugar is available.
-/
example (α : Sort u) (P : α → Prop) :
  Subtype P = {a : α // P a}
:= rfl
/-

An expression of a subtype is given by an expression of the parent type together with a proof of the defining predicate.
-/
example (α : Sort u) (P : α → Prop) (a : α) (h : P a) :
  {x : α // P x} := ⟨a, h⟩
/-

A concrete example is given by the even natural numbers.{margin}[We switch from our version of natural numbers `N` to the standard `ℕ` for the remaining examples. {ref "sec-class-hierarchy"}[Earlier] we did not place `N` in the type class hierarchy of Mathlib, rather we rebuild a small part of the hierarchy. Here we make use of a larger portion of the standard hierarchy.]
-/
abbrev EvenNat := {n : ℕ // ∃ m, n = 2 * m}

example : EvenNat := ⟨4, ⟨2, rfl⟩⟩
/-

Subtypes come with coercion.
-/
example (x : ℕ) (y : EvenNat) : ℕ := x + y
/-


## Equality of subtype expressions

Due to proof irrelevance, two expressions inhabiting a subtype are equal if the associated expressions inhabiting the parent type are equal.
-/
open Subtype in
example (α : Sort u) (P : α → Prop) (a₁ a₂ : α)
  (h₁ : P a₁) (h₂ : P a₂) (h : a₁ = a₂)
  : mk a₁ h₁ = mk a₂ h₂
:=
  Eq.subst
    (motive := λ v ↦ ∀ (h : P v), mk a₁ h₁ = mk v h)
    h
    (λ _ ↦ Eq.refl (mk a₁ h₁))
    h₂
/-

Similarly to {ref "sec-constructor-inj"}[constructor injectivity] theorems, Lean generates constructor equality theorems. The above example can be proven using such theorem for `Subtype.mk`.
-/
#print Subtype.mk.injEq

open Subtype in
example (α : Sort u) (P : α → Prop) (a₁ a₂ : α)
  (h₁ : P a₁) (h₂ : P a₂) (h : a₁ = a₂)
  : mk a₁ h₁ = mk a₂ h₂
:=
  (mk.injEq a₁ h₁ a₂ h₂).mpr h
/-

In a concrete case, equality can be proven simply by `rfl`.
-/
example : (⟨4, ⟨2, rfl⟩⟩ : EvenNat) = ⟨4, ⟨2, by grind⟩⟩
:= rfl
/-


# Subsets

Contrary to subtypes, subsets are implemented simply as predicates, though they come with syntactic sugar.
-/
example (α : Type u) : Set α = (α → Prop) := rfl

example (α : Type u) (P : α → Prop) : {a | P a} = P := rfl
/-

We can define the subtype of even natural numbers by using the set of even natural numbers.
-/
example :
  {n : ℕ // ∃ m, n = 2 * m} = Subtype {n | ∃ m, n = 2 * m}
:= rfl
/-

Although `Set α` is defined as `α → Prop`, Mathlib's position is that this is an implementation detail which should not be relied on.{margin}[All three examples above break this abstraction barrier.] Instead, `setOf` and `∈` should be used to convert between sets and predicates.
-/
example (α : Type u) (P : α → Prop) : {a | P a} = setOf P
:= rfl

example (α : Type u) (S : Set α) : S = setOf (λ a ↦ a ∈ S)
:= rfl

example (α : Type u) (P : α → Prop) (a : α) :
  (a ∈ {x | P x}) = P a
:= rfl

example : ({1, 2} : Set ℕ) = setOf (λ n ↦ n = 1 ∨ n = 2)
:= rfl
/-


# Substructures

Mathlib uses a uniform pattern for many substructures: subgroups, subsemigroups, submodules, and so on. Here we focus on [subsemigroups][subsemigroup]. `Subsemigroup` is a structure with two fields: a subset of a semigroup called `carrier` and a proof that the subset is closed under multiplication.{margin}[In fact, `Subsemigroup` can be used to define a submagma as well. The parent is not assumed to be associative.]

[subsemigroup]: https://en.wikipedia.org/wiki/Semigroup#Subsemigroups_and_ideals

-/
#print Subsemigroup
/-

Even natural numbers form a subsemigroup.{margin}[Contrary to the subtype `EvenNat`, the subsemigroup `evenNat` is not a type, as reflected by the lowercase name.]
-/
def evenNat : Subsemigroup ℕ where
  carrier := {n | ∃ m, n = 2 * m}
  mul_mem' :=
    λ {x y} hx hy ↦
    let ⟨mx, hmx⟩ := hx
    let ⟨my, hmy⟩ := hy
    have : x * y = 2 * (2 * mx * my) := by grind
    ⟨2 * mx * my, this⟩
/-


## Equality of subsemigroups

Due to proof irrelevance, two subsemigroups with the same carrier are equal. We give two proofs.
-/
def mul_mem {M : Type u} [Mul M] (s : Set M) :=
  ∀ {a b : M}, a ∈ s → b ∈ s → a * b ∈ s

open Subsemigroup in
example
  {M : Type u} [Mul M] {s₁ s₂ : Set M}
  (h₁ : mul_mem s₁) (h₂ : mul_mem s₂) (h : s₁ = s₂)
  : mk s₁ h₁ = mk s₂ h₂
:=
  (mk.injEq s₁ h₁ s₂ h₂).mpr h

open Subsemigroup in
lemma mk_pf_irrel
  {M : Type u} [Mul M] {s₁ s₂ : Set M}
  (h₁ : mul_mem s₁) (h₂ : mul_mem s₂) (h : s₁ = s₂)
  : mk s₁ h₁ = mk s₂ h₂
:=
  Eq.subst
    (motive := λ s ↦ ∀ (h : mul_mem s), mk s₁ h₁ = mk s h)
    h
    (λ _ ↦ Eq.refl (mk s₁ h₁))
    h₂
/-


# Coercing to subsets

A subsemigroup is identified with its carrier via coercion.
-/
example (G : Type u) [Semigroup G] (S : Subsemigroup G) :
  S = S.carrier := rfl

example : (evenNat : Set ℕ) = {n | ∃ m, n = 2 * m} := rfl
/-
Mathlib uses `SetLike` type class to implement such coercion pattern for many substructures. A `SetLike α β` instance says that expressions of type `α` can be viewed as subsets of type `β`. The type class has two fields: a function `coe` from `α` to subsets of `β` and a proof that this function is injective.
-/
#print SetLike

example (α : Type u) (β : Type v) [SetLike α β] :
  α → Set β := SetLike.coe
/-

`SetLike` expressions can be coerced into subsets using `coe`.
-/
example (α : Type u) (β : Type v) [SetLike α β] (a : α) :
  Set β := a

example (α : Type u) (β : Type v) [SetLike α β] (a : α) :
  a = SetLike.coe a := rfl
/-

In the case of `Subsemigroup`, the function `coe` is given by the projection `carrier`. The full `SetLike` instance bundles this projection with a proof of its injectivity.
-/
example (G : Type u) [Semigroup G] :
  SetLike (Subsemigroup G) G := Subsemigroup.instSetLike

open Function Subsemigroup in
lemma carrier_inj (G : Type u) [Semigroup G]
  : Injective (carrier : Subsemigroup G → Set G)
:=
  λ p₁ p₂ h ↦
  let ⟨s₁, h₁⟩ := p₁
  let ⟨s₂, h₂⟩ := p₂
  mk_pf_irrel h₁ h₂ h

open Subsemigroup in
example (G : Type u) [Semigroup G] :
  instSetLike = ⟨carrier, carrier_inj G⟩ := rfl
/-


# Coercing to sorts

In addition to subsets, `SetLike` expressions can be coerced into subtypes.
-/
example (α : Type u) (β : Type v) [SetLike α β] (a : α) :
  a = {x : β // x ∈ a} := rfl
/-

Coercion to subtypes uses the general mechanism of coercion to sorts.
-/
example (α : Type u) (β : Type v) [SetLike α β] :
  CoeSort α (Type v) := inferInstance
/-

The type class `CoeSort` has a single field called `coe`.
-/
#print CoeSort

example (α : Sort u) (γ : Sort w) [CoeSort α γ] :
  α → γ := CoeSort.coe
/-

For `SetLike`, the `CoeSort` instance is defined using the membership relation.
-/
example (α : Type u) (β : Type v) [SetLike α β] :
  CoeSort α (Type v) := SetLike.instCoeSortType

example (α : Type u) (β : Type v) [SetLike α β] :
  SetLike.instCoeSortType = ⟨λ a : α ↦ {x : β // x ∈ a}⟩
:= rfl
/-

While `evenNat` is not a type, it can be coerced into a subtype, and thus used in contexts where type is expected.
-/
example : Semigroup evenNat := inferInstance

example (x : ℕ) (y : evenNat) : ℕ := x + y
/-
In both examples `evenNat` is coerced into a subtype using the sort coercion from `SetLike`. The second example then applies a further coercion from the subtype to its parent type `ℕ`. The first example relies on a `Semigroup` instance that Mathlib provides for every subsemigroup.
-/
