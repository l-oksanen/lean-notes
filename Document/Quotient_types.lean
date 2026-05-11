/-
Quotient types
%%%
tag := "sec-quotient-types"
%%%
-/
import Mathlib.Data.Quot
import Document.Type_classes
/-

Quotient types encode [equivalence classes][equivalence-class]. As an example, we construct integers as the quotient set of $`\mathbb N^2` by the equivalence relation $`\sim`, where $`(n_1, k_1) \sim (n_2, k_2)` if and only if $`n_1 + k_2 = n_2 + k_1`.{margin}[Using integers, the relation can be rewritten as $`n_1 - k_1 = n_2 - k_2`.] Positive integers are then given by the equivalence classes $`[(n, 0)]`, $`n \in \mathbb N \setminus \{0\}`, and negative integers by $`[(0, k)]`, $`k \in \mathbb N \setminus \{0\}`.

[equivalence-class]: https://en.wikipedia.org/wiki/Equivalence_class

We will implement integers as the quotient type by the followin relation.{margin}[We have imported our earlier definitions.]
-/
def N2.r (p₁ p₂ : Nat' × Nat') : Prop :=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  n₁ + k₂ = n₂ + k₁
/-
We begin by showing that `r` is an equivalence relation.


# Equivalence relations

An [equivalence relation][equivalence-relation] is a binary relation that is reflexive, symmetric, and transitive. We show that `r` has these three properties. Reflexivity and symmetry are inherited from equality.

[equivalence-relation]: https://en.wikipedia.org/wiki/Equivalence_relation

-/
lemma N2.r_refl (p : Nat' × Nat') : r p p := rfl

lemma N2.r_symm {p q : Nat' × Nat'}
  (h : r p q)
  : r q p
:= h.symm
/-

Transitivity follows from properties of addition on `Nat'`. We isolate a step in the proof as a lemma that will be reused.
-/
lemma Nat'.add_right_comm {a b c : Nat'}
  : a + b + c = a + c + b
:=
  calc
    (a + b) + c
    _ = a + (b + c) := add_assoc
    _ = a + (c + b) := congrArg (a + ·) add_comm
    _ = (a + c) + b := add_assoc.symm

open Nat' in
lemma N2.r_trans {p₁ p₂ p₃ : Nat' × Nat'}
  (h1 : r p₁ p₂) (h2 : r p₂ p₃)
  : r p₁ p₃
:=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  let ⟨n₃, k₃⟩ := p₃
  have := calc
    (n₁ + k₃) + k₂
    _ = (n₁ + k₂) + k₃ := add_right_comm
    _ = (n₂ + k₁) + k₃ := congrArg (· + k₃) h1
    _ = (n₂ + k₃) + k₁ := add_right_comm
    _ = (n₃ + k₂) + k₁ := congrArg (· + k₁) h2
    _ = (n₃ + k₁) + k₂ := add_right_comm
  add_right_cancel this
/-


# Formation of quotient types

A quotient type is formed from a [setoid][setoid], a set equipped with an equivalence relation, encoded as the type class `Setoid`.

[setoid]: https://en.wikipedia.org/wiki/Setoid

-/
#print Setoid

instance N2.instSetoid : Setoid (Nat' × Nat') where
  r := r
  iseqv := ⟨r_refl, r_symm, r_trans⟩
/-

The equivalence relation bundled in `Setoid` comes with syntactic sugar.
-/
example (p q : Nat' × Nat') : (p ≈ q) = N2.r p q := rfl
/-

Like the formation of inductive types using `inductive`, the formation of a quotient type is a primitive feature implemented in the kernel. The primitive is called `Quot`. Like a recursor, it has a function type but is built into the kernel.
-/
#print Quot

example (α : Sort u) : (α → α → Prop) → Sort u := Quot
/-
`Quot` takes a relation as its argument. The variant `Quotient`, parameterized by a setoid, is preferred in practice.
-/
example (α : Sort u) : Setoid α → Sort u := Quotient

example (α : Sort u) (s : Setoid α) :
  Quotient s = Quot s.r
:= rfl
/-

Integers are encoded by
-/
def Z : Type := Quotient N2.instSetoid
/-


# Introduction of quotient expressions

Expressions of a quotient type are introduced using `Quot.mk`. Like `Quot`, it has a function type but is built into the kernel.
-/
#print Quot.mk

example (α : Sort u) :
  (r : α → α → Prop) → α → Quot r := Quot.mk
/-
The variant `Quotient.mk` is parameterized by a setoid.
-/
example (α : Sort u) :
  (s : Setoid α) → α → Quotient s := Quotient.mk

example (α : Sort u) (s : Setoid α) :
  Quotient.mk s = Quot.mk s.r
:= rfl
/-

The following syntactic sugar is provided.
-/
example (α : Sort u) (s : Setoid α) (a : α) :
  Quotient.mk s a = ⟦a⟧
:= rfl
/-

We introduce `0` as an integer.
-/
def Z.zero : Z := ⟦(0, 0)⟧
/-


# Equality of quotient expressions

The quotient axiom and its converse say that two equivalence classes `⟦x⟧` and `⟦y⟧` are equal if and only if `x` and `y` are related by the underlying equivalence.

## Quotient axiom

Axioms are propositions postulated without proof. `Quot.sound` is one of the small number of axioms postulated by the kernel.
-/
#print Quot.sound

example (α : Sort u) (r : α → α → Prop) (x y : α)
  (h : r x y)
  : Quot.mk r x = Quot.mk r y
:= Quot.sound h
/-
The variant `Quotient.sound` is parametrized by a setoid.
-/
example (α : Sort u) (s : Setoid α) (x y : α)
  (h : x ≈ y)
  : (⟦x⟧ : Quotient s) = ⟦y⟧
:= Quotient.sound h

example (α : Sort u) (s : Setoid α) (x y : α)
  (h : x ≈ y)
  : Quotient.sound h = Quot.sound h
:= rfl
/-

An integer `⟦(n, k)⟧` is zero if and only if `n = k`. We show now the _if_ direction. The _only if_ direction is shown later.
-/
open Nat' in
example (n k : Nat')
  (h : n = k)
  : ⟦(n, k)⟧ = Z.zero
:=
  have : (n, k) ≈ (0, 0) := calc
    n + 0
    _ = 0 + n := add_comm
    _ = n := zero_add
    _ = k := h
    _ = 0 + k := zero_add.symm
  Quotient.sound this
/-


## Quotient exactness

The implication opposite to `Quotient.sound` is called `Quotient.exact`. Contrary to `Quotient.sound`, it is a regular theorem, not an axiom.
-/
example  (α : Sort u) (s : Setoid α) (x y : α)
  (h : (⟦x⟧ : Quotient s) = ⟦y⟧)
  : x ≈ y
:= Quotient.exact h
/-

We are now ready to prove the _only if_ direction of the characterization of zero.
-/
open Nat' in
example (n k : Nat')
  (h : ⟦(n, k)⟧ = Z.zero)
  : n = k
:=
  have : n + 0 = 0 + k := Quotient.exact h
  calc
    n = 0 + n := zero_add.symm
    _ = n + 0 := add_comm
    _ = 0 + k := this
    _ = k := zero_add
/-

Positive integers were described {ref "sec-quotient-types"}[above] as equivalence classes `⟦(n, 0)⟧` with `n ≠ 0`. The example below justifies this by showing that the map `n ↦ ⟦(n, 0)⟧` is injective.
-/
open Nat' in
example (n m : Nat')
  (h : (⟦(n, 0)⟧ : Z) = ⟦(m, 0)⟧)
  : n = m
:=
  have : n + 0 = m + 0 := Quotient.exact h
  calc
    n = 0 + n := zero_add.symm
    _ = n + 0 := add_comm
    _ = m + 0 := this
    _ = 0 + m := add_comm
    _ = m := zero_add
/-


# Elimination of quotient expressions

The elimination principle for quotients is `Quot.lift`. If a function on the underlying type respects the equivalence relation, as stated in the compatibility condition `h` below, then `Quot.lift` turns it into a function on the quotient. Like the introduction principle, the elimination principle has a function type but is built into the kernel.
-/
#print Quot.lift

example (α : Sort u) (r : α → α → Prop) (β : Sort v)
  (f : α → β) (q : Quot r)
  (h : ∀ (x y : α), r x y → f x = f y) :
  β := Quot.lift f h q
/-
The variant `Quotient.lift` is parametrized by a setoid.
-/
example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → β) (ec : Quotient s)
  (h : ∀ (x y : α), x ≈ y → f x = f y) :
  β := Quotient.lift f h ec

example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → β)
  (h : ∀ (x y : α), x ≈ y → f x = f y)
  : Quotient.lift f h = Quot.lift f h
:= rfl
/-

In order to define negation on `Z`, we first define negation on `Nat' × Nat'` and show that it respects `N2.r`.
-/
def N2.neg (p : Nat' × Nat') :=
  let ⟨n, k⟩ := p
  (k, n)

open Nat' in
lemma N2.neg_resp_r {p q : Nat' × Nat'}
  (h : p ≈ q)
  : neg p ≈ neg q
:=
  let ⟨n, k⟩ := p
  let ⟨m, l⟩ := q
  calc
    k + m
    _ = m + k := add_comm
    _ = n + l := h.symm
    _ = l + n := add_comm
/-

The codomain of the lifted negation should be `Z`. For this reason, we need to turn `N2.neg` into a function from `Nat' × Nat'` to `Z` satisfying the below compatibility condition `h`.
-/
example (f : Nat' × Nat' → Z) (ec : Z)
  (h : ∀ (x y : Nat' × Nat'), x ≈ y → f x = f y) :
  Z := Quotient.lift f h ec
/-
A suitable function is obtained via introduction.
-/
example : Nat' × Nat' → Z := λ p ↦ ⟦N2.neg p⟧
/-
The compatibility condition follows from `N2.neg_resp_r` and `Quotient.sound`. We define negation on `Z` by
-/
def Z.neg := Quotient.lift
  (λ p ↦ ⟦N2.neg p⟧)
  (λ _ _ h ↦ Quotient.sound (N2.neg_resp_r h))
/-


# Quotient reduction

Analogously to {ref "sec-iota-reduction"}[$`\iota`-reduction] that governs the composition of elimination and introduction of expressions of an inductive type, quotient reduction causes `Quotient.lift` to reduce when composed with `Quotient.mk`.
-/
example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → β) (x : α)
  (h : ∀ (x y : α), x ≈ y → f x = f y)
  : Quotient.lift f h ⟦x⟧ = f x
:= rfl

variable (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → β) (x : α)
  (h : ∀ (x y : α), x ≈ y → f x = f y)
in
#reduce Quotient.lift f h ⟦x⟧
/-

Quotient reduction enables the following.
-/
open Z in
example : neg zero = zero := rfl

example (n k : Nat') :
  Z.neg ⟦(n, k)⟧ = ⟦(k, n)⟧
:= rfl

example (n k : Nat') :
  Z.neg (Z.neg ⟦(n, k)⟧) = ⟦(n, k)⟧
:= rfl
/-


# Induction principle for quotients

The induction principle for quotients follows the structure of recursors for inductive types: in order to prove that a predicate holds for all equivalence classes, it suffices to prove that it holds for each `⟦a⟧` with `a` inhabiting the underlying type. The induction principle is `Quot.ind`. Like the elimination principle `Quot.lift`, it has a function type but is built into the kernel.
-/
#print Quot.ind

example (α : Sort u) (r : α → α → Prop)
  (motive : Quot r → Prop) (q : Quot r)
  (h : (∀ (a : α), motive (Quot.mk r a)))
  : motive q
:= Quot.ind h q
/-
The variant `Quotient.ind` is parametrized by a setoid.
-/
#print Quotient.ind

example (α : Sort u) (s : Setoid α)
  (motive : Quotient s → Prop) (ec : Quotient s)
  (h : (∀ (a : α), motive ⟦a⟧))
  : motive ec
:= Quotient.ind h ec
/-

Elimination of double negation.
-/
example :
  ∀ x : Z, Z.neg (Z.neg x) = x
:= Quotient.ind (λ _ ↦ rfl)
/-
The following variant fails to compile if the motive is omitted.
-/
example (x : Z) :
  Z.neg (Z.neg x) = x
:=
  (Quotient.ind
    (motive := λ y ↦ Z.neg (Z.neg y) = y)
    (λ _ ↦ rfl)
  ) x
/-


# Binary operations

Binary operations like addition can be lifted using `Quotient.lift₂`, specialized here to the case where both arguments of the binary operation have the same type. This case is sufficient for our purposes.
-/
example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → α → β) (ec₁ ec₂ : Quotient s)
  (h : ∀ (x₁ y₁ x₂ y₂ : α),
    x₁ ≈ x₂ → y₁ ≈ y₂ → f x₁ y₁ = f x₂ y₂
  ) :
  β := Quotient.lift₂ f h ec₁ ec₂
/-

`Quotient.lift₂` is implemented using `Quotient.lift` twice. We define a partially-applied lift, called `F` below, then lift again. As `F` acts on equivalence classes, the proof of the compatibility condition associated with the second lift relies on the induction principle `Quotient.ind`.
-/
example (α : Sort u) (β : Sort v) (s : Setoid α)
  (f : α → α → β) (ec₁ ec₂ : Quotient s)
  (h : ∀ (x₁ y₁ x₂ y₂ : α),
    x₁ ≈ x₂ → y₁ ≈ y₂ → f x₁ y₁ = f x₂ y₂
  )
  : (Quotient.lift₂ f h) ec₁ ec₂
    =
    let F (x : α) (ec : Quotient s) :=
      have (y₁ y₂ : α) (hy : y₁ ≈ y₂) : f x y₁ = f x y₂
        := h x y₁ x y₂ (s.refl x) hy
      Quotient.lift (f x) this ec
    have (x₁ x₂ : α) (hx : x₁ ≈ x₂) : F x₁ ec₂ = F x₂ ec₂
      := Quotient.ind
        (motive := λ ec ↦ F x₁ ec = F x₂ ec)
        (λ y ↦ h x₁ y x₂ y hx (s.refl y))
        ec₂
    Quotient.lift (λ x ↦ F x ec₂) this ec₁
:= rfl
/-

We define addition on `Z` by defining addition on `Nat' × Nat'`, showing that it respects `N2.r`, and lifting it.
-/
def N2.add (p₁ p₂ : Nat' × Nat') :=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  (n₁ + n₂, k₁ + k₂)

open Nat' in
lemma N2.add_resp_r {p₁ q₁ p₂ q₂ : Nat' × Nat'}
  (hp : p₁ ≈ q₁) (hq : p₂ ≈ q₂)
  : add p₁ p₂ ≈ add q₁ q₂
:=
  let ⟨n₁, k₁⟩ := p₁
  let ⟨n₂, k₂⟩ := p₂
  let ⟨m₁, l₁⟩ := q₁
  let ⟨m₂, l₂⟩ := q₂
  have {a b c d : Nat'} := calc
    (a + b) + (c + d)
    _ = ((a + b) + c) + d := add_assoc.symm
    _ = ((a + c) + b) + d := congrArg (· + d) add_right_comm
    _ = (a + c) + (b + d) := add_assoc
  calc
    (n₁ + n₂) + (l₁ + l₂)
    _ = (n₁ + l₁) + (n₂ + l₂) := this
    _ = (m₁ + k₁) + (n₂ + l₂) := congrArg (· + (n₂ + l₂)) hp
    _ = (m₁ + k₁) + (m₂ + k₂) := congrArg ((m₁ + k₁) + ·) hq
    _ = (m₁ + m₂) + (k₁ + k₂) := this.symm

def Z.add := Quotient.lift₂
  (λ p q ↦ ⟦N2.add p q⟧)
  (λ _ _ _ _ hp hq ↦ Quotient.sound (N2.add_resp_r hp hq))
/-

We can now show that `1 - 1 = 0`.
-/
open Z in
example : add ⟦(1, 0)⟧ ⟦(0, 1)⟧ = zero := Quotient.sound rfl
/-

The standard integers `Int` are not defined as a quotient, but as an inductive type with separate constructors for non-negative and negative cases. Consequently, computing with them does not require the quotient axiom, as we have {ref "sec-definitional-equality-naive"}[seen].
-/
