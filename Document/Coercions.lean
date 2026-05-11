/-
Coercions
%%%
tag := "sec-coercions"
%%%
-/
import Document.Type_classes
/-
When Lean's elaborator encounters an expression with unexpected type, it attempts to automatically insert a coercion, that is, a function from the unexpected type to the expected type. The search of a suitable function is based on instance synthesis.

As an illustration, consider our version of natural numbers `Nat'`.{margin}[We have imported our earlier definitions.]
-/
example (x y : Nat') : Nat' := x + y
/-

The following invalid example triggers the coercion mechanism, but instance synthesis fails to find a coercion.
```lean +error
example (x : Nat) (y : Nat') : Nat' := x + y
```

We can define a coercion from `Nat` to `Nat'` using `Coe` type class.
-/
def Nat'.ofNat (n : Nat) : Nat' :=
  match n with
  | 0 => Nat'.zero
  | n + 1 => (Nat'.ofNat n).succ

instance : Coe Nat Nat' where
  coe := Nat'.ofNat
/-

We can now add expressions of types `Nat` and `Nat'`.
-/
example (x : Nat) (y : Nat') : Nat' := x + y

example (x : Nat') (y : Nat) : Nat' := x + y
/-


# Subtypes

`Subtype` is a structure similar to `Prod`. It takes a predicate as a parameter and comes with syntactic sugar.
-/
#print Subtype

example (α : Sort u) (P : α → Prop) :
  Subtype P = {a : α // P a}
:= rfl
/-

An expression of a subtype is given by an expression of the parent type together with a proof of the defining predicate.
-/
example (α : Sort u) (P : α → Prop) (a : α) (h : P a) :
  {x : α // P x} := ⟨a, h⟩
/-

A concrete example is given by the even natural numbers.
-/
example : {n : ℕ // ∃ m, n = 2 * m} := ⟨4, by use 2⟩
/-

Subtypes come with coercion.
-/
example (x : ℕ) (y : {n : ℕ // ∃ m, n = 2 * m}) : ℕ :=
  x + y
/-


# Reducibility

Corercion works well for named subtypes if names are [reducible][reducible] in the sense that they unfolded automatically. [Abbreviations][abbrev] {index}[`abbrev`] are identical to definitions with `def`, except they are reducible.

[reducible]: https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#reducibility
[abbrev]: https://lean-lang.org/doc/reference/latest/Definitions/Definitions/#--tech-term-Abbreviations

-/
abbrev EvenNat := {n : ℕ // ∃ m, n = 2 * m}

example (x : ℕ) (y : EvenNat) : ℕ := x + y
/-

The `def` command generally creates semireducible names that are not unfolded by potentially expensive automation such as type class instance synthesis.
```lean +error
def EvenNat' := {n : ℕ // ∃ m, n = 2 * m}

example (x : ℕ) (y : EvenNat') : ℕ := x + y
```


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


# Algebraic substructures

A [subsemigroup][subsemigroup] is a structure with two fields: a subset of a semigroup called `carrier` and a proof that the multiplication is closed in the subset.{margin}[In fact, `Subsemigroup` can be used to define a submagma as well. The parent is not assumed to be associative.] This is a typical design pattern for algebraic substructures in Mathlib.

[subsemigroup]: https://en.wikipedia.org/wiki/Semigroup#Subsemigroups_and_ideals

-/
#print Subsemigroup
/-

Even natural numbers form a subsemigroup, hence a semigroup.
-/
def EvenNatSg : Subsemigroup ℕ where
  carrier := {n | ∃ m, n = 2 * m}
  mul_mem' := by
    rintro x y ⟨mx, rfl⟩ ⟨my, rfl⟩
    use 2 * mx * my
    grind

example : Semigroup EvenNatSg := by infer_instance
/-


# Coercing to sorts

Coercion works from `EvenNatSg` to `Nat`.
-/
example (x : ℕ) (y : EvenNatSg) : ℕ := x + y
/-

In fact, `EvenNatSg` itself can be coerced into a subtype.
-/
example : EvenNatSg = {n : ℕ // n ∈ EvenNatSg} := rfl
/-

The coercion from `EvenNatSg` to `Nat` works via this coercion to a subtype that we study next. Already `n ∈ EvenNatSg` deserves an explanation: `EvenNatSg` is not a set, but its type `Subsemigroup ℕ` carries a `SetLike` instance, which is what licenses the membership notation.
-/
example (G : Type u) [Semigroup G] :
  SetLike (Subsemigroup G) G := by infer_instance
/-

The type class `SetLike` has two fields: a function `coe` and a proof that the function is injective.
-/
#print SetLike

example (α : Type u) (β : Type v) [SetLike α β] (a : α) :
  Set β := SetLike.coe a
/-

In the case of `Subsemigroup` the function `coe` is given by the projection `carrier`.
-/
example (G : Type u) [Semigroup G] :
  SetLike (Subsemigroup G) G := Subsemigroup.instSetLike

open Function Subsemigroup in
lemma carrier_inj (G : Type u) [Semigroup G]
  : Injective (carrier : Subsemigroup G → Set G)
:= by
  rintro ⟨s₁, pf₁⟩ ⟨s₂, pf₂⟩ rfl
  rfl

open Subsemigroup in
example (G : Type u) [Semigroup G] :
  instSetLike = ⟨carrier, carrier_inj G⟩ := rfl
/-

`SetLike` expressions can be coerced to subsets.
-/
example (α : Type u) (β : Type v) [SetLike α β] (a : α) :
  Set β := a

example (α : Type u) (β : Type v) [SetLike α β] (a : α) :
  a = {x : β | x ∈ a} := rfl

example (G : Type u) [Semigroup G] (S : Subsemigroup G) :
  Set G := S

example (G : Type u) [Semigroup G] (S : Subsemigroup G) :
  S = {x : G | x ∈ S} := rfl
/-

The same `SetLike` expressions can be also coerced to subtypes, when context so requires.
-/
example (α : Type u) (β : Type v) [SetLike α β] (a : α) :
  a = {x : β // x ∈ a} := rfl

example (G : Type u) [Semigroup G] (S : Subsemigroup G) :
  S = {x : G // x ∈ S} := rfl
/-

Coercion to subtypes uses the general mechanism of coercion to sorts.
-/
example (α : Type u) (β : Type v) [SetLike α β] :
  CoeSort α (Type v) := by infer_instance
/-

The type class `CoeSort` has a single field called `coe`.
-/
#print CoeSort

example (α : Sort u) (β : Sort v) [CoeSort α β] (a : α) :
  β := CoeSort.coe a
/-

For `SetLike` the `CoeSort` instance is defined using the membership relation.
-/
example (α : Type u) (β : Type v) [SetLike α β] :
  CoeSort α (Type v) := SetLike.instCoeSortType

example (α : Type u) (β : Type v) [SetLike α β] :
  SetLike.instCoeSortType = ⟨λ a : α ↦ {x : β // x ∈ a}⟩
:= rfl
