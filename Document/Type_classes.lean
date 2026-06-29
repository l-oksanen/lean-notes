/-
Type classes
%%%
tag := "sec-type-classes"
%%%
-/
import Mathlib
import Document.Peano
/-

Like structures, type classes are a feature of the elaboration stage. Both are implemented as inductive types with a single constructor together with projections for their fields. Expressions inhabiting a type class are called instances. The difference between type classes and structures shows up when they appear as the domain of a function: an instance of a type class can be supplied by a search procedure distinct from the unification used for ordinary implicit arguments. This elaboration-time search procedure is called [instance synthesis][instance-synthesis].

[instance-synthesis]: https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Synthesis/

One of the simplest type classes is `Add`.
-/
#print Add
/-
The instance synthesis finds an expression of type `Add Nat`. {index}[`#synth`]
-/
#synth Add Nat

example : Add Nat := instAddNat
/-


# Preliminaries

The `def` command creates [semireducible][reducibility] names that are unfolded in certain cases, including definitional equality checks, but not during potentially expensive automation such as instance synthesis.

[reducibility]: https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/#reducibility

Consider the following definition reducing to `Nat'`.
-/
def N_semired := Nat'

#reduce (types := true) N_semired
/-
Instance synthesis does not unfold `N_semired` and therefore does not find the `Add' Nat'` instance.
```lean +error
#synth Add' N_semired
```

[Abbreviations][abbrev] {index}[`abbrev`] differ from definitions with `def` only in their reducibility. They create reducible names, which are unfolded even during potentially expensive automation.

[abbrev]: https://lean-lang.org/doc/reference/latest/Definitions/Definitions/#--tech-term-Abbreviations

Declared as an abbreviation, `N_reducible` unfolds to `Nat'` during instance synthesis, and the search succeeds.
-/
abbrev N_reducible := Nat

#synth Add N_reducible
/-


# Formation

We define our version of `Add`, {index}[`class … where`] and compare it to our own version of `Prod`.
-/
class Add' (α : Type u) where
  add : α → α → α

structure Prod' (α : Type u) (β : Type v) where
  fst : α
  snd : β
/-
The `class` declaration results in formation of an inductive type with a single constructor called `mk`, just like `structure` declaration.
-/
example (α : Type u) : Type u := Add' α

example :
  (α : Type u) /- parameter -/ →
  (α → α → α) /- field (add) -/ →
  Add' α /- codomain -/
:= @Add'.mk

example (α β : Type u) : Type u := Prod' α β

example :
  (α : Type u) /- parameter -/ →
  (β : Type v) /- parameter -/ →
  α /- field (fst) -/ →
  β /- field (snd) -/ →
  Prod' α β /- codomain -/
:= @Prod'.mk
/-


# Introduction

Returning to our version of natural numbers `Nat'`, we define an instance `Add' Nat'`.{margin}[We have imported our earlier definitions. In the next example, `Nat'` is a link to its definition.] The syntax of instance declarations resembles record-style definitions, as the side-by-side examples below illustrate. {index}[`instance … where`]
-/
instance Nat'.instAdd' : Add' Nat' where
  add := Nat'.add

example : Add' Nat' := Nat'.instAdd'

def origin : Prod' ℕ ℕ where
  fst := 0
  snd := 0

example : Prod' ℕ ℕ := origin
/-
Giving a name is optional in instance declarations.


# Ad-hoc polymorphism

Type classes enable [ad-hoc polymorphism][ad-hoc-polymorphism], meaning that a function can have different implementations for different types. As an illustration, we consider doubling on `Add'`. {index}[`[…]`]

[ad-hoc-polymorphism]: https://en.wikipedia.org/wiki/Ad_hoc_polymorphism

-/
def Add'.double {α : Type u} [Add' α] (x : α) : α :=
  Add'.add x x
/-
Here `[Add' α]` denotes an instance argument of type `Add' α`. Like an implicit argument, it is supplied automatically, but via instance synthesis rather than unification. The polymorphism is due to the function `Add'.add` being provided by the instance. Because instance synthesis finds `Nat'.instAdd'`, `Add'.double` works immediately on `Nat'`.
-/
abbrev N := Nat'

example (x : N) : N := Add'.double x

example (x : N) : Add'.double x = x.add x := rfl
/-
The corresponding explicit versions read
-/
example (x : N) : N :=
  @Add'.double N Nat'.instAdd' x

example (x : N) :
  @Add'.double N Nat'.instAdd' x = x.add x
:= rfl
/-


# Output parameters

By default, the parameters of a type class are treated as inputs to instance synthesis. In some cases, certain parameters should be viewed as determined by other parameters. Annotating parameters as output parameters causes them to be ignored in the sense that instance synthesis selects an instance matching the non-output parameters and uses it to determine the output parameters.

We consider the type class `HAdd` as an example. It encodes heterogeneous addition, where the two summands may have distinct types, and the codomain may differ from both. The codomain is annotated as an output parameter. While the annotation `outParam` affects the instance synthesis, from the point of view of the kernel it is simply the identity function.
-/
#print HAdd

#print outParam
/-

To see the effect of the annotation, we compare `HAdd` to its variant that omits the annotation.
-/
example (α β γ : Type) [HAdd α β γ] (a : α) (b : β) :
  HAdd.hAdd a b = HAdd.hAdd a b
:= rfl

class HAddNoOutParam (α β γ: Type) : Type where
  hAdd : α → β → γ

example (α β γ : Type) [HAddNoOutParam α β γ]
  (a : α) (b : β) :
  HAddNoOutParam.hAdd (γ := γ) a b = HAddNoOutParam.hAdd a b
:= rfl
/-
Contrary to `HAdd`, `HAddNoOutParam` requires the codomain to be supplied explicitly. Omitting it makes instance synthesis fail.
```lean +error
example (α β γ : Type) [HAddNoOutParam α β γ]
  (a : α) (b : β) :
  HAddNoOutParam.hAdd a b = HAddNoOutParam.hAdd a b
:= rfl
```


# Overloading

The type class `HAdd` is responsible for the `+` notation. We can [overload][overloading] `+` notation for `Add'`.

[overloading]: https://en.wikipedia.org/wiki/Operator_overloading
-/
instance (α : Type u) [Add' α] : HAdd α α α where
  hAdd := Add'.add
/-
Here we let Lean assign the instance an automatic name. The name can be seen using `#synth`.
-/
variable (α : Type u) [Add' α] in
#synth HAdd α α α
/-

Now `+` can be used on `N`.
-/
example (x y : N) : N := x + y

example (x y : N) : x + y = Nat'.add x y := rfl
/-
The `+` notation on `N` is resolved via two instances, the above unnamed instance and `Nat'.instAdd'` from earlier.
-/
#synth HAdd N N N
/-


# Numeric literals

The numeric literal parser is guided by `OfNat` type class.
-/
instance (n : Nat) : OfNat N n where
  ofNat := Nat.rec Nat'.zero (λ _ hi ↦ hi.succ) n

example : Nat'.zero = 0 := rfl
example : Nat'.zero.succ = 1 := rfl
/-

We can now compute in `N` using numeric literals with type annotation.
-/
#reduce (2 : N)

example : (2 : N) + (2 : N) = (4 : N) := rfl
/-


# Class hierarchy
%%%
tag := "sec-class-hierarchy"
%%%

Lean has parallel hierarchies for additive and multiplicative notation. We will consider the hierarchy rooted at `Add`. The mathematical concept corresponding to the root `Add` is [magma][magma]. A [semigroup][semigroup] is a magma whose binary operation is associative. {index}[extends]

[magma]: https://en.wikipedia.org/wiki/Magma_(algebra)
[semigroup]: https://en.wikipedia.org/wiki/Semigroup

-/
#print AddSemigroup

class AddSemigroup' (G : Type u) extends Add' G where
  add_assoc : ∀ a b c : G, (a + b) + c = a + (b + c)
/-
The `extends` clause makes `AddSemigroup'` inherit the fields from `Add'`, and `add_assoc` is stated in terms of the inherited `+`. If there is an expression of type `AddSemigroup' G` then there is an expression of type `Add' G`.

Such instances are retrieved using the function `inferInstance`, which simply returns its instance argument. To illustrate this, we define our own version. We want to return an instance argument `[i : α]` at an arbitrary type `α`, but declaring such an argument is rejected by default since the type `α` is not recognized as a type class. This check is disabled by setting the option `checkBinderAnnotations` to `false`, allowing us to define `inferInstance'` as the identity function.
-/
set_option checkBinderAnnotations false in
def inferInstance' {α : Sort u} [i : α] := i

example (G : Type u) [AddSemigroup' G] : Add' G
:= inferInstance'
/-

Constructing an expression of type `AddSemigroup' N` amounts to providing a proof that `Nat'.add` is associative.{margin}[Recall that we have already shown the associativity. In the example, `Nat'.add_assoc` is a link to its definition.]
-/
instance : AddSemigroup' N where
  add_assoc := @Nat'.add_assoc
/-

Mathlib has a rich hierarchy of classes. [Mathematics in Lean][mathematics-in-lean] gives an introduction to this hierarchy.

[mathematics-in-lean]: https://leanprover-community.github.io/mathematics_in_lean

-/
