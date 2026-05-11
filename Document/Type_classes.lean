/-
Type classes
%%%
tag := "sec-type-classes"
%%%
-/
import Mathlib
import Document.Peano
/-

Like structures, type classes are a feature of the elaboration stage. Both are implemented as inductive types with a single constructor together with projections for their fields. Expressions inhabiting a type class are called instances. The difference between type classes and structures shows up when they appear as the domain of a function: an instance of a type class can be supplied by a search procedure distinct from the unification used for ordinary implicit arguments.

One of the simplest type classes is `Add`.
-/
#print Add
/-
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

Returning to our version of natural numbers `Nat'`, we define an instance `Add' Nat'`.{margin}[We have imported our earlier definitions. In the next example, `Nat'` is a link that takes to its definition.] The syntax of instance declarations resembles record-style definitions, as the side-by-side examples below illustrate. {index}[`instance … where`]
-/
instance Nat'.instAdd' : Add' Nat' where
  add := Nat'.add

example : Add' Nat' := Nat'.instAdd'

def origin : Prod' ℕ ℕ where
  fst := 0
  snd := 0

example : Prod' ℕ ℕ := origin
/-

Giving a name is optional in instance declarations, and Lean's instance synthesis can search for an expression of a required type at the elaboration stage. Instance synthesis can be tested using `#synth` command. {index}[`#synth`]
-/
#synth Add' Nat'
/-


# Ad-hoc polymorphism

Type classes enable [ad-hoc polymorphism][ad-hoc-polymorphism], meaning that a function can have different implementations for different types. As an illustration, we consider doubling on `Add'`. {index}[`[…]`]

[ad-hoc-polymorphism]: https://en.wikipedia.org/wiki/Ad_hoc_polymorphism

-/
def Add'.double {α : Type u} [Add' α] (x : α) : α :=
  Add'.add x x
/-
Here `[Add' α]` denotes an instance argument of type `Add' α`. Like an implicit argument, it is supplied automatically, but via instance synthesis rather than unification. The polymorphism is due to the function `Add'.add` being provided by the instance. Because instance synthesis finds `Nat'.instAdd'`, `Add'.double` works immediately on `Nat'`.
-/
example (x : Nat') : Nat' := Add'.double x

example (x : Nat') : Add'.double x = x.add x := rfl
/-
The corresponding explicit versions read
-/
example (x : Nat') : Nat' :=
  @Add'.double Nat' Nat'.instAdd' x

example (x : Nat') :
  @Add'.double Nat' Nat'.instAdd' x = x.add x
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

Now `+` can be used on `Nat'`.
-/
example (x y : Nat') : Nat' := x + y

example (x y : Nat') : x + y = Nat'.add x y := rfl
/-
The `+` notation on `Nat'` is resolved via two instances, the above unnamed instance and `Nat'.instAdd'` from earlier.
-/
#synth HAdd Nat' Nat' Nat'
/-


# Numeric literals

The numeric literal parser is guided by `OfNat` type class.
-/
instance (n : Nat) : OfNat Nat' n where
  ofNat := Nat.rec Nat'.zero (λ _ hi ↦ hi.succ) n

example : Nat'.zero = 0 := rfl
example : Nat'.zero.succ = 1 := rfl
/-

We can now compute in `Nat'` using numeric literals with type annotation.
-/
#reduce (2 : Nat')

example : (2 : Nat') + (2 : Nat') = (4 : Nat') := rfl
/-


# Class hierarchy

Lean has parallel hierarchies for additive and multiplicative notation. We will consider the hierarchy rooted at `Add`. The mathematical concept corresponding to the root `Add` is [magma][magma]. A [semigroup][semigroup] is a magma whose binary operation is associative. {index}[extends]

[magma]: https://en.wikipedia.org/wiki/Magma_(algebra)
[semigroup]: https://en.wikipedia.org/wiki/Semigroup

-/
#print AddSemigroup

class AddSemigroup' (G : Type u) extends Add' G where
  add_assoc : ∀ a b c : G, (a + b) + c = a + (b + c)
/-
The `extends` clause makes `AddSemigroup'` inherit the fields from `Add'`, and `add_assoc` is stated in terms of the inherited `+`. If there is an expression of type `AddSemigroup' G` then there is an expression of type `Add' G`. The latter expression can be retrieved using `inferInstance`.
-/
#print inferInstance

example (G : Type u) [AddSemigroup' G] : Add' G
:= inferInstance
/-

Constructing an expression of type `AddSemigroup' Nat'` amounts to providing a proof that `Nat'.add` is associative.{margin}[Recall that we have already shown the associativity. In the example, `add_assoc` is a link that takes to its definition.]
-/
instance : AddSemigroup' Nat' where
  add_assoc := @Nat'.add_assoc
/-

Mathlib has a rich hierarchy of classes. [Mathematics in Lean][mathematics-in-lean] gives an introduction to this hierarchy.

[mathematics-in-lean]: https://leanprover-community.github.io/mathematics_in_lean

-/
