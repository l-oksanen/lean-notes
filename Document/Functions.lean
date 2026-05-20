/-
Functions
%%%
tag := "sec-functions"
%%%
-/
--import Mathlib.Data.Nat.Init
import Mathlib
import Counterexamples.Girard
/-
-/
-- -show
namespace Document.Functions
/-
We consider a sublanguage which is a [pure type system][pure-type-system]. A pure type system is defined by its universes, the relations between the universes, and a number of rules. The rules govern

[pure-type-system]: https://en.wikipedia.org/wiki/Pure_type_system

* formation: how a type is created
* introduction: how expressions of a type are created
* elimination: how expressions of a type are transformed to expressions of another type
* reduction: how introduction and elimination interact

In the case of Lean, a further category is useful:

* equality: which expressions of a type are equal

These organizational categories are applied here to functions. We later apply them to inductive types and quotient types.

We call the formation rule for function types the {ref "sec-impredicative-lub-rule"}[impredicative maximum rule]. To understand the rule, we must first consider the universes and the relations between them. We introduce also proof irrelevance, since it lies behind an exceptional case of the rule.


# Preliminaries

If `a` has type `α`, we say that `a` inhabits `α` and that `α` is inhabited. Recall that `Prop` is the universe of propositions. Each expression inhabiting `Prop` is a type encoding a proposition, and proving a proposition amounts to giving an expression inhabiting the proposition. We call an expression inhabiting a proposition a proof.

Definitional equality includes proof irrelevance: any two proofs of the same proposition are equal.
-/
example (p : Prop) (pf₁ pf₂ : p) : pf₁ = pf₂ := rfl
/-


## Universes
%%%
tag := "sec-universes"
%%%


The universe of propositions `Prop` inhabits the type universe `Type`.
-/
example : Type := Prop
/-
`Type` itself inhabits a type.
-/
example : Type 1 := Type
/-
In fact, there is an infinite sequence of type universes,
-/
example : Type 2 := Type 1
example : Type 3 := Type 2
/-
and so on. `Type` is an abbreviation for `Type 0`.
-/
example : Type = Type 0 := rfl
/-

The infinite sequence `Prop, Type 0, Type 1, …` is syntactic sugar for the universe hierarchy `Sort 0, Sort 1, Sort 2, …`. Here `Sort u` is called a universe and `u` is its level. We can verify that the two sequences coincide using {lean}`rfl`.
-/
example : Prop = Sort 0 := rfl
example : Type u = Sort (u + 1) := rfl
/-


## Relations between universes

A pure type system comes with a relation on its universes specifying which universes inhabit each other. In the case of Lean this relation is fully described by
-/
example : Sort (u + 1) := Sort u
/-
Each universe inhabits the next one and no others.

More generally, each type `α` inhabits `Sort u` for exactly one `u`. We say that this `Sort u` is the universe of `α`.


# Formation

An elementary function type is formed as follows.
-/
example (α β : Type) : Type := α → β
/-
Here the types `α` and `β` specify the [domain][domain] and [codomain][codomain], respectively.

[domain]: https://en.wikipedia.org/wiki/Domain_of_a_function
[codomain]: https://en.wikipedia.org/wiki/Codomain

The function type
-/
example (α β γ : Type) : Type := α → β → γ
/-
is often viewed as encoding the type of functions taking two arguments, the first in `α` and the second in `β`, and yielding an expression in `γ`. For this reason, we occasionally refer to `γ` as the final codomain. Observe that the domain is `α` and the codomain is `β → γ`. The final codomain `γ` is the codomain of the codomain.
-/
example (α β γ : Type) : (α → β → γ) = (α → (β → γ)) := rfl
/-


## Universe polymorphism

{ref "sec-primitives"}[Recall] that {lean}`Prod` encodes the Cartesian product. It is a function taking two types as arguments.
-/
example : Type → Type → Type := Prod
/-
In fact, {lean}`Prod` is a more general [universe-polymorphic][univ-polymorphic] function.

[univ-polymorphic]: https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/#--tech-term-universe-polymorphism

-/
example : Type u → Type v → Type (max u v) := Prod
/-
We will {ref "sec-well-formedness"}[return] shortly to the maximum appearing in the final codomain. The difference between the above two examples is that in the first, `Prod` is instantiated with a fixed level of the universe hierarchy. It is a special case of the second.


## Implicit arguments

We have used extensively `rfl`. It is a function taking two implicit arguments.
-/
#check rfl
/-
Implicit arguments {index}[`{… : …}`] are written using curly braces `{…}`. They are translated into explicit arguments during elaboration.
-/
example : {α : Sort u} → {a : α} → a = a := rfl
/-

Inference of implicit arguments can be disabled using `@`. {index}[`@`]
-/
example : (α : Sort u) → (a : α) → a = a := @rfl

example (α : Sort u) (a : α) : a = a := @rfl α a
/-
Like {lean}`Prod`, {lean}`@rfl` is a function taking two arguments: first a type `α`, and then an expression `a` of that type. Its final codomain `a = a` depends on the arguments.


## Pi-types
%%%
tag := "sec-pi-types"
%%%

To simplify the notation, we define the following function taking two arguments, the first of which is implicit.
-/
def X {I : Sort u} (i : I) : Prop := i = i
/-
Consider the following partial application of {lean}`@rfl`.
-/
example (I : Sort u) : (i : I) → X i := @rfl I
/-
We refer to `(i : I) → X i` as a [$`\Pi`-type][pi-type] and `i : I` as the _index_ of the $`\Pi`-type.{margin}[$`\Pi`-types are also called dependent function types.]  Such a type can be thought of as encoding an [indexed product][indexed-product] of sets,
$$`
\prod_{i \in I} X_i
=
\left\{\left. f: I \to \bigcup_{i \in I} X_i\ \right|
\ f(i) \in X_i,\ i \in I \right\}.
`

[pi-type]: https://en.wikipedia.org/wiki/Dependent_type#%CE%A0_type
[indexed-product]: https://en.wikipedia.org/wiki/Cartesian_product#Infinite_Cartesian_products

All function types are $`\Pi`-types.
-/
example
  (α : Sort u) (β : Sort v) : (α → β) = ((a : α) → β)
:= rfl
/-
As the codomain `β` does not depend on the argument `a`, we can rewrite this function type leaving `a` as a hole. {index}[`_`]
-/
example
  (α : Sort u) (β : Sort v) : (α → β) = ((_ : α) → β)
:= rfl
/-


## Impredicative maximum rule
%%%
tag := "sec-impredicative-lub-rule"
%%%

The formation of a $`\Pi`-type type is governed by the following _impredicative maximum rule_.{margin}[This name is not used in the Lean Language Reference; the rule itself is described in [Predicativity][predicativity]. The [level expression][level-expression] `imax u v` is called the impredicative maximum (or least upper bound) of `u` and `v`. We have named the rule accordingly.]

[predicativity]: https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/#The-Lean-Language-Reference--The-Type-System--Universes--Predicativity
[level-expression]: https://lean-lang.org/doc/reference/latest/The-Type-System/Universes/?terms=imax#level-expressions

-/
def imax_rule (I : Sort u) (X : I → Sort v) :
  Sort (imax u v) := (i : I) → X i
/-
where
-/
example : Sort (imax _ 0) = Sort 0 := rfl

example : Sort (imax u (v + 1)) = Sort (max u (v + 1))
:= rfl
/-

Consider the implication.
-/
example (p : Prop) (q : Prop) : Prop := p → q
/-
The type `Prop` of `p → q` arises from the impredicative maximum rule. Indeed, since
-/
example (p : Prop) : Sort 0 := p
example (q : Prop) : Sort 0 := q
/-
the rule applies with `u = 0` and `v = 0`, yielding the type
-/
example : Sort (imax 0 0) = Prop := rfl
/-

Let us now consider universal quantification.
-/
example
  (α : Sort u) (P : α → Prop)
  : (∀ a : α, P a) = ((a : α) → P a)
:= rfl
/-
The type of predicates on `α` satisfies
-/
example (α : Sort u) : Sort (max u 1) := α → Prop
/-
Here `Sort (max u 1)` arises from impredicative maximum rule. Indeed, since
-/
example : Sort 1 := Prop
/-
the rule applies with `v = 1`, yielding `Sort (max u 1)`. The universal quantification, on the other hand, is a proposition.
-/
example (α : Sort u) (P : α → Prop) : Prop := (a : α) → P a
/-
Here `Prop` arises from the impredicative maximum rule. Indeed, since the evaluation `P a` of a predicate is a proposition,
-/
example (α : Sort u) (P : α → Prop) (a : α) : Sort 0 := P a
/-
the rule applies with `v = 0` yielding
-/
example : Prop = Sort (imax _ 0) := rfl
/-


## Girard's paradox
%%%
tag := "sec-girard"
%%%

The impredicative maximum rule relies on the infinite sequence of universes as seen by considering the function type with the same universe as domain and codomain.
-/
def pi : Type (w + 1) := Type w → Type w
/-
Having an infinite number of universes is not a feature introduced by choice, rather it is the price of consistency. [Certain historical][system-U] pure type systems that lack such stratification are inconsistent.

[system-U]: https://en.wikipedia.org/wiki/System_U

In Lean, violating the impredicative maximum rule would lead to Girard's paradox, formulated as follows.
-/
example
  (π : (Type w → Type w) → Type w)
  (Λ : {ξ : Type w → Type w} → ((i : Type w) → ξ i) → π ξ)
  (app : {ξ : Type w → Type w} → π ξ → (i : Type w) → ξ i)
  (β : ∀
    {ξ : Type w → Type w}
    (f : (i : Type w) → ξ i)
    (x : Type w),
    app (Λ f) x = f x
  )
  : 1 = 0
:= False.elim (Counterexample.girard π Λ app β)
/-
The paradox assumes a formation rule `π`, incompatible with the special case `pi` of the impredicative maximum rule. The codomain of `π` is one level below the universe of `pi`.

In the paradox, `Λ`, `app`, and `β` model $`\lambda`-abstraction, function application, and $`\beta`-reduction, respectively. These concepts are described below. The flawed formation rule `π`, together with `Λ`, `app`, and `β`, leads to the contradiction `1 = 0`.

The special case of `imax`
-/
example : Sort (imax _ 0) = Prop := rfl
/-
is related to proof irrelevance. Heuristically speaking, since proofs carry no information beyond the fact that a proposition holds, they do not enable the kind of self-referential constructions that lead to paradoxes.{margin}[Restricted elimination, considered {ref "sec-restricted-elimination"}[later], is also necessary for consistency. It is closely related to proof irrelevance.]


# Introduction

Functions are introduced by $`\lambda`-abstraction. For instance, the type `α → α` is inhabited for any type `α`.
-/
def I₁ {α : Sort u} : α → α := λ x ↦ x
/-
Here the $`\lambda`-abstraction `λ x ↦ x` gives the identity function. Here is a variant of the identity function taking an implicit argument.
-/
def I₁' {α : Sort u} : {_ : α} → α := λ {x} ↦ x
/-
Here are some syntactic variations. {index}[`·`]
-/
def I₂ {α : Sort u} (x : α) := x

def I₂' {α : Sort u} {x : α} := x

def I₃ {α : Sort u} := λ x : α ↦ x

variable {α : Sort u} in
def I₄ (x : α) := x

def I₅ {α : Sort u} : α → α := (·)
/-
Observe that the codomain is not specified explicitly in these examples. Lean can infer it based on the domain.

The functions `I₁`, `I₂`, and `I₃` coincide by `rfl`, but the following example is too ambiguous.
```lean +error
example {α : Sort u} : I₁ = I₂ := rfl
```
To prove the equality, we must provide more information or disable inference of implicit arguments.
-/
example {α : Sort u} : (I₁ : α → α) = I₂ := rfl

example : @I₁ = @I₂ := rfl
/-
Named arguments allow specifying implicit parameters explicitly. {index}[`(… := …)`]
-/
example {α : Sort u} : I₁ (α := α) = I₂ := rfl
/-
The implicit variant is even more ambiguous.
```lean +error
example {α : Sort u} : I₁' (α := α) = I₂' := rfl
```
Nonetheless, the functions `I₁'` and `I₂'` coincide.
-/
example : @I₁' = @I₂' := rfl
/-
Moreover,
-/
example : @I₁ = @I₁' := rfl
/-

The notation `id` is provided for the identity function.
-/
example {α : Sort u} : I₁ (α := α) = id := rfl
/-

The following function taking two arguments ignores the second one.{margin}[In the context of combinatory logic, this function is called the [combinator K][combinator-K].]

[combinator-K]: https://en.wikipedia.org/wiki/Combinatory_logic#Examples_of_combinators

-/
def K {α β: Type} : α → β → α := λ x _ ↦ x
/-


# Elimination

Functions are eliminated by application.
-/
example (α β : Type) (f : α → β) (a : α) : β := f a
/-
More generally,
-/
example (I : Sort u) (X : I → Sort v)
  (f : (i : I) → X i) (i : I) :
  X i := f i
/-

[Partial application][partial-application] produces a function taking the remaining arguments.

[partial-application]: https://en.wikipedia.org/wiki/Partial_application

-/
example (α β γ: Type) (f : α → β → γ) (a : α) : β → γ := f a
/-

In contrast, _saturated application_ produces an expression that is not a function.
-/
example (α β γ: Type) (f : α → β → γ) (a : α) (b : β) :
  γ := f a b
/-


## Local definitions

Consider the following function.
-/
def pq (x : ℕ) : ℕ :=
  (x + 1)^2 + 3*(x + 1) + 1
/-

We can avoid repeating the expression `x + 1` by composing two functions.
-/
def q (x : ℕ) : ℕ := x + 1
def p (y : ℕ) : ℕ := y^2 + 3*y + 1
def pq₁ (x : ℕ) := p (q x)
/-

This introduces two names `p` and `q`. Such auxiliary definitions can be avoided as follows. {index}[have]
-/
def pq₂ (x : ℕ) :=
  have y := x + 1
  y^2 + 3*y + 1
/-
Here `have` is syntactic sugar for $`\lambda`-abstraction and application.
-/
example (α : Sort u) (β : Sort v) (a : α) (b : β) :
  (
    have x : α := a
    b
  ) = (λ x : α ↦ b) a := rfl
/-
The parentheses around the `have` syntax can be omitted.
-/
example (α : Sort u) (β : Sort v) (a : α) (b : β) :
  have x : α := a
  b = (λ x : α ↦ b) a := rfl
/-

In particular, the following coincides with `pq₂`.
-/
def pq₃ (x : ℕ) :=
  (λ y ↦ y^2 + 3*y + 1) (x + 1)
/-


## Steps in proofs
%%%
tag := "sec-proof-steps"
%%%

A typical use of `have` is to isolate steps in proofs. Consider the universal instantiation followed by modus ponens.
-/
example (α : Sort u) (P Q : α → Prop)
  (h1 : ∀ a : α, P a → Q a) (h2 : ∀ a : α, P a)
  : ∀ a : α, Q a
:=
  λ a : α ↦
  have Pa := h2 a
  h1 a Pa
/-
We can read the first line of the example as introducing the symbols involved in the statement, which itself consists of the second and third lines. The statement is:

* Suppose `h1 : …` and `h2 : …`.
* Then `∀ a : α, Q a`.

The leading `:` on the third line reads as "Then" and `:=` on the fourth line as "Proof:".{margin}[It is due to this reading that we prefer the indentation in the example over the one in [Mathlib's style guidelines][style-guide]. When not proving a proposition, we adopt the usual indentation style.] The proof has the reading:

[style-guide]: https://leanprover-community.github.io/contribute/style.html#structuring-definitions-and-theorems

1. Let `a : α`.
2. We have `P a` by hypothesis `h2`, applied to `a`.
3. We conclude by hypothesis `h1`, applied to `a` and the fact `P a`.

Naming every intermediate step can become cumbersome. Omitting the name after `have` makes the step accessible as `this`.
-/
example (α : Sort u) (P Q : α → Prop)
  (h1 : ∀ a : α, P a → Q a) (h2 : ∀ a : α, P a)
  : ∀ a : α, Q a
:=
  λ a : α ↦
  have : P a := h2 a
  h1 a this
/-
A proof can also be referenced by its type using `‹…›` notation.{margin}[This introduces no ambiguity, since any two proofs of the same proposition are equal.] {index}[`‹…›`]
-/
example (α : Sort u) (P Q : α → Prop)
  (h1 : ∀ a : α, P a → Q a) (h2 : ∀ a : α, P a)
  : ∀ a : α, Q a
:=
  λ a : α ↦
  have : P a := h2 a
  h1 a ‹P a›
/-


## Syntactic abbreviation

A more general [abbreviation][local-def] is given by `let`. {index}[let]

[local-def]: https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html#local-definitions

-/
def pq₄ (x : ℕ) : ℕ :=
  let y := x + 1
  y^2 + 3*y + 1
/-

There are cases where `let` is applicable but `have` is not.
-/
def I₆ {α : Sort u} :=
  let t := α
  λ x : t ↦ x
/-


# Reduction

{ref "sec-definitional-equality-naive"}[Recall] that having the same normal form is a sufficient condition for two expressions to be definitionally equal. Computing normal forms involves several kinds of reduction, three of which are related to the concepts introduced in this section.


## beta-reduction

$`\beta`-reduction corresponds to applying a function to an argument by substitution.

-/
example (α : Sort u) (β : Sort v) (f : α → β) (a : α) :
  (λ x ↦ f x) a = f a
:= rfl

variable (α : Sort u) (β : Sort v) (f : α → β) (a : α) in
#reduce (λ x ↦ f x) a
/-


## delta-reduction

$`\delta`-reduction replaces a defined name by its defining expression.{margin}[Names are referred to as constants in the Lean Language Reference, see [Definitions][definitions].]

[definitions]: https://lean-lang.org/doc/reference/latest/Definitions/Definitions/#The-Lean-Language-Reference--Definitions--Definitions

-/
def ℕ2 := ℕ × ℕ

example : ℕ2 = (ℕ × ℕ) := rfl
/-

By default, `#reduce` does not reduce inside types.
-/
#reduce ℕ2
/-
We can force reduction inside types as follows.
-/
#reduce (types := true) ℕ2
/-


## zeta-reduction

$`\zeta`-reduction expands a `let`-abbreviation.

{index}[`;`]
-/
example : (let t := ℕ; t × t) = (ℕ × ℕ) := rfl

#reduce (types := true) (let t := ℕ; t × t)
/-
The semicolon is a syntactic device that allows multiple expressions to be written on a single line. Replacing it by a line break leaves the expression intact.


# Equality
%%%
tag := "sec-function-eta-equivalence"
%%%

In addition to reduction, definitional equality identifies certain expressions that differ only by trivial abstraction. This identification is called $`\eta`-equivalence. For functions, $`\eta`-equivalence says that a function is definitionally equal to the $`\lambda`-abstraction obtained by applying the function to an argument.
-/
example (α : Sort u) (β : Sort v) (f : α → β)
  : (λ x ↦ f x) = f
:= rfl
/-
The definitional equality of the left and right-hand sides is not based on them having the same normal form. In fact, the left-hand side does not reduce.
-/
variable (α : Sort u) (β : Sort v) (f : α → β) in
#reduce λ x ↦ f x
/-

Reduction and $`\eta`-equivalence differ in a fundamental way: the former has an [intensional][intensional-extensional] nature while the latter is a limited kind of extensionality.

[intensional-extensional]: https://en.wikipedia.org/wiki/Extensional_and_intensional_definitions

The principle of [functional extensionality][extensionality-principles] holds in Lean, but not by `rfl`.{margin}[We give a proof of `funext` {ref "sec-function-extensionality-proof"}[later].]
-/
example (α : Sort u) (β : Sort v) (f g : α → β)
  (h : ∀ (x : α), f x = g x)
  : f = g
:= funext h
/-
[extensionality-principles]: https://en.wikipedia.org/wiki/Extensionality#Extensionality_principles


# Rules of the type theory

The following rules govern the concepts introduced so far. They constitute a pure type system. For each rule, we first present an example and then its abstract formulation. In the abstract formulations, we write $`\operatorname{Sort}_{u}` for `Sort u`, $`\Pi x : \alpha.\; \beta` for `(x : α) → β x`, and $`\equiv` for definitional equality. Moreover, $`\Gamma` denotes an arbitrary [typing context][typing-context] and $`\beta[x := a]` denotes [substitution][substitution].{margin}[The substitution replaces all free occurrences of $`x` in the expression $`\beta` with the expression $`a`.] We use the [standard notation][typing-rule] for typing rules.

[substitution]: https://en.wikipedia.org/wiki/Lambda_calculus_definition#Substitution
[typing-context]: https://en.wikipedia.org/wiki/Typing_environment
[typing-rule]: https://en.wikipedia.org/wiki/Typing_rule

1. Axioms

-/
example : Sort (u + 1) := Sort u
/-
$$`
\frac{
}{
\vdash
\operatorname{Sort}_{u} : \operatorname{Sort}_{u + 1}
}
`

2. Start

-/
example (α : Sort u) (a : α) : α := a
/-
$$`
\frac{
\Gamma \vdash  \alpha : \operatorname{Sort}_{u}
}{
\Gamma, a : \alpha \vdash  a : \alpha
}
`

3. [Weakening][weakening]

[weakening]: https://en.wikipedia.org/wiki/Monotonicity_of_entailment

-/
example (α : Sort u) (a : α) (β : Sort v) (b : β) : α := a
/-
$$`
\frac{
\Gamma \vdash  a : \alpha
\quad
\Gamma \vdash  \beta : \operatorname{Sort}_v
}{
\Gamma, b : \beta \vdash  a : \alpha
}
`

4. Product{margin}[This is the {ref "sec-impredicative-lub-rule"}[impredicative maximum rule].]

-/
example (α : Sort u) (β : α → Sort v) :
  Sort (imax u v) := (x : α) → β x
/-
$$`
\frac{
\Gamma \vdash  \alpha : \operatorname{Sort}_{u}
\quad
\Gamma, x : \alpha \vdash  \beta : \operatorname{Sort}_{v}
}{
\Gamma \vdash  \Pi x : \alpha.\; \beta
: \operatorname{Sort}_{\operatorname{imax} u \; v}
}
`

5. Application

-/
example (α : Sort u) (β : α → Sort v)
  (f : (x : α) → β x) (a : α) :
  β a := f a
/-
$$`
\frac{
\Gamma \vdash  f : \Pi x : \alpha.\; \beta
\quad
\Gamma \vdash  a : \alpha
}{
\Gamma \vdash  f\; a : \beta[x := a]
}
`

6. Abstraction

-/
example (α : Sort u) (β : α → Sort v)
  (f : (a : α) → β a) :
  (a : α) → β a := λ x ↦ f x
/-
$$`
\frac{
\Gamma, x : \alpha \vdash  e : \beta
\quad
\Gamma \vdash  \Pi x : \alpha.\; \beta
: \operatorname{Sort}_{v}
}{
\Gamma \vdash
\lambda x : \alpha \mapsto e
: \Pi x : \alpha.\; \beta
}
`

7. Conversion

-/
example (α : Sort u) (a : α) :
  let β := α
  β := a
/-
$$`
\frac{
\Gamma \vdash  a : \alpha
\quad
\Gamma \vdash  \alpha\equiv\beta
}{
\Gamma \vdash  a : \beta
}
`


# Further proofs

-/
example : @I₁ = @I₂ := rfl
example : @I₁ = @I₃ := rfl
example : @I₁ = @I₄ := rfl
example : @I₁ = @I₅ := rfl
example : @I₁ = @I₆ := rfl

example : pq = pq₁ := rfl
example : pq = pq₂ := rfl
example : pq = pq₃ := rfl
example : pq = pq₄ := rfl
