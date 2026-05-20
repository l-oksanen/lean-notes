/-
First-order logic
%%%
tag := "sec-logic"
%%%
-/
import Mathlib.Data.Nat.Init
import Mathlib.Order.BooleanAlgebra.Defs
/-
Proving a proposition in Lean amounts to constructing an expression whose type is that proposition. This is a manifestation of the [Curry–Howard correspondence][Curry-Howard]. More explicitly, the correspondence can be summarized by the following encoding of concepts from [first-order logic][1st-order-logic]:

* well-formed [formula][formula]: an expression `p` of type {lean}`Prop`
* proof: an expression of type `p`
* formula is true: there is an expression of type `p`
* formula is false: there is no expression of type `p`
* truth `⊤`: an inductive type with a single constant constructor
* falsehood `⊥`: an inductive type with no constructors
* [implication][implication] `→`: function type
* [conjunction][conjunction] `∧`: like {lean}`Prod` but in the universe `Prop`
* [disjunction][disjunction] `∨`: like {lean}`Sum` but in the universe `Prop`
* [universal quantification][universal-quantification]: $`\Pi`-type
* [existential quantification][existential-quantification]: an inductive type with a predicate as a parameter

[Curry-Howard]: https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
[1st-order-logic]: https://en.wikipedia.org/wiki/First-order_logic
[formula]: https://en.wikipedia.org/wiki/Well-formed_formula
[implication]: https://en.wikipedia.org/wiki/Logical_implication
[conjunction]: https://en.wikipedia.org/wiki/Logical_conjunction
[disjunction]: https://en.wikipedia.org/wiki/Logical_disjunction
[universal-quantification]: https://en.wikipedia.org/wiki/Universal_quantification
[existential-quantification]: https://en.wikipedia.org/wiki/Existential_quantification


# Truth, falsehood and negation

Proposition {lean}`True` is defined as an inductive type with a single constructor that takes no arguments.
-/
#print True
/-
It can be defined as follows.
-/
inductive True' : Prop where
  | intro : True'
/-

The proposition `True'` can be proven by the constructor.{margin}[{ref "sec-anon-const-syntax"}[Recall] the anonymous constructor syntax.]
-/
example : True' := True'.intro
example : True' := ⟨⟩
/-

The following syntactic sugar is available for the standard version.
-/
example : ⊤ = True := rfl
example : trivial = True.intro := rfl
/-
allowing
-/
example : ⊤ := trivial
/-


Proposition {lean}`False` is defined as an inductive type without constructors.
-/
#print False

inductive False' : Prop
/-
As there are no constructors, there are no expressions of type `False'`. It becomes meaningful via negation.
-/
#print Not

def Not' (p : Prop) := p → False'
/-
It follows from the above two definitions that
-/
example : (Not' False') = (False' → False') := rfl
/-

The identity function maps from a type to itself.
-/
example (α : Sort u) : id = λ x : α ↦ x := rfl

example : Not' False' := id
/-

The following syntactic sugar is provided.
-/
example : ⊥ = False := rfl
example : (λ p ↦ ¬p) = Not := rfl
/-
allowing
-/
example : ¬False := id
/-


# Principle of explosion

Both `False` and `False'` are uninhabited, that is,
there are no expressions of either type. Uninhabited propositions encode contradictions. From a contradiction, any proposition can be derived by the [principle of explosion][explosion]. The recursor `False.rec` encodes the principle of explosion.

[explosion]: https://en.wikipedia.org/wiki/Principle_of_explosion

-/
#print False.rec

example : False → False' := False.rec
/-

The arguments of the recursor are implicit, and Lean infers them from the context. The type of {lean}`@False.rec` is
-/
example :
  (motive : False → Sort u) /- motive -/ →
  (h : False) /- major premise -/ →
  motive h /- codomain -/
:= @False.rec
/-
and an explicit version of the above proof reads
-/
example : False → False' := @False.rec λ _ ↦ False'
/-
Here `@False.rec` is evaluated partially, and the only argument `λ _ ↦ False'` is the motive. The proof works, since the partially applied function has the domain `False`, given by major premise, and since its codomain `motive h` is `False'`,
-/
example (h : False) :
  let motive := λ _ ↦ False'
  False' = motive h := rfl
/-

{ref "sec-pattern-matching"}[Recall] that pattern matching is implemented using recursors. The [nomatch expression][nomatch] is a pattern match with zero cases, and `nofun` is shorthand for a function that applies `nomatch` to its arguments. {index}[nomatch] {index}[nofun]

[nomatch]: https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/#The-Lean-Language-Reference--Terms--Pattern-Matching--Other-Pattern-Matching-Operators

-/
example : False → False' := λ h ↦ nomatch h
example : False → False' := nofun
/-

The principle of explosion applies starting from `False'` as well.
-/
example : False' → False := False'.rec
example : False' → False := nofun
/-


# Lemmas and theorems

We can give a name to a proven proposition in several ways.
{index}[lemma] {index}[theorem]
-/
def explosion : False → False' := nofun
def explosion₁ (h : False) : False' := nomatch h
lemma explosion₂ (h : False) : False' := nomatch h
theorem explosion₃ (h : False) : False' := nomatch h
/-
Despite the syntactic differences, all these define the same function. The following indentation suggest reading `h : False'` as a hypothesis and `False` as the conclusion.{margin}[{ref "sec-proof-steps"}[Recall] that `:` before the conclusion `False` can be read as "Then" and `:=` as "Proof:".]
-/
lemma explosion₄
  (h : False)
  : False'
:=
  nomatch h
/-

Lemmas can be used in subsequent proofs.
-/
example : Not' False := explosion
/-


# Propositional calculus

Compound propositions in [propositional calculus][propositional-calculus] are formed by using the logical connectives: conjunction, disjunction, implication, and negation. We know already how negation and implication are encoded. Conjunction and disjunction are inductive types.

[propositional-calculus]: https://en.wikipedia.org/wiki/Propositional_calculus

-/
#print And
#print Or

inductive And' (p q : Prop) : Prop where
  | intro (hl : p) (hr : q) : And' p q

inductive Or' (p q : Prop) : Prop where
  | inl (h : p) : Or' p q
  | inr (h : q) : Or' p q
/-

These definitions encode [conjunction][conjunction-intro] and [disjunction introductions][disjunction-intro].{margin}[We use again the anonymous constructor syntax.]

[disjunction-intro]: https://en.wikipedia.org/wiki/Disjunction_introduction
[conjunction-intro]: https://en.wikipedia.org/wiki/Conjunction_introduction

-/
variable (p q : Prop)

example (hl : p) (hr : q) : And' p q := ⟨hl, hr⟩

example (h : p) : Or' p q := Or'.inl h
example (h : q) : Or' p q := Or'.inr h
/-

The following syntactic sugar is available for the standard versions.
-/
example : (p ∧ q) = And p q := rfl
example : (p ∨ q) = Or p q := rfl
/-


## Conjunction elimination

Deconstruction via pattern matching enables proofs of statements involving compound hypotheses. We illustrate [conjunction elimination][conjunction-elim].

[conjunction-elim]: https://en.wikipedia.org/wiki/Conjunction_elimination

-/
example (h : And' p q) : p
:=
  match h with
  | And'.intro hp _ => hp
/-
This is just the projection function associated to the first field of `And'`.{margin}[{ref "sec-structures"}[Recall] that projection functions are generated for structures in this manner. While we could have defined `And'` as a structure, its definition as an inductive type illustrates the fact that structures are merely a convenience.] Here are two alternative proofs using the shorthand related to the {ref "sec-anon-const-syntax"}[anonymous constructor syntax].
-/
example (h : And' p q) : p
:=
  let ⟨hp, _⟩ := h
  hp

example (h : And' p q) : p
:=
  let ⟨_, _⟩ := h
  ‹p›
/-

Here is a proof that bypasses the user-facing surface syntax and employs the recursor `And'.rec` directly.
-/
example (p q : Prop) (h : And' p q) : p
:= And'.rec (λ hp _ ↦ hp) h
/-

-/
-- -show
compile_inductive% And'
/-
Let us write this proof more explicitly. The recursor of `And'` has the type
-/
example :
  (p q : Prop) /- parameters -/ →
  {motive : And' p q → Sort u} /- motive -/ →

  -- minor premises:
  ((hl : p) → (hr : q) → motive (And'.intro hl hr)) →

  (h : And' p q) /- major premise -/ →
  motive h /- codomain -/
:= @And'.rec
/-
The minor premise corresponds to the only constructor `intro`. The explicit proof
-/
example (p q : Prop) (h : And' p q) : p
:= @And'.rec
  p q /- parameters -/
  (λ _ ↦ p) /- motive -/
  (λ hp _ ↦ hp) /- minor premise -/
  h /- major premise -/
/-
works, since the codomain `motive h` is `p`,
-/
example (p q : Prop) (h : And' p q) :
  let motive := λ _ ↦ p
  p = motive h := rfl
/-
and since `λ hp _ ↦ hp` has the type `p → q → p` of the minor premise,
-/
example (p q : Prop) (h : And' p q) :
  let motive := λ _ ↦ p
  ((hl : p) → (hr : q) → motive (And'.intro hl hr)) :=
    λ hp _ ↦ hp

example (p q : Prop) (h : And' p q) :
  let motive := λ _ ↦ p
  ((hl : p) → (hr : q) → motive (And'.intro hl hr))
    = (p → q → p)
:= rfl
/-

The standard `And` is a structure with fields `left` and `right`.
-/
example (h : p ∧ q) : p := h.left
/-


## Commutativity of disjunction

Let us now turn to disjunction and consider its [commutativity][commutativity]. Deconstruction of a disjunctive hypothesis results in two cases. We give two formulations.

[commutativity]: https://en.wikipedia.org/wiki/Commutative_property#Truth_functional_connectives

-/
example (h : Or' p q) : Or' q p
:=
  match h with
  | Or'.inl hp => Or'.inr hp
  | Or'.inr hq => Or'.inl hq

example (h : Or' p q) : Or' q p
:=
  match h with
  | Or'.inl _ => Or'.inr ‹p›
  | Or'.inr _ => Or'.inl ‹q›

/-
This is a [proof by case analysis][proof-by-case-analysis]: `h` was either constructed with `inl` or with `inr`. In the former case, we construct a new `Or'` expression using `inr`, and in the latter case `inl` is used. In other words, we swap the roles of `inl` and `inr`.

[proof-by-case-analysis]: https://en.wikipedia.org/wiki/Proof_by_exhaustion

Here is a proof that uses the recursor `Or'.rec` directly.
-/
example (p q : Prop) (h : Or' p q) : Or' q p
:= Or'.rec
  (λ hp ↦ Or'.inr hp)
  (λ hq ↦ Or'.inl hq)
  h
/-

An explicit version reads
-/
example :
  (p q : Prop) /- parameters -/ →
  (motive : Or' p q → Prop) /- motive -/ →

  -- minor premises:
  ((h : p) → motive (Or'.inl h)) /- inl -/ →
  ((h : q) → motive (Or'.inr h)) /- inr -/ →

  (h : Or' p q) /- major premise -/ →
  motive h /- codomain -/
:= @Or'.rec


example (p q : Prop) (h : Or' p q) : Or' q p
:= @Or'.rec
  p q /- parameters -/
  (λ _ ↦ Or' q p) /- motive -/

  -- minor premises:
  (λ hp ↦ Or'.inr hp) /- inl -/
  (λ hq ↦ Or'.inl hq) /- inr -/

  h /- major premise -/
/-
The proof works since the codomain `motive h` is `Or' q p`,
-/
example (p q : Prop) (h : Or' p q) :
  let motive := λ _ ↦ Or' q p
  Or' q p = motive h := rfl
/-
and since `λ hp ↦ Or'.inr hp` and `λ hq ↦ Or'.inl hq` have the types of the minor premises associated to `inl` and `inr`, respectively. Indeed,
-/
example (p q : Prop) (h : Or' p q) :
  let motive := λ (_ : Or' p q) ↦ Or' q p
  ((h : p) → motive (Or'.inl h)) := λ hp ↦ Or'.inr hp

example (p q : Prop) (h : Or' p q) :
  let motive := λ (_ : Or' p q) ↦ Or' q p
  ((h : q) → motive (Or'.inr h)) := λ hq ↦ Or'.inl hq
/-
Here
-/
example (p q : Prop) (h : Or' p q) :
  let motive := λ (_ : Or' p q) ↦ Or' q p
  ((h : p) → motive (Or'.inl h)) = (p → Or' q p) := rfl

example (p q : Prop) (h : Or' p q) :
  let motive := λ (_ : Or' p q) ↦ Or' q p
  ((h : q) → motive (Or'.inr h)) = (q → Or' q p) := rfl
/-


# Restricted elimination
%%%
tag := "sec-restricted-elimination"
%%%

Inspecting the type of `Or.rec`, we see that `Or.rec` differs from all other recursors we have seen so far in that its motive's codomain is not an arbitrary universe `Sort u` but `Prop`. This is a manifestation of [restricted elimination][restricted-elimination]: propositions can be eliminated only into expressions of type `Prop` unless they have at most one constructor, whose arguments have type `Prop` or are shared with the type constructor.{margin}[For our immediate purposes, the only relevant shared arguments are parameters. The third argument of the type constructor of {lean}`Acc` illustrates the general case. This argument is shared with the only type constructor but it cannot be promoted to a parameter due to not satisfying the {ref "sec-params"}[uniformity requirement].]

[restricted-elimination]: https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/?terms=restricted%20elimination#propositions

Restricted elimination can be understood as the flipside of {ref "sec-impredicative-lub-rule"}[proof irrelevance]. Indeed, without such restriction, proof irrelevance would lead to inconsistency via
-/
example (p : Prop) (proof₁ proof₂ : p) (f : p → Sort u)
  : f proof₁ = f proof₂
:= rfl
/-

For instance, `True ∨ True` admits two proofs using distinct constructors
-/
def proof₁ : True ∨ True := Or.inl trivial
def proof₂ : True ∨ True := Or.inr trivial
/-
These proofs are definitionally equal. Consequently,
-/
example (f : True ∨ True → Sort u) : f proof₁ = f proof₂
:= rfl
/-
The following function violates restricted elimination.
```lean +error
def bad (h : True ∨ True) := match h with
  | Or.inl _ => 0
  | Or.inr _ => 1
```
If it were allowed, then taking `bad` as `f` in the above example would lead to `0 = 1`.


# Existential quantification

Existential quantification is encoded as an inductive type.
-/
#print Exists

inductive Exists' {α : Sort u} (P : α → Prop) : Prop where
  | intro (a : α) (h : P a) : Exists' P
/-

The definition is based on [existential generalization][existential-generalization]. We give two formulations.

[existential-generalization]: https://en.wikipedia.org/wiki/Existential_generalization

-/
example (α : Sort u) (P : α → Prop) (a : α)
  (h : P a) : Exists' P
:= Exists'.intro a h

example (α : Sort u) (P : α → Prop) (a : α)
  (h : P a) : Exists' P
:= ⟨a, h⟩
/-

Deconstruction enables [existential instantiation][existential-instantiation]. We give three formulations.

[existential-instantiation]: https://en.wikipedia.org/wiki/Existential_instantiation

-/
example (α : Sort u) (P : α → Prop)
  (h1 : Exists' P) (h2 : ∀ a : α, P a → q) : q
:=
  let ⟨a, h⟩ := h1
  h2 a h

example (α : Sort u) (P : α → Prop)
  (h1 : Exists' P) (h2 : ∀ a : α, P a → q) : q
:=
  match h1 with
  | Exists'.intro a h => h2 a h

example (α : Sort u) (P : α → Prop)
  (h1 : Exists' P) (h2 : ∀ a : α, P a → q) : q
:=
  Exists'.rec (λ a h ↦ h2 a h) h1
/-

Propositions of form `Exists' p` can be eliminated only into expressions of type `Prop`, as seen from the motive in
-/
#print Exists'.rec
/-
The field `a : α` of `Exists'.intro` does not have type `Prop` and is not shared with the type constructor.

Syntactic sugar is provided for the standard version.
-/
example (α : Sort u) (P : α → Prop) :
  (∃ a : α, P a) = Exists P := rfl
/-


# Further proofs and remarks

-/
example : explosion = explosion₁ := rfl
example : explosion = explosion₂ := rfl
example : explosion = explosion₃ := rfl
example : explosion = explosion₄ := rfl

example (h : And' p q) : q
:=
  match h with
  | ⟨_, hq⟩ => hq

example (h : p ∧ q) : q := h.right
