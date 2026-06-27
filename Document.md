#doc (Manual) "Notes on Lean" =>

%%%
shortTitle := "Notes on Lean"
shortContextTitle := "Notes"
authors := ["Lauri Oksanen", "Niklas Halonen"]
authorshipNote := "lauri.oksanen@helsinki.fi"
%%%


# Introduction

We will consider [Lean][lean]'s type theory as a language for writing [formal proofs][formal-proof]. The part of Lean that enforces the rules of the type theory is called the kernel. The type theory is designed to be simple, enabling the kernel to remain small. From a foundational perspective, trusting Lean means trusting the correctness of this small kernel.

Expressed directly in kernel primitives, even simple proofs can be very verbose. The user-facing surface syntax is more implicit and compressed. Elaboration translates surface syntax into primitives, filling in the implicit pieces. Tactics are an especially powerful form of this compression, and it is typical to write proofs as tactic blocks. 

We begin by outlining the most important kernel primitives, namely the type and proposition universes, functions, and inductive types, as well as the kernel-level notion of definitional equality. We then take a brief look at tactics.

[lean]: https://lean-lang.org/
[formal-proof]: https://en.wikipedia.org/wiki/Formal_proof

{include 2 Document.Primitives}
{include 2 Document.Tactic_proofs}


# Foundations

Lean is highly expressive language while consisting of only a few kinds of expressions.{margin}[For the moment, we omit expressions related to {ref "sec-quotient-types"}[quotient types], and effectively consider a [sublanguage][sublanguage].] Every type is either a universe in the universe hierarchy, a function type, or arises from the type constructor of an inductive type. The remaining expressions can be organized along two axes: 

```
<!--HTML-->
<table class="custom-concepts-2d">
  <thead>
    <tr><th></th><th>introduction</th><th>elimination</th></tr>
  </thead>
  <tbody>
    <tr><th>function</th><td><code class="math inline">\lambda</code>-abstraction</td><td>evaluation</td></tr>
    <tr><th>inductive type</th><td>constructor</td><td>recursor</td></tr>
  </tbody>
</table>
```

We present the formation, introduction, elimination, and reduction rules for functions and inductive types. The notion of equality of functions and expressions of an inductive type is also discussed. 

[sublanguage]: https://en.wikipedia.org/wiki/Sublanguage

{include 2 Document.Functions}
{include 2 Document.Inductive_types}


# Constructions

We have now seen all the primitive notions in Lean's type theory. To reiterate, they are universes, function types, and inductive types,{margin}[We view formation of function and inductive types as primitive notions. This does not include concrete function types or inductive types.] together with introduction and elimination of expressions of the latter two types. In addition, we have considered the concrete inductive types `Eq` and `Nat`, as well as the [product][product-type] and [sum][sum-type] types `Prod` and `Sum`.

We begin with an encoding of first-order logic using inductive types. This involves product and sum types similar to `Prod` and `Sum`, a [dependent sum type][dep-sum-type], a [unit type][unit-type], and an [empty type][empty-type].{margin}[These types are called `And`, `Or`, `Exists`, `True`, and `False`.] The remainder of the chapter then takes a deeper look at `Eq` and `Nat`.

[product-type]: https://en.wikipedia.org/wiki/Product_type
[sum-type]: https://en.wikipedia.org/wiki/Sum_type
[dep-sum-type]: https://en.wikipedia.org/wiki/Dependent_type#%CE%A3_type
[unit-type]: https://en.wikipedia.org/wiki/Unit_type
[empty-type]: https://en.wikipedia.org/wiki/Empty_type

{include 2 Document.Logic}
{include 2 Document.Equality}
{include 2 Document.Peano}


# Relating types

This chapter collects three tools for working with types:

* _Type classes_ let shared structure across types be organized into hierarchies.

* _Quotient types_ encode equivalence classes by identifying expressions under an equivalence relation.

* _Coercions_ encode embeddings between types, and more generally, let expressions of one type be used implicitly where another is expected.

Type classes underpin the other two: quotient types are formed from instances of the `Setoid` type class, and coercions are implemented as type class instances at the elaboration stage. Type classes are inductive types with special elaboration-level features, so they require no new kernel-level primitives. Quotient types, by contrast, come with a number of primitives for their formation, the introduction and elimination of quotient expressions, and reasoning about them.

{include 2 Document.Type_classes}
{include 2 Document.Quotient_types}
{include 2 Document.Coercions}


# Axioms

Axioms are propositions postulated without proof. There are seven [standard][standard-axioms] axioms, three of which have mathematical content.{margin}[Three of the remaining axioms concern performance optimizations whose soundness rests on the compiler beyond the kernel. The final one is used by [sorry][sorry].] These three are the quotient axiom, propositional extensionality, and the [axiom of choice][axiom-of-choice]. The first two are similar in that they postulate equality assuming equivalence.

[standard-axioms]: https://lean-lang.org/doc/reference/4.28.0-rc1/Axioms/#standard-axioms
[sorry]: https://lean-lang.org/doc/reference/4.28.0-rc1/Tactic-Proofs/Tactic-Reference/#sorry
[axiom-of-choice]: https://en.wikipedia.org/wiki/Axiom_of_choice

{include 2 Document.Axioms_eq}
{include 2 Document.Axiom_choice}


# Index

{theIndex}
