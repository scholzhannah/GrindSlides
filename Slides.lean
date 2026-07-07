import VersoSlides

-- for the second example
import Mathlib.Data.Finset.Defs

-- for the third example
import Mathlib.Data.Finset.Card

-- for even example
import Mathlib.Algebra.Group.Int.Even

-- for a distribution example
import Mathlib.Analysis.Distribution.Support

-- for a category theory example
import Mathlib.CategoryTheory.Iso

-- cardinality, iso symbol
open Finset CategoryTheory Distribution

open VersoSlides

#doc (Slides) "A short introduction to `grind`" =>

# A short introduction to `grind`

# Basic usage

* recent tactic, announced: July 2025
* meant to automatically provide proofs for easy goals

# Intuition

* "virtual whiteboard"
* to start: hypotheses and negated conclusion on the whiteboard
* employs different engines to discover a proof
* engines write discovered facts on the whiteboard for other engines to use

# Goals of presentation

* basic understanding of the workings of `grind`
* focus on usage and user interface
* read the [Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/) for more detail

# Error messages

%%%
vertical := some true
%%%
```lean +error
theorem exists_subset_or_subset_of_two_mul_lt_card
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind
```

## Error messages

```lean +error
example (n k : ℕ) (h1 : 2 * n = k) : k = 5 := by
  grind
```

# Basic derivations of new facts

%%%
vertical := some true
%%%

"basic": no specialized solvers or lemmas

## Congruence Closure

For a function `f` and `a₁ = bₙ`, ..., `aₙ = bₙ` in the context, `grind` equates `f a₁ ... aₙ` and `f b₁ ... bₙ`.

## Constraint Propagation

Deriving basic logical consequences of propositions in {lean}`True` and {lean}`False` classes, e.g.

* Boolean Connectives (e.g. `A ∧ B = ⊤` implies `A = ⊤` and `B = ⊤`)
* Inductive Types (e.g. if `some a = some b` then `a = b`)
* Projections (e.g. if `(a₁, a₂) = (b₁, b₂)` then `a₁ = a₂`)

## Case splits

Splitting for example on `if`-expressions and `match`-statements.

* splits can make `grind` slow
* use option `trace.grind.split` to inspect splits
* disable certain types of splits: `grind -splitIfs`, `grind -splitMatch`
* limit (or increase) case depth: `grind (splits := n)` (default: 9)

# E-matching

%%%
vertical := some true
%%%

* use of tagged lemmas in `grind`
* basic tag: `@[grind *]` where `*` is a modifier

## Basic functionality

* index of lemmas and corresponding patterns
* when pattern matches terms in context, tries to apply ("instantiate") the corresponding theorem
* very powerful with thorough tagging
* very slow with too general tagging

## Indexable expressions

* indexable: expression that starts with a constant other than {lean}`Eq`, {lean}`HEq`, {lean}`Iff`, {lean}`And`, {lean}`Or` and {lean}`Not`
* For example: `t = s` (where `s` and `t` are some terms) cannot be used as a pattern

## Multi-patterns

Theorems can have multi-patterns:
multiple patterns need to match before the theorem is tried.

```lean -panel
theorem card_ne_zero_of_mem {α : Type*} {s : Finset α}
    {a : α} (h : a ∈ s) : #s ≠ 0 :=
  (not_congr card_eq_zero).2 <| ne_empty_of_mem h
```

* `#s ≠ 0`, `#s = 0`: not indexable, cannot be used as patterns
* `#s` and `a ∈ s` individually are too general
* Mathlib uses `#s` and `a ∈ s` as a multi-pattern

## Default Patterns

* modifiers to `grind` pick patterns according to a specific algorithm
* `grind?` shows which pattern is picked
* arguments are indexed with numbers starting with 0 for the first argument
* some modifiers require all arguments to be fixed ("covered") by the resulting pattern

## `=`: left side of equality

* for equalities: use left side as a pattern
* fails if left side doesn't cover all arguments

```lean -stretch
@[grind? =]
lemma even_iff {n : ℤ} : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩
```

## `=_`: right side of equality

* for equalities: use right side as a pattern
* fails if right side doesn't cover all arguments

```lean -stretch
@[grind? =_]
theorem toList_toArray {α : Type*} {n : ℕ}
    {xs : Vector α n} : xs.toArray.toList = xs.toList :=
  rfl
```

##  `_=_`: both sides of equality as two patterns

* two patterns corresponding to `=` and `=_`
* theorem is used if the left or the right side matches

```lean -stretch
@[simp, grind? _=_]
theorem trans_symm {C : Type*} [Category C] {X Y Z : C}
    (α : X ≅ Y) (β : Y ≅ Z) :
    (α ≪≫ β).symm = β.symm ≪≫ α.symm :=
  rfl
```

## `→`: starting with hypotheses

* add hypotheses to multi-pattern until all arguments are covered
* start with first hypothesis

```lean -stretch
@[aesop safe forward, grind? →]
lemma EqOn.eq_of_mem {α β : Type*} {s : Set α}
    {f₁ f₂ : α → β} {a : α} (h : s.EqOn f₁ f₂)
    (ha : a ∈ s) : f₁ a = f₂ a :=
  h ha
```

## `.`: starting with conclusion

* add conclusion or hypotheses to multi-pattern until all arguments are covered
* start with conclusion and then first hypothesis

```lean -stretch
@[grind? .]
theorem isClosed_dsupport {α β F V : Type*} [FunLike F α β]
    [TopologicalSpace α] [Zero β] [Zero V] {f : F → V} :
    IsClosed (dsupport f) := by
  grind [dsupport, isClosed_sInter]
```
## Further modifiers

* more algorithms for the order of picking patterns, e.g. `←`, `⇒` and `⇐`
* modifiers for specific types of theorems: e.g. `inj`, `ext`
* read the Language Reference!

## `grind!`

* minimally indexable: subexpression that has no indexable subexpression (up to some priorities)
* `grind!` only picks minimal indexable subexpressions as patterns

## `grind!` Example

```lean +error -stretch
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind? .]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]

example {a b c : ℕ} (h₁ : f b = a) (h₂ : f c = a) :
    b = c := by
  grind
```

## `grind!` Example

```lean -stretch
@[grind!? .]
theorem gf' (x : Nat) : g (f x) = x := by
  simp [f, g]

example {a b c : ℕ} (h₁ : f b = a) (h₂ : f c = a) :
    b = c := by
  grind
```



# Welcome

This is a presentation built with
[`verso-slides`](https://github.com/leanprover/verso-slides).

# Lean Code

Here is a Lean code block:

```lean
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n
```

The function {lean}`fib` computes Fibonacci numbers.

# Thank You

:::fragment
Questions?
:::
