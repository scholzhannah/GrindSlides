import VersoSlides

-- cannot be in the same file
import Slides.AddAttr

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

-- for a list example
import Mathlib.Data.Bool.Count

-- graph example
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

-- for the example instance
import Mathlib.Algebra.Ring.GrindInstances

-- cardinality, iso symbol, dsupp
open Finset CategoryTheory Distribution

open VersoSlides

#doc (Slides) "A short introduction to `grind`" =>

# A short introduction to `grind`

# Basic usage

* recent tactic, announced: July 2025
* meant to automatically provide proofs for easy goals

# Goals of presentation

* basic understanding of the workings of `grind`
* focus on usage and user interface
* see a lot of Mathlib examples
* read the [Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/) for more detail

# Intuition

* "virtual whiteboard"
* to start: hypotheses and negated conclusion on the whiteboard
* employs different engines to discover a proof
* engines write discovered facts on the whiteboard for other engines to use

# Error messages

%%%
vertical := some true
%%%
```lean +error
theorem exists_subset_or_subset_of_two_mul_lt_card
    {α : Type*} [DecidableEq α] {X Y : Finset α}
    {n : ℕ} (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α,
      n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
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
lemma even_iff {n : ℤ} :
    Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ ↦ by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩
```

## `=_`: right side of equality

* for equalities: use right side as a pattern
* fails if right side doesn't cover all arguments

```lean -stretch
@[grind? =_]
theorem toList_toArray {α : Type*} {n : ℕ}
    {xs : Vector α n} :
    xs.toArray.toList = xs.toList :=
  rfl
```

##  `_=_`: both sides of equality as two patterns

* two patterns corresponding to `=` and `=_`
* theorem is used if the left or the right side matches

```lean -stretch
@[simp, grind? _=_]
theorem trans_symm {C : Type*} [Category C]
    {X Y Z : C} (α : X ≅ Y) (β : Y ≅ Z) :
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
theorem isClosed_dsupport {α β F V : Type*}
    [FunLike F α β] [TopologicalSpace α]
    [Zero β] [Zero V] {f : F → V} :
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

example {a b c : ℕ} (h₁ : f b = a)
    (h₂ : f c = a) : b = c := by
  grind
```

## `grind!` Example

```lean -stretch
@[grind!? .]
theorem gf' (x : Nat) : g (f x) = x := by
  simp [f, g]

example {a b c : ℕ} (h₁ : f b = a)
    (h₂ : f c = a) : b = c := by
  grind
```

## Custom patterns

can be specified with `grind_pattern`

```lean -panel
theorem mul_left_iff {M : Type*}
    [Monoid M] {a b : M} (ha : IsUnit a) :
    IsUnit (a * b) ↔ IsUnit b :=
  show IsUnit (ha.unit * b) ↔ _ by
    simp [-IsUnit.unit_spec]

grind_pattern mul_left_iff =>
  IsUnit a, IsUnit (a * b)
```

## Custom patterns

```lean -show
open List
```

```lean -panel
@[simp]
theorem count_false_add_count_true'
    (l : List Bool) :
    count false l + count true l = length l :=
  count_not_add_count l true

grind_pattern count_false_add_count_true' =>
  count false l
grind_pattern count_false_add_count_true' =>
  count true l

```

## Picking a Pattern

Tagging with `@[grind]` gives suggestions.

```lean -stretch
@[grind]
theorem gf'' (x : Nat) : g (f x) = x := by
  simp [f, g]
```

## Identifying bad tagging

* bad tagging can make `grind` very slow
* see instantiated theorems with `trace.grind.ematch.instance`
* loops in tagging can be caught with `#grind_lint`

## Loop example

```lean
attribute [grind =] List.reverse_flatMap
  List.flatMap_reverse

#grind_lint inspect List.reverse_flatMap

-- !fragment
set_option trace.grind.ematch.instance true in
#grind_lint inspect List.reverse_flatMap
```

## Finding loops

Mathlib performs the following check:

```
#grind_lint check (min := 20) in module Mathlib
```

this gives

```
instantiating `Set.Icc.convexComb_symm` triggers 24 additional `grind` theorem instantiations
instantiating `Path.symm_apply` triggers 24 additional `grind` theorem instantiations
```

## Preventing loops

```lean -panel -stretch
grind_pattern reverse_flatMap => (l.flatMap f).reverse where
  f =/= List.reverse ∘ _

grind_pattern flatMap_reverse => l.reverse.flatMap f where
  f =/= List.reverse ∘ _
```

## Recommended patterns

* `simp` lemmas should usually also be tagged with `grind =`
* exceptions: lemmas that introduce case distinctions on the right side

## Figuring out lemmas that should be tagged

* when a `grind` call fails despite you thinking that it shouldn't
* identify missing tags either manually or using `grind +suggestions`

```lean
@[simp]
theorem isAdjMatrix_adjMatrix' (α : Type*)
    {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] [Zero α] [One α] :
    (G.adjMatrix α).IsAdjMatrix where
  zero_or_one := by grind? +suggestions
```

## Restricting e-matching

* generation of hypothesis/conclusion: 0
* generation of expression generated through e-matching: one higher than the highest of the terms used
* set upper generation limit for expressions considered: `grind (gen := n)` (default: 8)


# Satellite solvers

%%%
vertical := some true
%%%

* `grind` employs several satellite solvers to solve problems of a specific nature
* For example:
  * `cutsat` for linear integer arithmetic
  * `ring` for algebraic expressions in rings
  * `linarith` for linear arithmetic problems not solved by `cutsat`
* not the same as Mathlib tactics of same name

## Satellite solvers - instances

* `grind` defines special instances that are used in the solvers
  * e.g. {lean}`Lean.Grind.ToInt`, {lean}`Lean.Grind.CommRing`
* Mathlib derives these instances from the standard Mathlib notions
  * e.g. {lean}`CommRing.toGrindCommRing`

# Interactive mode

%%%
vertical := some true
%%%

```lean
theorem exists_subset_or_subset_of_two_mul_lt_card''
    {α : Type*} [DecidableEq α] {X Y : Finset α}
    {n : ℕ} (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α,
      n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X) := by
      grind?
    finish
```

## Interactive mode - Example

```lean -panel
grind_pattern card_union_add_card_inter => #(s ∪ t), s ∩ t
grind_pattern card_union_add_card_inter => s ∪ t, #(s ∩ t)
grind_pattern card_union_add_card_inter => #(s ∪ t), #s
grind_pattern card_union_add_card_inter => #(s ∪ t), #t
grind_pattern card_union_add_card_inter => #(s ∩ t), #s
grind_pattern card_union_add_card_inter => #(s ∩ t), #t

grind_pattern card_sdiff_add_card_inter =>
  #(s \ t), #(s ∩ t)
grind_pattern card_sdiff_add_card_inter => #(s \ t), #s
```

## Interactive mode tactic language

Some features of Lean's tactic language also work in the interactive mode.

For example: `all_goals`, `<;>` and `have`

## `grind`-specific tactics

* use satellite solvers explicitly by writing their name, e.g. `ring`, `linarith`
* `cases` expects an anchor which can be chosen with `cases?`

```lean
@[simp] lemma forall_mem_not_eq {α : Type*} {s : Finset α}
    {a : α} : (∀ b ∈ s, ¬ a = b) ↔ a ∉ s := by
  grind =>
    cases?
    sorry
```

## `grind`-specific tactics

* `finish`: instructs `grind` to finish the proof itself
* `finish?`: provides a more detailed proof in tactic language

```lean
lemma two_mul_ediv_two_of_even' {n : ℤ} :
    Even n → 2 * (n / 2) = n := by
  grind =>
    finish?
```

## `grind`-specific tactics

* `instantiate`: use e-matching to instantiate theorems and consider additionally provided theorems

```lean -panel
theorem isAdjMatrix_adjMatrix''' (α : Type*) {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] [Zero α]
    [One α] : (G.adjMatrix α).IsAdjMatrix where
  zero_or_one := by
    -- Mathlib proof: `grind [SimpleGraph.adjMatrix_apply]`
    grind =>
      instantiate [SimpleGraph.adjMatrix_apply]
      finish
```

## Query commands

* output specific parts of the typical error messages
* for example: `show_splits`, `show_state`, `show_true`,`show_asserted` and `show_eqcs`

```lean
theorem exists_subset_or_subset_of_two_mul_lt_card''''
    {α : Type*} [DecidableEq α] {X Y : Finset α}
    {n : ℕ} (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α,
      n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X)
    show_eqcs
    finish
```

# Miscellaneous further things

%%%
vertical := some true
%%%

Local `grind`

* using `grind` locally, e.g. when setting up basic theory around a definition
* for theorems: `@[local grind *]` and `local grind_pattern`
* for definitions in the same file: `grind +locals`

## Custom `grind` sets

* Using `grind` only in a certain situation, e.e. only when proving things about a specific object

```
/-- The `compactness` attribute is a custom grind-set
specialized to prove that sets are compact.
It is called by the `compactness` tactic. -/
register_grind_attr compactness

/-- The `closedness` attribute is a custom grind-set
specialized to prove that sets are closed.
It is called by the `closedness` tactic. -/
register_grind_attr closedness
```

## Custom `grind` sets

```lean -panel
attribute [compactness .] isCompact_Icc

@[to_dual self, simp, closedness =]
theorem closure_Icc' {α : Type*} [TopologicalSpace α]
    [Preorder α]  [OrderClosedTopology α] (a b : α) :
    closure (Set.Icc a b) = Set.Icc a b :=
  isClosed_Icc.closure_eq

example : IsCompact <|
    closure (Set.Icc (1 : ℝ) (3 : ℝ)) := by
  grind only [compactness, closedness]
```

## Style and Conventions

* no real consensus yet
* a few suggestions here

## Style: Example 1

```lean -panel -stretch
example {α} [CommSemiring α] (x y : α) :
    (x + y) ^ 2 = x ^ 2 + 2 • x * y + y ^ 2 := by
  ring

example {α} [CommSemiring α] (x y : α) :
    (x + y) ^ 2 = x ^ 2 + 2 • x * y + y ^ 2 := by
  grind
```

## Style: Example 2

```lean -show
open Polynomial
```

```lean -panel
lemma eq_of_natDegree_lt_card_of_eval_eq {R} [CommRing R]
    [IsDomain R] (p q : R[X]) {ι} [Fintype ι] {f : ι → R}
    (hf : Function.Injective f)
    (heval : ∀ i : ι, eval (f i) p = eval (f i) q)
    (hcard : max p.natDegree q.natDegree < Fintype.card ι) :
    p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  · simpa [eval_sub, sub_eq_zero]
  · grind [natDegree_sub_le]

lemma eq_of_natDegree_lt_card_of_eval_eq' {R} [CommRing R]
    [IsDomain R] (p q : R[X]) {ι} [Fintype ι] {f : ι → R}
    (hf : Function.Injective f)
    (heval : ∀ i : ι, eval (f i) p = eval (f i) q)
    (hcard : max p.natDegree q.natDegree < Fintype.card ι) :
    p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  all_goals grind [eval_sub, sub_eq_zero, natDegree_sub_le]
```

## Style: Example 3

```lean -panel
theorem exists_subset_or_subset_of_two_mul_lt_card5
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  grind =>
    have : #(X ∪ Y) = #X + #(Y \ X)
    finish

theorem exists_subset_or_subset_of_two_mul_lt_card6
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
  have : #(X ∪ Y) = #X + #(Y \ X) := by grind
  grind
```

## Maintainability

* `grind` bugs: `grind?` doesn't produce working proofs
* can make bumping projects harder
* Mathlib lints against this (`verifyGrindOnly`) but doesn't change present offences

# Sources

* [relevant section in the Language Reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)
* [Lean 4.25.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/#The-Lean-Language-Reference--Release-Notes--Lean-4___25___0-_LPAR_2025-11-14_RPAR_--Highlights--Grind--Interactive-mode)
* [Lean 4.28.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.28.0/#The-Lean-Language-Reference--Release-Notes--Lean-4___28___0-_LPAR_2026-02-17_RPAR_--Highlights--User-Defined-Grind-Attributes)
* [style suggestions by Chris Henson](https://github.com/chenson2018/leanprover-community.github.io/blob/grind-style/templates/contribute/grind.md)

# Slides and Write-up

* Slides: [scholzhannah.de/GrindSlides](scholzhannah.de/GrindSlides)
* Write-up: [scholzhannah.de/GrindWriteUp](scholzhannah.de/GrindWriteUp)
