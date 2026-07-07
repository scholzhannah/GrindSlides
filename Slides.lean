import VersoSlides

-- for the second example
import Mathlib.Data.Finset.Defs

-- for the third example
import Mathlib.Data.Finset.Card

-- cardinality symbol
open Finset

open VersoSlides

#doc (Slides) "A short introduction to `grind`" =>

# Basic usage

* recent tactic, announced:
* meant to automatically provide proofs for easy goals
* examples from Mathlib

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

```lean
theorem exists_subset_or_subset_of_two_mul_lt_card''
    {α : Type*} [DecidableEq α] {X Y : Finset α} {n : ℕ}
    (hXY : 2 * n < #(X ∪ Y)) :
    ∃ C : Finset α, n < #C ∧ (C ⊆ X ∨ C ⊆ Y) := by
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
