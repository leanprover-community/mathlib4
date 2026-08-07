/-
Copyright (c) 2026 Chris Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Chen
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed
public import Mathlib.Order.SetNotation

/-!
# Directed complete partial orders

This file defines *directed complete partial orders* (DCPOs). These are partial orders for which
every nonempty directed set has a least upper bound.

Notable examples:
* `Part` (without requiring choice).
* `ScottContinuous` functions between `DirectedCompletePartialOrder`s.
* A `CompletePartialOrder` is exactly a DCPO which is also `OrderBot`.

DCPOs are useful for the formalisation of the semantics of programming languages. Their
`MonoidalClosed` structure with respect to `ScottContinuous` functions helps define the meaning of
concurrent procedures and coinductive data structures.

DCPOs essentially generalise `OmegaCompletePartialOrder`s to arbitrary cardinalities [Recursive
Domain Equations, Fact 1.a][smyth_plotkin1982].

For *pointed* directed complete partial orders, see `CompletePartialOrder`, which removes the
nonemptiness constraint.

## References

* [Smyth and Plotkin, *The Category-Theoretic Solution of Recursive Domain
  Equations*][smyth_plotkin1982]
* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags

directed complete partial order, directedly complete partial order, dcpo
-/

@[expose] public section

/--
Directed complete partial orders are partial orders
where every nonempty, directed set has a least upper bound.
-/
class DirectedCompletePartialOrder (α : Type*)
    extends PartialOrder α, SupSet α where

  /-- For each nonempty, directed set `s` which is bounded above, `sSup s` is
  the least upper bound of `s`. -/
  lubOfNonemptyDirected : ∀ d, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d (sSup d)

  -- TODO(rfc): once LawfulSup exists, drop the `SupSet` and go for `Nonempty {u | IsLUB d u}`?

variable {ι : Sort*} {α : Type*}

/--
Create a `DirectedCompletePartialOrder` from a `PartialOrder` and `SupSet`
such that for every nonempty directed set `d`, `sSup d` is the least upper bound of `d`.
-/
@[reducible]
def DirectedCompletePartialOrder.ofLubOfNonemptyDirected
    [PartialOrder α] [SupSet α]
    (lub_of_nonempty_directed : ∀ d : Set α, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB d (sSup d)) :
    DirectedCompletePartialOrder α where
  lubOfNonemptyDirected := lub_of_nonempty_directed

-- TODO(review): these next ones are verbatim from ConditionallyCompletePartialOrder and
-- CompletePartialOrder.

section DirectedSets

variable [DirectedCompletePartialOrder α]

variable {f : ι → α} {d : Set α} {a : α}

-- TODO(review): Current name emulates the phrase "directed supremum".
-- `isLUB_dir_sSup`, `isLUB_dsSup`?
protected lemma DirectedOn.isLUB_dirSSup (h_dir : DirectedOn (· ≤ ·) d)
    (h_non : d.Nonempty) : IsLUB d (sSup d) :=
  DirectedCompletePartialOrder.lubOfNonemptyDirected d h_non h_dir

protected lemma DirectedOn.le_dirSSup (hd : DirectedOn (· ≤ ·) d)
    (ha : a ∈ d) : a ≤ sSup d :=
  (hd.isLUB_dirSSup ⟨a, ha⟩).1 ha

protected lemma DirectedOn.dirSSup_le (hd : DirectedOn (· ≤ ·) d)
    (h_non : d.Nonempty) (ha : ∀ b ∈ d, b ≤ a) : sSup d ≤ a :=
  (hd.isLUB_dirSSup h_non).2 ha

-- TODO(review): `le_dir_iSup`, `le_diSup`?
protected lemma Directed.le_dirISup (hf : Directed (· ≤ ·) f)
    (i : ι) : f i ≤ ⨆ j, f j :=
  hf.directedOn_range.le_dirSSup <| Set.mem_range_self _

protected lemma Directed.dirISup_le [Nonempty ι] (hf : Directed (· ≤ ·) f)
    (ha : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
  hf.directedOn_range.dirSSup_le (Set.range_nonempty _) <| Set.forall_mem_range.2 ha

end DirectedSets

end
