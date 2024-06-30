/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal
import Mathlib.Data.Matroid.Init

/-!
# Matroids

A `Matroid` is a structure that combinatorially abstracts
the notion of linear independence and dependence;
matroids have connections with graph theory, discrete optimization,
additive combinatorics and algebraic geometry.
Mathematically, a matroid `M` is a structure on a set `E` comprising a
collection of subsets of `E` called the bases of `M`,
where the bases are required to obey certain axioms.

This file gives a definition of a matroid `M` in terms of its bases,
and some API relating independent sets (subsets of bases) and the notion of a
basis of a set `X` (a maximal independent subset of `X`).

## Main definitions

* a `Matroid α` on a type `α` is a structure comprising a 'ground set'
  and a suitably behaved 'base' predicate.

Given `M : Matroid α` ...

* `M.E` denotes the ground set of `M`, which has type `Set α`
* For `B : Set α`, `M.Base B` means that `B` is a base of `M`.
* For `I : Set α`, `M.Indep I` means that `I` is independent in `M`
    (that is, `I` is contained in a base of `M`).
* For `D : Set α`, `M.Dep D` means that `D` is contained in the ground set of `M`
    but isn't independent.
* For `I : Set α` and `X : Set α`, `M.Basis I X` means that `I` is a maximal independent
    subset of `X`.
* `M.Finite` means that `M` has finite ground set.
* `M.Nonempty` means that the ground set of `M` is nonempty.
* `FiniteRk M` means that the bases of `M` are finite.
* `InfiniteRk M` means that the bases of `M` are infinite.
* `RkPos M` means that the bases of `M` are nonempty.
* `Finitary M` means that a set is independent if and only if all its finite subsets are
    independent.

* `aesop_mat` : a tactic designed to prove `X ⊆ M.E` for some set `X` and matroid `M`.

## Implementation details

There are a few design decisions worth discussing.

### Finiteness
  The first is that our matroids are allowed to be infinite.
  Unlike with many mathematical structures, this isn't such an obvious choice.
  Finite matroids have been studied since the 1930's,
  and there was never controversy as to what is and isn't an example of a finite matroid -
  in fact, surprisingly many apparently different definitions of a matroid
  give rise to the same class of objects.

  However, generalizing different definitions of a finite matroid
  to the infinite in the obvious way (i.e. by simply allowing the ground set to be infinite)
  gives a number of different notions of 'infinite matroid' that disagree with each other,
  and that all lack nice properties.
  Many different competing notions of infinite matroid were studied through the years;
  in fact, the problem of which definition is the best was only really solved in 2013,
  when Bruhn et al. [2] showed that there is a unique 'reasonable' notion of an infinite matroid
  (these objects had previously defined by Higgs under the name 'B-matroid').
  These are defined by adding one carefully chosen axiom to the standard set,
  and adapting existing axioms to not mention set cardinalities;
  they enjoy nearly all the nice properties of standard finite matroids.

  Even though at least 90% of the literature is on finite matroids,
  B-matroids are the definition we use, because they allow for additional generality,
  nearly all theorems are still true and just as easy to state,
  and (hopefully) the more general definition will prevent the need for a costly future refactor.
  The disadvantage is that developing API for the finite case is harder work
  (for instance, it is harder to prove that something is a matroid in the first place,
  and one must deal with `ℕ∞` rather than `ℕ`).
  For serious work on finite matroids, we provide the typeclasses
  `[M.Finite]` and `[FiniteRk M]` and associated API.

### Cardinality
  Just as with bases of a vector space,
  all bases of a finite matroid `M` are finite and have the same cardinality;
  this cardinality is an important invariant known as the 'rank' of `M`.
  For infinite matroids, bases are not in general equicardinal;
  in fact the equicardinality of bases of infinite matroids is independent of ZFC [3].
  What is still true is that either all bases are finite and equicardinal,
  or all bases are infinite. This means that the natural notion of 'size'
  for a set in matroid theory is given by the function `Set.encard`, which
  is the cardinality as a term in `ℕ∞`. We use this function extensively
  in building the API; it is preferable to both `Set.ncard` and `Finset.card`
  because it allows infinite sets to be handled without splitting into cases.

### The ground `Set`
  A last place where we make a consequential choice is making the ground set of a matroid
  a structure field of type `Set α` (where `α` is the type of 'possible matroid elements')
  rather than just having a type `α` of all the matroid elements.
  This is because of how common it is to simultaneously consider
  a number of matroids on different but related ground sets.
  For example, a matroid `M` on ground set `E` can have its structure
  'restricted' to some subset `R ⊆ E` to give a smaller matroid `M ↾ R` with ground set `R`.
  A statement like `(M ↾ R₁) ↾ R₂ = M ↾ R₂` is mathematically obvious.
  But if the ground set of a matroid is a type, this doesn't typecheck,
  and is only true up to canonical isomorphism.
  Restriction is just the tip of the iceberg here;
  one can also 'contract' and 'delete' elements and sets of elements
  in a matroid to give a smaller matroid,
  and in practice it is common to make statements like `M₁.E = M₂.E ∩ M₃.E` and
  `((M ⟋ e) ↾ R) ⟋ C = M ⟋ (C ∪ {e}) ↾ R`.
  Such things are a nightmare to work with unless `=` is actually propositional equality
  (especially because the relevant coercions are usually between sets and not just elements).

  So the solution is that the ground set `M.E` has type `Set α`,
  and there are elements of type `α` that aren't in the matroid.
  The tradeoff is that for many statements, one now has to add
  hypotheses of the form `X ⊆ M.E` to make sure than `X` is actually 'in the matroid',
  rather than letting a 'type of matroid elements' take care of this invisibly.
  It still seems that this is worth it.
  The tactic `aesop_mat` exists specifically to discharge such goals
  with minimal fuss (using default values).
  The tactic works fairly well, but has room for improvement.
  Even though the carrier set is written `M.E`,

  A related decision is to not have matroids themselves be a typeclass.
  This would make things be notationally simpler
  (having `Base` in the presence of `[Matroid α]` rather than `M.Base` for a term `M : Matroid α`)
  but is again just too awkward when one has multiple matroids on the same type.
  In fact, in regular written mathematics,
  it is normal to explicitly indicate which matroid something is happening in,
  so our notation mirrors common practice.

### Notation
  We use a couple of nonstandard conventions in theorem names that are related to the above.
  First, we mirror common informal practice by referring explicitly to the `ground` set rather
  than the notation `E`. (Writing `ground` everywhere in a proof term would be unwieldy, and
  writing `E` in theorem names would be unnatural to read.)

  Second, because we are typically interested in subsets of the ground set `M.E`,
  using `Set.compl` is inconvenient, since `Xᶜ ⊆ M.E` is typically false for `X ⊆ M.E`.
  On the other hand (especially when duals arise), it is common to complement
  a set `X ⊆ M.E` *within* the ground set, giving `M.E \ X`.
  For this reason, we use the term `compl` in theorem names to refer to taking a set difference
  with respect to the ground set, rather than a complement within a type. The lemma
  `compl_base_dual` is one of the many examples of this.

## References

[1] The standard text on matroid theory
[J. G. Oxley, Matroid Theory, Oxford University Press, New York, 2011.]

[2] The robust axiomatic definition of infinite matroids
[H. Bruhn, R. Diestel, M. Kriesell, R. Pendavingh, P. Wollan, Axioms for infinite matroids,
  Adv. Math 239 (2013), 18-46]

[3] Equicardinality of matroid bases is independent of ZFC.
[N. Bowler, S. Geschke, Self-dual uniform matroids on infinite sets,
  Proc. Amer. Math. Soc. 144 (2016), 459-471]
-/

set_option autoImplicit true

open Set

/-- A predicate `P` on sets satisfies the **exchange property** if,
  for all `X` and `Y` satisfying `P` and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that
  swapping `a` for `b` in `X` maintains `P`. -/
def Matroid.ExchangeProperty {α : Type _} (P : Set α → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

/-- A set `X` has the maximal subset property for a predicate `P` if every subset of `X` satisfying
  `P` is contained in a maximal subset of `X` satisfying `P`.  -/
def Matroid.ExistsMaximalSubsetProperty {α : Type _} (P : Set α → Prop) (X : Set α) : Prop :=
  ∀ I, P I → I ⊆ X → (maximals (· ⊆ ·) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).Nonempty

/-- A `Matroid α` is a ground set `E` of type `Set α`, and a nonempty collection of its subsets
  satisfying the exchange property and the maximal subset property. Each such set is called a
  `Base` of `M`. An `Indep`endent set is just a set contained in a base, but we include this
  predicate as a structure field for better definitional properties.

  In most cases, using this definition directly is not the best way to construct a matroid,
  since it requires specifying both the bases and independent sets. If the bases are known,
  use `Matroid.ofBase` or a variant. If just the independent sets are known,
  define an `IndepMatroid`, and then use `IndepMatroid.matroid`.
  -/
@[ext] structure Matroid (α : Type _) where
  /-- `M` has a ground set `E`. -/
  (E : Set α)
  /-- `M` has a predicate `Base` definining its bases. -/
  (Base : Set α → Prop)
  /-- `M` has a predicate `Indep` defining its independent sets. -/
  (Indep : Set α → Prop)
  /-- The `Indep`endent sets are those contained in `Base`s. -/
  (indep_iff' : ∀ ⦃I⦄, Indep I ↔ ∃ B, Base B ∧ I ⊆ B)
  /-- There is at least one `Base`. -/
  (exists_base : ∃ B, Base B)
  /-- For any bases `B`, `B'` and `e ∈ B \ B'`, there is some `f ∈ B' \ B` for which `B-e+f`
    is a base. -/
  (base_exchange : Matroid.ExchangeProperty Base)
  /-- Every independent subset `I` of a set `X` for is contained in a maximal independent
    subset of `X`. -/
  (maximality : ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
  /-- Every base is contained in the ground set. -/
  (subset_ground : ∀ B, Base B → B ⊆ E)

namespace Matroid

variable {α : Type*} {M : Matroid α}

/-- Typeclass for a matroid having finite ground set. Just a wrapper for `M.E.Finite`-/
protected class Finite (M : Matroid α) : Prop where
  /-- The ground set is finite -/
  (ground_finite : M.E.Finite)

/-- Typeclass for a matroid having nonempty ground set. Just a wrapper for `M.E.Nonempty`-/
protected class Nonempty (M : Matroid α) : Prop where
  /-- The ground set is nonempty -/
  (ground_nonempty : M.E.Nonempty)

theorem ground_nonempty (M : Matroid α) [M.Nonempty] : M.E.Nonempty :=
  Nonempty.ground_nonempty

theorem ground_nonempty_iff (M : Matroid α) : M.E.Nonempty ↔ M.Nonempty :=
  ⟨fun h ↦ ⟨h⟩, fun ⟨h⟩ ↦ h⟩

theorem ground_finite (M : Matroid α) [M.Finite] : M.E.Finite :=
  Finite.ground_finite

theorem set_finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X ⊆ M.E := by aesop) : X.Finite :=
  M.ground_finite.subset hX

instance finite_of_finite [Finite α] {M : Matroid α} : M.Finite :=
  ⟨Set.toFinite _⟩

/-- A `FiniteRk` matroid is one whose bases are finite -/
class FiniteRk (M : Matroid α) : Prop where
  /-- There is a finite base -/
  exists_finite_base : ∃ B, M.Base B ∧ B.Finite

instance finiteRk_of_finite (M : Matroid α) [M.Finite] : FiniteRk M :=
  ⟨M.exists_base.imp (fun B hB ↦ ⟨hB, M.set_finite B (M.subset_ground _ hB)⟩)⟩

/-- An `InfiniteRk` matroid is one whose bases are infinite. -/
class InfiniteRk (M : Matroid α) : Prop where
  /-- There is an infinite base -/
  exists_infinite_base : ∃ B, M.Base B ∧ B.Infinite

/-- A `RkPos` matroid is one whose bases are nonempty. -/
class RkPos (M : Matroid α) : Prop where
  /-- The empty set isn't a base -/
  empty_not_base : ¬M.Base ∅

theorem rkPos_iff_empty_not_base : M.RkPos ↔ ¬M.Base ∅ :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

section exchange
namespace ExchangeProperty

variable {Base : Set α → Prop} (exch : ExchangeProperty Base)

/-- A family of sets with the exchange property is an antichain. -/
theorem antichain (hB : Base B) (hB' : Base B') (h : B ⊆ B') : B = B' :=
  h.antisymm (fun x hx ↦ by_contra
    (fun hxB ↦ let ⟨_, hy, _⟩ := exch B' B hB' hB x ⟨hx, hxB⟩; hy.2 <| h hy.1))

theorem encard_diff_le_aux (exch : ExchangeProperty Base) (hB₁ : Base B₁) (hB₂ : Base B₂) :
    (B₁ \ B₂).encard ≤ (B₂ \ B₁).encard := by
  obtain (he | hinf | ⟨e, he, hcard⟩) :=
    (B₂ \ B₁).eq_empty_or_encard_eq_top_or_encard_diff_singleton_lt
  · rw [exch.antichain hB₂ hB₁ (diff_eq_empty.mp he)]
  · exact le_top.trans_eq hinf.symm

  obtain ⟨f, hf, hB'⟩ := exch B₂ B₁ hB₂ hB₁ e he

  have : encard (insert f (B₂ \ {e}) \ B₁) < encard (B₂ \ B₁) := by
    rw [insert_diff_of_mem _ hf.1, diff_diff_comm]; exact hcard

  have hencard := encard_diff_le_aux exch hB₁ hB'
  rw [insert_diff_of_mem _ hf.1, diff_diff_comm, ← union_singleton, ← diff_diff, diff_diff_right,
    inter_singleton_eq_empty.mpr he.2, union_empty] at hencard

  rw [← encard_diff_singleton_add_one he, ← encard_diff_singleton_add_one hf]
  exact add_le_add_right hencard 1
termination_by (B₂ \ B₁).encard

/-- For any two sets `B₁`, `B₂` in a family with the exchange property, the differences `B₁ \ B₂`
and `B₂ \ B₁` have the same `ℕ∞`-cardinality. -/
theorem encard_diff_eq (hB₁ : Base B₁) (hB₂ : Base B₂) : (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  (encard_diff_le_aux exch hB₁ hB₂).antisymm (encard_diff_le_aux exch hB₂ hB₁)

/-- Any two sets `B₁`, `B₂` in a family with the exchange property have the same
`ℕ∞`-cardinality. -/
theorem encard_base_eq (hB₁ : Base B₁) (hB₂ : Base B₂) : B₁.encard = B₂.encard := by
rw [← encard_diff_add_encard_inter B₁ B₂, exch.encard_diff_eq hB₁ hB₂, inter_comm,
     encard_diff_add_encard_inter]

end ExchangeProperty

end exchange

section aesop

/-- The `aesop_mat` tactic attempts to prove a set is contained in the ground set of a matroid.
  It uses a `[Matroid]` ruleset, and is allowed to fail. -/
macro (name := aesop_mat) "aesop_mat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (config := { terminal := true })
  (rule_sets := [$(Lean.mkIdent `Matroid):ident]))

/- We add a number of trivial lemmas (deliberately specialized to statements in terms of the
  ground set of a matroid) to the ruleset `Matroid` for `aesop`. -/

@[aesop unsafe 5% (rule_sets := [Matroid])]
private theorem inter_right_subset_ground (hX : X ⊆ M.E) :
    X ∩ Y ⊆ M.E := inter_subset_left.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
private theorem inter_left_subset_ground (hX : X ⊆ M.E) :
    Y ∩ X ⊆ M.E := inter_subset_right.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
private theorem diff_subset_ground (hX : X ⊆ M.E) : X \ Y ⊆ M.E :=
  diff_subset.trans hX

@[aesop unsafe 10% (rule_sets := [Matroid])]
private theorem ground_diff_subset_ground : M.E \ X ⊆ M.E :=
  diff_subset_ground rfl.subset

@[aesop unsafe 10% (rule_sets := [Matroid])]
private theorem singleton_subset_ground (he : e ∈ M.E) : {e} ⊆ M.E :=
  singleton_subset_iff.mpr he

@[aesop unsafe 5% (rule_sets := [Matroid])]
private theorem subset_ground_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : X ⊆ M.E :=
  hXY.trans hY

@[aesop unsafe 5% (rule_sets := [Matroid])]
private theorem mem_ground_of_mem_of_subset (hX : X ⊆ M.E) (heX : e ∈ X) : e ∈ M.E :=
  hX heX

@[aesop safe (rule_sets := [Matroid])]
private theorem insert_subset_ground {e : α} {X : Set α} {M : Matroid α}
    (he : e ∈ M.E) (hX : X ⊆ M.E) : insert e X ⊆ M.E :=
    insert_subset he hX

@[aesop safe (rule_sets := [Matroid])]
private theorem ground_subset_ground {M : Matroid α} : M.E ⊆ M.E :=
  rfl.subset

attribute [aesop safe (rule_sets := [Matroid])] empty_subset union_subset iUnion_subset

end aesop
section Base

@[aesop unsafe 10% (rule_sets := [Matroid])]
theorem Base.subset_ground (hB : M.Base B) : B ⊆ M.E :=
  M.subset_ground B hB

theorem Base.exchange (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hx : e ∈ B₁ \ B₂) :
    ∃ y ∈ B₂ \ B₁, M.Base (insert y (B₁ \ {e}))  :=
  M.base_exchange B₁ B₂ hB₁ hB₂ _ hx

theorem Base.exchange_mem (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
    ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.Base (insert y (B₁ \ {e})) := by
  simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

theorem Base.eq_of_subset_base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hB₁B₂ : B₁ ⊆ B₂) :
    B₁ = B₂ :=
  M.base_exchange.antichain hB₁ hB₂ hB₁B₂

theorem Base.not_base_of_ssubset (hB : M.Base B) (hX : X ⊂ B) : ¬ M.Base X :=
  fun h ↦ hX.ne (h.eq_of_subset_base hB hX.subset)

theorem Base.insert_not_base (hB : M.Base B) (heB : e ∉ B) : ¬ M.Base (insert e B) :=
  fun h ↦ h.not_base_of_ssubset (ssubset_insert heB) hB

theorem Base.encard_diff_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  M.base_exchange.encard_diff_eq hB₁ hB₂

theorem Base.ncard_diff_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := by
  rw [ncard_def, hB₁.encard_diff_comm hB₂, ← ncard_def]

theorem Base.card_eq_card_of_base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    B₁.encard = B₂.encard := by
  rw [M.base_exchange.encard_base_eq hB₁ hB₂]

theorem Base.ncard_eq_ncard_of_base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) : B₁.ncard = B₂.ncard := by
  rw [ncard_def B₁, hB₁.card_eq_card_of_base hB₂, ← ncard_def]

theorem Base.finite_of_finite (hB : M.Base B) (h : B.Finite) (hB' : M.Base B') : B'.Finite :=
  (finite_iff_finite_of_encard_eq_encard (hB.card_eq_card_of_base hB')).mp h

theorem Base.infinite_of_infinite (hB : M.Base B) (h : B.Infinite) (hB₁ : M.Base B₁) :
    B₁.Infinite :=
  by_contra (fun hB_inf ↦ (hB₁.finite_of_finite (not_infinite.mp hB_inf) hB).not_infinite h)

theorem Base.finite [FiniteRk M] (hB : M.Base B) : B.Finite :=
  let ⟨B₀,hB₀⟩ := ‹FiniteRk M›.exists_finite_base
  hB₀.1.finite_of_finite hB₀.2 hB

theorem Base.infinite [InfiniteRk M] (hB : M.Base B) : B.Infinite :=
  let ⟨B₀,hB₀⟩ := ‹InfiniteRk M›.exists_infinite_base
  hB₀.1.infinite_of_infinite hB₀.2 hB

theorem empty_not_base [h : RkPos M] : ¬M.Base ∅ :=
  h.empty_not_base

theorem Base.nonempty [RkPos M] (hB : M.Base B) : B.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact M.empty_not_base hB

theorem Base.rkPos_of_nonempty (hB : M.Base B) (h : B.Nonempty) : M.RkPos := by
  rw [rkPos_iff_empty_not_base]
  intro he
  obtain rfl := he.eq_of_subset_base hB (empty_subset B)
  simp at h

theorem Base.finiteRk_of_finite (hB : M.Base B) (hfin : B.Finite) : FiniteRk M :=
  ⟨⟨B, hB, hfin⟩⟩

theorem Base.infiniteRk_of_infinite (hB : M.Base B) (h : B.Infinite) : InfiniteRk M :=
  ⟨⟨B, hB, h⟩⟩

theorem not_finiteRk (M : Matroid α) [InfiniteRk M] : ¬ FiniteRk M := by
  intro h; obtain ⟨B,hB⟩ := M.exists_base; exact hB.infinite hB.finite

theorem not_infiniteRk (M : Matroid α) [FiniteRk M] : ¬ InfiniteRk M := by
  intro h; obtain ⟨B,hB⟩ := M.exists_base; exact hB.infinite hB.finite

theorem finite_or_infiniteRk (M : Matroid α) : FiniteRk M ∨ InfiniteRk M :=
  let ⟨B, hB⟩ := M.exists_base
  B.finite_or_infinite.elim
  (Or.inl ∘ hB.finiteRk_of_finite) (Or.inr ∘ hB.infiniteRk_of_infinite)

theorem Base.diff_finite_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite :=
  finite_iff_finite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

theorem Base.diff_infinite_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite :=
  infinite_iff_infinite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

theorem eq_of_base_iff_base_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃B⦄, B ⊆ M₁.E → (M₁.Base B ↔ M₂.Base B)) : M₁ = M₂ := by
  have h' : ∀ B, M₁.Base B ↔ M₂.Base B :=
    fun B ↦ ⟨fun hB ↦ (h hB.subset_ground).1 hB,
      fun hB ↦ (h <| hB.subset_ground.trans_eq hE.symm).2 hB⟩
  ext <;> simp [hE, M₁.indep_iff', M₂.indep_iff', h']

theorem base_compl_iff_mem_maximals_disjoint_base (hB : B ⊆ M.E := by aesop_mat) :
    M.Base (M.E \ B) ↔ B ∈ maximals (· ⊆ ·) {I | I ⊆ M.E ∧ ∃ B, M.Base B ∧ Disjoint I B} := by
  simp_rw [mem_maximals_setOf_iff, and_iff_right hB, and_imp, forall_exists_index]
  refine ⟨fun h ↦ ⟨⟨_, h, disjoint_sdiff_right⟩,
    fun I hI B' ⟨hB', hIB'⟩ hBI ↦ hBI.antisymm ?_⟩, fun ⟨⟨B', hB', hBB'⟩,h⟩ ↦ ?_⟩
  · rw [hB'.eq_of_subset_base h, ← subset_compl_iff_disjoint_right, diff_eq, compl_inter,
      compl_compl] at hIB'
    · exact fun e he ↦ (hIB' he).elim (fun h' ↦ (h' (hI he)).elim) id
    rw [subset_diff, and_iff_right hB'.subset_ground, disjoint_comm]
    exact disjoint_of_subset_left hBI hIB'
  rw [h diff_subset B' ⟨hB', disjoint_sdiff_left⟩]
  · simpa [hB'.subset_ground]
  simp [subset_diff, hB, hBB']

end Base
section dep_indep

/-- A subset of `M.E` is `Dep`endent if it is not `Indep`endent . -/
def Dep (M : Matroid α) (D : Set α) : Prop := ¬M.Indep D ∧ D ⊆ M.E

theorem indep_iff : M.Indep I ↔ ∃ B, M.Base B ∧ I ⊆ B :=
  M.indep_iff' (I := I)

theorem setOf_indep_eq (M : Matroid α) : {I | M.Indep I} = lowerClosure ({B | M.Base B}) := by
  simp_rw [indep_iff]
  rfl

theorem Indep.exists_base_superset (hI : M.Indep I) : ∃ B, M.Base B ∧ I ⊆ B :=
  indep_iff.1 hI

theorem dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D ⊆ M.E := Iff.rfl

theorem setOf_dep_eq (M : Matroid α) : {D | M.Dep D} = {I | M.Indep I}ᶜ ∩ Iic M.E := rfl

@[aesop unsafe 30% (rule_sets := [Matroid])]
theorem Indep.subset_ground (hI : M.Indep I) : I ⊆ M.E := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  exact hIB.trans hB.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]
theorem Dep.subset_ground (hD : M.Dep D) : D ⊆ M.E :=
  hD.2

theorem indep_or_dep (hX : X ⊆ M.E := by aesop_mat) : M.Indep X ∨ M.Dep X := by
  rw [Dep, and_iff_left hX]
  apply em

theorem Indep.not_dep (hI : M.Indep I) : ¬ M.Dep I :=
  fun h ↦ h.1 hI

theorem Dep.not_indep (hD : M.Dep D) : ¬ M.Indep D :=
  hD.1

theorem dep_of_not_indep (hD : ¬ M.Indep D) (hDE : D ⊆ M.E := by aesop_mat) : M.Dep D :=
  ⟨hD, hDE⟩

theorem indep_of_not_dep (hI : ¬ M.Dep I) (hIE : I ⊆ M.E := by aesop_mat) : M.Indep I :=
  by_contra (fun h ↦ hI ⟨h, hIE⟩)

@[simp] theorem not_dep_iff (hX : X ⊆ M.E := by aesop_mat) : ¬ M.Dep X ↔ M.Indep X := by
  rw [Dep, and_iff_left hX, not_not]

@[simp] theorem not_indep_iff (hX : X ⊆ M.E := by aesop_mat) : ¬ M.Indep X ↔ M.Dep X := by
  rw [Dep, and_iff_left hX]

theorem indep_iff_not_dep : M.Indep I ↔ ¬M.Dep I ∧ I ⊆ M.E := by
  rw [dep_iff, not_and, not_imp_not]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, h.subset_ground⟩, fun h ↦ h.1 h.2⟩

theorem Indep.subset (hJ : M.Indep J) (hIJ : I ⊆ J) : M.Indep I := by
  obtain ⟨B, hB, hJB⟩ := hJ.exists_base_superset
  exact indep_iff.2 ⟨B, hB, hIJ.trans hJB⟩

theorem Dep.superset (hD : M.Dep D) (hDX : D ⊆ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  dep_of_not_indep (fun hI ↦ (hI.subset hDX).not_dep hD)

theorem Base.indep (hB : M.Base B) : M.Indep B :=
  indep_iff.2 ⟨B, hB, subset_rfl⟩

@[simp] theorem empty_indep (M : Matroid α) : M.Indep ∅ :=
  Exists.elim M.exists_base (fun _ hB ↦ hB.indep.subset (empty_subset _))

theorem Dep.nonempty (hD : M.Dep D) : D.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hD.not_indep M.empty_indep

theorem Indep.finite [FiniteRk M] (hI : M.Indep I) : I.Finite :=
  let ⟨_, hB, hIB⟩ := hI.exists_base_superset
  hB.finite.subset hIB

theorem Indep.rkPos_of_nonempty (hI : M.Indep I) (hne : I.Nonempty) : M.RkPos := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  exact hB.rkPos_of_nonempty (hne.mono hIB)

theorem Indep.inter_right (hI : M.Indep I) (X : Set α) : M.Indep (I ∩ X) :=
  hI.subset inter_subset_left

theorem Indep.inter_left (hI : M.Indep I) (X : Set α) : M.Indep (X ∩ I) :=
  hI.subset inter_subset_right

theorem Indep.diff (hI : M.Indep I) (X : Set α) : M.Indep (I \ X) :=
  hI.subset diff_subset

theorem Base.eq_of_subset_indep (hB : M.Base B) (hI : M.Indep I) (hBI : B ⊆ I) : B = I :=
  let ⟨B', hB', hB'I⟩ := hI.exists_base_superset
  hBI.antisymm (by rwa [hB.eq_of_subset_base hB' (hBI.trans hB'I)])

theorem base_iff_maximal_indep : M.Base B ↔ M.Indep B ∧ ∀ I, M.Indep I → B ⊆ I → B = I := by
  refine ⟨fun h ↦ ⟨h.indep, fun _ ↦ h.eq_of_subset_indep ⟩, fun ⟨h, h'⟩ ↦ ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_base_superset
  rwa [h' _ hB'.indep hBB']

theorem setOf_base_eq_maximals_setOf_indep : {B | M.Base B} = maximals (· ⊆ ·) {I | M.Indep I} := by
  ext B; rw [mem_maximals_setOf_iff, mem_setOf, base_iff_maximal_indep]

theorem Indep.base_of_maximal (hI : M.Indep I) (h : ∀ J, M.Indep J → I ⊆ J → I = J) : M.Base I :=
  base_iff_maximal_indep.mpr ⟨hI,h⟩

theorem Base.dep_of_ssubset (hB : M.Base B) (h : B ⊂ X) (hX : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  ⟨fun hX ↦ h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩

theorem Base.dep_of_insert (hB : M.Base B) (heB : e ∉ B) (he : e ∈ M.E := by aesop_mat) :
    M.Dep (insert e B) := hB.dep_of_ssubset (ssubset_insert heB) (insert_subset he hB.subset_ground)

theorem Base.mem_of_insert_indep (hB : M.Base B) (heB : M.Indep (insert e B)) : e ∈ B :=
  by_contra fun he ↦ (hB.dep_of_insert he (heB.subset_ground (mem_insert _ _))).not_indep heB

/-- If the difference of two Bases is a singleton, then they differ by an insertion/removal -/
theorem Base.eq_exchange_of_diff_eq_singleton (hB : M.Base B) (hB' : M.Base B') (h : B \ B' = {e}) :
    ∃ f ∈ B' \ B, B' = (insert f B) \ {e} := by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f ≠ e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_diff_singleton_comm hne] at hb
  refine ⟨f, hf, (hb.eq_of_subset_base hB' ?_).symm⟩
  rw [diff_subset_iff, insert_subset_iff, union_comm, ← diff_subset_iff, h, and_iff_left rfl.subset]
  exact Or.inl hf.1

theorem Base.exchange_base_of_indep (hB : M.Base B) (hf : f ∉ B)
    (hI : M.Indep (insert f (B \ {e}))) : M.Base (insert f (B \ {e})) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_base_superset
  have hcard := hB'.encard_diff_comm hB
  rw [insert_subset_iff, ← diff_eq_empty, diff_diff_comm, diff_eq_empty, subset_singleton_iff_eq]
    at hIB'
  obtain ⟨hfB, (h | h)⟩ := hIB'
  · rw [h, encard_empty, encard_eq_zero, eq_empty_iff_forall_not_mem] at hcard
    exact (hcard f ⟨hfB, hf⟩).elim
  rw [h, encard_singleton, encard_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  obtain (rfl : f = x) := hx.subset ⟨hfB, hf⟩
  simp_rw [← h, ← singleton_union, ← hx, sdiff_sdiff_right_self, inf_eq_inter, inter_comm B,
    diff_union_inter]
  exact hB'

theorem Base.exchange_base_of_indep' (hB : M.Base B) (he : e ∈ B) (hf : f ∉ B)
    (hI : M.Indep (insert f B \ {e})) : M.Base (insert f B \ {e}) := by
  have hfe : f ≠ e := by rintro rfl; exact hf he
  rw [← insert_diff_singleton_comm hfe] at *
  exact hB.exchange_base_of_indep hf hI

theorem Base.insert_dep (hB : M.Base B) (h : e ∈ M.E \ B) : M.Dep (insert e B) := by
  rw [← not_indep_iff (insert_subset h.1 hB.subset_ground)]
  exact h.2 ∘ (fun hi ↦ insert_eq_self.mp (hB.eq_of_subset_indep hi (subset_insert e B)).symm)

theorem Indep.exists_insert_of_not_base (hI : M.Indep I) (hI' : ¬M.Base I) (hB : M.Base B) :
    ∃ e ∈ B \ I, M.Indep (insert e I) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_base_superset
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by (rintro rfl; exact hI' hB')))
  obtain (hxB | hxB) := em (x ∈ B)
  · exact ⟨x, ⟨hxB, hx⟩, hB'.indep.subset (insert_subset hxB' hIB') ⟩
  obtain ⟨e,he, hBase⟩ := hB'.exchange hB ⟨hxB',hxB⟩
  exact ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩,
    indep_iff.2 ⟨_, hBase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩

/-- This is the same as `Indep.exists_insert_of_not_base`, but phrased so that
  it is defeq to the augmentation axiom for independent sets. -/
theorem Indep.exists_insert_of_not_mem_maximals (M : Matroid α) ⦃I B : Set α⦄ (hI : M.Indep I)
    (hInotmax : I ∉ maximals (· ⊆ ·) {I | M.Indep I}) (hB : B ∈ maximals (· ⊆ ·) {I | M.Indep I}) :
    ∃ x ∈ B \ I, M.Indep (insert x I) := by
  simp only [mem_maximals_iff, mem_setOf_eq, not_and, not_forall, exists_prop,
    exists_and_left, iff_true_intro hI, true_imp_iff] at hB hInotmax
  refine hI.exists_insert_of_not_base (fun hIb ↦ ?_) ?_
  · obtain ⟨I', hII', hI', hne⟩ := hInotmax
    exact hne <| hIb.eq_of_subset_indep hII' hI'
  exact hB.1.base_of_maximal fun J hJ hBJ ↦ hB.2 hJ hBJ

theorem ground_indep_iff_base : M.Indep M.E ↔ M.Base M.E :=
  ⟨fun h ↦ h.base_of_maximal (fun _ hJ hEJ ↦ hEJ.antisymm hJ.subset_ground), Base.indep⟩

theorem Base.exists_insert_of_ssubset (hB : M.Base B) (hIB : I ⊂ B) (hB' : M.Base B') :
    ∃ e ∈ B' \ I, M.Indep (insert e I) :=
(hB.indep.subset hIB.subset).exists_insert_of_not_base
    (fun hI ↦ hIB.ne (hI.eq_of_subset_base hB hIB.subset)) hB'

theorem eq_of_indep_iff_indep_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ I, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) : M₁ = M₂ :=
  let h' : ∀ I, M₁.Indep I ↔ M₂.Indep I := fun I ↦
    (em (I ⊆ M₁.E)).elim (h I) (fun h' ↦ iff_of_false (fun hi ↦ h' (hi.subset_ground))
      (fun hi ↦ h' (hi.subset_ground.trans_eq hE.symm)))
  eq_of_base_iff_base_forall hE (fun B _ ↦ by simp_rw [base_iff_maximal_indep, h'])

theorem eq_iff_indep_iff_indep_forall {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ I, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I) :=
⟨fun h ↦ by (subst h; simp), fun h ↦ eq_of_indep_iff_indep_forall h.1 h.2⟩

/-- A `Finitary` matroid is one where a set is independent if and only if it all
  its finite subsets are independent, or equivalently a matroid whose circuits are finite. -/
class Finitary (M : Matroid α) : Prop where
  /-- `I` is independent if all its finite subsets are independent. -/
  indep_of_forall_finite : ∀ I, (∀ J, J ⊆ I → J.Finite → M.Indep J) → M.Indep I

theorem indep_of_forall_finite_subset_indep {M : Matroid α} [Finitary M] (I : Set α)
    (h : ∀ J, J ⊆ I → J.Finite → M.Indep J) : M.Indep I :=
  Finitary.indep_of_forall_finite I h

theorem indep_iff_forall_finite_subset_indep {M : Matroid α} [Finitary M] :
    M.Indep I ↔ ∀ J, J ⊆ I → J.Finite → M.Indep J :=
  ⟨fun h _ hJI _ ↦ h.subset hJI, Finitary.indep_of_forall_finite I⟩

instance finitary_of_finiteRk {M : Matroid α} [FiniteRk M] : Finitary M :=
⟨ by
  refine fun I hI ↦ I.finite_or_infinite.elim (hI _ Subset.rfl) (fun h ↦ False.elim ?_)
  obtain ⟨B, hB⟩ := M.exists_base
  obtain ⟨I₀, hI₀I, hI₀fin, hI₀card⟩ := h.exists_subset_ncard_eq (B.ncard + 1)
  obtain ⟨B', hB', hI₀B'⟩ := (hI _ hI₀I hI₀fin).exists_base_superset
  have hle := ncard_le_ncard hI₀B' hB'.finite
  rw [hI₀card, hB'.ncard_eq_ncard_of_base hB, Nat.add_one_le_iff] at hle
  exact hle.ne rfl ⟩

/-- Matroids obey the maximality axiom -/
theorem existsMaximalSubsetProperty_indep (M : Matroid α) :
    ∀ X, X ⊆ M.E → ExistsMaximalSubsetProperty M.Indep X :=
  M.maximality

end dep_indep

section Basis

/-- A Basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'Basis' is used to refer to what we call a 'Base'). -/
def Basis (M : Matroid α) (I X : Set α) : Prop :=
  I ∈ maximals (· ⊆ ·) {A | M.Indep A ∧ A ⊆ X} ∧ X ⊆ M.E

/-- A `Basis'` is a basis without the requirement that `X ⊆ M.E`. This is convenient for some
  API building, especially when working with rank and closure.  -/
def Basis' (M : Matroid α) (I X : Set α) : Prop :=
  I ∈ maximals (· ⊆ ·) {A | M.Indep A ∧ A ⊆ X}

theorem Basis'.indep (hI : M.Basis' I X) : M.Indep I :=
  hI.1.1

theorem Basis.indep (hI : M.Basis I X) : M.Indep I :=
  hI.1.1.1

theorem Basis.subset (hI : M.Basis I X) : I ⊆ X :=
  hI.1.1.2

theorem Basis.basis' (hI : M.Basis I X) : M.Basis' I X :=
  hI.1

theorem Basis'.basis (hI : M.Basis' I X) (hX : X ⊆ M.E := by aesop_mat) : M.Basis I X :=
  ⟨hI, hX⟩

theorem Basis'.subset (hI : M.Basis' I X) : I ⊆ X :=
  hI.1.2

theorem setOf_basis_eq (M : Matroid α) (hX : X ⊆ M.E := by aesop_mat) :
    {I | M.Basis I X} = maximals (· ⊆ ·) ({I | M.Indep I} ∩ Iic X) := by
  ext I; simp [Matroid.Basis, maximals, iff_true_intro hX]

@[aesop unsafe 15% (rule_sets := [Matroid])]
theorem Basis.subset_ground (hI : M.Basis I X) : X ⊆ M.E :=
  hI.2

theorem Basis.basis_inter_ground (hI : M.Basis I X) : M.Basis I (X ∩ M.E) := by
  convert hI
  rw [inter_eq_self_of_subset_left hI.subset_ground]

@[aesop unsafe 15% (rule_sets := [Matroid])]
theorem Basis.left_subset_ground (hI : M.Basis I X) : I ⊆ M.E :=
  hI.indep.subset_ground

theorem Basis.eq_of_subset_indep (hI : M.Basis I X) (hJ : M.Indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
    I = J :=
  hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

theorem Basis.Finite (hI : M.Basis I X) [FiniteRk M] : I.Finite := hI.indep.finite

theorem basis_iff' :
    M.Basis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ J, M.Indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.E := by
  simp [Basis, mem_maximals_setOf_iff, and_assoc, and_congr_left_iff, and_imp,
    and_congr_left_iff, and_congr_right_iff, @Imp.swap (_ ⊆ X)]

theorem basis_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ J, M.Indep J → I ⊆ J → J ⊆ X → I = J) := by
  rw [basis_iff', and_iff_left hX]

theorem basis'_iff_basis_inter_ground : M.Basis' I X ↔ M.Basis I (X ∩ M.E) := by
  rw [Basis', Basis, and_iff_left inter_subset_right]
  convert Iff.rfl using 3
  ext I
  simp only [subset_inter_iff, mem_setOf_eq, and_congr_right_iff, and_iff_left_iff_imp]
  exact fun h _ ↦ h.subset_ground

theorem basis'_iff_basis (hX : X ⊆ M.E := by aesop_mat) : M.Basis' I X ↔ M.Basis I X := by
  rw [basis'_iff_basis_inter_ground, inter_eq_self_of_subset_left hX]

theorem basis_iff_basis'_subset_ground : M.Basis I X ↔ M.Basis' I X ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.basis', h.subset_ground⟩, fun h ↦ (basis'_iff_basis h.2).mp h.1⟩

theorem Basis'.basis_inter_ground (hIX : M.Basis' I X) : M.Basis I (X ∩ M.E) :=
  basis'_iff_basis_inter_ground.mp hIX

theorem Basis'.eq_of_subset_indep (hI : M.Basis' I X) (hJ : M.Indep J) (hIJ : I ⊆ J)
    (hJX : J ⊆ X) : I = J :=
  hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)

theorem Basis'.insert_not_indep (hI : M.Basis' I X) (he : e ∈ X \ I) : ¬ M.Indep (insert e I) :=
  fun hi ↦ he.2 <| insert_eq_self.1 <| Eq.symm <|
    hI.eq_of_subset_indep hi (subset_insert _ _) (insert_subset he.1 hI.subset)

theorem basis_iff_mem_maximals (hX : X ⊆ M.E := by aesop_mat):
    M.Basis I X ↔ I ∈ maximals (· ⊆ ·) {I | M.Indep I ∧ I ⊆ X} := by
  rw [Basis, and_iff_left hX]

theorem basis_iff_mem_maximals_Prop (hX : X ⊆ M.E := by aesop_mat):
    M.Basis I X ↔ I ∈ maximals (· ⊆ ·) (fun I ↦ M.Indep I ∧ I ⊆ X) :=
  basis_iff_mem_maximals

theorem Indep.basis_of_maximal_subset (hI : M.Indep I) (hIX : I ⊆ X)
    (hmax : ∀ ⦃J⦄, M.Indep J → I ⊆ J → J ⊆ X → J ⊆ I) (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X := by
  rw [basis_iff (by aesop_mat : X ⊆ M.E), and_iff_right hI, and_iff_right hIX]
  exact fun J hJ hIJ hJX ↦ hIJ.antisymm (hmax hJ hIJ hJX)

theorem Basis.basis_subset (hI : M.Basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.Basis I Y := by
  rw [basis_iff (hYX.trans hI.subset_ground), and_iff_right hI.indep, and_iff_right hIY]
  exact fun J hJ hIJ hJY ↦ hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX)

@[simp] theorem basis_self_iff_indep : M.Basis I I ↔ M.Indep I := by
  rw [basis_iff', and_iff_right rfl.subset, and_assoc, and_iff_left_iff_imp]
  exact fun hi ↦ ⟨fun _ _ ↦ subset_antisymm, hi.subset_ground⟩

theorem Indep.basis_self (h : M.Indep I) : M.Basis I I :=
  basis_self_iff_indep.mpr h

@[simp] theorem basis_empty_iff (M : Matroid α) : M.Basis I ∅ ↔ I = ∅ :=
  ⟨fun h ↦ subset_empty_iff.mp h.subset, fun h ↦ by (rw [h]; exact M.empty_indep.basis_self)⟩

theorem Basis.dep_of_ssubset (hI : M.Basis I X) (hIY : I ⊂ Y) (hYX : Y ⊆ X) : M.Dep Y := by
  have : X ⊆ M.E := hI.subset_ground
  rw [← not_indep_iff]
  exact fun hY ↦ hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)

theorem Basis.insert_dep (hI : M.Basis I X) (he : e ∈ X \ I) : M.Dep (insert e I) :=
  hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset he.1 hI.subset)

theorem Basis.mem_of_insert_indep (hI : M.Basis I X) (he : e ∈ X) (hIe : M.Indep (insert e I)) :
    e ∈ I :=
  by_contra (fun heI ↦ (hI.insert_dep ⟨he, heI⟩).not_indep hIe)

theorem Basis'.mem_of_insert_indep (hI : M.Basis' I X) (he : e ∈ X) (hIe : M.Indep (insert e I)) :
    e ∈ I :=
  hI.basis_inter_ground.mem_of_insert_indep ⟨he, hIe.subset_ground (mem_insert _ _)⟩ hIe

theorem Basis.not_basis_of_ssubset (hI : M.Basis I X) (hJI : J ⊂ I) : ¬ M.Basis J X :=
  fun h ↦ hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

theorem Indep.subset_basis_of_subset (hI : M.Indep I) (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ J, M.Basis J X ∧ I ⊆ J := by
  obtain ⟨J, ⟨(hJ : M.Indep J),hIJ,hJX⟩, hJmax⟩ := M.maximality X hX I hI hIX
  use J
  rw [and_iff_left hIJ, basis_iff, and_iff_right hJ, and_iff_right hJX]
  exact fun K hK hJK hKX ↦ hJK.antisymm (hJmax ⟨hK, hIJ.trans hJK, hKX⟩ hJK)

theorem Indep.subset_basis'_of_subset (hI : M.Indep I) (hIX : I ⊆ X) :
    ∃ J, M.Basis' J X ∧ I ⊆ J := by
  simp_rw [basis'_iff_basis_inter_ground]
  exact hI.subset_basis_of_subset (subset_inter hIX hI.subset_ground)

theorem exists_basis (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I, M.Basis I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X)
  ⟨_,hI⟩

theorem exists_basis' (M : Matroid α) (X : Set α) : ∃ I, M.Basis' I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_basis'_of_subset (empty_subset X)
  ⟨_,hI⟩

theorem exists_basis_subset_basis (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    ∃ I J, M.Basis I X ∧ M.Basis J Y ∧ I ⊆ J := by
  obtain ⟨I, hI⟩ := M.exists_basis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩

theorem Basis.exists_basis_inter_eq_of_superset (hI : M.Basis I X) (hXY : X ⊆ Y)
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J Y ∧ J ∩ X = I := by
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY)
  refine ⟨J, hJ, subset_antisymm ?_ (subset_inter hIJ hI.subset)⟩
  exact fun e he ↦ hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset he.1 hIJ))

theorem exists_basis_union_inter_basis (M : Matroid α) (X Y : Set α) (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ I, M.Basis I (X ∪ Y) ∧ M.Basis (I ∩ Y) Y :=
  let ⟨J, hJ⟩ := M.exists_basis Y
  (hJ.exists_basis_inter_eq_of_superset subset_union_right).imp
  (fun I hI ↦ ⟨hI.1, by rwa [hI.2]⟩)

theorem Indep.eq_of_basis (hI : M.Indep I) (hJ : M.Basis J I) : J = I :=
  hJ.eq_of_subset_indep hI hJ.subset rfl.subset

theorem Basis.exists_base (hI : M.Basis I X) : ∃ B, M.Base B ∧ I = B ∩ X :=
  let ⟨B,hB, hIB⟩ := hI.indep.exists_base_superset
  ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset)
    (by rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    inter_subset_right])⟩

@[simp] theorem basis_ground_iff : M.Basis B M.E ↔ M.Base B := by
  rw [base_iff_maximal_indep, basis_iff', and_assoc, and_congr_right]
  rw [and_iff_left (rfl.subset : M.E ⊆ M.E)]
  exact fun h ↦ ⟨fun h' I hI hBI ↦ h'.2 _ hI hBI hI.subset_ground,
    fun h' ↦ ⟨h.subset_ground,fun J hJ hBJ _ ↦ h' J hJ hBJ⟩⟩

theorem Base.basis_ground (hB : M.Base B) : M.Basis B M.E :=
  basis_ground_iff.mpr hB

theorem Indep.basis_iff_forall_insert_dep (hI : M.Indep I) (hIX : I ⊆ X) :
    M.Basis I X ↔ ∀ e ∈ X \ I, M.Dep (insert e I) := by
  rw [basis_iff', and_iff_right hIX, and_iff_right hI]
  refine ⟨fun h e he ↦ ⟨fun hi ↦ he.2 ?_, insert_subset (h.2 he.1) hI.subset_ground⟩,
    fun h ↦ ⟨fun J hJ hIJ hJX ↦ hIJ.antisymm (fun e heJ ↦ by_contra (fun heI ↦ ?_)), ?_⟩⟩
  · exact (h.1 _ hi (subset_insert _ _) (insert_subset he.1 hIX)).symm.subset (mem_insert e I)
  · exact (h e ⟨hJX heJ, heI⟩).not_indep (hJ.subset (insert_subset heJ hIJ))
  rw [← diff_union_of_subset hIX, union_subset_iff, and_iff_left hI.subset_ground]
  exact fun e he ↦ (h e he).subset_ground (mem_insert _ _)

theorem Indep.basis_of_forall_insert (hI : M.Indep I) (hIX : I ⊆ X)
    (he : ∀ e ∈ X \ I, M.Dep (insert e I)) : M.Basis I X :=
  (hI.basis_iff_forall_insert_dep hIX).mpr he

theorem Indep.basis_insert_iff (hI : M.Indep I) :
    M.Basis I (insert e I) ↔ M.Dep (insert e I) ∨ e ∈ I := by
  simp_rw [hI.basis_iff_forall_insert_dep (subset_insert _ _), dep_iff, insert_subset_iff,
    and_iff_left hI.subset_ground, mem_diff, mem_insert_iff, or_and_right, and_not_self,
    or_false, and_imp, forall_eq]
  tauto

theorem Basis.iUnion_basis_iUnion {ι : Type _} (X I : ι → Set α) (hI : ∀ i, M.Basis (I i) (X i))
    (h_ind : M.Indep (⋃ i, I i)) : M.Basis (⋃ i, I i) (⋃ i, X i) := by
  refine h_ind.basis_of_forall_insert
    (iUnion_subset (fun i ↦ (hI i).subset.trans (subset_iUnion _ _))) ?_
  rintro e ⟨⟨_, ⟨⟨i, hi, rfl⟩, (hes : e ∈ X i)⟩⟩, he'⟩
  rw [mem_iUnion, not_exists] at he'
  refine ((hI i).insert_dep ⟨hes, he' _⟩).superset (insert_subset_insert (subset_iUnion _ _)) ?_
  rw [insert_subset_iff, iUnion_subset_iff, and_iff_left (fun i ↦ (hI i).indep.subset_ground)]
  exact (hI i).subset_ground hes

theorem Basis.basis_iUnion {ι : Type _} [Nonempty ι] (X : ι → Set α)
    (hI : ∀ i, M.Basis I (X i)) : M.Basis I (⋃ i, X i) := by
  convert Basis.iUnion_basis_iUnion X (fun _ ↦ I) (fun i ↦ hI i) _ <;> rw [iUnion_const]
  exact (hI (Classical.arbitrary ι)).indep

theorem Basis.basis_sUnion {Xs : Set (Set α)} (hne : Xs.Nonempty) (h : ∀ X ∈ Xs, M.Basis I X) :
    M.Basis I (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion]
  have := Iff.mpr nonempty_coe_sort hne
  exact Basis.basis_iUnion _ fun X ↦ (h X X.prop)

theorem Indep.basis_setOf_insert_basis (hI : M.Indep I) :
    M.Basis I {x | M.Basis I (insert x I)} := by
  refine hI.basis_of_forall_insert (fun e he ↦ (?_ : M.Basis _ _))
    (fun e he ↦ ⟨fun hu ↦ he.2 ?_, he.1.subset_ground⟩)
  · rw [insert_eq_of_mem he]; exact hI.basis_self
  simpa using (hu.eq_of_basis he.1).symm

theorem Basis.union_basis_union (hIX : M.Basis I X) (hJY : M.Basis J Y) (h : M.Indep (I ∪ J)) :
    M.Basis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  refine Basis.iUnion_basis_iUnion _ _ ?_ ?_
  · simp only [Bool.forall_bool, cond_false, cond_true]; exact ⟨hJY, hIX⟩
  rwa [← union_eq_iUnion]

theorem Basis.basis_union (hIX : M.Basis I X) (hIY : M.Basis I Y) : M.Basis I (X ∪ Y) := by
    convert hIX.union_basis_union hIY _ <;> rw [union_self]; exact hIX.indep

theorem Basis.basis_union_of_subset (hI : M.Basis I X) (hJ : M.Indep J) (hIJ : I ⊆ J) :
    M.Basis J (J ∪ X) := by
  convert hJ.basis_self.union_basis_union hI _ <;>
  rw [union_eq_self_of_subset_right hIJ]
  assumption

theorem Basis.insert_basis_insert (hI : M.Basis I X) (h : M.Indep (insert e I)) :
    M.Basis (insert e I) (insert e X) := by
  simp_rw [← union_singleton] at *
  exact hI.union_basis_union (h.subset subset_union_right).basis_self h

theorem Base.base_of_basis_superset (hB : M.Base B) (hBX : B ⊆ X) (hIX : M.Basis I X) :
    M.Base I := by
  by_contra h
  obtain ⟨e,heBI,he⟩ := hIX.indep.exists_insert_of_not_base h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)

theorem Indep.exists_base_subset_union_base (hI : M.Indep I) (hB : M.Base B) :
    ∃ B', M.Base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B := by
  obtain ⟨B', hB', hIB'⟩ := hI.subset_basis_of_subset <| subset_union_left (t := B)
  exact ⟨B', hB.base_of_basis_superset subset_union_right hB', hIB', hB'.subset⟩

theorem Basis.inter_eq_of_subset_indep (hIX : M.Basis I X) (hIJ : I ⊆ J) (hJ : M.Indep J) :
    J ∩ X = I :=
(subset_inter hIJ hIX.subset).antisymm'
  (fun _ he ↦ hIX.mem_of_insert_indep he.2 (hJ.subset (insert_subset he.1 hIJ)))

theorem Basis'.inter_eq_of_subset_indep (hI : M.Basis' I X) (hIJ : I ⊆ J) (hJ : M.Indep J) :
    J ∩ X = I := by
  rw [← hI.basis_inter_ground.inter_eq_of_subset_indep hIJ hJ, inter_comm X, ← inter_assoc,
    inter_eq_self_of_subset_left hJ.subset_ground]

theorem Base.basis_of_subset (hX : X ⊆ M.E := by aesop_mat) (hB : M.Base B) (hBX : B ⊆ X) :
    M.Basis B X := by
  rw [basis_iff, and_iff_right hB.indep, and_iff_right hBX]
  exact fun J hJ hBJ _ ↦ hB.eq_of_subset_indep hJ hBJ

theorem exists_basis_disjoint_basis_of_subset (M : Matroid α) {X Y : Set α} (hXY : X ⊆ Y)
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ I J, M.Basis I X ∧ M.Basis (I ∪ J) Y ∧ Disjoint X J := by
  obtain ⟨I, I', hI, hI', hII'⟩ := M.exists_basis_subset_basis hXY
  refine ⟨I, I' \ I, hI, by rwa [union_diff_self, union_eq_self_of_subset_left hII'], ?_⟩
  rw [disjoint_iff_forall_ne]
  rintro e heX _ ⟨heI', heI⟩ rfl
  exact heI <| hI.mem_of_insert_indep heX (hI'.indep.subset (insert_subset heI' hII'))

end Basis

section Finite

/-- For finite `E`, finitely many matroids have ground set contained in `E`. -/
theorem finite_setOf_matroid {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E ⊆ E}.Finite := by
  set f : Matroid α → Set α × (Set (Set α)) := fun M ↦ ⟨M.E, {B | M.Base B}⟩
  have hf : f.Injective := by
    refine fun M M' hMM' ↦ ?_
    rw [Prod.mk.injEq, and_comm, Set.ext_iff, and_comm] at hMM'
    exact eq_of_base_iff_base_forall hMM'.1 (fun B _ ↦ hMM'.2 B)
  rw [← Set.finite_image_iff hf.injOn]
  refine (hE.finite_subsets.prod hE.finite_subsets.finite_subsets).subset ?_
  rintro _ ⟨M, hE : M.E ⊆ E, rfl⟩
  simp only [Set.mem_prod, Set.mem_setOf_eq, Set.setOf_subset_setOf]
  exact ⟨hE, fun B hB ↦ hB.subset_ground.trans hE⟩

/-- For finite `E`, finitely many matroids have ground set `E`. -/
theorem finite_setOf_matroid' {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E = E}.Finite :=
  (finite_setOf_matroid hE).subset (fun M ↦ by rintro rfl; exact rfl.subset)

end Finite
