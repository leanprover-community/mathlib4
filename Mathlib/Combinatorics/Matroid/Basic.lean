/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.UpperLower.Closure

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
* For `B : Set α`, `M.IsBase B` means that `B` is a base of `M`.
* For `I : Set α`, `M.Indep I` means that `I` is independent in `M`
    (that is, `I` is contained in a base of `M`).
* For `D : Set α`, `M.Dep D` means that `D` is contained in the ground set of `M`
    but isn't independent.
* For `I : Set α` and `X : Set α`, `M.IsBasis I X` means that `I` is a maximal independent
    subset of `X`.
* `M.Finite` means that `M` has finite ground set.
* `M.Nonempty` means that the ground set of `M` is nonempty.
* `RankFinite M` means that the bases of `M` are finite.
* `RankInfinite M` means that the bases of `M` are infinite.
* `RankPos M` means that the bases of `M` are nonempty.
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
  `[M.Finite]` and `[RankFinite M]` and associated API.

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

  A related decision is to not have matroids themselves be a typeclass.
  This would make things be notationally simpler
  (having `Base` in the presence of `[Matroid α]` rather than `M.Base` for a term `M : Matroid α`)
  but is again just too awkward when one has multiple matroids on the same type.
  In fact, in regular written mathematics,
  it is normal to explicitly indicate which matroid something is happening in,
  so our notation mirrors common practice.

### Notation
  We use a few nonstandard conventions in theorem names that are related to the above.
  First, we mirror common informal practice by referring explicitly to the `ground` set rather
  than the notation `E`. (Writing `ground` everywhere in a proof term would be unwieldy, and
  writing `E` in theorem names would be unnatural to read.)

  Second, because we are typically interested in subsets of the ground set `M.E`,
  using `Set.compl` is inconvenient, since `Xᶜ ⊆ M.E` is typically false for `X ⊆ M.E`.
  On the other hand (especially when duals arise), it is common to complement
  a set `X ⊆ M.E` *within* the ground set, giving `M.E \ X`.
  For this reason, we use the term `compl` in theorem names to refer to taking a set difference
  with respect to the ground set, rather than a complement within a type. The lemma
  `compl_isBase_dual` is one of the many examples of this.

  Finally, in theorem names, matroid predicates that apply to sets
  (such as `Base`, `Indep`, `IsBasis`) are typically used as suffixes rather than prefixes.
  For instance, we have `ground_indep_iff_isBase` rather than `indep_ground_iff_isBase`.

## References

* [J. Oxley, Matroid Theory][oxley2011]
* [H. Bruhn, R. Diestel, M. Kriesell, R. Pendavingh, P. Wollan, Axioms for infinite matroids,
  Adv. Math 239 (2013), 18-46][bruhnDiestelKriesellPendavinghWollan2013]
* [N. Bowler, S. Geschke, Self-dual uniform matroids on infinite sets,
  Proc. Amer. Math. Soc. 144 (2016), 459-471][bowlerGeschke2015]
-/

@[expose] public section

assert_not_exists Field

open Set

/-- A predicate `P` on sets satisfies the **exchange property** if,
for all `X` and `Y` satisfying `P` and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that
swapping `a` for `b` in `X` maintains `P`. -/
def Matroid.ExchangeProperty {α : Type*} (P : Set α → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

/-- A set `X` has the maximal subset property for a predicate `P` if every subset of `X` satisfying
`P` is contained in a maximal subset of `X` satisfying `P`. -/
def Matroid.ExistsMaximalSubsetProperty {α : Type*} (P : Set α → Prop) (X : Set α) : Prop :=
  ∀ I, P I → I ⊆ X → ∃ J, I ⊆ J ∧ Maximal (fun K ↦ P K ∧ K ⊆ X) J

/-- A `Matroid α` is a ground set `E` of type `Set α`, and a nonempty collection of its subsets
satisfying the exchange property and the maximal subset property. Each such set is called a
`Base` of `M`. An `Indep`endent set is just a set contained in a base, but we include this
predicate as a structure field for better definitional properties.

In most cases, using this definition directly is not the best way to construct a matroid,
since it requires specifying both the bases and independent sets. If the bases are known,
use `Matroid.ofBase` or a variant. If just the independent sets are known,
define an `IndepMatroid`, and then use `IndepMatroid.matroid`.
-/
structure Matroid (α : Type*) where
  /-- `M` has a ground set `E`. -/
  (E : Set α)
  /-- `M` has a predicate `Base` defining its bases. -/
  (IsBase : Set α → Prop)
  /-- `M` has a predicate `Indep` defining its independent sets. -/
  (Indep : Set α → Prop)
  /-- The `Indep`endent sets are those contained in `Base`s. -/
  (indep_iff' : ∀ ⦃I⦄, Indep I ↔ ∃ B, IsBase B ∧ I ⊆ B)
  /-- There is at least one `Base`. -/
  (exists_isBase : ∃ B, IsBase B)
  /-- For any bases `B`, `B'` and `e ∈ B \ B'`, there is some `f ∈ B' \ B` for which `B-e+f`
  is a base. -/
  (isBase_exchange : Matroid.ExchangeProperty IsBase)
  /-- Every independent subset `I` of a set `X` for is contained in a maximal independent
  subset of `X`. -/
  (maximality : ∀ X, X ⊆ E → Matroid.ExistsMaximalSubsetProperty Indep X)
  /-- Every base is contained in the ground set. -/
  (subset_ground : ∀ B, IsBase B → B ⊆ E)

attribute [local ext] Matroid

namespace Matroid

variable {α : Type*} {M : Matroid α}

instance (M : Matroid α) : Nonempty {B // M.IsBase B} :=
  nonempty_subtype.2 M.exists_isBase

/-- Typeclass for a matroid having finite ground set. Just a wrapper for `M.E.Finite`. -/
@[mk_iff] protected class Finite (M : Matroid α) : Prop where
  /-- The ground set is finite -/
  (ground_finite : M.E.Finite)

/-- Typeclass for a matroid having nonempty ground set. Just a wrapper for `M.E.Nonempty`. -/
protected class Nonempty (M : Matroid α) : Prop where
  /-- The ground set is nonempty -/
  (ground_nonempty : M.E.Nonempty)

theorem ground_nonempty (M : Matroid α) [M.Nonempty] : M.E.Nonempty :=
  Nonempty.ground_nonempty

theorem ground_nonempty_iff (M : Matroid α) : M.E.Nonempty ↔ M.Nonempty :=
  ⟨fun h ↦ ⟨h⟩, fun ⟨h⟩ ↦ h⟩

lemma nonempty_type (M : Matroid α) [h : M.Nonempty] : Nonempty α :=
  ⟨M.ground_nonempty.some⟩

theorem ground_finite (M : Matroid α) [M.Finite] : M.E.Finite :=
  Finite.ground_finite

theorem set_finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X ⊆ M.E := by aesop) : X.Finite :=
  M.ground_finite.subset hX

instance finite_of_finite [Finite α] {M : Matroid α} : M.Finite :=
  ⟨Set.toFinite _⟩

/-- A `RankFinite` matroid is one whose bases are finite -/
@[mk_iff] class RankFinite (M : Matroid α) : Prop where
  /-- There is a finite base -/
  exists_finite_isBase : ∃ B, M.IsBase B ∧ B.Finite

instance rankFinite_of_finite (M : Matroid α) [M.Finite] : RankFinite M :=
  ⟨M.exists_isBase.imp (fun B hB ↦ ⟨hB, M.set_finite B (M.subset_ground _ hB)⟩)⟩

/-- An `RankInfinite` matroid is one whose bases are infinite. -/
@[mk_iff] class RankInfinite (M : Matroid α) : Prop where
  /-- There is an infinite base -/
  exists_infinite_isBase : ∃ B, M.IsBase B ∧ B.Infinite

/-- A `RankPos` matroid is one whose bases are nonempty. -/
@[mk_iff] class RankPos (M : Matroid α) : Prop where
  /-- The empty set isn't a base -/
  empty_not_isBase : ¬M.IsBase ∅

instance rankPos_nonempty {M : Matroid α} [M.RankPos] : M.Nonempty := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain rfl | ⟨e, heB⟩ := B.eq_empty_or_nonempty
  · exact False.elim <| RankPos.empty_not_isBase hB
  exact ⟨e, M.subset_ground B hB heB ⟩

section exchange
namespace ExchangeProperty

variable {IsBase : Set α → Prop} {B B' : Set α}

/-- A family of sets with the exchange property is an antichain. -/
theorem antichain (exch : ExchangeProperty IsBase) (hB : IsBase B) (hB' : IsBase B') (h : B ⊆ B') :
    B = B' :=
  h.antisymm (fun x hx ↦ by_contra
    (fun hxB ↦ let ⟨_, hy, _⟩ := exch B' B hB' hB x ⟨hx, hxB⟩; hy.2 <| h hy.1))

theorem encard_sdiff_le_aux {B₁ B₂ : Set α}
    (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    (B₁ \ B₂).encard ≤ (B₂ \ B₁).encard := by
  obtain (he | hinf | ⟨e, he, hcard⟩) :=
    (B₂ \ B₁).eq_empty_or_encard_eq_top_or_encard_sdiff_singleton_lt
  · rw [exch.antichain hB₂ hB₁ (sdiff_eq_empty.mp he)]
  · exact le_top.trans_eq hinf.symm
  obtain ⟨f, hf, hB'⟩ := exch B₂ B₁ hB₂ hB₁ e he
  have : encard (insert f (B₂ \ {e}) \ B₁) < encard (B₂ \ B₁) := by
    rw [insert_sdiff_of_mem _ hf.1, sdiff_sdiff_comm]; exact hcard
  have hencard := encard_sdiff_le_aux exch hB₁ hB'
  rw [insert_sdiff_of_mem _ hf.1, sdiff_sdiff_comm, ← union_singleton, ← sdiff_sdiff,
    sdiff_sdiff_right, inter_singleton_eq_empty.mpr he.2, union_empty] at hencard
  rw [← encard_sdiff_singleton_add_one he, ← encard_sdiff_singleton_add_one hf]
  gcongr
termination_by (B₂ \ B₁).encard

@[deprecated (since := "2026-06-03")] alias encard_diff_le_aux := encard_sdiff_le_aux

variable {B₁ B₂ : Set α}

/-- For any two sets `B₁`, `B₂` in a family with the exchange property, the differences `B₁ \ B₂`
and `B₂ \ B₁` have the same `ℕ∞`-cardinality. -/
theorem encard_sdiff_eq (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  (encard_sdiff_le_aux exch hB₁ hB₂).antisymm (encard_sdiff_le_aux exch hB₂ hB₁)

@[deprecated (since := "2026-06-03")] alias encard_diff_eq := encard_sdiff_eq

/-- Any two sets `B₁`, `B₂` in a family with the exchange property have the same
`ℕ∞`-cardinality. -/
theorem encard_isBase_eq (exch : ExchangeProperty IsBase) (hB₁ : IsBase B₁) (hB₂ : IsBase B₂) :
    B₁.encard = B₂.encard := by
  rw [← encard_sdiff_add_encard_inter B₁ B₂, exch.encard_sdiff_eq hB₁ hB₂, inter_comm,
    encard_sdiff_add_encard_inter]

end ExchangeProperty

end exchange

section aesop

-- This is necessary as `aesop` uses private lemmas for its proof terms: without this option,
-- the aesop proofs will not work, and any `aesop` auto-params will not fire.
set_option backward.privateInPublic true

/-- The `aesop_mat` tactic attempts to prove a set is contained in the ground set of a matroid.
  It uses a `[Matroid]` ruleset, and is allowed to fail. -/
macro (name := aesop_mat) "aesop_mat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (config := {terminal := true})
  (rule_sets := [$(Lean.mkIdent `Matroid):ident]))

/- We add a number of trivial lemmas (deliberately specialized to statements in terms of the
  ground set of a matroid) to the ruleset `Matroid` for `aesop`. -/

variable {X Y : Set α} {e : α}

@[aesop unsafe 5% (rule_sets := [Matroid])]
private theorem inter_right_subset_ground (hX : X ⊆ M.E) :
    X ∩ Y ⊆ M.E := inter_subset_left.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
private theorem inter_left_subset_ground (hX : X ⊆ M.E) :
    Y ∩ X ⊆ M.E := inter_subset_right.trans hX

@[aesop unsafe 5% (rule_sets := [Matroid])]
private theorem sdiff_subset_ground (hX : X ⊆ M.E) : X \ Y ⊆ M.E :=
  sdiff_subset.trans hX

@[deprecated (since := "2026-06-03")] alias diff_subset_ground := sdiff_subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
private theorem ground_sdiff_subset_ground : M.E \ X ⊆ M.E :=
  sdiff_subset_ground rfl.subset

@[deprecated (since := "2026-06-03")] alias ground_diff_subset_ground := ground_sdiff_subset_ground

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

section IsBase

variable {B B₁ B₂ : Set α}

@[aesop unsafe 10% (rule_sets := [Matroid])]
theorem IsBase.subset_ground (hB : M.IsBase B) : B ⊆ M.E :=
  M.subset_ground B hB

theorem IsBase.exchange {e : α} (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hx : e ∈ B₁ \ B₂) :
    ∃ y ∈ B₂ \ B₁, M.IsBase (insert y (B₁ \ {e})) :=
  M.isBase_exchange B₁ B₂ hB₁ hB₂ _ hx

theorem IsBase.exchange_mem {e : α}
    (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
    ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.IsBase (insert y (B₁ \ {e})) := by
  simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

theorem IsBase.eq_of_subset_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) (hB₁B₂ : B₁ ⊆ B₂) :
    B₁ = B₂ :=
  M.isBase_exchange.antichain hB₁ hB₂ hB₁B₂

theorem IsBase.not_isBase_of_ssubset {X : Set α} (hB : M.IsBase B) (hX : X ⊂ B) : ¬ M.IsBase X :=
  fun h ↦ hX.ne (h.eq_of_subset_isBase hB hX.subset)

theorem IsBase.insert_not_isBase {e : α} (hB : M.IsBase B) (heB : e ∉ B) :
    ¬ M.IsBase (insert e B) :=
  fun h ↦ h.not_isBase_of_ssubset (ssubset_insert heB) hB

theorem IsBase.encard_sdiff_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  M.isBase_exchange.encard_sdiff_eq hB₁ hB₂

@[deprecated (since := "2026-06-03")] alias IsBase.encard_diff_comm := IsBase.encard_sdiff_comm

theorem IsBase.ncard_sdiff_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := by
  rw [ncard_def, hB₁.encard_sdiff_comm hB₂, ← ncard_def]

@[deprecated (since := "2026-06-03")] alias IsBase.ncard_diff_comm := IsBase.ncard_sdiff_comm

theorem IsBase.encard_eq_encard_of_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    B₁.encard = B₂.encard := by
  rw [M.isBase_exchange.encard_isBase_eq hB₁ hB₂]

theorem IsBase.ncard_eq_ncard_of_isBase (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    B₁.ncard = B₂.ncard := by
  rw [ncard_def B₁, hB₁.encard_eq_encard_of_isBase hB₂, ← ncard_def]

theorem IsBase.finite_of_finite {B' : Set α}
    (hB : M.IsBase B) (h : B.Finite) (hB' : M.IsBase B') : B'.Finite :=
  (finite_iff_finite_of_encard_eq_encard (hB.encard_eq_encard_of_isBase hB')).mp h

theorem IsBase.infinite_of_infinite (hB : M.IsBase B) (h : B.Infinite) (hB₁ : M.IsBase B₁) :
    B₁.Infinite := by
  contrapose! h; exact hB₁.finite_of_finite h hB

theorem IsBase.finite [RankFinite M] (hB : M.IsBase B) : B.Finite :=
  let ⟨_, hB₀⟩ := ‹RankFinite M›.exists_finite_isBase
  hB₀.1.finite_of_finite hB₀.2 hB

theorem IsBase.infinite [RankInfinite M] (hB : M.IsBase B) : B.Infinite :=
  let ⟨_, hB₀⟩ := ‹RankInfinite M›.exists_infinite_isBase
  hB₀.1.infinite_of_infinite hB₀.2 hB

theorem empty_not_isBase [h : RankPos M] : ¬M.IsBase ∅ :=
  h.empty_not_isBase

theorem IsBase.nonempty [RankPos M] (hB : M.IsBase B) : B.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact M.empty_not_isBase hB

theorem IsBase.rankPos_of_nonempty (hB : M.IsBase B) (h : B.Nonempty) : M.RankPos := by
  rw [rankPos_iff]
  intro he
  obtain rfl := he.eq_of_subset_isBase hB (empty_subset B)
  simp at h

theorem IsBase.rankFinite_of_finite (hB : M.IsBase B) (hfin : B.Finite) : RankFinite M :=
  ⟨⟨B, hB, hfin⟩⟩

theorem IsBase.rankInfinite_of_infinite (hB : M.IsBase B) (h : B.Infinite) : RankInfinite M :=
  ⟨⟨B, hB, h⟩⟩

theorem not_rankFinite (M : Matroid α) [RankInfinite M] : ¬ RankFinite M := by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite

theorem not_rankInfinite (M : Matroid α) [RankFinite M] : ¬ RankInfinite M := by
  intro h; obtain ⟨B, hB⟩ := M.exists_isBase; exact hB.infinite hB.finite

theorem rankFinite_or_rankInfinite (M : Matroid α) : RankFinite M ∨ RankInfinite M :=
  let ⟨B, hB⟩ := M.exists_isBase
  B.finite_or_infinite.imp hB.rankFinite_of_finite hB.rankInfinite_of_infinite

@[simp]
theorem not_rankFinite_iff (M : Matroid α) : ¬ RankFinite M ↔ RankInfinite M :=
  M.rankFinite_or_rankInfinite.elim (fun h ↦ iff_of_false (by simpa) M.not_rankInfinite)
    fun h ↦ iff_of_true M.not_rankFinite h

@[simp]
theorem not_rankInfinite_iff (M : Matroid α) : ¬ RankInfinite M ↔ RankFinite M := by
  rw [← not_rankFinite_iff, not_not]

theorem IsBase.sdiff_finite_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite :=
  finite_iff_finite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_finite_comm := IsBase.sdiff_finite_comm

theorem IsBase.sdiff_infinite_comm (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂) :
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite :=
  infinite_iff_infinite_of_encard_eq_encard (hB₁.encard_sdiff_comm hB₂)

@[deprecated (since := "2026-06-03")] alias IsBase.diff_infinite_comm := IsBase.sdiff_infinite_comm

theorem ext_isBase {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃B⦄, B ⊆ M₁.E → (M₁.IsBase B ↔ M₂.IsBase B)) : M₁ = M₂ := by
  have h' : ∀ B, M₁.IsBase B ↔ M₂.IsBase B :=
    fun B ↦ ⟨fun hB ↦ (h hB.subset_ground).1 hB,
      fun hB ↦ (h <| hB.subset_ground.trans_eq hE.symm).2 hB⟩
  ext <;> simp [hE, M₁.indep_iff', M₂.indep_iff', h']

theorem ext_iff_isBase {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ ⦃B⦄, B ⊆ M₁.E → (M₁.IsBase B ↔ M₂.IsBase B) :=
  ⟨fun h ↦ by simp [h], fun ⟨hE, h⟩ ↦ ext_isBase hE h⟩

theorem isBase_compl_iff_maximal_disjoint_isBase (hB : B ⊆ M.E := by aesop_mat) :
    M.IsBase (M.E \ B) ↔ Maximal (fun I ↦ I ⊆ M.E ∧ ∃ B, M.IsBase B ∧ Disjoint I B) B := by
  simp_rw [maximal_iff, and_iff_right hB, and_imp, forall_exists_index]
  refine ⟨fun h ↦ ⟨⟨_, h, disjoint_sdiff_right⟩,
    fun I hI B' ⟨hB', hIB'⟩ hBI ↦ hBI.antisymm ?_⟩, fun ⟨⟨B', hB', hBB'⟩,h⟩ ↦ ?_⟩
  · rw [hB'.eq_of_subset_isBase h, ← subset_compl_iff_disjoint_right, sdiff_eq, compl_inter,
      compl_compl] at hIB'
    · exact fun e he ↦ (hIB' he).elim (fun h' ↦ (h' (hI he)).elim) id
    rw [subset_sdiff, and_iff_right hB'.subset_ground, disjoint_comm]
    exact disjoint_of_subset_left hBI hIB'
  rw [h sdiff_subset B' ⟨hB', disjoint_sdiff_left⟩]
  · simpa [hB'.subset_ground]
  simp [subset_sdiff, hB, hBB']

end IsBase
section dep_indep

/-- A subset of `M.E` is `Dep`endent if it is not `Indep`endent . -/
def Dep (M : Matroid α) (D : Set α) : Prop := ¬M.Indep D ∧ D ⊆ M.E

variable {B B' I J D X : Set α} {e f : α}

theorem indep_iff : M.Indep I ↔ ∃ B, M.IsBase B ∧ I ⊆ B :=
  M.indep_iff' (I := I)

set_option backward.isDefEq.respectTransparency false in
theorem setOf_indep_eq (M : Matroid α) : {I | M.Indep I} = lowerClosure ({B | M.IsBase B}) := by
  simp_rw [indep_iff, lowerClosure, LowerSet.coe_mk, mem_setOf]

theorem Indep.exists_isBase_superset (hI : M.Indep I) : ∃ B, M.IsBase B ∧ I ⊆ B :=
  indep_iff.1 hI

theorem dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D ⊆ M.E := Iff.rfl

theorem setOf_dep_eq (M : Matroid α) : {D | M.Dep D} = {I | M.Indep I}ᶜ ∩ Iic M.E := rfl

@[aesop unsafe 30% (rule_sets := [Matroid])]
theorem Indep.subset_ground (hI : M.Indep I) : I ⊆ M.E := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
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
  obtain ⟨B, hB, hJB⟩ := hJ.exists_isBase_superset
  exact indep_iff.2 ⟨B, hB, hIJ.trans hJB⟩

theorem Dep.superset (hD : M.Dep D) (hDX : D ⊆ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  dep_of_not_indep (fun hI ↦ (hI.subset hDX).not_dep hD)

theorem IsBase.indep (hB : M.IsBase B) : M.Indep B :=
  indep_iff.2 ⟨B, hB, subset_rfl⟩

@[simp] theorem empty_indep (M : Matroid α) : M.Indep ∅ :=
  Exists.elim M.exists_isBase (fun _ hB ↦ hB.indep.subset (empty_subset _))

theorem Dep.nonempty (hD : M.Dep D) : D.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hD.not_indep M.empty_indep

theorem Indep.finite [RankFinite M] (hI : M.Indep I) : I.Finite :=
  let ⟨_, hB, hIB⟩ := hI.exists_isBase_superset
  hB.finite.subset hIB

theorem Indep.rankPos_of_nonempty (hI : M.Indep I) (hne : I.Nonempty) : M.RankPos := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact hB.rankPos_of_nonempty (hne.mono hIB)

theorem Indep.inter_right (hI : M.Indep I) (X : Set α) : M.Indep (I ∩ X) :=
  hI.subset inter_subset_left

theorem Indep.inter_left (hI : M.Indep I) (X : Set α) : M.Indep (X ∩ I) :=
  hI.subset inter_subset_right

theorem Indep.sdiff (hI : M.Indep I) (X : Set α) : M.Indep (I \ X) :=
  hI.subset sdiff_subset

@[deprecated (since := "2026-06-03")] alias Indep.diff := Indep.sdiff

theorem IsBase.eq_of_subset_indep (hB : M.IsBase B) (hI : M.Indep I) (hBI : B ⊆ I) : B = I :=
  let ⟨B', hB', hB'I⟩ := hI.exists_isBase_superset
  hBI.antisymm (by rwa [hB.eq_of_subset_isBase hB' (hBI.trans hB'I)])

theorem isBase_iff_maximal_indep : M.IsBase B ↔ Maximal M.Indep B := by
  rw [maximal_subset_iff]
  refine ⟨fun h ↦ ⟨h.indep, fun _ ↦ h.eq_of_subset_indep⟩, fun ⟨h, h'⟩ ↦ ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_superset
  rwa [h' hB'.indep hBB']

theorem Indep.isBase_of_maximal (hI : M.Indep I) (h : ∀ ⦃J⦄, M.Indep J → I ⊆ J → I = J) :
    M.IsBase I := by
  rwa [isBase_iff_maximal_indep, maximal_subset_iff, and_iff_right hI]

theorem IsBase.dep_of_ssubset (hB : M.IsBase B) (h : B ⊂ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Dep X :=
  ⟨fun hX ↦ h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩

theorem IsBase.dep_of_insert (hB : M.IsBase B) (heB : e ∉ B) (he : e ∈ M.E := by aesop_mat) :
    M.Dep (insert e B) := hB.dep_of_ssubset (ssubset_insert heB) (insert_subset he hB.subset_ground)

theorem IsBase.mem_of_insert_indep (hB : M.IsBase B) (heB : M.Indep (insert e B)) : e ∈ B :=
  by_contra fun he ↦ (hB.dep_of_insert he (heB.subset_ground (mem_insert _ _))).not_indep heB

/-- If the difference of two IsBases is a singleton, then they differ by an insertion/removal -/
theorem IsBase.eq_exchange_of_sdiff_eq_singleton (hB : M.IsBase B) (hB' : M.IsBase B')
    (h : B \ B' = {e}) : ∃ f ∈ B' \ B, B' = (insert f B) \ {e} := by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f ≠ e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_sdiff_singleton_comm hne] at hb
  refine ⟨f, hf, (hb.eq_of_subset_isBase hB' ?_).symm⟩
  rw [sdiff_subset_iff, insert_subset_iff, union_comm, ← sdiff_subset_iff, h,
    and_iff_left rfl.subset]
  exact Or.inl hf.1

@[deprecated (since := "2026-06-03")]
alias IsBase.eq_exchange_of_diff_eq_singleton := IsBase.eq_exchange_of_sdiff_eq_singleton

theorem IsBase.exchange_isBase_of_indep (hB : M.IsBase B) (hf : f ∉ B)
    (hI : M.Indep (insert f (B \ {e}))) : M.IsBase (insert f (B \ {e})) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hcard := hB'.encard_sdiff_comm hB
  rw [insert_subset_iff, ← sdiff_eq_empty, sdiff_sdiff_comm, sdiff_eq_empty,
    subset_singleton_iff_eq] at hIB'
  obtain ⟨hfB, (h | h)⟩ := hIB'
  · rw [h, encard_empty, encard_eq_zero, eq_empty_iff_forall_notMem] at hcard
    exact (hcard f ⟨hfB, hf⟩).elim
  rw [h, encard_singleton, encard_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  obtain (rfl : f = x) := hx.subset ⟨hfB, hf⟩
  simp_rw [← h, ← singleton_union, ← hx, _root_.sdiff_sdiff_right_self, inf_eq_inter, inter_comm B,
    sdiff_union_inter]
  exact hB'

theorem IsBase.exchange_isBase_of_indep' (hB : M.IsBase B) (he : e ∈ B) (hf : f ∉ B)
    (hI : M.Indep (insert f B \ {e})) : M.IsBase (insert f B \ {e}) := by
  have hfe : f ≠ e := ne_of_mem_of_not_mem he hf |>.symm
  rw [← insert_sdiff_singleton_comm hfe] at *
  exact hB.exchange_isBase_of_indep hf hI

lemma insert_isBase_of_insert_indep {M : Matroid α} {I : Set α} {e f : α}
    (he : e ∉ I) (hf : f ∉ I) (heI : M.IsBase (insert e I)) (hfI : M.Indep (insert f I)) :
    M.IsBase (insert f I) := by
  obtain rfl | hef := eq_or_ne e f
  · assumption
  simpa [sdiff_singleton_eq_self he, hfI]
    using heI.exchange_isBase_of_indep (e := e) (f := f) (by simp [hef.symm, hf])

theorem IsBase.insert_dep (hB : M.IsBase B) (h : e ∈ M.E \ B) : M.Dep (insert e B) := by
  rw [← not_indep_iff (insert_subset h.1 hB.subset_ground)]
  exact h.2 ∘ (fun hi ↦ insert_eq_self.mp (hB.eq_of_subset_indep hi (subset_insert e B)).symm)

theorem Indep.exists_insert_of_not_isBase (hI : M.Indep I) (hI' : ¬M.IsBase I) (hB : M.IsBase B) :
    ∃ e ∈ B \ I, M.Indep (insert e I) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by (rintro rfl; exact hI' hB')))
  by_cases hxB : x ∈ B
  · exact ⟨x, ⟨hxB, hx⟩, hB'.indep.subset (insert_subset hxB' hIB')⟩
  obtain ⟨e, he, hBase⟩ := hB'.exchange hB ⟨hxB', hxB⟩
  exact ⟨e, ⟨he.1, notMem_subset hIB' he.2⟩,
    indep_iff.2 ⟨_, hBase, insert_subset_insert (subset_sdiff_singleton hIB' hx)⟩⟩

/-- This is the same as `Indep.exists_insert_of_not_isBase`, but phrased so that
  it is defeq to the augmentation axiom for independent sets. -/
theorem Indep.exists_insert_of_not_maximal (M : Matroid α) ⦃I B : Set α⦄ (hI : M.Indep I)
    (hInotmax : ¬ Maximal M.Indep I) (hB : Maximal M.Indep B) :
    ∃ x ∈ B \ I, M.Indep (insert x I) := by
  simp only [maximal_subset_iff, hI, not_and, not_forall, exists_prop, true_imp_iff] at hB hInotmax
  refine hI.exists_insert_of_not_isBase (fun hIb ↦ ?_) ?_
  · obtain ⟨I', hII', hI', hne⟩ := hInotmax
    exact hne <| hIb.eq_of_subset_indep hII' hI'
  exact hB.1.isBase_of_maximal fun J hJ hBJ ↦ hB.2 hJ hBJ

theorem Indep.isBase_of_forall_insert (hB : M.Indep B)
    (hBmax : ∀ e ∈ M.E \ B, ¬ M.Indep (insert e B)) : M.IsBase B := by
  by_contra hnb
  obtain ⟨B', hB'⟩ := M.exists_isBase
  obtain ⟨e, he, h⟩ := hB.exists_insert_of_not_isBase hnb hB'
  exact hBmax e ⟨hB'.subset_ground he.1, he.2⟩ h

theorem ground_indep_iff_isBase : M.Indep M.E ↔ M.IsBase M.E :=
  ⟨fun h ↦ h.isBase_of_maximal (fun _ hJ hEJ ↦ hEJ.antisymm hJ.subset_ground), IsBase.indep⟩

theorem IsBase.exists_insert_of_ssubset (hB : M.IsBase B) (hIB : I ⊂ B) (hB' : M.IsBase B') :
    ∃ e ∈ B' \ I, M.Indep (insert e I) :=
  (hB.indep.subset hIB.subset).exists_insert_of_not_isBase
    (fun hI ↦ hIB.ne (hI.eq_of_subset_isBase hB hIB.subset)) hB'

@[ext] theorem ext_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃I⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) : M₁ = M₂ :=
  have h' : M₁.Indep = M₂.Indep := by
    ext I
    by_cases hI : I ⊆ M₁.E
    · rwa [h]
    exact iff_of_false (fun hi ↦ hI hi.subset_ground)
      (fun hi ↦ hI (hi.subset_ground.trans_eq hE.symm))
  ext_isBase hE (fun B _ ↦ by simp_rw [isBase_iff_maximal_indep, h'])

theorem ext_iff_indep {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ ⦃I⦄, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I) :=
  ⟨fun h ↦ by (subst h; simp), fun h ↦ ext_indep h.1 h.2⟩

/-- If every base of `M₁` is independent in `M₂` and vice versa, then `M₁ = M₂`. -/
lemma ext_isBase_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hM₁ : ∀ ⦃B⦄, M₁.IsBase B → M₂.Indep B) (hM₂ : ∀ ⦃B⦄, M₂.IsBase B → M₁.Indep B) : M₁ = M₂ := by
  refine ext_indep hE fun I hIE ↦ ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
    exact (hM₁ hB).subset hIB
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact (hM₂ hB).subset hIB

/-- A `Finitary` matroid is one where a set is independent if and only if it all
  its finite subsets are independent, or equivalently a matroid whose circuits are finite. -/
@[mk_iff] class Finitary (M : Matroid α) : Prop where
  /-- `I` is independent if all its finite subsets are independent. -/
  indep_of_forall_finite : ∀ I, (∀ J, J ⊆ I → J.Finite → M.Indep J) → M.Indep I

theorem indep_of_forall_finite_subset_indep {M : Matroid α} [Finitary M] (I : Set α)
    (h : ∀ J, J ⊆ I → J.Finite → M.Indep J) : M.Indep I :=
  Finitary.indep_of_forall_finite I h

theorem indep_iff_forall_finite_subset_indep {M : Matroid α} [Finitary M] :
    M.Indep I ↔ ∀ J, J ⊆ I → J.Finite → M.Indep J :=
  ⟨fun h _ hJI _ ↦ h.subset hJI, Finitary.indep_of_forall_finite I⟩

instance finitary_of_rankFinite {M : Matroid α} [RankFinite M] : Finitary M where
  indep_of_forall_finite I hI := by
    refine I.finite_or_infinite.elim (hI _ Subset.rfl) (fun h ↦ False.elim ?_)
    obtain ⟨B, hB⟩ := M.exists_isBase
    obtain ⟨I₀, hI₀I, hI₀fin, hI₀card⟩ := h.exists_subset_ncard_eq (B.ncard + 1)
    obtain ⟨B', hB', hI₀B'⟩ := (hI _ hI₀I hI₀fin).exists_isBase_superset
    have hle := ncard_le_ncard hI₀B' hB'.finite
    rw [hI₀card, hB'.ncard_eq_ncard_of_isBase hB, Nat.add_one_le_iff] at hle
    exact hle.ne rfl

/-- Matroids obey the maximality axiom -/
theorem existsMaximalSubsetProperty_indep (M : Matroid α) :
    ∀ X, X ⊆ M.E → ExistsMaximalSubsetProperty M.Indep X :=
  M.maximality

end dep_indep

section copy

/-- create a copy of `M : Matroid α` with independence and base predicates and ground set defeq
to supplied arguments that are provably equal to those of `M`. -/
@[simps] def copy (M : Matroid α) (E : Set α) (IsBase Indep : Set α → Prop) (hE : E = M.E)
    (hB : ∀ B, IsBase B ↔ M.IsBase B) (hI : ∀ I, Indep I ↔ M.Indep I) : Matroid α where
  E := E
  IsBase := IsBase
  Indep := Indep
  indep_iff' _ := by simp_rw [hI, hB, M.indep_iff]
  exists_isBase := by
    simp_rw [hB]
    exact M.exists_isBase
  isBase_exchange := by
    simp_rw [show IsBase = M.IsBase from funext (by simp [hB])]
    exact M.isBase_exchange
  maximality := by
    simp_rw [hE, show Indep = M.Indep from funext (by simp [hI])]
    exact M.maximality
  subset_ground := by
    simp_rw [hE, hB]
    exact M.subset_ground

/-- create a copy of `M : Matroid α` with an independence predicate and ground set defeq
to supplied arguments that are provably equal to those of `M`. -/
@[simps!] def copyIndep (M : Matroid α) (E : Set α) (Indep : Set α → Prop)
    (hE : E = M.E) (h : ∀ I, Indep I ↔ M.Indep I) : Matroid α :=
  M.copy E M.IsBase Indep hE (fun _ ↦ Iff.rfl) h

/-- create a copy of `M : Matroid α` with a base predicate and ground set defeq
to supplied arguments that are provably equal to those of `M`. -/
@[simps!] def copyBase (M : Matroid α) (E : Set α) (IsBase : Set α → Prop)
    (hE : E = M.E) (h : ∀ B, IsBase B ↔ M.IsBase B) : Matroid α :=
  M.copy E IsBase M.Indep hE h (fun _ ↦ Iff.rfl)

end copy

section IsBasis

/-- A Basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'Basis' is used to refer to what we call a 'Base'). -/
def IsBasis (M : Matroid α) (I X : Set α) : Prop :=
  Maximal (fun A ↦ M.Indep A ∧ A ⊆ X) I ∧ X ⊆ M.E

/-- `Matroid.IsBasis' I X` is the same as `Matroid.IsBasis I X`,
without the requirement that `X ⊆ M.E`. This is convenient for some
API building, especially when working with rank and closure. -/
def IsBasis' (M : Matroid α) (I X : Set α) : Prop :=
  Maximal (fun A ↦ M.Indep A ∧ A ⊆ X) I

variable {B I J X Y : Set α} {e : α}

theorem IsBasis'.indep (hI : M.IsBasis' I X) : M.Indep I :=
  hI.1.1

theorem IsBasis.indep (hI : M.IsBasis I X) : M.Indep I :=
  hI.1.1.1

theorem IsBasis.subset (hI : M.IsBasis I X) : I ⊆ X :=
  hI.1.1.2

theorem IsBasis.isBasis' (hI : M.IsBasis I X) : M.IsBasis' I X :=
  hI.1

theorem IsBasis'.isBasis (hI : M.IsBasis' I X) (hX : X ⊆ M.E := by aesop_mat) : M.IsBasis I X :=
  ⟨hI, hX⟩

theorem IsBasis'.subset (hI : M.IsBasis' I X) : I ⊆ X :=
  hI.1.2


@[aesop unsafe 15% (rule_sets := [Matroid])]
theorem IsBasis.subset_ground (hI : M.IsBasis I X) : X ⊆ M.E :=
  hI.2

theorem IsBasis.isBasis_inter_ground (hI : M.IsBasis I X) : M.IsBasis I (X ∩ M.E) := by
  convert! hI
  rw [inter_eq_self_of_subset_left hI.subset_ground]

@[aesop unsafe 15% (rule_sets := [Matroid])]
theorem IsBasis.left_subset_ground (hI : M.IsBasis I X) : I ⊆ M.E :=
  hI.indep.subset_ground

theorem IsBasis.eq_of_subset_indep (hI : M.IsBasis I X) (hJ : M.Indep J) (hIJ : I ⊆ J)
    (hJX : J ⊆ X) : I = J :=
  hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

theorem IsBasis.Finite (hI : M.IsBasis I X) [RankFinite M] : I.Finite := hI.indep.finite

theorem isBasis_iff' :
    M.IsBasis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ ⦃J⦄, M.Indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.E := by
  rw [IsBasis, maximal_subset_iff]
  tauto

theorem isBasis_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ J, M.Indep J → I ⊆ J → J ⊆ X → I = J) := by
  rw [isBasis_iff', and_iff_left hX]

theorem isBasis'_iff_isBasis_inter_ground : M.IsBasis' I X ↔ M.IsBasis I (X ∩ M.E) := by
  rw [IsBasis', IsBasis, and_iff_left inter_subset_right, maximal_iff_maximal_of_imp_of_forall]
  · exact fun I hI ↦ ⟨hI.1, hI.2.trans inter_subset_left⟩
  exact fun I hI ↦ ⟨I, rfl.le, hI.1, subset_inter hI.2 hI.1.subset_ground⟩

theorem isBasis'_iff_isBasis (hX : X ⊆ M.E := by aesop_mat) : M.IsBasis' I X ↔ M.IsBasis I X := by
  rw [isBasis'_iff_isBasis_inter_ground, inter_eq_self_of_subset_left hX]

theorem isBasis_iff_isBasis'_subset_ground : M.IsBasis I X ↔ M.IsBasis' I X ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.isBasis', h.subset_ground⟩, fun h ↦ (isBasis'_iff_isBasis h.2).mp h.1⟩

theorem IsBasis'.isBasis_inter_ground (hIX : M.IsBasis' I X) : M.IsBasis I (X ∩ M.E) :=
  isBasis'_iff_isBasis_inter_ground.mp hIX

theorem IsBasis'.eq_of_subset_indep (hI : M.IsBasis' I X) (hJ : M.Indep J) (hIJ : I ⊆ J)
    (hJX : J ⊆ X) : I = J :=
  hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)

theorem IsBasis'.insert_not_indep (hI : M.IsBasis' I X) (he : e ∈ X \ I) : ¬ M.Indep (insert e I) :=
  fun hi ↦ he.2 <| insert_eq_self.1 <| Eq.symm <|
    hI.eq_of_subset_indep hi (subset_insert _ _) (insert_subset he.1 hI.subset)

theorem isBasis_iff_maximal (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ Maximal (fun I ↦ M.Indep I ∧ I ⊆ X) I := by
  rw [IsBasis, and_iff_left hX]

theorem Indep.isBasis_of_maximal_subset (hI : M.Indep I) (hIX : I ⊆ X)
    (hmax : ∀ ⦃J⦄, M.Indep J → I ⊆ J → J ⊆ X → J ⊆ I) (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X := by
  rw [isBasis_iff (by aesop_mat : X ⊆ M.E), and_iff_right hI, and_iff_right hIX]
  exact fun J hJ hIJ hJX ↦ hIJ.antisymm (hmax hJ hIJ hJX)

theorem IsBasis.isBasis_subset (hI : M.IsBasis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) :
    M.IsBasis I Y := by
  rw [isBasis_iff (hYX.trans hI.subset_ground), and_iff_right hI.indep, and_iff_right hIY]
  exact fun J hJ hIJ hJY ↦ hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX)

@[simp] theorem isBasis_self_iff_indep : M.IsBasis I I ↔ M.Indep I := by
  rw [isBasis_iff', and_iff_right rfl.subset, and_assoc, and_iff_left_iff_imp]
  exact fun hi ↦ ⟨fun _ _ ↦ subset_antisymm, hi.subset_ground⟩

theorem Indep.isBasis_self (h : M.Indep I) : M.IsBasis I I :=
  isBasis_self_iff_indep.mpr h

@[simp] theorem isBasis_empty_iff (M : Matroid α) : M.IsBasis I ∅ ↔ I = ∅ :=
  ⟨fun h ↦ subset_empty_iff.mp h.subset, fun h ↦ by (rw [h]; exact M.empty_indep.isBasis_self)⟩

theorem IsBasis.dep_of_ssubset (hI : M.IsBasis I X) (hIY : I ⊂ Y) (hYX : Y ⊆ X) : M.Dep Y := by
  have : X ⊆ M.E := hI.subset_ground
  rw [← not_indep_iff]
  exact fun hY ↦ hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)

theorem IsBasis.insert_dep (hI : M.IsBasis I X) (he : e ∈ X \ I) : M.Dep (insert e I) :=
  hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset he.1 hI.subset)

theorem IsBasis.mem_of_insert_indep (hI : M.IsBasis I X) (he : e ∈ X) (hIe : M.Indep (insert e I)) :
    e ∈ I :=
  by_contra (fun heI ↦ (hI.insert_dep ⟨he, heI⟩).not_indep hIe)

theorem IsBasis'.mem_of_insert_indep (hI : M.IsBasis' I X) (he : e ∈ X)
    (hIe : M.Indep (insert e I)) : e ∈ I :=
  hI.isBasis_inter_ground.mem_of_insert_indep ⟨he, hIe.subset_ground (mem_insert _ _)⟩ hIe

theorem IsBasis.not_isBasis_of_ssubset (hI : M.IsBasis I X) (hJI : J ⊂ I) : ¬ M.IsBasis J X :=
  fun h ↦ hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

theorem Indep.subset_isBasis_of_subset (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : X ⊆ M.E := by aesop_mat) : ∃ J, M.IsBasis J X ∧ I ⊆ J := by
  obtain ⟨J, hJ, hJmax⟩ := M.maximality X hX I hI hIX
  exact ⟨J, ⟨hJmax, hX⟩, hJ⟩

theorem Indep.subset_isBasis'_of_subset (hI : M.Indep I) (hIX : I ⊆ X) :
    ∃ J, M.IsBasis' J X ∧ I ⊆ J := by
  simp_rw [isBasis'_iff_isBasis_inter_ground]
  exact hI.subset_isBasis_of_subset (subset_inter hIX hI.subset_ground)

theorem exists_isBasis (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I, M.IsBasis I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis_of_subset (empty_subset X)
  ⟨_, hI⟩

theorem exists_isBasis' (M : Matroid α) (X : Set α) : ∃ I, M.IsBasis' I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_isBasis'_of_subset (empty_subset X)
  ⟨_, hI⟩

theorem exists_isBasis_subset_isBasis (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    ∃ I J, M.IsBasis I X ∧ M.IsBasis J Y ∧ I ⊆ J := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩

theorem IsBasis.exists_isBasis_inter_eq_of_superset (hI : M.IsBasis I X) (hXY : X ⊆ Y)
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ J, M.IsBasis J Y ∧ J ∩ X = I := by
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans hXY)
  refine ⟨J, hJ, subset_antisymm ?_ (subset_inter hIJ hI.subset)⟩
  exact fun e he ↦ hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset he.1 hIJ))

theorem exists_isBasis_union_inter_isBasis (M : Matroid α) (X Y : Set α)
    (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    ∃ I, M.IsBasis I (X ∪ Y) ∧ M.IsBasis (I ∩ Y) Y :=
  let ⟨J, hJ⟩ := M.exists_isBasis Y
  (hJ.exists_isBasis_inter_eq_of_superset subset_union_right).imp
  (fun I hI ↦ ⟨hI.1, by rwa [hI.2]⟩)

theorem Indep.eq_of_isBasis (hI : M.Indep I) (hJ : M.IsBasis J I) : J = I :=
  hJ.eq_of_subset_indep hI hJ.subset rfl.subset

theorem IsBasis.exists_isBase (hI : M.IsBasis I X) : ∃ B, M.IsBase B ∧ I = B ∩ X :=
  let ⟨B,hB, hIB⟩ := hI.indep.exists_isBase_superset
  ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset)
    (by rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    inter_subset_right])⟩

@[simp] theorem isBasis_ground_iff : M.IsBasis B M.E ↔ M.IsBase B := by
  rw [IsBasis, and_iff_left rfl.subset, isBase_iff_maximal_indep,
    maximal_and_iff_right_of_imp (fun _ h ↦ h.subset_ground),
    and_iff_left_of_imp (fun h ↦ h.1.subset_ground)]

theorem IsBase.isBasis_ground (hB : M.IsBase B) : M.IsBasis B M.E :=
  isBasis_ground_iff.mpr hB

theorem Indep.isBasis_iff_forall_insert_dep (hI : M.Indep I) (hIX : I ⊆ X) :
    M.IsBasis I X ↔ ∀ e ∈ X \ I, M.Dep (insert e I) := by
  rw [IsBasis, maximal_iff_forall_insert (fun I J hI hIJ ↦ ⟨hI.1.subset hIJ, hIJ.trans hI.2⟩)]
  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, mem_sdiff, and_imp,
    Dep, hI.subset_ground]
  exact ⟨fun h e heX heI ↦ ⟨fun hi ↦ h.1 e heI hi heX, h.2 heX⟩,
    fun h ↦ ⟨fun e heI hi heX ↦ (h e heX heI).1 hi,
      fun e heX ↦ (em (e ∈ I)).elim (fun h ↦ hI.subset_ground h) fun heI ↦ (h _ heX heI).2 ⟩⟩

theorem Indep.isBasis_of_forall_insert (hI : M.Indep I) (hIX : I ⊆ X)
    (he : ∀ e ∈ X \ I, M.Dep (insert e I)) : M.IsBasis I X :=
  (hI.isBasis_iff_forall_insert_dep hIX).mpr he

theorem Indep.isBasis_insert_iff (hI : M.Indep I) :
    M.IsBasis I (insert e I) ↔ M.Dep (insert e I) ∨ e ∈ I := by
  simp_rw [hI.isBasis_iff_forall_insert_dep (subset_insert _ _), dep_iff, insert_subset_iff,
    and_iff_left hI.subset_ground, mem_sdiff, mem_insert_iff, or_and_right, and_not_self,
    or_false, and_imp, forall_eq]
  tauto

theorem IsBasis.iUnion_isBasis_iUnion {ι : Type _} (X I : ι → Set α)
    (hI : ∀ i, M.IsBasis (I i) (X i)) (h_ind : M.Indep (⋃ i, I i)) :
    M.IsBasis (⋃ i, I i) (⋃ i, X i) := by
  refine h_ind.isBasis_of_forall_insert
    (iUnion_subset (fun i ↦ (hI i).subset.trans (subset_iUnion _ _))) ?_
  rintro e ⟨⟨_, ⟨⟨i, hi, rfl⟩, (hes : e ∈ X i)⟩⟩, he'⟩
  rw [mem_iUnion, not_exists] at he'
  refine ((hI i).insert_dep ⟨hes, he' _⟩).superset (insert_subset_insert (subset_iUnion _ _)) ?_
  rw [insert_subset_iff, iUnion_subset_iff, and_iff_left (fun i ↦ (hI i).indep.subset_ground)]
  exact (hI i).subset_ground hes

theorem IsBasis.isBasis_iUnion {ι : Type _} [Nonempty ι] (X : ι → Set α)
    (hI : ∀ i, M.IsBasis I (X i)) : M.IsBasis I (⋃ i, X i) := by
  convert! IsBasis.iUnion_isBasis_iUnion X (fun _ ↦ I) (fun i ↦ hI i) _ <;> rw [iUnion_const]
  exact (hI (Classical.arbitrary ι)).indep

theorem IsBasis.isBasis_sUnion {Xs : Set (Set α)} (hne : Xs.Nonempty)
    (h : ∀ X ∈ Xs, M.IsBasis I X) : M.IsBasis I (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion]
  have := Iff.mpr nonempty_coe_sort hne
  exact IsBasis.isBasis_iUnion _ fun X ↦ h X X.prop

theorem Indep.isBasis_setOf_insert_isBasis (hI : M.Indep I) :
    M.IsBasis I {x | M.IsBasis I (insert x I)} := by
  refine hI.isBasis_of_forall_insert (fun e he ↦ (?_ : M.IsBasis _ _))
    (fun e he ↦ ⟨fun hu ↦ he.2 ?_, he.1.subset_ground⟩)
  · rw [insert_eq_of_mem he]; exact hI.isBasis_self
  simpa using (hu.eq_of_isBasis he.1).symm

theorem IsBasis.union_isBasis_union (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y)
    (h : M.Indep (I ∪ J)) : M.IsBasis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  refine IsBasis.iUnion_isBasis_iUnion _ _ ?_ ?_
  · simp only [Bool.forall_bool, cond_false, cond_true]; exact ⟨hJY, hIX⟩
  rwa [← union_eq_iUnion]

theorem IsBasis.isBasis_union (hIX : M.IsBasis I X) (hIY : M.IsBasis I Y) :
    M.IsBasis I (X ∪ Y) := by
  convert! hIX.union_isBasis_union hIY _ <;> rw [union_self]; exact hIX.indep

theorem IsBasis.isBasis_union_of_subset (hI : M.IsBasis I X) (hJ : M.Indep J) (hIJ : I ⊆ J) :
    M.IsBasis J (J ∪ X) := by
  convert! hJ.isBasis_self.union_isBasis_union hI _ <;>
  rw [union_eq_self_of_subset_right hIJ]
  assumption

theorem IsBasis.insert_isBasis_insert (hI : M.IsBasis I X) (h : M.Indep (insert e I)) :
    M.IsBasis (insert e I) (insert e X) := by
  simp_rw [← union_singleton] at *
  exact hI.union_isBasis_union (h.subset subset_union_right).isBasis_self h

theorem IsBase.isBase_of_isBasis_superset (hB : M.IsBase B) (hBX : B ⊆ X) (hIX : M.IsBasis I X) :
    M.IsBase I := by
  by_contra h
  obtain ⟨e, heBI, he⟩ := hIX.indep.exists_insert_of_not_isBase h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)

theorem Indep.exists_isBase_subset_union_isBase (hI : M.Indep I) (hB : M.IsBase B) :
    ∃ B', M.IsBase B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B := by
  obtain ⟨B', hB', hIB'⟩ := hI.subset_isBasis_of_subset <| subset_union_left (t := B)
  exact ⟨B', hB.isBase_of_isBasis_superset subset_union_right hB', hIB', hB'.subset⟩

theorem IsBasis.inter_eq_of_subset_indep (hIX : M.IsBasis I X) (hIJ : I ⊆ J) (hJ : M.Indep J) :
    J ∩ X = I :=
(subset_inter hIJ hIX.subset).antisymm'
  (fun _ he ↦ hIX.mem_of_insert_indep he.2 (hJ.subset (insert_subset he.1 hIJ)))

theorem IsBasis'.inter_eq_of_subset_indep (hI : M.IsBasis' I X) (hIJ : I ⊆ J) (hJ : M.Indep J) :
    J ∩ X = I := by
  rw [← hI.isBasis_inter_ground.inter_eq_of_subset_indep hIJ hJ, inter_comm X, ← inter_assoc,
    inter_eq_self_of_subset_left hJ.subset_ground]

theorem IsBase.isBasis_of_subset (hX : X ⊆ M.E := by aesop_mat) (hB : M.IsBase B) (hBX : B ⊆ X) :
    M.IsBasis B X := by
  rw [isBasis_iff, and_iff_right hB.indep, and_iff_right hBX]
  exact fun J hJ hBJ _ ↦ hB.eq_of_subset_indep hJ hBJ

theorem exists_isBasis_disjoint_isBasis_of_subset (M : Matroid α) {X Y : Set α} (hXY : X ⊆ Y)
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ I J, M.IsBasis I X ∧ M.IsBasis (I ∪ J) Y ∧ Disjoint X J := by
  obtain ⟨I, I', hI, hI', hII'⟩ := M.exists_isBasis_subset_isBasis hXY
  refine ⟨I, I' \ I, hI, by rwa [union_sdiff_self, union_eq_self_of_subset_left hII'], ?_⟩
  rw [disjoint_iff_forall_ne]
  rintro e heX _ ⟨heI', heI⟩ rfl
  exact heI <| hI.mem_of_insert_indep heX (hI'.indep.subset (insert_subset heI' hII'))

end IsBasis

section Finite

/-- For finite `E`, finitely many matroids have ground set contained in `E`. -/
theorem finite_setOf_matroid {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E ⊆ E}.Finite := by
  set f : Matroid α → Set α × (Set (Set α)) := fun M ↦ ⟨M.E, {B | M.IsBase B}⟩
  have hf : f.Injective := by
    refine fun M M' hMM' ↦ ?_
    rw [Prod.mk.injEq, and_comm, Set.ext_iff, and_comm] at hMM'
    exact ext_isBase hMM'.1 (fun B _ ↦ hMM'.2 B)
  rw [← Set.finite_image_iff hf.injOn]
  refine (hE.finite_subsets.prod hE.finite_subsets.finite_subsets).subset ?_
  rintro _ ⟨M, hE : M.E ⊆ E, rfl⟩
  simp only [Set.mem_prod, Set.mem_setOf_eq]
  exact ⟨hE, fun B hB ↦ hB.subset_ground.trans hE⟩

/-- For finite `E`, finitely many matroids have ground set `E`. -/
theorem finite_setOf_matroid' {E : Set α} (hE : E.Finite) : {M : Matroid α | M.E = E}.Finite :=
  (finite_setOf_matroid hE).subset (fun M ↦ by rintro rfl; exact subset_refl M.E)

end Finite

end Matroid
