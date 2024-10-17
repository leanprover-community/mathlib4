/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.UrysohnsLemma

/-!
# Continuous partition of unity

In this file we define `PartitionOfUnity (ι X : Type*) [TopologicalSpace X] (s : Set X := univ)`
to be a continuous partition of unity on `s` indexed by `ι`. More precisely,
`f : PartitionOfUnity ι X s` is a collection of continuous functions `f i : C(X, ℝ)`, `i : ι`,
such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* `∑ᶠ i, f i x = 1` for all `x ∈ s`;
* `∑ᶠ i, f i x ≤ 1` for all `x : X`.

In the case `s = univ` the last assumption follows from the previous one but it is convenient to
have this assumption in the case `s ≠ univ`.

We also define a bump function covering,
`BumpCovering (ι X : Type*) [TopologicalSpace X] (s : Set X := univ)`, to be a collection of
functions `f i : C(X, ℝ)`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets;
* each `f i` is nonnegative;
* for each `x ∈ s` there exists `i : ι` such that `f i y = 1` in a neighborhood of `x`.

The term is motivated by the smooth case.

If `f` is a bump function covering indexed by a linearly ordered type, then
`g i x = f i x * ∏ᶠ j < i, (1 - f j x)` is a partition of unity, see
`BumpCovering.toPartitionOfUnity`. Note that only finitely many terms `1 - f j x` are not equal
to one, so this product is well-defined.

Note that `g i x = ∏ᶠ j ≤ i, (1 - f j x) - ∏ᶠ j < i, (1 - f j x)`, so most terms in the sum
`∑ᶠ i, g i x` cancel, and we get `∑ᶠ i, g i x = 1 - ∏ᶠ i, (1 - f i x)`, and the latter product
equals zero because one of `f i x` is equal to one.

We say that a partition of unity or a bump function covering `f` is *subordinate* to a family of
sets `U i`, `i : ι`, if the closure of the support of each `f i` is included in `U i`. We use
Urysohn's Lemma to prove that a locally finite open covering of a normal topological space admits a
subordinate bump function covering (hence, a subordinate partition of unity), see
`BumpCovering.exists_isSubordinate_of_locallyFinite`. If `X` is a paracompact space, then any
open covering admits a locally finite refinement, hence it admits a subordinate bump function
covering and a subordinate partition of unity, see `BumpCovering.exists_isSubordinate`.

We also provide two slightly more general versions of these lemmas,
`BumpCovering.exists_isSubordinate_of_locallyFinite_of_prop` and
`BumpCovering.exists_isSubordinate_of_prop`, to be used later in the construction of a smooth
partition of unity.

## Implementation notes

Most (if not all) books only define a partition of unity of the whole space. However, quite a few
proofs only deal with `f i` such that `tsupport (f i)` meets a specific closed subset, and
it is easier to formalize these proofs if we don't have other functions right away.

We use `WellOrderingRel j i` instead of `j < i` in the definition of
`BumpCovering.toPartitionOfUnity` to avoid a `[LinearOrder ι]` assumption. While
`WellOrderingRel j i` is a well order, not only a strict linear order, we never use this property.

## Tags

partition of unity, bump function, Urysohn's lemma, normal space, paracompact space
-/

universe u v

open Function Set Filter Topology

noncomputable section

/-- A continuous partition of unity on a set `s : Set X` is a collection of continuous functions
`f i` such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* the functions `f i` are nonnegative;
* the sum `∑ᶠ i, f i x` is equal to one for every `x ∈ s` and is less than or equal to one
  otherwise.

If `X` is a normal paracompact space, then `PartitionOfUnity.exists_isSubordinate` guarantees
that for every open covering `U : Set (Set X)` of `s` there exists a partition of unity that is
subordinate to `U`.
-/
structure PartitionOfUnity (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collection of continuous functions underlying this partition of unity -/
  toFun : ι → C(X, ℝ)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 ≤ toFun
  /-- the functions sum up to one on `s` -/
  sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, toFun i x = 1
  /-- the functions sum up to at most one, globally -/
  sum_le_one' : ∀ x, ∑ᶠ i, toFun i x ≤ 1

/-- A `BumpCovering ι X s` is an indexed family of functions `f i`, `i : ι`, such that

* the supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there
  exists a neighborhood `U ∋ x` such that all but finitely many functions `f i` are zero on `U`;
* for all `i`, `x` we have `0 ≤ f i x ≤ 1`;
* each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`.

One of the main use cases for a `BumpCovering` is to define a `PartitionOfUnity`, see
`BumpCovering.toPartitionOfUnity`, but some proofs can directly use a `BumpCovering` instead of
a `PartitionOfUnity`.

If `X` is a normal paracompact space, then `BumpCovering.exists_isSubordinate` guarantees that for
every open covering `U : Set (Set X)` of `s` there exists a `BumpCovering` of `s` that is
subordinate to `U`.
-/
structure BumpCovering (ι X : Type*) [TopologicalSpace X] (s : Set X := univ) where
  /-- The collections of continuous functions underlying this bump covering -/
  toFun : ι → C(X, ℝ)
  /-- the supports of the underlying functions are a locally finite family of sets -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- the functions are non-negative -/
  nonneg' : 0 ≤ toFun
  /-- the functions are each at most one -/
  le_one' : toFun ≤ 1
  /-- Each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`. -/
  eventuallyEq_one' : ∀ x ∈ s, ∃ i, toFun i =ᶠ[𝓝 x] 1

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

namespace PartitionOfUnity

variable {E : Type*} [AddCommMonoid E] [SMulWithZero ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  {s : Set X} (f : PartitionOfUnity ι X s)

instance : FunLike (PartitionOfUnity ι X s) ι C(X, ℝ) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

theorem locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure

theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

theorem sum_eq_one {x : X} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx

/-- If `f` is a partition of unity on `s`, then for every `x ∈ s` there exists an index `i` such
that `0 < f i x`. -/
theorem exists_pos {x : X} (hx : x ∈ s) : ∃ i, 0 < f i x := by
  have H := f.sum_eq_one hx
  contrapose! H
  simpa only [fun i => (H i).antisymm (f.nonneg i x), finsum_zero] using zero_ne_one

theorem sum_le_one (x : X) : ∑ᶠ i, f i x ≤ 1 :=
  f.sum_le_one' x

theorem sum_nonneg (x : X) : 0 ≤ ∑ᶠ i, f i x :=
  finsum_nonneg fun i => f.nonneg i x

theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  (single_le_finsum i (f.locallyFinite.point_finite x) fun j => f.nonneg j x).trans (f.sum_le_one x)

section finsupport

variable {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)

/-- The support of a partition of unity at a point `x₀` as a `Finset`.
  This is the set of `i : ι` such that `x₀ ∈ support f i`, i.e. `f i ≠ x₀`. -/
def finsupport : Finset ι := (ρ.locallyFinite.point_finite x₀).toFinset

@[simp]
theorem mem_finsupport (x₀ : X) {i} :
    i ∈ ρ.finsupport x₀ ↔ i ∈ support fun i ↦ ρ i x₀ := by
  simp only [finsupport, mem_support, Finite.mem_toFinset, mem_setOf_eq]

@[simp]
theorem coe_finsupport (x₀ : X) :
    (ρ.finsupport x₀ : Set ι) = support fun i ↦ ρ i x₀ := by
  ext
  rw [Finset.mem_coe, mem_finsupport]

variable {x₀ : X}

theorem sum_finsupport (hx₀ : x₀ ∈ s) : ∑ i ∈ ρ.finsupport x₀, ρ i x₀ = 1 := by
  rw [← ρ.sum_eq_one hx₀, finsum_eq_sum_of_support_subset _ (ρ.coe_finsupport x₀).superset]

theorem sum_finsupport' (hx₀ : x₀ ∈ s) {I : Finset ι} (hI : ρ.finsupport x₀ ⊆ I) :
    ∑ i ∈ I, ρ i x₀ = 1 := by
  classical
  rw [← Finset.sum_sdiff hI, ρ.sum_finsupport hx₀]
  suffices ∑ i ∈ I \ ρ.finsupport x₀, (ρ i) x₀ = ∑ i ∈ I \ ρ.finsupport x₀, 0 by
    rw [this, add_left_eq_self, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  rintro x hx
  simp only [Finset.mem_sdiff, ρ.mem_finsupport, mem_support, Classical.not_not] at hx
  exact hx.2

theorem sum_finsupport_smul_eq_finsum {M : Type*} [AddCommGroup M] [Module ℝ M] (φ : ι → X → M) :
    ∑ i ∈ ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ := by
  apply (finsum_eq_sum_of_support_subset _ _).symm
  have : (fun i ↦ (ρ i) x₀ • φ i x₀) = (fun i ↦ (ρ i) x₀) • (fun i ↦ φ i x₀) :=
    funext fun _ => (Pi.smul_apply' _ _ _).symm
  rw [ρ.coe_finsupport x₀, this, support_smul]
  exact inter_subset_left

end finsupport

section fintsupport -- partitions of unity have locally finite `tsupport`

variable {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X)

/-- The `tsupport`s of a partition of unity are locally finite. -/
theorem finite_tsupport : {i | x₀ ∈ tsupport (ρ i)}.Finite := by
  rcases ρ.locallyFinite x₀ with ⟨t, t_in, ht⟩
  apply ht.subset
  rintro i hi
  simp only [inter_comm]
  exact mem_closure_iff_nhds.mp hi t t_in

/-- The tsupport of a partition of unity at a point `x₀` as a `Finset`.
  This is the set of `i : ι` such that `x₀ ∈ tsupport f i`. -/
def fintsupport (x₀ : X) : Finset ι :=
  (ρ.finite_tsupport x₀).toFinset

theorem mem_fintsupport_iff (i : ι) : i ∈ ρ.fintsupport x₀ ↔ x₀ ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _

theorem eventually_fintsupport_subset :
    ∀ᶠ y in 𝓝 x₀, ρ.fintsupport y ⊆ ρ.fintsupport x₀ := by
  apply (ρ.locallyFinite.closure.eventually_subset (fun _ ↦ isClosed_closure) x₀).mono
  intro y hy z hz
  rw [PartitionOfUnity.mem_fintsupport_iff] at *
  exact hy hz

theorem finsupport_subset_fintsupport : ρ.finsupport x₀ ⊆ ρ.fintsupport x₀ := fun i hi ↦ by
  rw [ρ.mem_fintsupport_iff]
  apply subset_closure
  exact (ρ.mem_finsupport x₀).mp hi

theorem eventually_finsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.finsupport y ⊆ ρ.fintsupport x₀ :=
  (ρ.eventually_fintsupport_subset x₀).mono
    fun y hy ↦ (ρ.finsupport_subset_fintsupport y).trans hy

end fintsupport

/-- If `f` is a partition of unity on `s : Set X` and `g : X → E` is continuous at every point of
the topological support of some `f i`, then `fun x ↦ f i x • g x` is continuous on the whole space.
-/
theorem continuous_smul {g : X → E} {i : ι} (hg : ∀ x ∈ tsupport (f i), ContinuousAt g x) :
    Continuous fun x => f i x • g x :=
  continuous_of_tsupport fun x hx =>
    ((f i).continuousAt x).smul <| hg x <| tsupport_smul_subset_left _ _ hx

/-- If `f` is a partition of unity on a set `s : Set X` and `g : ι → X → E` is a family of functions
such that each `g i` is continuous at every point of the topological support of `f i`, then the sum
`fun x ↦ ∑ᶠ i, f i x • g i x` is continuous on the whole space. -/
theorem continuous_finsum_smul [ContinuousAdd E] {g : ι → X → E}
    (hg : ∀ (i), ∀ x ∈ tsupport (f i), ContinuousAt (g i) x) :
    Continuous fun x => ∑ᶠ i, f i x • g i x :=
  (continuous_finsum fun i => f.continuous_smul (hg i)) <|
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _

/-- A partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same type if
for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def IsSubordinate (U : ι → Set X) : Prop :=
  ∀ i, tsupport (f i) ⊆ U i

variable {f}

theorem exists_finset_nhd' {s : Set X} (ρ : PartitionOfUnity ι X s) (x₀ : X) :
    ∃ I : Finset ι, (∀ᶠ x in 𝓝[s] x₀, ∑ i ∈ I, ρ i x = 1) ∧
      ∀ᶠ x in 𝓝 x₀, support (ρ · x) ⊆ I := by
  rcases ρ.locallyFinite.exists_finset_support x₀ with ⟨I, hI⟩
  refine ⟨I, eventually_nhdsWithin_iff.mpr (hI.mono fun x hx x_in ↦ ?_), hI⟩
  have : ∑ᶠ i : ι, ρ i x = ∑ i ∈ I, ρ i x := finsum_eq_sum_of_support_subset _ hx
  rwa [eq_comm, ρ.sum_eq_one x_in] at this

theorem exists_finset_nhd (ρ : PartitionOfUnity ι X univ) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, ∑ i ∈ I, ρ i x = 1 ∧ support (ρ · x) ⊆ I := by
  rcases ρ.exists_finset_nhd' x₀ with ⟨I, H⟩
  use I
  rwa [nhdsWithin_univ, ← eventually_and] at H

theorem exists_finset_nhd_support_subset {U : ι → Set X} (hso : f.IsSubordinate U)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ is : Finset ι, ∃ n ∈ 𝓝 x, n ⊆ ⋂ i ∈ is, U i ∧ ∀ z ∈ n, (support (f · z)) ⊆ is :=
  f.locallyFinite.exists_finset_nhd_support_subset hso ho x

/-- If `f` is a partition of unity that is subordinate to a family of open sets `U i` and
`g : ι → X → E` is a family of functions such that each `g i` is continuous on `U i`, then the sum
`fun x ↦ ∑ᶠ i, f i x • g i x` is a continuous function. -/
theorem IsSubordinate.continuous_finsum_smul [ContinuousAdd E] {U : ι → Set X}
    (ho : ∀ i, IsOpen (U i)) (hf : f.IsSubordinate U) {g : ι → X → E}
    (hg : ∀ i, ContinuousOn (g i) (U i)) : Continuous fun x => ∑ᶠ i, f i x • g i x :=
  f.continuous_finsum_smul fun i _ hx => (hg i).continuousAt <| (ho i).mem_nhds <| hf i hx

end PartitionOfUnity

namespace BumpCovering

variable {s : Set X} (f : BumpCovering ι X s)

instance : FunLike (BumpCovering ι X s) ι C(X, ℝ) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

@[simp]
lemma apply_coe{i : ι} : f.toFun i = f i := rfl

protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

theorem locallyFinite_tsupport : LocallyFinite fun i => tsupport (f i) :=
  f.locallyFinite.closure

protected theorem point_finite (x : X) : { i | f i x ≠ 0 }.Finite :=
  f.locallyFinite.point_finite x

theorem nonneg (i : ι) (x : X) : 0 ≤ f i x :=
  f.nonneg' i x

theorem le_one (i : ι) (x : X) : f i x ≤ 1 :=
  f.le_one' i x

open Classical in
/-- A `BumpCovering` that consists of a single function, uniformly equal to one, defined as an
example for `Inhabited` instance. -/
protected def single (i : ι) (s : Set X) : BumpCovering ι X s where
  toFun := Pi.single i 1
  locallyFinite' x := by
    refine ⟨univ, univ_mem, (finite_singleton i).subset ?_⟩
    rintro j ⟨x, hx, -⟩
    contrapose! hx
    rw [mem_singleton_iff] at hx
    simp [hx]
  nonneg' := le_update_iff.2 ⟨fun _ => zero_le_one, fun _ _ => le_rfl⟩
  le_one' := update_le_iff.2 ⟨le_rfl, fun _ _ _ => zero_le_one⟩
  eventuallyEq_one' x _ := ⟨i, by rw [Pi.single_eq_same, ContinuousMap.coe_one]⟩

open Classical in
@[simp]
theorem coe_single (i : ι) (s : Set X) : ⇑(BumpCovering.single i s) = Pi.single i 1 := by
  rfl

instance [Inhabited ι] : Inhabited (BumpCovering ι X s) :=
  ⟨BumpCovering.single default s⟩

/-- A collection of bump functions `f i` is subordinate to a family of sets `U i` indexed by the
same type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def IsSubordinate (f : BumpCovering ι X s) (U : ι → Set X) : Prop :=
  ∀ i, tsupport (f i) ⊆ U i

theorem IsSubordinate.mono {f : BumpCovering ι X s} {U V : ι → Set X} (hU : f.IsSubordinate U)
    (hV : ∀ i, U i ⊆ V i) : f.IsSubordinate V :=
  fun i => Subset.trans (hU i) (hV i)

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, see
`BumpCovering.exists_isSubordinate`. This version assumes that `p : (X → ℝ) → Prop` is a predicate
that satisfies Urysohn's lemma, and provides a `BumpCovering` such that each function of the
covering satisfies `p`. -/
theorem exists_isSubordinate_of_locallyFinite_of_prop [NormalSpace X] (p : (X → ℝ) → Prop)
    (h01 : ∀ s t, IsClosed s → IsClosed t → Disjoint s t →
      ∃ f : C(X, ℝ), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U)
    (hU : s ⊆ ⋃ i, U i) : ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U := by
  rcases exists_subset_iUnion_closure_subset hs ho (fun x _ => hf.point_finite x) hU with
    ⟨V, hsV, hVo, hVU⟩
  have hVU' : ∀ i, V i ⊆ U i := fun i => Subset.trans subset_closure (hVU i)
  rcases exists_subset_iUnion_closure_subset hs hVo (fun x _ => (hf.subset hVU').point_finite x)
      hsV with
    ⟨W, hsW, hWo, hWV⟩
  choose f hfp hf0 hf1 hf01 using fun i =>
    h01 _ _ (isClosed_compl_iff.2 <| hVo i) isClosed_closure
      (disjoint_right.2 fun x hx => Classical.not_not.2 (hWV i hx))
  have hsupp : ∀ i, support (f i) ⊆ V i := fun i => support_subset_iff'.2 (hf0 i)
  refine ⟨⟨f, hf.subset fun i => Subset.trans (hsupp i) (hVU' i), fun i x => (hf01 i x).1,
      fun i x => (hf01 i x).2, fun x hx => ?_⟩,
    hfp, fun i => Subset.trans (closure_mono (hsupp i)) (hVU i)⟩
  rcases mem_iUnion.1 (hsW hx) with ⟨i, hi⟩
  exact ⟨i, ((hf1 i).mono subset_closure).eventuallyEq_of_mem ((hWo i).mem_nhds hi)⟩

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, see
`BumpCovering.exists_isSubordinate`. -/
theorem exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, f.IsSubordinate U :=
  let ⟨f, _, hfU⟩ :=
    exists_isSubordinate_of_locallyFinite_of_prop (fun _ => True)
      (fun _ _ hs ht hd =>
        (exists_continuous_zero_one_of_isClosed hs ht hd).imp fun _ hf => ⟨trivial, hf⟩)
      hs U ho hf hU
  ⟨f, hfU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. This version assumes that
`p : (X → ℝ) → Prop` is a predicate that satisfies Urysohn's lemma, and provides a
`BumpCovering` such that each function of the covering satisfies `p`. -/
theorem exists_isSubordinate_of_prop [NormalSpace X] [ParacompactSpace X] (p : (X → ℝ) → Prop)
    (h01 : ∀ s t, IsClosed s → IsClosed t → Disjoint s t →
      ∃ f : C(X, ℝ), p f ∧ EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hs : IsClosed s) (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : BumpCovering ι X s, (∀ i, p (f i)) ∧ f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩
  exact ⟨f, hfp, hf.mono hVU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `BumpCovering ι X s` that is subordinate to `U`. -/
theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) : ∃ f : BumpCovering ι X s, f.IsSubordinate U := by
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩
  rcases exists_isSubordinate_of_locallyFinite hs V hVo hVf hsV with ⟨f, hf⟩
  exact ⟨f, hf.mono hVU⟩

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : X) (hx : x ∈ s) : ι :=
  (f.eventuallyEq_one' x hx).choose

theorem eventuallyEq_one (x : X) (hx : x ∈ s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
  (f.eventuallyEq_one' x hx).choose_spec

theorem ind_apply (x : X) (hx : x ∈ s) : f (f.ind x hx) x = 1 :=
  (f.eventuallyEq_one x hx).eq_of_nhds

/-- Partition of unity defined by a `BumpCovering`. We use this auxiliary definition to prove some
properties of the new family of functions before bundling it into a `PartitionOfUnity`. Do not use
this definition, use `BumpCovering.toPartitionOfUnity` instead.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals one, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `LinearOrder ι`, we use `WellOrderingRel` instead of `(<)`. -/
def toPOUFun (i : ι) (x : X) : ℝ :=
  f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x)

theorem toPOUFun_zero_of_zero {i : ι} {x : X} (h : f i x = 0) : f.toPOUFun i x = 0 := by
  rw [toPOUFun, h, zero_mul]

theorem support_toPOUFun_subset (i : ι) : support (f.toPOUFun i) ⊆ support (f i) :=
  fun _ => mt <| f.toPOUFun_zero_of_zero

open Classical in
theorem toPOUFun_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
    f.toPOUFun i x = f i x * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - f j x) := by
  refine congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ fun {j} hj => ?_)
  rw [Ne, sub_eq_self] at hj
  rw [Finset.mem_filter, Iff.comm, and_iff_right_iff_imp]
  exact flip (ht j) hj

theorem sum_toPOUFun_eq (x : X) : ∑ᶠ i, f.toPOUFun i x = 1 - ∏ᶠ i, (1 - f i x) := by
  set s := (f.point_finite x).toFinset
  have hs : (s : Set ι) = { i | f i x ≠ 0 } := Finite.coe_toFinset _
  have A : (support fun i => toPOUFun f i x) ⊆ s := by
    rw [hs]
    exact fun i hi => f.support_toPOUFun_subset i hi
  have B : (mulSupport fun i => 1 - f i x) ⊆ s := by
    rw [hs, mulSupport_one_sub]
    exact fun i => id
  classical
  letI : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  rw [finsum_eq_sum_of_support_subset _ A, finprod_eq_prod_of_mulSupport_subset _ B,
    Finset.prod_one_sub_ordered, sub_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  convert f.toPOUFun_eq_mul_prod _ _ _ fun j _ hj => _
  rwa [Finite.mem_toFinset]

open Classical in
theorem exists_finset_toPOUFun_eventuallyEq (i : ι) (x : X) : ∃ t : Finset ι,
    f.toPOUFun i =ᶠ[𝓝 x] f i * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - f j) := by
  rcases f.locallyFinite x with ⟨U, hU, hf⟩
  use hf.toFinset
  filter_upwards [hU] with y hyU
  simp only [ContinuousMap.coe_prod, Pi.mul_apply, Finset.prod_apply]
  apply toPOUFun_eq_mul_prod
  intro j _ hj
  exact hf.mem_toFinset.2 ⟨y, ⟨hj, hyU⟩⟩

theorem continuous_toPOUFun (i : ι) : Continuous (f.toPOUFun i) := by
  refine (f i).continuous.mul <|
    continuous_finprod_cond (fun j _ => continuous_const.sub (f j).continuous) ?_
  simp only [mulSupport_one_sub]
  exact f.locallyFinite

/-- The partition of unity defined by a `BumpCovering`.

The partition of unity is given by the formula `g i x = f i x * ∏ᶠ j < i, (1 - f j x)`. In other
words, `g i x = ∏ᶠ j < i, (1 - f j x) - ∏ᶠ j ≤ i, (1 - f j x)`, so
`∑ᶠ i, g i x = 1 - ∏ᶠ j, (1 - f j x)`. If `x ∈ s`, then one of `f j x` equals one, hence the product
of `1 - f j x` vanishes, and `∑ᶠ i, g i x = 1`.

In order to avoid an assumption `LinearOrder ι`, we use `WellOrderingRel` instead of `(<)`. -/
def toPartitionOfUnity : PartitionOfUnity ι X s where
  toFun i := ⟨f.toPOUFun i, f.continuous_toPOUFun i⟩
  locallyFinite' := f.locallyFinite.subset f.support_toPOUFun_subset
  nonneg' i x :=
    mul_nonneg (f.nonneg i x) (finprod_cond_nonneg fun j _ => sub_nonneg.2 <| f.le_one j x)
  sum_eq_one' x hx := by
    simp only [ContinuousMap.coe_mk, sum_toPOUFun_eq, sub_eq_self]
    apply finprod_eq_zero (fun i => 1 - f i x) (f.ind x hx)
    · simp only [f.ind_apply x hx, sub_self]
    · rw [mulSupport_one_sub]
      exact f.point_finite x
  sum_le_one' x := by
    simp only [ContinuousMap.coe_mk, sum_toPOUFun_eq, sub_le_self_iff]
    exact finprod_nonneg fun i => sub_nonneg.2 <| f.le_one i x

theorem toPartitionOfUnity_apply (i : ι) (x : X) :
    f.toPartitionOfUnity i x = f i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - f j x) := rfl

open Classical in
theorem toPartitionOfUnity_eq_mul_prod (i : ι) (x : X) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → f j x ≠ 0 → j ∈ t) :
    f.toPartitionOfUnity i x = f i x * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - f j x) :=
  f.toPOUFun_eq_mul_prod i x t ht

open Classical in
theorem exists_finset_toPartitionOfUnity_eventuallyEq (i : ι) (x : X) : ∃ t : Finset ι,
    f.toPartitionOfUnity i =ᶠ[𝓝 x] f i * ∏ j ∈ t.filter fun j => WellOrderingRel j i, (1 - f j) :=
  f.exists_finset_toPOUFun_eventuallyEq i x

theorem toPartitionOfUnity_zero_of_zero {i : ι} {x : X} (h : f i x = 0) :
    f.toPartitionOfUnity i x = 0 :=
  f.toPOUFun_zero_of_zero h

theorem support_toPartitionOfUnity_subset (i : ι) :
    support (f.toPartitionOfUnity i) ⊆ support (f i) :=
  f.support_toPOUFun_subset i

theorem sum_toPartitionOfUnity_eq (x : X) :
    ∑ᶠ i, f.toPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - f i x) :=
  f.sum_toPOUFun_eq x

theorem IsSubordinate.toPartitionOfUnity {f : BumpCovering ι X s} {U : ι → Set X}
    (h : f.IsSubordinate U) : f.toPartitionOfUnity.IsSubordinate U :=
  fun i => Subset.trans (closure_mono <| f.support_toPartitionOfUnity_subset i) (h i)

end BumpCovering

namespace PartitionOfUnity

variable {s : Set X}

instance [Inhabited ι] : Inhabited (PartitionOfUnity ι X s) :=
  ⟨BumpCovering.toPartitionOfUnity default⟩

/-- If `X` is a normal topological space and `U` is a locally finite open covering of a closed set
`s`, then there exists a `PartitionOfUnity ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : LocallyFinite U` can be omitted, see
`BumpCovering.exists_isSubordinate`. -/
theorem exists_isSubordinate_of_locallyFinite [NormalSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hf : LocallyFinite U) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite hs U ho hf hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `PartitionOfUnity ι X s` that is subordinate to `U`. -/
theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X] (hs : IsClosed s) (U : ι → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U :=
  let ⟨f, hf⟩ := BumpCovering.exists_isSubordinate hs U ho hU
  ⟨f.toPartitionOfUnity, hf.toPartitionOfUnity⟩

-- /-- If `X` is a locally compact `R2Space` and `U` is an open covering of a compact set `s`, then
-- there exists a `PartitionOfUnity ι X s` that is subordinate to `U`. -/
-- theorem exists_isSubordinate_of_isCompact [R1Space X] [LocallyCompactSpace X] (hs : IsCompact s)
--     (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
--     ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U ∧ ∀ ι, HasCompactSupport (f ι) := by
--   have : ∃ Uc : ι → Set X, (∀ (i : ι), IsOpen (Uc i)) ∧ (∀ (i : ι), IsCompact
--       (closure (Uc i))) ∧ s ⊆ ⋃ i, Uc i ∧ (∀ (i : ι), Uc i ⊆ U i) := by
--     set Uc := fun (i : ι) => Classical.choose (exists_isOpen_superset_and_isCompact_closure
--       hs) ∩ U i
--     set spUc := Classical.choose_spec (exists_isOpen_superset_and_isCompact_closure hs)
--     use Uc
--     refine ⟨fun i => IsOpen.inter spUc.1 (ho i), ?_, ?_, ?_⟩
--     · intro i
--       apply IsCompact.of_isClosed_subset spUc.2.2 isClosed_closure
--       exact closure_mono inter_subset_left
--     · rw [← inter_iUnion _ U]
--       exact subset_inter spUc.2.1 hU
--     · exact fun i => inter_subset_right
--   obtain ⟨Uc, hUcopen, hUcccompact, hssubUc, hUsubUc⟩ := this
--   obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover hs Uc hUcopen hssubUc
--   by_cases htcard : t.card = 0
--   · have tempty : t = ∅ := Finset.card_eq_zero.mp htcard
--     have : s = ∅ := by
--       rw [tempty] at ht
--       simp only [Finset.not_mem_empty, iUnion_of_empty, iUnion_empty, subset_empty_iff] at ht
--       exact ht
--     set g := fun i => (0 : C(X, ℝ)) with hg
--     set f : BumpCovering ι X s :=
--       ⟨g,
--       by
--       intro x
--       use univ
--       simp only [univ_mem, inter_univ, support_nonempty_iff, ne_eq, true_and]
--       have h : {i | ¬⇑(g i) = 0} = ∅ := by
--        rw [hg]
--        simp only [ContinuousMap.coe_zero, not_true_eq_false, setOf_false]
--       rw [h]
--       exact finite_empty,
--       by
--       intro i
--       simp only [Pi.zero_apply, le_refl],
--       by
--       intro x
--       rw [hg]
--       simp only [Pi.one_apply]
--       intro x
--       simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.zero_apply, ContinuousMap.one_apply,
--         zero_le_one],
--       by
--       intro x
--       rw [this]
--       exact fun a ↦ False.elim a
--       ⟩ with hf
--     use BumpCovering.toPartitionOfUnity f
--     have : ∀ i, f.toPartitionOfUnity i = 0 := by
--       intro i
--       ext x
--       rw [BumpCovering.toPartitionOfUnity_apply]
--       simp only [BumpCovering.apply_coe, ContinuousMap.zero_apply, mul_eq_zero]
--       exact mul_eq_mul_left_iff.mp rfl
--     constructor
--     · intro i
--       rw [this]
--       simp only [ContinuousMap.coe_zero]
--       rw [tsupport, support_zero']
--       simp only [closure_empty, empty_subset]
--     · intro i
--       rw [this]
--       simp only [ContinuousMap.coe_zero]
--       rw [HasCompactSupport, tsupport, support_zero']
--       simp only [closure_empty, isCompact_empty]
--   · sorry
  -- · have htW : ∀ (x : X), x ∈ t → ∃ (Wx : Set X), x ∈ Wx ∧ IsOpen Wx ∧ IsCompact (closure Wx)
  --       ∧ ∃ (i : Fin (Nat.succ n)), (closure Wx) ⊆ sc i := by
  --     intro x hx
  --     obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((Set.mem_of_subset_of_mem htsubsc) hx)
  --     obtain ⟨cWx, hcWxCompact, hxinintcWx, hcWxsubsi⟩ := exists_compact_subset (hscopen i) hi
  --     use interior cWx
  --     refine ⟨hxinintcWx, ?_, ?_, ?_⟩
  --     · simp only [isOpen_interior]
  --     · apply IsCompact.of_isClosed_subset hcWxCompact isClosed_closure
  --       nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcWxCompact)]
  --       exact closure_mono interior_subset
  --     · use i
  --       apply _root_.subset_trans _ hcWxsubsi
  --       nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hcWxCompact)]
  --       exact closure_mono interior_subset
  --   set W : X → Set X := fun x => if hx : x ∈ t then Classical.choose (htW x hx) else default
  --     with hW
  --   have htWnhds : ∀ (x : X), x ∈ t → W x ∈ nhds x := by
  --     intro x hx
  --     apply mem_nhds_iff.mpr
  --     use W x
  --     refine ⟨subset_refl (W x), ?_⟩
  --     rw [hW]
  --     simp only
  --     rw [dif_pos hx]
  --     exact And.intro (Classical.choose_spec (htW x hx)).2.1 (Classical.choose_spec (htW x hx)).1
  --   obtain ⟨ι, hι⟩ := IsCompact.elim_nhds_subcover htcp W htWnhds
  --   set Wx : Fin (Nat.succ n) → ι → Set X := fun i xj =>
  --     if closure (W xj) ⊆ sc i then closure (W xj) else ∅
  --     with hWx
  --   set H : Fin (Nat.succ n) → Set X := fun i => ⋃ xj, closure (Wx i xj)
  --     with hH
  --   have IsClosedH : ∀ (i : Fin (Nat.succ n)), IsClosed (H i) := by
  --     intro i
  --     rw [hH]
  --     simp only
  --     exact isClosed_iUnion_of_finite (fun (xj : ι) => isClosed_closure)
  --   have IsHSubS : ∀ (i : Fin (Nat.succ n)), H i ⊆ sc i := by
  --     intro i
  --     rw [hH]
  --     simp only
  --     apply Set.iUnion_subset
  --     intro xj
  --     rw [hWx]
  --     simp only
  --     by_cases hmV : closure (W xj) ⊆ sc i
  --     · rw [if_pos hmV, closure_closure]
  --       exact hmV
  --     · rw [if_neg hmV, closure_empty]
  --       exact Set.empty_subset _
  --   set g : Fin (Nat.succ n) → C(X, ℝ) := fun i => Classical.choose
  --     (exists_tsupport_one_of_isOpen_isClosed (hscopen i) (hscccompact i) (IsClosedH i) (IsHSubS i))
  --     with hg
  --   set f : Fin (Nat.succ n) → C(X, ℝ) :=
  --     fun i => (∏ j in { j : Fin (Nat.succ n) | j < i }.toFinset, (1 - g j)) * g i
  --     with hf
  --   use f
  --   refine ⟨?_, ?_, ?_, ?_⟩
  --   · intro i
  --     apply _root_.subset_trans tsupport_mul_subset_right
  --     apply subset_trans _ (hssubsc i)
  --     exact (Classical.choose_spec
  --       (exists_tsupport_one_of_isOpen_isClosed (hscopen i) (hscccompact i) (IsClosedH i)
  --       (IsHSubS i))).1
  --   · have hsumf (m : ℕ) (hm : m < Nat.succ n) :
  --         ∑ j in { j : Fin (Nat.succ n) | j ≤ ⟨m, hm⟩ }.toFinset, f j
  --         = 1 - (∏ j in { j : Fin (Nat.succ n) | j ≤ ⟨m, hm⟩ }.toFinset, (1 - g j)) := by
  --       induction' m with m ihm
  --       · simp only [Nat.zero_eq, Fin.zero_eta, Fin.le_zero_iff, setOf_eq_eq_singleton,
  --         toFinset_singleton, Finset.sum_singleton, Finset.prod_singleton, sub_sub_cancel]
  --         rw [hf]
  --         simp only [Fin.not_lt_zero, setOf_false, toFinset_empty, Finset.prod_empty, one_mul]
  --       · have hmlt : m < Nat.succ n := by
  --           exact Nat.lt_of_succ_lt hm
  --         have hUnion: { j : Fin (Nat.succ n) | j ≤ ⟨m + 1, hm⟩}
  --             = { j : Fin (Nat.succ n) | j ≤ ⟨m, hmlt⟩ } ∪ {⟨m+1, hm⟩} := by
  --           simp only [union_singleton]
  --           ext j
  --           simp only [Nat.cast_add, Nat.cast_one, mem_setOf_eq, mem_insert_iff]
  --           constructor
  --           · intro hj
  --             by_cases hjm : j.1 ≤ m
  --             · right
  --               exact hjm
  --             · push_neg at hjm
  --               left
  --               rw [Fin.ext_iff]
  --               simp only
  --               rw [Fin.le_def] at hj
  --               exact (Nat.le_antisymm hjm hj).symm
  --           · intro hj
  --             rcases hj with hjmone | hjmle
  --             · exact le_of_eq hjmone
  --             · rw [Fin.le_def]
  --               simp only
  --               rw [Fin.le_def] at hjmle
  --               simp only at hjmle
  --               rw [Nat.le_add_one_iff]
  --               left
  --               exact hjmle
  --         simp_rw [hUnion]
  --         simp only [union_singleton, toFinset_insert, mem_setOf_eq, toFinset_setOf]
  --         rw [Finset.sum_insert _, Finset.prod_insert _]
  --         simp only [mem_setOf_eq, toFinset_setOf] at ihm
  --         rw [ihm hmlt, sub_mul, one_mul, hf]
  --         ring_nf
  --         simp only [mem_setOf_eq, toFinset_setOf]
  --         have honeaddm: 1+m < Nat.succ n := by
  --           rw [add_comm 1 m]
  --           exact hm
  --         have hxlem : Finset.filter (fun (x : Fin (Nat.succ n)) =>
  --             x < { val := 1+m, isLt := honeaddm })
  --             = Finset.filter (fun (x : Fin (Nat.succ n)) => x ≤ { val := m, isLt := hmlt }) := by
  --           ext Finset.univ a
  --           simp only [Finset.mem_filter, and_congr_right_iff]
  --           intro _
  --           rw [Fin.le_def, Fin.lt_def]
  --           simp only
  --           rw [add_comm 1 m]
  --           exact Nat.lt_add_one_iff
  --         rw [hxlem]
  --         ring
  --         all_goals
  --           simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
  --           rw [Fin.lt_def]
  --           simp only [Fin.val_natCast]
  --           exact lt_add_one m
  --     intro x hx
  --     have huniv : {j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset = Finset.univ := by
  --       ext j
  --       simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, Finset.mem_filter, Finset.mem_univ,
  --         true_and, iff_true]
  --       apply Fin.mk_le_of_le_val
  --       simp only
  --       exact Nat.lt_succ_iff.mp j.isLt
  --     rw [← huniv]
  --     have heqfun (x : X) :
  --         (∑ j in { j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset, f j) x
  --         = (1 - (∏ j in { j : Fin (Nat.succ n) | j ≤ ⟨n, (lt_add_one n)⟩ }.toFinset, (1 - g j)))
  --         x := by
  --       apply Function.funext_iff.mp
  --       ext z
  --       exact congrFun (congrArg DFunLike.coe (hsumf n (lt_add_one n))) z
  --     simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, ContinuousMap.coe_sum, Finset.sum_apply,
  --       ContinuousMap.sub_apply, ContinuousMap.one_apply, ContinuousMap.coe_prod,
  --       ContinuousMap.coe_sub, ContinuousMap.coe_one, Finset.prod_apply, Pi.sub_apply,
  --       Pi.one_apply] at heqfun
  --     simp only [Nat.zero_eq, mem_setOf_eq, toFinset_setOf, Finset.sum_apply, Pi.one_apply]
  --     rw [heqfun]
  --     simp only [sub_eq_self]
  --     obtain ⟨xj, hxj⟩ := exists_exists_eq_and.mp (hι.2 hx)
  --     simp only [mem_iUnion, exists_prop] at hxj
  --     rw [hW] at hxj
  --     simp at hxj
  --     rw [dif_pos (hι.1 xj hxj.1)] at hxj
  --     obtain ⟨i, hi⟩ := (Classical.choose_spec (htW xj (hι.1 xj hxj.1))).2.2.2
  --     have hxHi : x ∈ H i := by
  --       rw [hH]
  --       simp only [mem_iUnion]
  --       use ⟨xj, hxj.1⟩
  --       rw [hWx]
  --       simp only [dite_eq_ite]
  --       rw [hW]
  --       simp only
  --       rw [dif_pos (hι.1 xj hxj.1)]
  --       apply Set.mem_of_mem_of_subset _ subset_closure
  --       simp only [mem_ite_empty_right]
  --       exact And.intro hi (Set.mem_of_mem_of_subset hxj.2 subset_closure)
  --     simp at huniv
  --     rw [huniv]
  --     apply Finset.prod_eq_zero (Finset.mem_univ i)
  --     rw [hg]
  --     simp only [mem_Icc]
  --     rw [(Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed
  --       (hscopen i) (hscccompact i) (IsClosedH i) (IsHSubS i))).2.1 hxHi]
  --     simp only [Pi.one_apply, sub_self]
  --   · intro i x
  --     rw [hf]
  --     simp only [mem_setOf_eq, toFinset_setOf, ContinuousMap.mul_apply, ContinuousMap.coe_prod,
  --       ContinuousMap.coe_sub, ContinuousMap.coe_one, Finset.prod_apply]
  --     apply unitInterval.mul_mem
  --     · apply unitInterval.prod_mem
  --       intro c _
  --       simp only [Pi.sub_apply, Pi.one_apply]
  --       rw [hg, ← unitInterval.mem_iff_one_sub_mem]
  --       exact (Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed (hscopen c)
  --         (hscccompact c) (IsClosedH c) (IsHSubS c))).2.2 x
  --     · rw [hg]
  --       simp only
  --       exact (Classical.choose_spec (exists_tsupport_one_of_isOpen_isClosed (hscopen i)
  --         (hscccompact i) (IsClosedH i) (IsHSubS i))).2.2 x
  --   · intro i
  --     apply IsCompact.of_isClosed_subset (hscccompact i) (isClosed_closure)
  --     apply closure_mono
  --     apply _root_.subset_trans (Function.support_mul_subset_right _ _)
  --     exact subset_trans subset_closure (Classical.choose_spec
  --       (exists_tsupport_one_of_isOpen_isClosed (hscopen i) (hscccompact i) (IsClosedH i)
  --       (IsHSubS i))).1


end PartitionOfUnity
