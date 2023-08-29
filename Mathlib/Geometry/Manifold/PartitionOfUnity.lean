/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.MetricSpace.PartitionOfUnity
import Mathlib.Topology.ShrinkingLemma

#align_import geometry.manifold.partition_of_unity from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Smooth partition of unity

In this file we define two structures, `SmoothBumpCovering` and `SmoothPartitionOfUnity`. Both
structures describe coverings of a set by a locally finite family of supports of smooth functions
with some additional properties. The former structure is mostly useful as an intermediate step in
the construction of a smooth partition of unity but some proofs that traditionally deal with a
partition of unity can use a `SmoothBumpCovering` as well.

Given a real manifold `M` and its subset `s`, a `SmoothBumpCovering ι I M s` is a collection of
`SmoothBumpFunction`s `f i` indexed by `i : ι` such that

* the center of each `f i` belongs to `s`;
* the family of sets `support (f i)` is locally finite;
* for each `x ∈ s`, there exists `i : ι` such that `f i =ᶠ[𝓝 x] 1`.
In the same settings, a `SmoothPartitionOfUnity ι I M s` is a collection of smooth nonnegative
functions `f i : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, `i : ι`, such that

* the family of sets `support (f i)` is locally finite;
* for each `x ∈ s`, the sum `∑ᶠ i, f i x` equals one;
* for each `x`, the sum `∑ᶠ i, f i x` is less than or equal to one.

We say that `f : SmoothBumpCovering ι I M s` is *subordinate* to a map `U : M → Set M` if for each
index `i`, we have `tsupport (f i) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.

We prove that on a smooth finitely dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → Set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `SmoothBumpCovering ι I M s`
subordinate to `U`. Then we use this fact to prove a similar statement about smooth partitions of
unity, see `SmoothPartitionOfUnity.exists_isSubordinate`.

Finally, we use existence of a partition of unity to prove lemma
`exists_smooth_forall_mem_convex_of_local` that allows us to construct a globally defined smooth
function from local functions.

## TODO

* Build a framework for to transfer local definitions to global using partition of unity and use it
  to define, e.g., the integral of a differential form over a manifold. Lemma
  `exists_smooth_forall_mem_convex_of_local` is a first step in this direction.

## Tags

smooth bump function, partition of unity
-/


universe uι uE uH uM uF

open Function Filter FiniteDimensional Set

open scoped Topology Manifold Classical Filter BigOperators

noncomputable section

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type uH}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-!
### Covering by supports of smooth bump functions

In this section we define `SmoothBumpCovering ι I M s` to be a collection of
`SmoothBumpFunction`s such that their supports is a locally finite family of sets and for each
`x ∈ s` some function `f i` from the collection is equal to `1` in a neighborhood of `x`. A covering
of this type is useful to construct a smooth partition of unity and can be used instead of a
partition of unity in some proofs.

We prove that on a smooth finite dimensional real manifold with `σ`-compact Hausdorff topology, for
any `U : M → Set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `SmoothBumpCovering ι I M s`
subordinate to `U`. Then we use this fact to prove a version of the Whitney embedding theorem: any
compact real manifold can be embedded into `ℝ^n` for large enough `n`.  -/

set_option autoImplicit true


variable (ι M)

/-- We say that a collection of `SmoothBumpFunction`s is a `SmoothBumpCovering` of a set `s` if

* `(f i).c ∈ s` for all `i`;
* the family `λ i, support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;

If `M` is a finite dimensional real manifold which is a `σ`-compact Hausdorff topological space,
then for every covering `U : M → Set M`, `∀ x, U x ∈ 𝓝 x`, there exists a `SmoothBumpCovering`
subordinate to `U`, see `SmoothBumpCovering.exists_isSubordinate`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
-- porting note: was @[nolint has_nonempty_instance]
structure SmoothBumpCovering (s : Set M := univ) where
  /-- The center point of each bump in the smooth covering. -/
  c : ι → M
  /-- A smooth bump function around `c i`. -/
  toFun : ∀ i, SmoothBumpFunction I (c i)
  /-- All the bump functions in the covering are centered at points in `s`. -/
  c_mem' : ∀ i, c i ∈ s
  /-- Around each point, there are only finitely many nonzero bump functions in the family. -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- Around each point in `s`, one of the bump functions is equal to `1`. -/
  eventuallyEq_one' : ∀ x ∈ s, ∃ i, toFun i =ᶠ[𝓝 x] 1
#align smooth_bump_covering SmoothBumpCovering

/-- We say that a collection of functions form a smooth partition of unity on a set `s` if

* all functions are infinitely smooth and nonnegative;
* the family `λ i, support (f i)` is locally finite;
* for all `x ∈ s` the sum `∑ᶠ i, f i x` equals one;
* for all `x`, the sum `∑ᶠ i, f i x` is less than or equal to one. -/
structure SmoothPartitionOfUnity (s : Set M := univ) where
  /-- The family of functions forming the partition of unity. -/
  toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
  /-- Around each point, there are only finitely many nonzero functions in the family. -/
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  /-- All the functions in the partition of unity are nonnegative. -/
  nonneg' : ∀ i x, 0 ≤ toFun i x
  /-- The functions in the partition of unity add up to `1` at any point of `s`. -/
  sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, toFun i x = 1
  /-- The functions in the partition of unity add up to at most `1` everywhere. -/
  sum_le_one' : ∀ x, ∑ᶠ i, toFun i x ≤ 1
#align smooth_partition_of_unity SmoothPartitionOfUnity

variable {ι I M}

namespace SmoothPartitionOfUnity

variable {s : Set M} (f : SmoothPartitionOfUnity ι I M s) {n : ℕ∞}

instance {s : Set M} : FunLike (SmoothPartitionOfUnity ι I M s) ι fun _ => C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ mk s toFun✝ locallyFinite'✝ nonneg'✝ sum_eq_one'✝ sum_le_one'✝ = g
                                      -- ⊢ mk s toFun✝¹ locallyFinite'✝¹ nonneg'✝¹ sum_eq_one'✝¹ sum_le_one'✝¹ = mk s t …
                                               -- 🎉 no goals

protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'
#align smooth_partition_of_unity.locally_finite SmoothPartitionOfUnity.locallyFinite

theorem nonneg (i : ι) (x : M) : 0 ≤ f i x :=
  f.nonneg' i x
#align smooth_partition_of_unity.nonneg SmoothPartitionOfUnity.nonneg

theorem sum_eq_one {x} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx
#align smooth_partition_of_unity.sum_eq_one SmoothPartitionOfUnity.sum_eq_one

theorem exists_pos_of_mem {x} (hx : x ∈ s) : ∃ i, 0 < f i x := by
  by_contra h
  -- ⊢ False
  push_neg at h
  -- ⊢ False
  have H : ∀ i, f i x = 0 := fun i ↦ le_antisymm (h i) (f.nonneg i x)
  -- ⊢ False
  have := f.sum_eq_one hx
  -- ⊢ False
  simp_rw [H] at this
  -- ⊢ False
  simpa
  -- 🎉 no goals

theorem sum_le_one (x : M) : ∑ᶠ i, f i x ≤ 1 :=
  f.sum_le_one' x
#align smooth_partition_of_unity.sum_le_one SmoothPartitionOfUnity.sum_le_one

/-- Reinterpret a smooth partition of unity as a continuous partition of unity. -/
def toPartitionOfUnity : PartitionOfUnity ι M s :=
  { f with toFun := fun i => f i }
#align smooth_partition_of_unity.to_partition_of_unity SmoothPartitionOfUnity.toPartitionOfUnity

theorem smooth_sum : Smooth I 𝓘(ℝ) fun x => ∑ᶠ i, f i x :=
  smooth_finsum (fun i => (f i).smooth) f.locallyFinite
#align smooth_partition_of_unity.smooth_sum SmoothPartitionOfUnity.smooth_sum

theorem le_one (i : ι) (x : M) : f i x ≤ 1 :=
  f.toPartitionOfUnity.le_one i x
#align smooth_partition_of_unity.le_one SmoothPartitionOfUnity.le_one

theorem sum_nonneg (x : M) : 0 ≤ ∑ᶠ i, f i x :=
  f.toPartitionOfUnity.sum_nonneg x
#align smooth_partition_of_unity.sum_nonneg SmoothPartitionOfUnity.sum_nonneg

theorem contMDiff_smul {g : M → F} {i} (hg : ∀ x ∈ tsupport (f i), ContMDiffAt I 𝓘(ℝ, F) n g x) :
    ContMDiff I 𝓘(ℝ, F) n fun x => f i x • g x :=
  contMDiff_of_support fun x hx =>
    ((f i).contMDiff.contMDiffAt.of_le le_top).smul <| hg x <| tsupport_smul_subset_left _ _ hx
#align smooth_partition_of_unity.cont_mdiff_smul SmoothPartitionOfUnity.contMDiff_smul

theorem smooth_smul {g : M → F} {i} (hg : ∀ x ∈ tsupport (f i), SmoothAt I 𝓘(ℝ, F) g x) :
    Smooth I 𝓘(ℝ, F) fun x => f i x • g x :=
  f.contMDiff_smul hg
#align smooth_partition_of_unity.smooth_smul SmoothPartitionOfUnity.smooth_smul

/-- If `f` is a smooth partition of unity on a set `s : Set M` and `g : ι → M → F` is a family of
functions such that `g i` is $C^n$ smooth at every point of the topological support of `f i`, then
the sum `λ x, ∑ᶠ i, f i x • g i x` is smooth on the whole manifold. -/
theorem contMDiff_finsum_smul {g : ι → M → F}
    (hg : ∀ (i), ∀ x ∈ tsupport (f i), ContMDiffAt I 𝓘(ℝ, F) n (g i) x) :
    ContMDiff I 𝓘(ℝ, F) n fun x => ∑ᶠ i, f i x • g i x :=
  (contMDiff_finsum fun i => f.contMDiff_smul (hg i)) <|
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _
#align smooth_partition_of_unity.cont_mdiff_finsum_smul SmoothPartitionOfUnity.contMDiff_finsum_smul

/-- If `f` is a smooth partition of unity on a set `s : Set M` and `g : ι → M → F` is a family of
functions such that `g i` is smooth at every point of the topological support of `f i`, then the sum
`λ x, ∑ᶠ i, f i x • g i x` is smooth on the whole manifold. -/
theorem smooth_finsum_smul {g : ι → M → F}
    (hg : ∀ (i), ∀ x ∈ tsupport (f i), SmoothAt I 𝓘(ℝ, F) (g i) x) :
    Smooth I 𝓘(ℝ, F) fun x => ∑ᶠ i, f i x • g i x :=
  f.contMDiff_finsum_smul hg
#align smooth_partition_of_unity.smooth_finsum_smul SmoothPartitionOfUnity.smooth_finsum_smul

theorem finsum_smul_mem_convex {g : ι → M → F} {t : Set F} {x : M} (hx : x ∈ s)
    (hg : ∀ i, f i x ≠ 0 → g i x ∈ t) (ht : Convex ℝ t) : ∑ᶠ i, f i x • g i x ∈ t :=
  ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg
#align smooth_partition_of_unity.finsum_smul_mem_convex SmoothPartitionOfUnity.finsum_smul_mem_convex

/-- A smooth partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same
type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def IsSubordinate (f : SmoothPartitionOfUnity ι I M s) (U : ι → Set M) :=
  ∀ i, tsupport (f i) ⊆ U i
#align smooth_partition_of_unity.is_subordinate SmoothPartitionOfUnity.IsSubordinate

variable {f} {U : ι → Set M}

@[simp]
theorem isSubordinate_toPartitionOfUnity :
    f.toPartitionOfUnity.IsSubordinate U ↔ f.IsSubordinate U :=
  Iff.rfl
#align smooth_partition_of_unity.is_subordinate_to_partition_of_unity SmoothPartitionOfUnity.isSubordinate_toPartitionOfUnity

alias ⟨_, IsSubordinate.toPartitionOfUnity⟩ := isSubordinate_toPartitionOfUnity
#align smooth_partition_of_unity.is_subordinate.to_partition_of_unity SmoothPartitionOfUnity.IsSubordinate.toPartitionOfUnity

/-- If `f` is a smooth partition of unity on a set `s : Set M` subordinate to a family of open sets
`U : ι → Set M` and `g : ι → M → F` is a family of functions such that `g i` is $C^n$ smooth on
`U i`, then the sum `λ x, ∑ᶠ i, f i x • g i x` is $C^n$ smooth on the whole manifold. -/
theorem IsSubordinate.contMDiff_finsum_smul {g : ι → M → F} (hf : f.IsSubordinate U)
    (ho : ∀ i, IsOpen (U i)) (hg : ∀ i, ContMDiffOn I 𝓘(ℝ, F) n (g i) (U i)) :
    ContMDiff I 𝓘(ℝ, F) n fun x => ∑ᶠ i, f i x • g i x :=
  f.contMDiff_finsum_smul fun i _ hx => (hg i).contMDiffAt <| (ho i).mem_nhds (hf i hx)
#align smooth_partition_of_unity.is_subordinate.cont_mdiff_finsum_smul SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul

/-- If `f` is a smooth partition of unity on a set `s : Set M` subordinate to a family of open sets
`U : ι → Set M` and `g : ι → M → F` is a family of functions such that `g i` is smooth on `U i`,
then the sum `λ x, ∑ᶠ i, f i x • g i x` is smooth on the whole manifold. -/
theorem IsSubordinate.smooth_finsum_smul {g : ι → M → F} (hf : f.IsSubordinate U)
    (ho : ∀ i, IsOpen (U i)) (hg : ∀ i, SmoothOn I 𝓘(ℝ, F) (g i) (U i)) :
    Smooth I 𝓘(ℝ, F) fun x => ∑ᶠ i, f i x • g i x :=
  hf.contMDiff_finsum_smul ho hg
#align smooth_partition_of_unity.is_subordinate.smooth_finsum_smul SmoothPartitionOfUnity.IsSubordinate.smooth_finsum_smul

end SmoothPartitionOfUnity

namespace BumpCovering

-- Repeat variables to drop `[FiniteDimensional ℝ E]` and `[SmoothManifoldWithCorners I M]`
theorem smooth_toPartitionOfUnity {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M] {s : Set M} (f : BumpCovering ι M s)
    (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) (i : ι) : Smooth I 𝓘(ℝ) (f.toPartitionOfUnity i) :=
  (hf i).mul <| (smooth_finprod_cond fun j _ => smooth_const.sub (hf j)) <| by
    simp only [Pi.sub_def, mulSupport_one_sub]
    -- ⊢ LocallyFinite fun i => support fun x => ↑(↑f i) x
    exact f.locallyFinite
    -- 🎉 no goals
#align bump_covering.smooth_to_partition_of_unity BumpCovering.smooth_toPartitionOfUnity

variable {s : Set M}

/-- A `BumpCovering` such that all functions in this covering are smooth generates a smooth
partition of unity.

In our formalization, not every `f : BumpCovering ι M s` with smooth functions `f i` is a
`SmoothBumpCovering`; instead, a `SmoothBumpCovering` is a covering by supports of
`SmoothBumpFunction`s. So, we define `BumpCovering.toSmoothPartitionOfUnity`, then reuse it
in `SmoothBumpCovering.toSmoothPartitionOfUnity`. -/
def toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) :
    SmoothPartitionOfUnity ι I M s :=
  { f.toPartitionOfUnity with
    toFun := fun i => ⟨f.toPartitionOfUnity i, f.smooth_toPartitionOfUnity hf i⟩ }
#align bump_covering.to_smooth_partition_of_unity BumpCovering.toSmoothPartitionOfUnity

@[simp]
theorem toSmoothPartitionOfUnity_toPartitionOfUnity (f : BumpCovering ι M s)
    (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) :
    (f.toSmoothPartitionOfUnity hf).toPartitionOfUnity = f.toPartitionOfUnity :=
  rfl
#align bump_covering.to_smooth_partition_of_unity_to_partition_of_unity BumpCovering.toSmoothPartitionOfUnity_toPartitionOfUnity

@[simp]
theorem coe_toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i))
    (i : ι) : ⇑(f.toSmoothPartitionOfUnity hf i) = f.toPartitionOfUnity i :=
  rfl
#align bump_covering.coe_to_smooth_partition_of_unity BumpCovering.coe_toSmoothPartitionOfUnity

theorem IsSubordinate.toSmoothPartitionOfUnity {f : BumpCovering ι M s} {U : ι → Set M}
    (h : f.IsSubordinate U) (hf : ∀ i, Smooth I 𝓘(ℝ) (f i)) :
    (f.toSmoothPartitionOfUnity hf).IsSubordinate U :=
  h.toPartitionOfUnity
#align bump_covering.is_subordinate.to_smooth_partition_of_unity BumpCovering.IsSubordinate.toSmoothPartitionOfUnity

end BumpCovering

namespace SmoothBumpCovering

variable {s : Set M} {U : M → Set M} (fs : SmoothBumpCovering ι I M s)

instance : CoeFun (SmoothBumpCovering ι I M s) fun x => ∀ i : ι, SmoothBumpFunction I (x.c i) :=
  ⟨toFun⟩

#noalign smooth_bump_covering.coe_mk

/--
We say that `f : SmoothBumpCovering ι I M s` is *subordinate* to a map `U : M → Set M` if for each
index `i`, we have `tsupport (f i) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.
-/
def IsSubordinate {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M → Set M) :=
  ∀ i, tsupport (f i) ⊆ U (f.c i)
#align smooth_bump_covering.is_subordinate SmoothBumpCovering.IsSubordinate

theorem IsSubordinate.support_subset {fs : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : fs.IsSubordinate U) (i : ι) : support (fs i) ⊆ U (fs.c i) :=
  Subset.trans subset_closure (h i)
#align smooth_bump_covering.is_subordinate.support_subset SmoothBumpCovering.IsSubordinate.support_subset

variable (I)

/-- Let `M` be a smooth manifold with corners modelled on a finite dimensional real vector space.
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → Set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
theorem exists_isSubordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s)
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ (ι : Type uM) (f : SmoothBumpCovering ι I M s), f.IsSubordinate U := by
  -- First we deduce some missing instances
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  -- ⊢ ∃ ι f, IsSubordinate f U
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- ⊢ ∃ ι f, IsSubordinate f U
  haveI : NormalSpace M := normal_of_paracompact_t2
  -- ⊢ ∃ ι f, IsSubordinate f U
  -- Next we choose a covering by supports of smooth bump functions
  have hB := fun x hx => SmoothBumpFunction.nhds_basis_support I (hU x hx)
  -- ⊢ ∃ ι f, IsSubordinate f U
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs hB with
    ⟨ι, c, f, hf, hsub', hfin⟩
  choose hcs hfU using hf
  -- ⊢ ∃ ι f, IsSubordinate f U
  -- Then we use the shrinking lemma to get a covering by smaller open
  rcases exists_subset_iUnion_closed_subset hs (fun i => (f i).isOpen_support)
    (fun x _ => hfin.point_finite x) hsub' with ⟨V, hsV, hVc, hVf⟩
  choose r hrR hr using fun i => (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i)
  -- ⊢ ∃ ι f, IsSubordinate f U
  refine' ⟨ι, ⟨c, fun i => (f i).updateRIn (r i) (hrR i), hcs, _, fun x hx => _⟩, fun i => _⟩
  · simpa only [SmoothBumpFunction.support_updateRIn]
    -- 🎉 no goals
  · refine' (mem_iUnion.1 <| hsV hx).imp fun i hi => _
    -- ⊢ ↑((fun i => SmoothBumpFunction.updateRIn (f i) (r i) (_ : r i ∈ Ioo 0 (f i). …
    exact ((f i).updateRIn _ _).eventuallyEq_one_of_dist_lt
      ((f i).support_subset_source <| hVf _ hi) (hr i hi).2
  · simpa only [SmoothBumpFunction.support_updateRIn, tsupport] using hfU i
    -- 🎉 no goals
#align smooth_bump_covering.exists_is_subordinate SmoothBumpCovering.exists_isSubordinate

variable {I}

protected theorem locallyFinite : LocallyFinite fun i => support (fs i) :=
  fs.locallyFinite'
#align smooth_bump_covering.locally_finite SmoothBumpCovering.locallyFinite

protected theorem point_finite (x : M) : {i | fs i x ≠ 0}.Finite :=
  fs.locallyFinite.point_finite x
#align smooth_bump_covering.point_finite SmoothBumpCovering.point_finite

theorem mem_chartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x ∈ (chartAt H (fs.c i)).source :=
  (fs i).support_subset_source <| by simp [h]
                                     -- 🎉 no goals
#align smooth_bump_covering.mem_chart_at_source_of_eq_one SmoothBumpCovering.mem_chartAt_source_of_eq_one

theorem mem_extChartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x ∈ (extChartAt I (fs.c i)).source := by
  rw [extChartAt_source]; exact fs.mem_chartAt_source_of_eq_one h
  -- ⊢ x ∈ (chartAt H (c s fs i)).toLocalEquiv.source
                          -- 🎉 no goals
#align smooth_bump_covering.mem_ext_chart_at_source_of_eq_one SmoothBumpCovering.mem_extChartAt_source_of_eq_one

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : ι :=
  (fs.eventuallyEq_one' x hx).choose
#align smooth_bump_covering.ind SmoothBumpCovering.ind

theorem eventuallyEq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
  (fs.eventuallyEq_one' x hx).choose_spec
#align smooth_bump_covering.eventually_eq_one SmoothBumpCovering.eventuallyEq_one

theorem apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
  (fs.eventuallyEq_one x hx).eq_of_nhds
#align smooth_bump_covering.apply_ind SmoothBumpCovering.apply_ind

theorem mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (fs <| fs.ind x hx) := by
  simp [fs.apply_ind x hx]
  -- 🎉 no goals
#align smooth_bump_covering.mem_support_ind SmoothBumpCovering.mem_support_ind

theorem mem_chartAt_ind_source (x : M) (hx : x ∈ s) : x ∈ (chartAt H (fs.c (fs.ind x hx))).source :=
  fs.mem_chartAt_source_of_eq_one (fs.apply_ind x hx)
#align smooth_bump_covering.mem_chart_at_ind_source SmoothBumpCovering.mem_chartAt_ind_source

theorem mem_extChartAt_ind_source (x : M) (hx : x ∈ s) :
    x ∈ (extChartAt I (fs.c (fs.ind x hx))).source :=
  fs.mem_extChartAt_source_of_eq_one (fs.apply_ind x hx)
#align smooth_bump_covering.mem_ext_chart_at_ind_source SmoothBumpCovering.mem_extChartAt_ind_source

/-- The index type of a `SmoothBumpCovering` of a compact manifold is finite. -/
protected def fintype [CompactSpace M] : Fintype ι :=
  fs.locallyFinite.fintypeOfCompact fun i => (fs i).nonempty_support
#align smooth_bump_covering.fintype SmoothBumpCovering.fintype

variable [T2Space M]

/-- Reinterpret a `SmoothBumpCovering` as a continuous `BumpCovering`. Note that not every
`f : BumpCovering ι M s` with smooth functions `f i` is a `SmoothBumpCovering`. -/
def toBumpCovering : BumpCovering ι M s where
  toFun i := ⟨fs i, (fs i).continuous⟩
  locallyFinite' := fs.locallyFinite
  nonneg' i _ := (fs i).nonneg
  le_one' i _ := (fs i).le_one
  eventuallyEq_one' := fs.eventuallyEq_one'
#align smooth_bump_covering.to_bump_covering SmoothBumpCovering.toBumpCovering

-- Porting note: `simpNF` says that `simp` can't simplify LHS but it can.
@[simp, nolint simpNF]
theorem isSubordinate_toBumpCovering {f : SmoothBumpCovering ι I M s} {U : M → Set M} :
    (f.toBumpCovering.IsSubordinate fun i => U (f.c i)) ↔ f.IsSubordinate U :=
  Iff.rfl
#align smooth_bump_covering.is_subordinate_to_bump_covering SmoothBumpCovering.isSubordinate_toBumpCovering

alias ⟨_, IsSubordinate.toBumpCovering⟩ := isSubordinate_toBumpCovering
#align smooth_bump_covering.is_subordinate.to_bump_covering SmoothBumpCovering.IsSubordinate.toBumpCovering

/-- Every `SmoothBumpCovering` defines a smooth partition of unity. -/
def toSmoothPartitionOfUnity : SmoothPartitionOfUnity ι I M s :=
  fs.toBumpCovering.toSmoothPartitionOfUnity fun i => (fs i).smooth
#align smooth_bump_covering.to_smooth_partition_of_unity SmoothBumpCovering.toSmoothPartitionOfUnity

theorem toSmoothPartitionOfUnity_apply (i : ι) (x : M) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - fs j x) :=
  rfl
#align smooth_bump_covering.to_smooth_partition_of_unity_apply SmoothBumpCovering.toSmoothPartitionOfUnity_apply

theorem toSmoothPartitionOfUnity_eq_mul_prod (i : ι) (x : M) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → fs j x ≠ 0 → j ∈ t) :
    fs.toSmoothPartitionOfUnity i x =
      fs i x * ∏ j in t.filter fun j => WellOrderingRel j i, (1 - fs j x) :=
  fs.toBumpCovering.toPartitionOfUnity_eq_mul_prod i x t ht
#align smooth_bump_covering.to_smooth_partition_of_unity_eq_mul_prod SmoothBumpCovering.toSmoothPartitionOfUnity_eq_mul_prod

theorem exists_finset_toSmoothPartitionOfUnity_eventuallyEq (i : ι) (x : M) :
    ∃ t : Finset ι,
      fs.toSmoothPartitionOfUnity i =ᶠ[𝓝 x]
        fs i * ∏ j in t.filter fun j => WellOrderingRel j i, ((1 : M → ℝ) - fs j) := by
  -- porting note: was defeq, now the continuous lemma uses bundled homs
  simpa using fs.toBumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq i x
  -- 🎉 no goals
#align smooth_bump_covering.exists_finset_to_smooth_partition_of_unity_eventually_eq SmoothBumpCovering.exists_finset_toSmoothPartitionOfUnity_eventuallyEq

theorem toSmoothPartitionOfUnity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) :
    fs.toSmoothPartitionOfUnity i x = 0 :=
  fs.toBumpCovering.toPartitionOfUnity_zero_of_zero h
#align smooth_bump_covering.to_smooth_partition_of_unity_zero_of_zero SmoothBumpCovering.toSmoothPartitionOfUnity_zero_of_zero

theorem support_toSmoothPartitionOfUnity_subset (i : ι) :
    support (fs.toSmoothPartitionOfUnity i) ⊆ support (fs i) :=
  fs.toBumpCovering.support_toPartitionOfUnity_subset i
#align smooth_bump_covering.support_to_smooth_partition_of_unity_subset SmoothBumpCovering.support_toSmoothPartitionOfUnity_subset

theorem IsSubordinate.toSmoothPartitionOfUnity {f : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : f.IsSubordinate U) : f.toSmoothPartitionOfUnity.IsSubordinate fun i => U (f.c i) :=
  h.toBumpCovering.toPartitionOfUnity
#align smooth_bump_covering.is_subordinate.to_smooth_partition_of_unity SmoothBumpCovering.IsSubordinate.toSmoothPartitionOfUnity

theorem sum_toSmoothPartitionOfUnity_eq (x : M) :
    ∑ᶠ i, fs.toSmoothPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
  fs.toBumpCovering.sum_toPartitionOfUnity_eq x
#align smooth_bump_covering.sum_to_smooth_partition_of_unity_eq SmoothBumpCovering.sum_toSmoothPartitionOfUnity_eq

end SmoothBumpCovering

variable (I)

/-- Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite dimensional manifold,
there exists an infinitely smooth function that is equal to `0` on `s` and to `1` on `t`.
See also `exists_smooth_zero_iff_one_iff_of_closed`, which ensures additionally that
`f` is equal to `0` exactly on `s` and to `1` exactly on `t`. -/
theorem exists_smooth_zero_one_of_closed [T2Space M] [SigmaCompactSpace M] {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  have : ∀ x ∈ t, sᶜ ∈ 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  -- ⊢ ∃ f, EqOn (↑f) 0 s ∧ EqOn (↑f) 1 t ∧ ∀ (x : M), ↑f x ∈ Icc 0 1
  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
  -- ⊢ ∃ f, EqOn (↑f) 0 s ∧ EqOn (↑f) 1 t ∧ ∀ (x : M), ↑f x ∈ Icc 0 1
  set g := f.toSmoothPartitionOfUnity
  -- ⊢ ∃ f, EqOn (↑f) 0 s ∧ EqOn (↑f) 1 t ∧ ∀ (x : M), ↑f x ∈ Icc 0 1
  refine'
    ⟨⟨_, g.smooth_sum⟩, fun x hx => _, fun x => g.sum_eq_one, fun x =>
      ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩
  suffices ∀ i, g i x = 0 by simp only [this, ContMDiffMap.coeFn_mk, finsum_zero, Pi.zero_apply]
  -- ⊢ ∀ (i : ι), ↑(↑g i) x = 0
  refine' fun i => f.toSmoothPartitionOfUnity_zero_of_zero _
  -- ⊢ ↑(SmoothBumpCovering.toFun t f i) x = 0
  exact nmem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)
  -- 🎉 no goals
#align exists_smooth_zero_one_of_closed exists_smooth_zero_one_of_closed

namespace SmoothPartitionOfUnity

/-- A `SmoothPartitionOfUnity` that consists of a single function, uniformly equal to one,
defined as an example for `Inhabited` instance. -/
def single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s :=
  (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    rcases eq_or_ne j i with (rfl | h)
    -- ⊢ Smooth I 𝓘(ℝ, ℝ) ↑(↑(BumpCovering.single j s) j)
    · simp only [smooth_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
      -- 🎉 no goals
    · simp only [smooth_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h, ContinuousMap.coe_zero]
      -- 🎉 no goals
#align smooth_partition_of_unity.single SmoothPartitionOfUnity.single

instance [Inhabited ι] (s : Set M) : Inhabited (SmoothPartitionOfUnity ι I M s) :=
  ⟨single I default s⟩

variable [T2Space M] [SigmaCompactSpace M]

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `SmoothPartitionOfUnity ι M s` that is subordinate to `U`. -/
theorem exists_isSubordinate {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) : ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  -- ⊢ ∃ f, IsSubordinate f U
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- ⊢ ∃ f, IsSubordinate f U
  haveI : NormalSpace M := normal_of_paracompact_t2
  -- ⊢ ∃ f, IsSubordinate f U
  -- porting note(https://github.com/leanprover/std4/issues/116):
  -- split `rcases` into `have` + `rcases`
  have := BumpCovering.exists_isSubordinate_of_prop (Smooth I 𝓘(ℝ)) ?_ hs U ho hU
  -- ⊢ ∃ f, IsSubordinate f U
  · rcases this with ⟨f, hf, hfU⟩
    -- ⊢ ∃ f, IsSubordinate f U
    exact ⟨f.toSmoothPartitionOfUnity hf, hfU.toSmoothPartitionOfUnity hf⟩
    -- 🎉 no goals
  · intro s t hs ht hd
    -- ⊢ ∃ f, Smooth I 𝓘(ℝ, ℝ) ↑f ∧ EqOn (↑f) 0 s ∧ EqOn (↑f) 1 t ∧ ∀ (x : M), ↑f x ∈ …
    rcases exists_smooth_zero_one_of_closed I hs ht hd with ⟨f, hf⟩
    -- ⊢ ∃ f, Smooth I 𝓘(ℝ, ℝ) ↑f ∧ EqOn (↑f) 0 s ∧ EqOn (↑f) 1 t ∧ ∀ (x : M), ↑f x ∈ …
    exact ⟨f, f.smooth, hf⟩
    -- 🎉 no goals
#align smooth_partition_of_unity.exists_is_subordinate SmoothPartitionOfUnity.exists_isSubordinate

theorem exists_isSubordinate_chartAt_source_of_isClosed {s : Set M} (hs : IsClosed s) :
    ∃ f : SmoothPartitionOfUnity s I M s,
      f.IsSubordinate (fun x ↦ (chartAt H (x : M)).source) := by
  apply exists_isSubordinate _ hs _ (fun i ↦ (chartAt H _).open_source) (fun x hx ↦ ?_)
  -- ⊢ x ∈ ⋃ (i : ↑s), (chartAt H ↑i).toLocalEquiv.source
  exact mem_iUnion_of_mem ⟨x, hx⟩ (mem_chart_source H x)
  -- 🎉 no goals

variable (M)
theorem exists_isSubordinate_chartAt_source :
    ∃ f : SmoothPartitionOfUnity M I M univ, f.IsSubordinate (fun x ↦ (chartAt H x).source) := by
  apply exists_isSubordinate _ isClosed_univ _ (fun i ↦ (chartAt H _).open_source) (fun x _ ↦ ?_)
  -- ⊢ x ∈ ⋃ (i : M), (chartAt H i).toLocalEquiv.source
  exact mem_iUnion_of_mem x (mem_chart_source H x)
  -- 🎉 no goals

end SmoothPartitionOfUnity

variable [SigmaCompactSpace M] [T2Space M] {t : M → Set F} {n : ℕ∞}

/-- Let `M` be a σ-compact Hausdorff finite dimensional topological manifold. Let `t : M → Set F`
be a family of convex sets. Suppose that for each point `x : M` there exists a neighborhood
`U ∈ 𝓝 x` and a function `g : M → F` such that `g` is $C^n$ smooth on `U` and `g y ∈ t y` for all
`y ∈ U`. Then there exists a $C^n$ smooth function `g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x`
for all `x`. See also `exists_smooth_forall_mem_convex_of_local` and
`exists_smooth_forall_mem_convex_of_local_const`. -/
theorem exists_contMDiffOn_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → F, ContMDiffOn I 𝓘(ℝ, F) n g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x := by
  choose U hU g hgs hgt using Hloc
  -- ⊢ ∃ g, ∀ (x : M), ↑g x ∈ t x
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ (fun x => interior (U x))
      (fun x => isOpen_interior) fun x _ => mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine' ⟨⟨fun x => ∑ᶠ i, f i x • g i x,
      hf.contMDiff_finsum_smul (fun i => isOpen_interior) fun i => (hgs i).mono interior_subset⟩,
    fun x => f.finsum_smul_mem_convex (mem_univ x) (fun i hi => hgt _ _ _) (ht _)⟩
  exact interior_subset (hf _ <| subset_closure hi)
  -- 🎉 no goals
#align exists_cont_mdiff_forall_mem_convex_of_local exists_contMDiffOn_forall_mem_convex_of_local

/-- Let `M` be a σ-compact Hausdorff finite dimensional topological manifold. Let `t : M → Set F`
be a family of convex sets. Suppose that for each point `x : M` there exists a neighborhood
`U ∈ 𝓝 x` and a function `g : M → F` such that `g` is smooth on `U` and `g y ∈ t y` for all `y ∈ U`.
Then there exists a smooth function `g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x` for all `x`.
See also `exists_contMDiffOn_forall_mem_convex_of_local` and
`exists_smooth_forall_mem_convex_of_local_const`. -/
theorem exists_smooth_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → F, SmoothOn I 𝓘(ℝ, F) g U ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  exists_contMDiffOn_forall_mem_convex_of_local I ht Hloc
#align exists_smooth_forall_mem_convex_of_local exists_smooth_forall_mem_convex_of_local

/-- Let `M` be a σ-compact Hausdorff finite dimensional topological manifold. Let `t : M → Set F` be
a family of convex sets. Suppose that for each point `x : M` there exists a vector `c : F` such that
for all `y` in a neighborhood of `x` we have `c ∈ t y`. Then there exists a smooth function
`g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x` for all `x`.  See also
`exists_contMDiffOn_forall_mem_convex_of_local` and `exists_smooth_forall_mem_convex_of_local`. -/
theorem exists_smooth_forall_mem_convex_of_local_const (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ c : F, ∀ᶠ y in 𝓝 x, c ∈ t y) : ∃ g : C^∞⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  exists_smooth_forall_mem_convex_of_local I ht fun x =>
    let ⟨c, hc⟩ := Hloc x
    ⟨_, hc, fun _ => c, smoothOn_const, fun _ => id⟩
#align exists_smooth_forall_mem_convex_of_local_const exists_smooth_forall_mem_convex_of_local_const

/-- Let `M` be a smooth σ-compact manifold with extended distance. Let `K : ι → Set M` be a locally
finite family of closed sets, let `U : ι → Set M` be a family of open sets such that `K i ⊆ U i` for
all `i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for any `i` and
`x ∈ K i`, we have `EMetric.closedBall x (δ x) ⊆ U i`. -/
theorem Emetric.exists_smooth_forall_closedBall_subset {M} [EMetricSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M}
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hfin : LocallyFinite K) :
    ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, EMetric.closedBall x (ENNReal.ofReal (δ x)) ⊆ U i := by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_swap ι M]
    using exists_smooth_forall_mem_convex_of_local_const I
      EMetric.exists_forall_closedBall_subset_aux₂
      (EMetric.exists_forall_closedBall_subset_aux₁ hK hU hKU hfin)
#align emetric.exists_smooth_forall_closed_ball_subset Emetric.exists_smooth_forall_closedBall_subset

/-- Let `M` be a smooth σ-compact manifold with a metric. Let `K : ι → Set M` be a locally finite
family of closed sets, let `U : ι → Set M` be a family of open sets such that `K i ⊆ U i` for all
`i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for any `i` and `x ∈ K i`,
we have `Metric.closedBall x (δ x) ⊆ U i`. -/
theorem Metric.exists_smooth_forall_closedBall_subset {M} [MetricSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M}
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hfin : LocallyFinite K) :
    ∃ δ : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, Metric.closedBall x (δ x) ⊆ U i := by
  rcases Emetric.exists_smooth_forall_closedBall_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  -- ⊢ ∃ δ, (∀ (x : M), 0 < ↑δ x) ∧ ∀ (i : ι) (x : M), x ∈ K i → closedBall x (↑δ x …
  refine' ⟨δ, hδ0, fun i x hx => _⟩
  -- ⊢ closedBall x (↑δ x) ⊆ U i
  rw [← Metric.emetric_closedBall (hδ0 _).le]
  -- ⊢ EMetric.closedBall x (ENNReal.ofReal (↑δ x)) ⊆ U i
  exact hδ i x hx
  -- 🎉 no goals
#align metric.exists_smooth_forall_closed_ball_subset Metric.exists_smooth_forall_closedBall_subset

lemma IsOpen.exists_msmooth_support_eq_aux {s : Set H} (hs : IsOpen s) :
    ∃ f : H → ℝ, f.support = s ∧ Smooth I 𝓘(ℝ) f ∧ Set.range f ⊆ Set.Icc 0 1 := by
  have h's : IsOpen (I.symm ⁻¹' s) := I.continuous_symm.isOpen_preimage _ hs
  -- ⊢ ∃ f, support f = s ∧ Smooth I 𝓘(ℝ, ℝ) f ∧ range f ⊆ Icc 0 1
  rcases h's.exists_smooth_support_eq with ⟨f, f_supp, f_diff, f_range⟩
  -- ⊢ ∃ f, support f = s ∧ Smooth I 𝓘(ℝ, ℝ) f ∧ range f ⊆ Icc 0 1
  refine ⟨f ∘ I, ?_, ?_, ?_⟩
  · rw [support_comp_eq_preimage, f_supp, ← preimage_comp]
    -- ⊢ ↑(ModelWithCorners.symm I) ∘ ↑I ⁻¹' s = s
    simp only [ModelWithCorners.symm_comp_self, preimage_id_eq, id_eq]
    -- 🎉 no goals
  · exact f_diff.comp_contMDiff contMDiff_model
    -- 🎉 no goals
  · exact Subset.trans (range_comp_subset_range _ _) f_range
    -- 🎉 no goals

/-- Given an open set in a finite-dimensional real manifold, there exists a nonnegative smooth
function with support equal to `s`. -/
theorem IsOpen.exists_msmooth_support_eq (hs : IsOpen s) :
    ∃ f : M → ℝ, f.support = s ∧ Smooth I 𝓘(ℝ) f ∧ ∀ x, 0 ≤ f x := by
  rcases SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M with ⟨f, hf⟩
  -- ⊢ ∃ f, support f = s ∧ Smooth I 𝓘(ℝ, ℝ) f ∧ ∀ (x : M), 0 ≤ f x
  have A : ∀ (c : M), ∃ g : H → ℝ,
      g.support = (chartAt H c).target ∩ (chartAt H c).symm ⁻¹' s ∧
      Smooth I 𝓘(ℝ) g ∧ Set.range g ⊆ Set.Icc 0 1 := by
    intro i
    apply IsOpen.exists_msmooth_support_eq_aux
    exact LocalHomeomorph.preimage_open_of_open_symm _ hs
  choose g g_supp g_diff hg using A
  -- ⊢ ∃ f, support f = s ∧ Smooth I 𝓘(ℝ, ℝ) f ∧ ∀ (x : M), 0 ≤ f x
  have h'g : ∀ c x, 0 ≤ g c x := fun c x ↦ (hg c (mem_range_self (f := g c) x)).1
  -- ⊢ ∃ f, support f = s ∧ Smooth I 𝓘(ℝ, ℝ) f ∧ ∀ (x : M), 0 ≤ f x
  have h''g : ∀ c x, 0 ≤ f c x * g c (chartAt H c x) :=
    fun c x ↦ mul_nonneg (f.nonneg c x) (h'g c _)
  refine ⟨fun x ↦ ∑ᶠ c, f c x * g c (chartAt H c x), ?_, ?_, ?_⟩
  · refine support_eq_iff.2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    -- ⊢ ∑ᶠ (c : M), ↑(↑f c) x * g c (↑(chartAt H c) x) ≠ 0
    · apply ne_of_gt
      -- ⊢ 0 < ∑ᶠ (c : M), ↑(↑f c) x * g c (↑(chartAt H c) x)
      have B : ∃ c, 0 < f c x * g c (chartAt H c x) := by
        obtain ⟨c, hc⟩ : ∃ c, 0 < f c x := f.exists_pos_of_mem (mem_univ x)
        refine ⟨c, mul_pos hc ?_⟩
        apply lt_of_le_of_ne (h'g _ _) (Ne.symm _)
        rw [← mem_support, g_supp, ← mem_preimage, preimage_inter]
        have Hx : x ∈ tsupport (f c) := subset_tsupport _ (ne_of_gt hc)
        simp [(chartAt H c).left_inv (hf c Hx), hx, (chartAt H c).map_source (hf c Hx)]
      apply finsum_pos' (fun c ↦ h''g c x) B
      -- ⊢ Set.Finite (support fun c => ↑(↑f c) x * g c (↑(chartAt H c) x))
      apply (f.locallyFinite.point_finite x).subset
      -- ⊢ (support fun c => ↑(↑f c) x * g c (↑(chartAt H c) x)) ⊆ {b | x ∈ support ↑(↑ …
      apply compl_subset_compl.2
      -- ⊢ (fun x_1 => ↑(↑f x_1) x = 0) ⊆ fun x_1 => (fun c => ↑(↑f c) x * g c (↑(chart …
      rintro c (hc : f c x = 0)
      -- ⊢ c ∈ fun x_1 => (fun c => ↑(↑f c) x * g c (↑(chartAt H c) x)) x_1 = 0
      simpa only [mul_eq_zero] using Or.inl hc
      -- 🎉 no goals
    · apply finsum_eq_zero_of_forall_eq_zero
      -- ⊢ ∀ (x_1 : M), ↑(↑f x_1) x * g x_1 (↑(chartAt H x_1) x) = 0
      intro c
      -- ⊢ ↑(↑f c) x * g c (↑(chartAt H c) x) = 0
      by_cases Hx : x ∈ tsupport (f c)
      -- ⊢ ↑(↑f c) x * g c (↑(chartAt H c) x) = 0
      · suffices g c (chartAt H c x) = 0 by simp only [this, mul_zero]
        -- ⊢ g c (↑(chartAt H c) x) = 0
        rw [← nmem_support, g_supp, ← mem_preimage, preimage_inter]
        -- ⊢ ¬x ∈ ↑(chartAt H c) ⁻¹' (chartAt H c).toLocalEquiv.target ∩ ↑(chartAt H c) ⁻ …
        contrapose! hx
        -- ⊢ x ∈ s
        simp only [mem_inter_iff, mem_preimage, (chartAt H c).left_inv (hf c Hx)] at hx
        -- ⊢ x ∈ s
        exact hx.2
        -- 🎉 no goals
      · have : x ∉ support (f c) := by contrapose! Hx; exact subset_tsupport _ Hx
        -- ⊢ ↑(↑f c) x * g c (↑(chartAt H c) x) = 0
        rw [nmem_support] at this
        -- ⊢ ↑(↑f c) x * g c (↑(chartAt H c) x) = 0
        simp [this]
        -- 🎉 no goals
  · apply SmoothPartitionOfUnity.smooth_finsum_smul
    -- ⊢ ∀ (i x : M), x ∈ tsupport ↑(↑f i) → SmoothAt I 𝓘(ℝ, ℝ) (fun x => g i (↑(char …
    intro c x hx
    -- ⊢ SmoothAt I 𝓘(ℝ, ℝ) (fun x => g c (↑(chartAt H c) x)) x
    apply (g_diff c (chartAt H c x)).comp
    -- ⊢ ContMDiffAt I I ⊤ (↑(chartAt H c)) x
    exact contMDiffAt_of_mem_maximalAtlas (SmoothManifoldWithCorners.chart_mem_maximalAtlas I _)
      (hf c hx)
  · intro x
    -- ⊢ 0 ≤ (fun x => ∑ᶠ (c : M), ↑(↑f c) x * g c (↑(chartAt H c) x)) x
    apply finsum_nonneg (fun c ↦ h''g c x)
    -- 🎉 no goals

/-- Given an open set `s` containing a closed set `t` in a finite-dimensional real manifold, there
exists a smooth function with support equal to `s`, taking values in `[0,1]`, and equal to `1`
exactly on `t`. -/
theorem exists_msmooth_support_eq_eq_one_iff
    {s t : Set M} (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : M → ℝ, Smooth I 𝓘(ℝ) f ∧ range f ⊆ Icc 0 1 ∧ support f = s
      ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  /- Take `f` with support equal to `s`, and `g` with support equal to `tᶜ`. Then `f / (f + g)`
  satisfies the conclusion of the theorem. -/
  rcases hs.exists_msmooth_support_eq I with ⟨f, f_supp, f_diff, f_pos⟩
  -- ⊢ ∃ f, Smooth I 𝓘(ℝ, ℝ) f ∧ range f ⊆ Icc 0 1 ∧ support f = s ∧ ∀ (x : M), x ∈ …
  rcases ht.isOpen_compl.exists_msmooth_support_eq I with ⟨g, g_supp, g_diff, g_pos⟩
  -- ⊢ ∃ f, Smooth I 𝓘(ℝ, ℝ) f ∧ range f ⊆ Icc 0 1 ∧ support f = s ∧ ∀ (x : M), x ∈ …
  have A : ∀ x, 0 < f x + g x := by
    intro x
    by_cases xs : x ∈ support f
    · have : 0 < f x := lt_of_le_of_ne (f_pos x) (Ne.symm xs)
      linarith [g_pos x]
    · have : 0 < g x := by
        apply lt_of_le_of_ne (g_pos x) (Ne.symm ?_)
        rw [← mem_support, g_supp]
        contrapose! xs
        simp at xs
        exact h.trans f_supp.symm.subset xs
      linarith [f_pos x]
  refine ⟨fun x ↦ f x / (f x + g x), ?_, ?_, ?_, ?_⟩
  -- show that `f / (f + g)` is smooth
  · exact f_diff.div₀ (f_diff.add g_diff) (fun x ↦ ne_of_gt (A x))
    -- 🎉 no goals
  -- show that the range is included in `[0, 1]`
  · refine range_subset_iff.2 (fun x ↦ ⟨div_nonneg (f_pos x) (A x).le, ?_⟩)
    -- ⊢ f x / (f x + g x) ≤ 1
    apply div_le_one_of_le _ (A x).le
    -- ⊢ f x ≤ f x + g x
    simpa only [le_add_iff_nonneg_right] using g_pos x
    -- 🎉 no goals
  -- show that the support is `s`
  · have B : support (fun x ↦ f x + g x) = univ := eq_univ_of_forall (fun x ↦ (A x).ne')
    -- ⊢ (support fun x => f x / (f x + g x)) = s
    simp only [support_div, f_supp, B, inter_univ]
    -- 🎉 no goals
  -- show that the function equals one exactly on `t`
  · intro x
    -- ⊢ x ∈ t ↔ (fun x => f x / (f x + g x)) x = 1
    simp [div_eq_one_iff_eq (A x).ne', self_eq_add_right, ← nmem_support, g_supp]
    -- 🎉 no goals

/-- Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite dimensional manifold,
there exists an infinitely smooth function that is equal to `0` exactly on `s` and to `1`
exactly on `t`. See also `exists_smooth_zero_one_of_closed` for a slightly weaker version. -/
theorem exists_msmooth_zero_iff_one_iff_of_closed {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : M → ℝ, Smooth I 𝓘(ℝ) f ∧ range f ⊆ Icc 0 1 ∧ (∀ x, x ∈ s ↔ f x = 0)
      ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  rcases exists_msmooth_support_eq_eq_one_iff I hs.isOpen_compl ht hd.subset_compl_left with
    ⟨f, f_diff, f_range, fs, ft⟩
  refine ⟨f, f_diff, f_range, ?_, ft⟩
  -- ⊢ ∀ (x : M), x ∈ s ↔ f x = 0
  simp [← nmem_support, fs]
  -- 🎉 no goals
