/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
public import Mathlib.Topology.MetricSpace.PartitionOfUnity
public import Mathlib.Topology.ShrinkingLemma

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

We prove that on a smooth finite-dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → Set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `SmoothBumpCovering ι I M s`
subordinate to `U`. Then we use this fact to prove a similar statement about smooth partitions of
unity, see `SmoothPartitionOfUnity.exists_isSubordinate`.

Finally, we use existence of a partition of unity to prove lemma
`exists_contMDiffMap_forall_mem_convex_of_local` that allows us to construct a globally defined
smooth function from local functions.

## TODO

* Build a framework to transfer local definitions to global using partition of unity and use it
  to define, e.g., the integral of a differential form over a manifold. Lemma
  `exists_contMDiffMap_forall_mem_convex_of_local` is a first step in this direction.

## Tags

smooth bump function, partition of unity
-/

@[expose] public section

universe uι uE uH uM uF

open Bundle Function Filter Module Set
open scoped Topology Manifold ContDiff

noncomputable section

variable {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] {H : Type uH}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type uM} [TopologicalSpace M]
  [ChartedSpace H M]

/-!
### Covering by supports of smooth bump functions

In this section we define `SmoothBumpCovering ι I M s` to be a collection of
`SmoothBumpFunction`s such that their supports are a locally finite family of sets and for each
`x ∈ s` some function `f i` from the collection is equal to `1` in a neighborhood of `x`. A covering
of this type is useful to construct a smooth partition of unity and can be used instead of a
partition of unity in some proofs.

We prove that on a smooth finite-dimensional real manifold with `σ`-compact Hausdorff topology, for
any `U : M → Set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `SmoothBumpCovering ι I M s`
subordinate to `U`. -/

variable (ι M)

/-- We say that a collection of `SmoothBumpFunction`s is a `SmoothBumpCovering` of a set `s` if

* `(f i).c ∈ s` for all `i`;
* the family `fun i ↦ support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;

If `M` is a finite-dimensional real manifold which is a `σ`-compact Hausdorff topological space,
then for every covering `U : M → Set M`, `∀ x, U x ∈ 𝓝 x`, there exists a `SmoothBumpCovering`
subordinate to `U`, see `SmoothBumpCovering.exists_isSubordinate`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
structure SmoothBumpCovering [FiniteDimensional ℝ E] (s : Set M := univ) where
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

/-- We say that a collection of functions form a smooth partition of unity on a set `s` if

* all functions are infinitely smooth and nonnegative;
* the family `fun i ↦ support (f i)` is locally finite;
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

variable {ι I M}

namespace SmoothPartitionOfUnity

variable {s : Set M} (f : SmoothPartitionOfUnity ι I M s) {n : ℕ∞}

instance {s : Set M} : FunLike (SmoothPartitionOfUnity ι I M s) ι C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

protected theorem locallyFinite : LocallyFinite fun i => support (f i) :=
  f.locallyFinite'

theorem nonneg (i : ι) (x : M) : 0 ≤ f i x :=
  f.nonneg' i x

theorem sum_eq_one {x} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 :=
  f.sum_eq_one' x hx

theorem exists_pos_of_mem {x} (hx : x ∈ s) : ∃ i, 0 < f i x := by
  by_contra! h
  have H : ∀ i, f i x = 0 := fun i ↦ le_antisymm (h i) (f.nonneg i x)
  have := f.sum_eq_one hx
  simp_rw [H] at this
  simpa

theorem sum_le_one (x : M) : ∑ᶠ i, f i x ≤ 1 :=
  f.sum_le_one' x

/-- Reinterpret a smooth partition of unity as a continuous partition of unity. -/
@[simps]
def toPartitionOfUnity : PartitionOfUnity ι M s :=
  { f with toFun := fun i => f i }

theorem contMDiff_sum : CMDiff ∞ fun x => ∑ᶠ i, f i x :=
  contMDiff_finsum (fun i => (f i).contMDiff) f.locallyFinite

theorem le_one (i : ι) (x : M) : f i x ≤ 1 :=
  f.toPartitionOfUnity.le_one i x

theorem sum_nonneg (x : M) : 0 ≤ ∑ᶠ i, f i x :=
  f.toPartitionOfUnity.sum_nonneg x

theorem finsum_smul_mem_convex {g : ι → M → F} {t : Set F} {x : M} (hx : x ∈ s)
    (hg : ∀ i, f i x ≠ 0 → g i x ∈ t) (ht : Convex ℝ t) : ∑ᶠ i, f i x • g i x ∈ t :=
  ht.finsum_mem (fun _ => f.nonneg _ _) (f.sum_eq_one hx) hg

theorem contMDiff_smul {g : M → F} {i} (hg : ∀ x ∈ tsupport (f i), CMDiffAt n g x) :
    CMDiff n fun x ↦ f i x • g x :=
  contMDiff_of_tsupport fun x hx =>
    ((f i).contMDiff.contMDiffAt.of_le (mod_cast le_top)).smul <| hg x
      <| tsupport_smul_subset_left _ _ hx

/-- If `f` is a smooth partition of unity on a set `s : Set M` and `g : ι → M → F` is a family of
functions such that `g i` is $C^n$ smooth at every point of the topological support of `f i`, then
the sum `fun x ↦ ∑ᶠ i, f i x • g i x` is smooth on the whole manifold. -/
theorem contMDiff_finsum_smul {g : ι → M → F}
    (hg : ∀ (i), ∀ x ∈ tsupport (f i), CMDiffAt n (g i) x) :
    CMDiff n fun x => ∑ᶠ i, f i x • g i x :=
  (contMDiff_finsum fun i => f.contMDiff_smul (hg i)) <|
    f.locallyFinite.subset fun _ => support_smul_subset_left _ _

theorem contMDiffAt_finsum {x₀ : M} {g : ι → M → F}
    (hφ : ∀ i, x₀ ∈ tsupport (f i) → CMDiffAt n (g i) x₀) :
    CMDiffAt n (fun x ↦ ∑ᶠ i, f i x • g i x) x₀ := by
  refine _root_.contMDiffAt_finsum (f.locallyFinite.smul_left _) fun i ↦ ?_
  by_cases hx : x₀ ∈ tsupport (f i)
  · exact ContMDiffAt.smul ((f i).contMDiff.of_le (mod_cast le_top)).contMDiffAt (hφ i hx)
  · exact contMDiffAt_of_notMem (compl_subset_compl.mpr
      (tsupport_smul_subset_left (f i) (g i)) hx) n

theorem contDiffAt_finsum {s : Set E} (f : SmoothPartitionOfUnity ι 𝓘(ℝ, E) E s) {x₀ : E}
    {g : ι → E → F} (hφ : ∀ i, x₀ ∈ tsupport (f i) → ContDiffAt ℝ n (g i) x₀) :
    ContDiffAt ℝ n (fun x ↦ ∑ᶠ i, f i x • g i x) x₀ := by
  simp only [← contMDiffAt_iff_contDiffAt] at *
  exact f.contMDiffAt_finsum hφ

section finsupport

variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x₀ : M)

/-- The support of a smooth partition of unity at a point `x₀` as a `Finset`.
This is the set of `i : ι` such that `x₀ ∈ support f i`, i.e. `f i x₀ ≠ 0`. -/
def finsupport : Finset ι := ρ.toPartitionOfUnity.finsupport x₀

@[simp]
theorem mem_finsupport {i : ι} : i ∈ ρ.finsupport x₀ ↔ i ∈ support fun i ↦ ρ i x₀ :=
  ρ.toPartitionOfUnity.mem_finsupport x₀

@[simp]
theorem coe_finsupport : (ρ.finsupport x₀ : Set ι) = support fun i ↦ ρ i x₀ :=
  ρ.toPartitionOfUnity.coe_finsupport x₀

theorem sum_finsupport (hx₀ : x₀ ∈ s) : ∑ i ∈ ρ.finsupport x₀, ρ i x₀ = 1 :=
  ρ.toPartitionOfUnity.sum_finsupport hx₀

theorem sum_finsupport' (hx₀ : x₀ ∈ s) {I : Finset ι} (hI : ρ.finsupport x₀ ⊆ I) :
    ∑ i ∈ I, ρ i x₀ = 1 :=
  ρ.toPartitionOfUnity.sum_finsupport' hx₀ hI

theorem sum_finsupport_smul_eq_finsum {A : Type*} [AddCommGroup A] [Module ℝ A] (φ : ι → M → A) :
    ∑ i ∈ ρ.finsupport x₀, ρ i x₀ • φ i x₀ = ∑ᶠ i, ρ i x₀ • φ i x₀ :=
  ρ.toPartitionOfUnity.sum_finsupport_smul_eq_finsum φ

end finsupport

section fintsupport -- smooth partitions of unity have locally finite `tsupport`
variable {s : Set M} (ρ : SmoothPartitionOfUnity ι I M s) (x₀ : M)

/-- The `tsupport`s of a smooth partition of unity are locally finite. -/
theorem finite_tsupport : {i | x₀ ∈ tsupport (ρ i)}.Finite :=
  ρ.toPartitionOfUnity.finite_tsupport _

/-- The tsupport of a partition of unity at a point `x₀` as a `Finset`.
This is the set of `i : ι` such that `x₀ ∈ tsupport f i`. -/
def fintsupport (x : M) : Finset ι :=
  (ρ.finite_tsupport x).toFinset

theorem mem_fintsupport_iff (i : ι) : i ∈ ρ.fintsupport x₀ ↔ x₀ ∈ tsupport (ρ i) :=
  Finite.mem_toFinset _

theorem eventually_fintsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.fintsupport y ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.eventually_fintsupport_subset _

theorem finsupport_subset_fintsupport : ρ.finsupport x₀ ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.finsupport_subset_fintsupport x₀

theorem eventually_finsupport_subset : ∀ᶠ y in 𝓝 x₀, ρ.finsupport y ⊆ ρ.fintsupport x₀ :=
  ρ.toPartitionOfUnity.eventually_finsupport_subset x₀

end fintsupport

section IsSubordinate

/-- A smooth partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same
type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def IsSubordinate (f : SmoothPartitionOfUnity ι I M s) (U : ι → Set M) :=
  ∀ i, tsupport (f i) ⊆ U i

variable {f}
variable {U : ι → Set M}

@[simp]
theorem isSubordinate_toPartitionOfUnity :
    f.toPartitionOfUnity.IsSubordinate U ↔ f.IsSubordinate U :=
  Iff.rfl

alias ⟨_, IsSubordinate.toPartitionOfUnity⟩ := isSubordinate_toPartitionOfUnity

/-- If `f` is a smooth partition of unity on a set `s : Set M` subordinate to a family of open sets
`U : ι → Set M` and `g : ι → M → F` is a family of functions such that `g i` is $C^n$ smooth on
`U i`, then the sum `fun x ↦ ∑ᶠ i, f i x • g i x` is $C^n$ smooth on the whole manifold. -/
theorem IsSubordinate.contMDiff_finsum_smul {g : ι → M → F} (hf : f.IsSubordinate U)
    (ho : ∀ i, IsOpen (U i)) (hg : ∀ i, CMDiff[U i] n (g i)) :
    CMDiff n fun x => ∑ᶠ i, f i x • g i x :=
  f.contMDiff_finsum_smul fun i _ hx => (hg i).contMDiffAt <| (ho i).mem_nhds (hf i hx)

end IsSubordinate

end SmoothPartitionOfUnity

namespace BumpCovering

-- Repeat variables to drop `[FiniteDimensional ℝ E]` and `[IsManifold I ∞ M]`
theorem contMDiff_toPartitionOfUnity {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type uM}
    [TopologicalSpace M] [ChartedSpace H M] {s : Set M} (f : BumpCovering ι M s)
    (hf : ∀ i, CMDiff ∞ (f i)) (i : ι) : CMDiff ∞ (f.toPartitionOfUnity i) :=
  (hf i).mul <| (contMDiff_finprod_cond fun j _ => contMDiff_const.sub (hf j)) <| by
    simp only [mulSupport_one_sub]
    exact f.locallyFinite

variable {s : Set M}

/-- A `BumpCovering` such that all functions in this covering are smooth generates a smooth
partition of unity.

In our formalization, not every `f : BumpCovering ι M s` with smooth functions `f i` is a
`SmoothBumpCovering`; instead, a `SmoothBumpCovering` is a covering by supports of
`SmoothBumpFunction`s. So, we define `BumpCovering.toSmoothPartitionOfUnity`, then reuse it
in `SmoothBumpCovering.toSmoothPartitionOfUnity`. -/
def toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, CMDiff ∞ (f i)) :
    SmoothPartitionOfUnity ι I M s :=
  { f.toPartitionOfUnity with
    toFun := fun i => ⟨f.toPartitionOfUnity i, f.contMDiff_toPartitionOfUnity hf i⟩ }

@[simp]
theorem toSmoothPartitionOfUnity_toPartitionOfUnity (f : BumpCovering ι M s)
    (hf : ∀ i, CMDiff ∞ (f i)) :
    (f.toSmoothPartitionOfUnity hf).toPartitionOfUnity = f.toPartitionOfUnity :=
  rfl

@[simp]
theorem coe_toSmoothPartitionOfUnity (f : BumpCovering ι M s) (hf : ∀ i, CMDiff ∞ (f i))
    (i : ι) : ⇑(f.toSmoothPartitionOfUnity hf i) = f.toPartitionOfUnity i :=
  rfl

theorem IsSubordinate.toSmoothPartitionOfUnity {f : BumpCovering ι M s} {U : ι → Set M}
    (h : f.IsSubordinate U) (hf : ∀ i, CMDiff ∞ (f i)) :
    (f.toSmoothPartitionOfUnity hf).IsSubordinate U :=
  h.toPartitionOfUnity

end BumpCovering

namespace SmoothBumpCovering

variable [FiniteDimensional ℝ E]
variable {s : Set M} {U : M → Set M} (fs : SmoothBumpCovering ι I M s)

instance : CoeFun (SmoothBumpCovering ι I M s) fun x => ∀ i : ι, SmoothBumpFunction I (x.c i) :=
  ⟨toFun⟩

/--
We say that `f : SmoothBumpCovering ι I M s` is *subordinate* to a map `U : M → Set M` if for each
index `i`, we have `tsupport (f i) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.
-/
def IsSubordinate {s : Set M} (f : SmoothBumpCovering ι I M s) (U : M → Set M) :=
  ∀ i, tsupport (f i) ⊆ U (f.c i)

theorem IsSubordinate.support_subset {fs : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : fs.IsSubordinate U) (i : ι) : support (fs i) ⊆ U (fs.c i) :=
  Subset.trans subset_closure (h i)

variable (I) in
/-- Let `M` be a smooth manifold modelled on a finite-dimensional real vector space.
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → Set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
theorem exists_isSubordinate [T2Space M] [SigmaCompactSpace M] (hs : IsClosed s)
    (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
    ∃ (ι : Type uM) (f : SmoothBumpCovering ι I M s), f.IsSubordinate U := by
  -- First we deduce some missing instances
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Next we choose a covering by supports of smooth bump functions
  have hB := fun x hx => SmoothBumpFunction.nhds_basis_support (I := I) (hU x hx)
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis_set hs hB with
    ⟨ι, c, f, hf, hsub', hfin⟩
  choose hcs hfU using hf
  -- Then we use the shrinking lemma to get a covering by smaller open
  rcases exists_subset_iUnion_closed_subset hs (fun i => (f i).isOpen_support)
    (fun x _ => hfin.point_finite x) hsub' with ⟨V, hsV, hVc, hVf⟩
  choose r hrR hr using fun i => (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i)
  refine ⟨ι, ⟨c, fun i => (f i).updateRIn (r i) (hrR i), hcs, ?_, fun x hx => ?_⟩, fun i => ?_⟩
  · simpa only [SmoothBumpFunction.support_updateRIn]
  · refine (mem_iUnion.1 <| hsV hx).imp fun i hi => ?_
    exact ((f i).updateRIn _ _).eventuallyEq_one_of_dist_lt
      ((f i).support_subset_source <| hVf _ hi) (hr i hi).2
  · simpa only [SmoothBumpFunction.support_updateRIn, tsupport] using hfU i

protected theorem locallyFinite : LocallyFinite fun i => support (fs i) :=
  fs.locallyFinite'

protected theorem point_finite (x : M) : {i | fs i x ≠ 0}.Finite :=
  fs.locallyFinite.point_finite x

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : ι :=
  (fs.eventuallyEq_one' x hx).choose

theorem eventuallyEq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
  (fs.eventuallyEq_one' x hx).choose_spec

theorem apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
  (fs.eventuallyEq_one x hx).eq_of_nhds

theorem mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (fs <| fs.ind x hx) := by
  simp [fs.apply_ind x hx]

theorem mem_chartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x ∈ (chartAt H (fs.c i)).source :=
  (fs i).support_subset_source <| by simp [h]

theorem mem_extChartAt_source_of_eq_one {i : ι} {x : M} (h : fs i x = 1) :
    x ∈ (extChartAt I (fs.c i)).source := by
  rw [extChartAt_source]; exact fs.mem_chartAt_source_of_eq_one h

theorem mem_chartAt_ind_source (x : M) (hx : x ∈ s) : x ∈ (chartAt H (fs.c (fs.ind x hx))).source :=
  fs.mem_chartAt_source_of_eq_one (fs.apply_ind x hx)

theorem mem_extChartAt_ind_source (x : M) (hx : x ∈ s) :
    x ∈ (extChartAt I (fs.c (fs.ind x hx))).source :=
  fs.mem_extChartAt_source_of_eq_one (fs.apply_ind x hx)

/-- The index type of a `SmoothBumpCovering` of a compact manifold is finite. -/
protected def fintype [CompactSpace M] : Fintype ι :=
  fs.locallyFinite.fintypeOfCompact fun i => (fs i).nonempty_support

variable [T2Space M]
variable [IsManifold I ∞ M]

/-- Reinterpret a `SmoothBumpCovering` as a continuous `BumpCovering`. Note that not every
`f : BumpCovering ι M s` with smooth functions `f i` is a `SmoothBumpCovering`. -/
def toBumpCovering : BumpCovering ι M s where
  toFun i := ⟨fs i, (fs i).continuous⟩
  locallyFinite' := fs.locallyFinite
  nonneg' i _ := (fs i).nonneg
  le_one' i _ := (fs i).le_one
  eventuallyEq_one' := fs.eventuallyEq_one'

@[simp]
theorem isSubordinate_toBumpCovering {f : SmoothBumpCovering ι I M s} {U : M → Set M} :
    (f.toBumpCovering.IsSubordinate fun i => U (f.c i)) ↔ f.IsSubordinate U :=
  Iff.rfl

alias ⟨_, IsSubordinate.toBumpCovering⟩ := isSubordinate_toBumpCovering

/-- Every `SmoothBumpCovering` defines a smooth partition of unity. -/
def toSmoothPartitionOfUnity : SmoothPartitionOfUnity ι I M s :=
  fs.toBumpCovering.toSmoothPartitionOfUnity fun i => (fs i).contMDiff

theorem toSmoothPartitionOfUnity_apply (i : ι) (x : M) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ᶠ (j) (_ : WellOrderingRel j i), (1 - fs j x) :=
  rfl

open Classical in
theorem toSmoothPartitionOfUnity_eq_mul_prod (i : ι) (x : M) (t : Finset ι)
    (ht : ∀ j, WellOrderingRel j i → fs j x ≠ 0 → j ∈ t) :
    fs.toSmoothPartitionOfUnity i x = fs i x * ∏ j ∈ t with WellOrderingRel j i, (1 - fs j x) :=
  fs.toBumpCovering.toPartitionOfUnity_eq_mul_prod i x t ht

open Classical in
theorem exists_finset_toSmoothPartitionOfUnity_eventuallyEq (i : ι) (x : M) :
    ∃ t : Finset ι,
      fs.toSmoothPartitionOfUnity i =ᶠ[𝓝 x]
        fs i * ∏ j ∈ t with WellOrderingRel j i, ((1 : M → ℝ) - fs j) := by
  simpa using fs.toBumpCovering.exists_finset_toPartitionOfUnity_eventuallyEq i x

theorem toSmoothPartitionOfUnity_zero_of_zero {i : ι} {x : M} (h : fs i x = 0) :
    fs.toSmoothPartitionOfUnity i x = 0 :=
  fs.toBumpCovering.toPartitionOfUnity_zero_of_zero h

theorem support_toSmoothPartitionOfUnity_subset (i : ι) :
    support (fs.toSmoothPartitionOfUnity i) ⊆ support (fs i) :=
  fs.toBumpCovering.support_toPartitionOfUnity_subset i

theorem IsSubordinate.toSmoothPartitionOfUnity {f : SmoothBumpCovering ι I M s} {U : M → Set M}
    (h : f.IsSubordinate U) : f.toSmoothPartitionOfUnity.IsSubordinate fun i => U (f.c i) :=
  h.toBumpCovering.toPartitionOfUnity

theorem sum_toSmoothPartitionOfUnity_eq (x : M) :
    ∑ᶠ i, fs.toSmoothPartitionOfUnity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
  fs.toBumpCovering.sum_toPartitionOfUnity_eq x

end SmoothBumpCovering

variable (I)
variable [FiniteDimensional ℝ E]
variable [IsManifold I ∞ M] {n : ℕ∞}

/-- Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite-dimensional manifold,
there exists an infinitely smooth function that is equal to `0` on `s` and to `1` on `t`.
See also `exists_contMDiff_zero_iff_one_iff_of_isClosed`, which ensures additionally that
`f` is equal to `0` exactly on `s` and to `1` exactly on `t`. -/
theorem exists_contMDiffMap_zero_one_of_isClosed [T2Space M] [SigmaCompactSpace M] {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc 0 1 := by
  have : ∀ x ∈ t, sᶜ ∈ 𝓝 x := fun x hx => hs.isOpen_compl.mem_nhds (disjoint_right.1 hd hx)
  rcases SmoothBumpCovering.exists_isSubordinate I ht this with ⟨ι, f, hf⟩
  set g := f.toSmoothPartitionOfUnity
  refine
    ⟨⟨_, g.contMDiff_sum.of_le (by simp)⟩, fun x hx => ?_, fun x => g.sum_eq_one, fun x =>
      ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩
  suffices ∀ i, g i x = 0 by simp only [this, ContMDiffMap.coeFn_mk, finsum_zero, Pi.zero_apply]
  refine fun i => f.toSmoothPartitionOfUnity_zero_of_zero ?_
  exact notMem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)

@[deprecated (since := "2025-12-17")]
alias exists_smooth_zero_one_of_isClosed := exists_contMDiffMap_zero_one_of_isClosed

/-- Given two disjoint closed sets `s, t` in a Hausdorff normal σ-compact finite-dimensional
manifold `M`, there exists a smooth function `f : M → [0,1]` that vanishes in a neighbourhood of `s`
and is equal to `1` in a neighbourhood of `t`. -/
theorem exists_contMDiffMap_zero_one_nhds_of_isClosed
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 0) ∧ (∀ᶠ x in 𝓝ˢ t, f x = 1) ∧
      ∀ x, f x ∈ Icc 0 1 := by
  obtain ⟨u, u_op, hsu, hut⟩ := normal_exists_closure_subset hs ht.isOpen_compl
    (subset_compl_iff_disjoint_left.mpr hd.symm)
  obtain ⟨v, v_op, htv, hvu⟩ := normal_exists_closure_subset ht isClosed_closure.isOpen_compl
    (subset_compl_comm.mp hut)
  obtain ⟨f, hfu, hfv, hf⟩ := exists_contMDiffMap_zero_one_of_isClosed I isClosed_closure
    isClosed_closure (subset_compl_iff_disjoint_left.mp hvu) (n := n)
  refine ⟨f, ?_, ?_, hf⟩
  · exact eventually_of_mem (mem_of_superset (u_op.mem_nhdsSet.mpr hsu) subset_closure) hfu
  · exact eventually_of_mem (mem_of_superset (v_op.mem_nhdsSet.mpr htv) subset_closure) hfv

@[deprecated (since := "2025-12-17")]
alias exists_smooth_zero_one_nhds_of_isClosed := exists_contMDiffMap_zero_one_nhds_of_isClosed

/-- Given two sets `s, t` in a Hausdorff normal σ-compact finite-dimensional manifold `M`
with `s` open and `s ⊆ interior t`, there is a smooth function `f : M → [0,1]` which is equal to `s`
in a neighbourhood of `s` and has support contained in `t`. -/
theorem exists_contMDiffMap_one_nhds_of_subset_interior
    [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
    {s t : Set M} (hs : IsClosed s) (hd : s ⊆ interior t) :
    ∃ f : C^n⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ᶠ x in 𝓝ˢ s, f x = 1) ∧ (∀ x ∉ t, f x = 0) ∧
      ∀ x, f x ∈ Icc 0 1 := by
  rcases exists_contMDiffMap_zero_one_nhds_of_isClosed I isOpen_interior.isClosed_compl hs
    (by rwa [← subset_compl_iff_disjoint_left, compl_compl]) (n := n) with ⟨f, h0, h1, hf⟩
  refine ⟨f, h1, fun x hx ↦ ?_, hf⟩
  exact h0.self_of_nhdsSet _ fun hx' ↦ hx <| interior_subset hx'

@[deprecated (since := "2025-12-17")]
alias exists_smooth_one_nhds_of_subset_interior := exists_contMDiffMap_one_nhds_of_subset_interior

namespace SmoothPartitionOfUnity

/-- A `SmoothPartitionOfUnity` that consists of a single function, uniformly equal to one,
defined as an example for `Inhabited` instance. -/
def single (i : ι) (s : Set M) : SmoothPartitionOfUnity ι I M s :=
  (BumpCovering.single i s).toSmoothPartitionOfUnity fun j => by
    classical
    rcases eq_or_ne j i with (rfl | h)
    · simp only [contMDiff_one, ContinuousMap.coe_one, BumpCovering.coe_single, Pi.single_eq_same]
    · simp only [contMDiff_zero, BumpCovering.coe_single, Pi.single_eq_of_ne h,
        ContinuousMap.coe_zero]

instance [Inhabited ι] (s : Set M) : Inhabited (SmoothPartitionOfUnity ι I M s) :=
  ⟨single I default s⟩

variable [T2Space M] [SigmaCompactSpace M]

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `SmoothPartitionOfUnity ι M s` that is subordinate to `U`. -/
theorem exists_isSubordinate {s : Set M} (hs : IsClosed s) (U : ι → Set M) (ho : ∀ i, IsOpen (U i))
    (hU : s ⊆ ⋃ i, U i) : ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- porting note(https://github.com/leanprover-community/batteries/issues/116):
  -- split `rcases` into `have` + `rcases`
  have := BumpCovering.exists_isSubordinate_of_prop (ContMDiff I 𝓘(ℝ) ∞) ?_ hs U ho hU
  · rcases this with ⟨f, hf, hfU⟩
    exact ⟨f.toSmoothPartitionOfUnity hf, hfU.toSmoothPartitionOfUnity hf⟩
  · intro s t hs ht hd
    rcases exists_contMDiffMap_zero_one_of_isClosed I hs ht hd with ⟨f, hf⟩
    exact ⟨f, f.contMDiff, hf⟩

theorem exists_isSubordinate_chartAt_source_of_isClosed {s : Set M} (hs : IsClosed s) :
    ∃ f : SmoothPartitionOfUnity s I M s,
      f.IsSubordinate (fun x ↦ (chartAt H (x : M)).source) := by
  apply exists_isSubordinate _ hs _ (fun i ↦ (chartAt H _).open_source) (fun x hx ↦ ?_)
  exact mem_iUnion_of_mem ⟨x, hx⟩ (mem_chart_source H x)

variable (M)
theorem exists_isSubordinate_chartAt_source :
    ∃ f : SmoothPartitionOfUnity M I M univ, f.IsSubordinate (fun x ↦ (chartAt H x).source) := by
  apply exists_isSubordinate _ isClosed_univ _ (fun i ↦ (chartAt H _).open_source) (fun x _ ↦ ?_)
  exact mem_iUnion_of_mem x (mem_chart_source H x)

end SmoothPartitionOfUnity

variable [SigmaCompactSpace M] [T2Space M] {t : M → Set F} {n : ℕ∞}

/-- Let `V` be a vector bundle over a σ-compact Hausdorff finite-dimensional topological manifold
`M`. Let `t : M → Set (V x)` be a family of convex sets in the fibers of `V`.
Suppose that for each point `x₀ : M` there exists a neighborhood `U_x₀` of `x₀` and a local
section `s_loc : M → V x` such that `s_loc` is $C^n$ smooth on `U_x₀` (when viewed as a map to
the total space of the bundle) and `s_loc y ∈ t y` for all `y ∈ U_x₀`.
Then there exists a global $C^n$ smooth section `s : Cₛ^n⟮I_M; F_fiber, V⟯` such that
`s x ∈ t x` for all `x : M`.
-/
theorem exists_contMDiffSection_forall_mem_convex_of_local
    {F_fiber : Type*} [NormedAddCommGroup F_fiber] [NormedSpace ℝ F_fiber]
    (V : M → Type*) [∀ x, AddCommGroup (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, Module ℝ (V x)]
    [TopologicalSpace (TotalSpace F_fiber V)] [FiberBundle F_fiber V] [VectorBundle ℝ F_fiber V]
    (t : ∀ x, Set (V x)) (ht_conv : ∀ x, Convex ℝ (t x))
    (Hloc :
      ∀ x₀ : M, ∃ U_x₀ ∈ 𝓝 x₀, ∃ (s_loc : (x : M) → V x),
        (CMDiff[U_x₀] n (T% s_loc)) ∧ (∀ y ∈ U_x₀, s_loc y ∈ t y)) :
    ∃ s : Cₛ^n⟮I; F_fiber, V⟯, ∀ x : M, s x ∈ t x := by
  choose W h_nhds s_loc s_smooth h_mem_t using Hloc
  -- Construct an open cover from the interiors of the given neighborhoods.
  let U (x : M) : Set M := interior (W x)
  have hU_covers_univ : univ ⊆ ⋃ x, U x := by
    intro x_pt _
    simp only [mem_iUnion]
    exact ⟨x_pt, mem_interior_iff_mem_nhds.mpr (h_nhds x_pt)⟩
  -- Obtain a smooth partition of unity subordinate to this open cover.
  obtain ⟨ρ, hρU⟩ : ∃ ρ : SmoothPartitionOfUnity M I M univ, ρ.IsSubordinate U :=
    SmoothPartitionOfUnity.exists_isSubordinate
      I isClosed_univ U (fun x ↦ isOpen_interior) hU_covers_univ
  -- Define the global section `s` by taking a weighted sum of the local sections.
  let s x : V x := ∑ᶠ j, (ρ j x) • s_loc j x
  -- Prove that `s`, when viewed as a map to the total space, is smooth.
  have (j : M) : CMDiff n (T% (fun x ↦ (ρ j x) • (s_loc j x))) := by
    refine ContMDiffOn.smul_section_of_tsupport ?_ isOpen_interior (hρU j)
      ((s_smooth j).mono interior_subset)
    exact ((ρ j).contMDiff).of_le (sup_eq_left.mp rfl) |>.contMDiffOn
  have hs : CMDiff n (T% s) := by
    apply ContMDiff.finsum_section_of_locallyFinite ?_ this
    -- Future: can grind do this?
    apply ρ.locallyFinite.subset fun i x hx ↦ ?_
    rw [support]
    rw [mem_setOf_eq] at hx ⊢
    exact left_ne_zero_of_smul hx
  -- Construct the smooth section and prove it lies in the convex sets `t x`.
  refine ⟨⟨s, hs⟩, fun x ↦ ?_⟩
  apply (ht_conv x).finsum_mem (ρ.nonneg · x) (ρ.sum_eq_one (mem_univ x))
  intro j h_ρjx_ne_zero
  have h_x_in_tsupport_ρj : x ∈ tsupport (ρ j) := subset_closure (mem_support.mpr h_ρjx_ne_zero)
  have h_x_in_Umap_j : x ∈ W j := interior_subset (hρU j h_x_in_tsupport_ρj)
  exact h_mem_t j x h_x_in_Umap_j

@[deprecated (since := "2025-12-17")]
alias exists_contMDiffOn_section_forall_mem_convex_of_local :=
  exists_contMDiffSection_forall_mem_convex_of_local

@[deprecated (since := "2025-12-17")]
alias exists_smooth_section_forall_mem_convex_of_local :=
  exists_contMDiffSection_forall_mem_convex_of_local

/-- Let `M` be a σ-compact Hausdorff finite-dimensional topological manifold. Let `t : M → Set F`
be a family of convex sets. Suppose that for each point `x : M` there exists a neighborhood
`U ∈ 𝓝 x` and a function `g : M → F` such that `g` is $C^n$ smooth on `U` and `g y ∈ t y` for all
`y ∈ U`. Then there exists a $C^n$ smooth function `g : C^n⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x`
for all `x`.

This is a special case of `exists_contMDiffSection_forall_mem_convex_of_local` where `V` is the
trivial bundle. See also `exists_contMDiffMap_mem_convex_of_local_const`. -/
theorem exists_contMDiffMap_forall_mem_convex_of_local (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ U ∈ 𝓝 x, ∃ g : M → F, CMDiff[U] n g ∧ ∀ y ∈ U, g y ∈ t y) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  let ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local I (fun _ ↦ F) t ht
    (fun x₀ ↦ let ⟨U, hU, g, hgs, hgt⟩ := Hloc x₀
      ⟨U, hU, g, fun y hy ↦ Bundle.contMDiffWithinAt_section |>.mpr <| hgs y hy, hgt⟩)
  ⟨⟨s, (Bundle.contMDiffAt_section _ |>.mp <| s.contMDiff ·)⟩, hs⟩

@[deprecated (since := "2025-12-17")]
alias exists_contMDiffOn_forall_mem_convex_of_local :=
  exists_contMDiffMap_forall_mem_convex_of_local

@[deprecated (since := "2025-12-17")]
alias exists_smooth_forall_mem_convex_of_local := exists_contMDiffMap_forall_mem_convex_of_local

/-- Let `M` be a σ-compact Hausdorff finite-dimensional topological manifold. Let `t : M → Set F` be
a family of convex sets. Suppose that for each point `x : M` there exists a vector `c : F` such that
for all `y` in a neighborhood of `x` we have `c ∈ t y`. Then there exists a smooth function
`g : C^n⟮I, M; 𝓘(ℝ, F), F⟯` such that `g x ∈ t x` for all `x`. See also
`exists_contMDiffMap_forall_mem_convex_of_local`. -/
theorem exists_contMDiffMap_forall_mem_convex_of_local_const (ht : ∀ x, Convex ℝ (t x))
    (Hloc : ∀ x : M, ∃ c : F, ∀ᶠ y in 𝓝 x, c ∈ t y) : ∃ g : C^n⟮I, M; 𝓘(ℝ, F), F⟯, ∀ x, g x ∈ t x :=
  exists_contMDiffMap_forall_mem_convex_of_local I ht fun x =>
    let ⟨c, hc⟩ := Hloc x
    ⟨_, hc, fun _ => c, contMDiffOn_const, fun _ => id⟩

@[deprecated (since := "2025-12-17")]
alias exists_smooth_forall_mem_convex_of_local_const :=
  exists_contMDiffMap_forall_mem_convex_of_local_const

/-- Let `M` be a smooth σ-compact manifold with extended distance. Let `K : ι → Set M` be a locally
finite family of closed sets, let `U : ι → Set M` be a family of open sets such that `K i ⊆ U i` for
all `i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for any `i` and
`x ∈ K i`, we have `Metric.closedEBall x (δ x) ⊆ U i`. -/
theorem Metric.exists_contMDiffMap_forall_closedEBall_subset
    {M : Type*} [EMetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M}
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hfin : LocallyFinite K) :
    ∃ δ : C^n⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x, 0 < δ x) ∧ ∀ i, ∀ x ∈ K i, Metric.closedEBall x (ENNReal.ofReal (δ x)) ⊆ U i := by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_iInter, @forall_swap ι M]
    using exists_contMDiffMap_forall_mem_convex_of_local_const I
      Metric.exists_forall_closedEBall_subset_aux₂
      (Metric.exists_forall_closedEBall_subset_aux₁ hK hU hKU hfin)

@[deprecated (since := "2026-01-24")]
alias Emetric.exists_contMDiffMap_forall_closedBall_subset :=
  Metric.exists_contMDiffMap_forall_closedEBall_subset

@[deprecated (since := "2025-12-17")]
alias Emetric.exists_smooth_forall_closedBall_subset :=
  Metric.exists_contMDiffMap_forall_closedEBall_subset

/-- Let `M` be a smooth σ-compact manifold with a metric. Let `K : ι → Set M` be a locally finite
family of closed sets, let `U : ι → Set M` be a family of open sets such that `K i ⊆ U i` for all
`i`. Then there exists a positive smooth function `δ : M → ℝ≥0` such that for any `i` and `x ∈ K i`,
we have `Metric.closedBall x (δ x) ⊆ U i`. -/
theorem Metric.exists_contMDiffMap_forall_closedBall_subset
    {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] {K : ι → Set M} {U : ι → Set M}
    (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i)
    (hfin : LocallyFinite K) :
    ∃ δ : C^n⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x, 0 < δ x) ∧ ∀ i, ∀ x ∈ K i, Metric.closedBall x (δ x) ⊆ U i := by
  rcases Metric.exists_contMDiffMap_forall_closedEBall_subset I hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, fun i x hx => ?_⟩
  rw [← Metric.closedEBall_ofReal (hδ0 _).le]
  exact hδ i x hx

@[deprecated (since := "2025-12-17")]
alias Metric.exists_smooth_forall_closedBall_subset :=
  Metric.exists_contMDiffMap_forall_closedBall_subset

lemma IsOpen.exists_contMDiff_support_eq_aux {s : Set H} (hs : IsOpen s) :
    ∃ f : H → ℝ, f.support = s ∧ CMDiff n f ∧ Set.range f ⊆ Set.Icc 0 1 := by
  have h's : IsOpen (I.symm ⁻¹' s) := I.continuous_symm.isOpen_preimage _ hs
  rcases h's.exists_contDiff_support_eq with ⟨f, f_supp, f_diff, f_range⟩
  refine ⟨f ∘ I, ?_, ?_, ?_⟩
  · rw [support_comp_eq_preimage, f_supp, ← preimage_comp]
    simp only [ModelWithCorners.symm_comp_self, preimage_id_eq, id_eq]
  · exact f_diff.comp_contMDiff contMDiff_model
  · exact Subset.trans (range_comp_subset_range _ _) f_range

@[deprecated (since := "2025-12-17")]
alias IsOpen.exists_msmooth_support_eq_aux := IsOpen.exists_contMDiff_support_eq_aux

/-- Given an open set in a finite-dimensional real manifold, there exists a nonnegative smooth
function with support equal to `s`. -/
theorem IsOpen.exists_contMDiff_support_eq {s : Set M} (hs : IsOpen s) :
    ∃ f : M → ℝ, f.support = s ∧ CMDiff n f ∧ ∀ x, 0 ≤ f x := by
  rcases SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M with ⟨f, hf⟩
  have A : ∀ (c : M), ∃ g : H → ℝ,
      g.support = (chartAt H c).target ∩ (chartAt H c).symm ⁻¹' s ∧
      CMDiff n g ∧ Set.range g ⊆ Set.Icc 0 1 := by
    intro i
    apply IsOpen.exists_contMDiff_support_eq_aux
    exact OpenPartialHomeomorph.isOpen_inter_preimage_symm _ hs
  choose g g_supp g_diff hg using A
  have h'g : ∀ c x, 0 ≤ g c x := fun c x ↦ (hg c (mem_range_self (f := g c) x)).1
  have h''g : ∀ c x, 0 ≤ f c x * g c (chartAt H c x) :=
    fun c x ↦ mul_nonneg (f.nonneg c x) (h'g c _)
  refine ⟨fun x ↦ ∑ᶠ c, f c x * g c (chartAt H c x), ?_, ?_, ?_⟩
  · refine support_eq_iff.2 ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · apply ne_of_gt
      have B : ∃ c, 0 < f c x * g c (chartAt H c x) := by
        obtain ⟨c, hc⟩ : ∃ c, 0 < f c x := f.exists_pos_of_mem (mem_univ x)
        refine ⟨c, mul_pos hc ?_⟩
        apply lt_of_le_of_ne (h'g _ _) (Ne.symm _)
        rw [← mem_support, g_supp, ← mem_preimage, preimage_inter]
        have Hx : x ∈ tsupport (f c) := subset_tsupport _ (ne_of_gt hc)
        simp [(chartAt H c).left_inv (hf c Hx), hx, (chartAt H c).map_source (hf c Hx)]
      apply finsum_pos (fun c ↦ h''g c x) B
      apply (f.locallyFinite.point_finite x).subset
      apply compl_subset_compl.2
      rintro c (hc : f c x = 0)
      simpa only [mul_eq_zero] using Or.inl hc
    · apply finsum_eq_zero_of_forall_eq_zero
      intro c
      by_cases Hx : x ∈ tsupport (f c)
      · suffices g c (chartAt H c x) = 0 by simp only [this, mul_zero]
        rw [← notMem_support, g_supp, ← mem_preimage, preimage_inter]
        contrapose! hx
        simp only [mem_inter_iff, mem_preimage, (chartAt H c).left_inv (hf c Hx)] at hx
        exact hx.2
      · have : x ∉ support (f c) := by contrapose! Hx; exact subset_tsupport _ Hx
        rw [notMem_support] at this
        simp [this]
  · apply SmoothPartitionOfUnity.contMDiff_finsum_smul
    intro c x hx
    apply (g_diff c (chartAt H c x)).comp
    exact contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas _)
      (hf c hx)
  · intro x
    apply finsum_nonneg (fun c ↦ h''g c x)

@[deprecated (since := "2025-12-17")]
alias IsOpen.exists_msmooth_support_eq := IsOpen.exists_contMDiff_support_eq

/-- Given an open set `s` containing a closed set `t` in a finite-dimensional real manifold, there
exists a smooth function with support equal to `s`, taking values in `[0,1]`, and equal to `1`
exactly on `t`. -/
theorem exists_contMDiff_support_eq_eq_one_iff
    {s t : Set M} (hs : IsOpen s) (ht : IsClosed t) (h : t ⊆ s) :
    ∃ f : M → ℝ, CMDiff n f ∧ range f ⊆ Icc 0 1 ∧ support f = s ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  /- Take `f` with support equal to `s`, and `g` with support equal to `tᶜ`. Then `f / (f + g)`
  satisfies the conclusion of the theorem. -/
  rcases hs.exists_contMDiff_support_eq I with ⟨f, f_supp, f_diff, f_pos⟩
  rcases ht.isOpen_compl.exists_contMDiff_support_eq I with ⟨g, g_supp, g_diff, g_pos⟩
  have A : ∀ x, 0 < f x + g x := by
    intro x
    by_cases xs : x ∈ support f
    · have : 0 < f x := lt_of_le_of_ne (f_pos x) (Ne.symm xs)
      linarith [g_pos x]
    · have : 0 < g x := by
        classical
        apply lt_of_le_of_ne (g_pos x) (Ne.symm ?_)
        rw [← mem_support, g_supp]
        contrapose! xs
        exact h.trans f_supp.symm.subset (by simpa using xs)
      linarith [f_pos x]
  refine ⟨fun x ↦ f x / (f x + g x), ?_, ?_, ?_, ?_⟩
  -- show that `f / (f + g)` is smooth
  · exact f_diff.div₀ (f_diff.add g_diff) (fun x ↦ ne_of_gt (A x))
  -- show that the range is included in `[0, 1]`
  · refine range_subset_iff.2 (fun x ↦ ⟨div_nonneg (f_pos x) (A x).le, ?_⟩)
    apply div_le_one_of_le₀ _ (A x).le
    simpa only [le_add_iff_nonneg_right] using g_pos x
  -- show that the support is `s`
  · have B : support (fun x ↦ f x + g x) = univ := eq_univ_of_forall (fun x ↦ (A x).ne')
    simp only [support_div, f_supp, B, inter_univ]
  -- show that the function equals one exactly on `t`
  · intro x
    simp [div_eq_one_iff_eq (A x).ne', left_eq_add, ← notMem_support, g_supp]

@[deprecated (since := "2025-12-17")]
alias exists_msmooth_support_eq_eq_one_iff := exists_contMDiff_support_eq_eq_one_iff

/-- Given two disjoint closed sets `s, t` in a Hausdorff σ-compact finite-dimensional manifold,
there exists an infinitely smooth function that is equal to `0` exactly on `s` and to `1`
exactly on `t`. See also `exists_contMDiffMap_zero_one_of_isClosed` for a
slightly weaker version. -/
theorem exists_contMDiff_zero_iff_one_iff_of_isClosed {s t : Set M}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : M → ℝ, CMDiff n f ∧ range f ⊆ Icc 0 1 ∧ (∀ x, x ∈ s ↔ f x = 0)
      ∧ (∀ x, x ∈ t ↔ f x = 1) := by
  rcases exists_contMDiff_support_eq_eq_one_iff I hs.isOpen_compl ht hd.subset_compl_left with
    ⟨f, f_diff, f_range, fs, ft⟩
  refine ⟨f, f_diff, f_range, ?_, ft⟩
  simp [← notMem_support, fs]

@[deprecated (since := "2025-12-17")]
alias exists_msmooth_zero_iff_one_iff_of_isClosed := exists_contMDiff_zero_iff_one_iff_of_isClosed
