/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Local frames in a vector bundle

Let `V → M` be a finite rank smooth vector bundle with standard fiber `F`.
Given a basis `b` for `F` and a local trivialisation `e` for `V`,
we construct a **smooth local frame** on `V` w.r.t. `e` and `b`,
i.e. a collection of sections `s_i` of `V` which is smooth on `e.baseSet` such that `{s_i x}` is a
basis of `V x` for each `x ∈ e.baseSet`. Any section `s` of `e` can be uniquely written as
`s = ∑ i, f^i s_i` near `x`, and `s` is smooth at `x` iff the functions `f^i` are.

We use this to construct local extensions of a vector to a section which is smooth on the
trivialisation domain.

## Main definitions and results
* `Basis.localFrame e b`: the local frame on `V` w.r.t. a local trivialisation `e` of `V` and a
  basis `b` of `F`. Use `b.localFrame e i` to access the i-th section in that frame.
* `b.contMDiffOn_localFrame_baseSet`: each section `b.localFrame e i` is smooth on `e.baseSet`
* `b.localFrame_toBasis_at e`: for each `x ∈ e.baseSet`, the vectors `b.localFrame e i x` form
  a basis of `F`
* `Basis.localFrame_repr e b i` describes the coefficient of sections of `V` w.r.t.`b.localFrame e`:
  `b.localFrame e i` is a linear map from sections of `V` to functions `M → 𝕜`.
* `b.localFrame_repr_spec e`: near `x`, we have
  `s = ∑ i, (b.localFrame_repr e i s) • b.localFrame e i`
* `b.localFrame_repr_congr e`: the coefficient `b.localFrame_repr e b i` of `s` in the local frame
  induced by `e` and `b` at `x` only depends on `s` at `x`.
* `b.contMDiffOn_localFrame_repr`: if `s` is a `C^k` section, each coefficient
  `b.localFrame_repr e i s` is `C^k` on `e.baseSet`
* `b.contMDiffAt_iff_localFrame_repr e`: a section `s` is `C^k` at `x ∈ e.baseSet`
  iff all of its frame coefficients are
* `b.contMDiffOn_iff_localFrame_repr e`: a section `s` is `C^k` on an open set `t ⊆ e.baseSet`
  iff all of its frame coefficients are

* TODO: mention all the localExtensionOn definitions and results

TODO add a more complete doc-string!

## Implementation notes
* local frames use the junk value pattern: they are defined on all of `M`, but their value is
  only meaningful inside `e.baseSet`
* something about local extensions (and different fields)

## Tags
vector bundle, local frame, smoothness

-/
open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 0 M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  -- not needed in this file
  -- [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle n F V I]
  -- `V` vector bundle

namespace Basis

variable {ι : Type*}

noncomputable def localFrame_toBasis_at
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {x : M} (hx : x ∈ e.baseSet) : Basis ι 𝕜 (V x) :=
  b.map (e.linearEquivAt (R := 𝕜) x hx).symm


open scoped Classical in
-- If x is outside of `e.baseSet`, this returns the junk value 0.
noncomputable def localFrame
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) : ι → (x : M) → V x := fun i x ↦
  -- idea: take the vector b i and apply the trivialisation e to it.
  if hx : x ∈ e.baseSet then b.localFrame_toBasis_at e hx i else 0

-- TODO: understand why this isn’t already a simp lemma
attribute [simp] Trivialization.apply_mk_symm

omit [IsManifold I 0 M] [ContMDiffVectorBundle n F V I] in
/-- Each local frame `s^i ∈ Γ(E)` of a `C^k` vector bundle, defined by a local trivialisation `e`,
is `C^k` on `e.baseSet`. -/
lemma contMDiffOn_localFrame_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) (i : ι) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F x (b.localFrame e i x)) e.baseSet := by
  rw [contMDiffOn_section_of_mem_baseSet₀]
  apply (contMDiffOn_const (c := b i)).congr
  intro y hy
  simp [localFrame, hy, localFrame_toBasis_at]

@[simp]
lemma localFrame_apply_of_mem_baseSet
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} {x : M} (hx : x ∈ e.baseSet) :
    b.localFrame e i x = b.localFrame_toBasis_at e hx i := by
  simp [localFrame, hx]

@[simp]
lemma localFrame_apply_of_notMem
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Basis ι 𝕜 F) {i : ι} {x : M} (hx : x ∉ e.baseSet) :
    b.localFrame e i x = 0 := by
  simp [localFrame, hx]


lemma localFrame_toBasis_at_coe
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) {x : M} (i : ι) (hx : x ∈ e.baseSet) :
    b.localFrame_toBasis_at e hx i = b.localFrame e i x := by simp [hx]

-- XXX: is this result actually needed now? perhaps not, because of the toBasis definition?
/-- At each point `x ∈ M`, the sections `{sⁱ(x)}` of a local frame form a basis for `V x`. -/
def isBasis_localFrame
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) : sorry := by
  -- the b i form a basis of F,
  -- and the trivialisation e is a linear equivalence (thus preserves bases)
  sorry

open scoped Classical in
/-- Coefficients of a section `s` of `V` w.r.t. the local frame `b.localFrame e i` -/
-- If x is outside of `e.baseSet`, this returns the junk value 0.
-- NB. We don't use simps here, as we prefer to have dedicated `_apply` lemmas for the separate
-- cases.
noncomputable def localFrame_repr
    (e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas e]
    (b : Basis ι 𝕜 F) (i : ι) : (Π x : M, V x) →ₗ[𝕜] M → 𝕜 where
  toFun s x := if hx : x ∈ e.baseSet then (b.localFrame_toBasis_at e hx).repr (s x) i else 0
  map_add' s s' := by
    ext x
    by_cases hx : x ∈ e.baseSet <;> simp [hx]
  map_smul' c s := by
    ext x
    by_cases hx : x ∈ e.baseSet <;> simp [hx]

variable {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [MemTrivializationAtlas e] {b : Basis ι 𝕜 F}

variable (e b) in
@[simp]
lemma localFrame_repr_apply_of_notMem_baseSet {x : M}
    (hx : x ∉ e.baseSet) (s : Π x : M, V x) (i : ι) : b.localFrame_repr e i s x = 0 := by
  simpa [localFrame_repr] using fun hx' ↦ (hx hx').elim

variable (e b) in
@[simp]
lemma localFrame_repr_apply_of_mem_baseSet {x : M}
    (hx : x ∈ e.baseSet) (s : Π x : M, V x) (i : ι) :
    b.localFrame_repr e i s x = (b.localFrame_toBasis_at e hx).repr (s x) i := by
  simp [localFrame_repr, hx]

-- uniqueness of the decomposition: follows from the IsBasis property above

-- TODO: better name?
lemma localFrame_repr_sum_eq [Fintype ι] (s : Π x : M,  V x) {x'} (hx : x' ∈ e.baseSet) :
    s x' = (∑ i, (b.localFrame_repr e i s x') • b.localFrame e i x') := by
  simp [Basis.localFrame_repr, hx]
  exact (sum_repr (localFrame_toBasis_at e b hx) (s x')).symm

variable (b) in
/-- A local frame locally spans the space of sections for `V`: for each local trivialisation `e`
  of `V` around `x`, we have `s = ∑ i, (b.localFrame_repr e i s) • b.localFrame e i` -/
lemma localFrame_repr_spec [Fintype ι] {x : M} (hxe : x ∈ e.baseSet) (s : Π x : M,  V x) :
    ∀ᶠ x' in 𝓝 x, s x' = ∑ i, (b.localFrame_repr e i s x') • b.localFrame e i x' :=
  eventually_nhds_iff.mpr ⟨e.baseSet, fun _ h ↦ localFrame_repr_sum_eq s h, e.open_baseSet, hxe⟩

variable {ι : Type*} {x : M}
  {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
  [MemTrivializationAtlas e]

/-- The representation of `s` in a local frame at `x` only depends on `s` at `x`. -/
lemma localFrame_repr_congr (b : Basis ι 𝕜 F)
    {s s' : Π x : M,  V x} {i : ι} (hss' : s x = s' x) :
    b.localFrame_repr e i s x = b.localFrame_repr e i s' x := by
  by_cases hxe : x ∈ e.baseSet
  · simp [localFrame_repr, hxe, localFrame_toBasis_at]
    congr
  · simp [localFrame_repr, hxe]

lemma localFrame_repr_apply_zero_at
    (b : Basis ι 𝕜 F) {s : Π x : M, V x} (hs : s x = 0) (i : ι) :
    b.localFrame_repr e i s x = 0 := by
  rw [b.localFrame_repr_congr (s' := 0) (by simp [hs])]
  simp
  -- This proof may indicate a missing simp lemma.
  -- by_cases hxe : x ∈ e.baseSet; swap
  -- · simp [localFrame_repr, hxe]
  -- simp [localFrame_repr, localFrame_toBasis_at, hxe, hs]
  -- have : e.symm x = 0 := sorry
  -- have : (e { proj := x, snd := 0 }).2 = 0 := by
  --   trans (e { proj := x, snd := e.symm x 0 }).2
  --   · simp [this]
  --   · simp [e.apply_mk_symm hxe]
  -- simp [this]

variable {n}

/-- Suppose `e` is a compatible trivialisation around `x ∈ M`, and `s` a bundle section.
Then the coefficient of `s` w.r.t. the local frame induced by `b` and `e`
equals the cofficient of "`s x` read in the trivialisation `e`" for `b i`. -/
lemma localFrame_repr_eq_repr (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F) {i : ι} {s : Π x : M, V x} :
    b.localFrame_repr e i s x = b.repr (e (s x)).2 i := by
  simp [b.localFrame_repr_apply_of_mem_baseSet e hxe, Basis.localFrame_toBasis_at]

omit [IsManifold I 0 M] [ContMDiffVectorBundle n F V I] in
/-- If `s` is `C^k` at `x`, so is its coefficient `b.localFrame_repr e i` in the local frame
near `x` induced by `e` and `b` -/
lemma contMDiffAt_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (hxe : x ∈ e.baseSet) (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) x)
    (i : ι) : ContMDiffAt I 𝓘(𝕜) k (b.localFrame_repr e i s) x := by
  -- This boils down to computing the frame coefficients in a local trivialisation.
  classical
  -- step 1: on e.baseSet, can compute the coefficient very well
  let aux := fun x ↦ b.repr (e (s x)).2 i
  -- Since e.baseSet is open, this is sufficient.
  suffices ContMDiffAt I 𝓘(𝕜) k aux x by
    apply this.congr_of_eventuallyEq_of_mem ?_ trivial
    apply eventuallyEq_of_mem (s := e.baseSet) (by simp [e.open_baseSet.mem_nhds hxe])
    intro y hy
    simp [aux, hy, Basis.localFrame_repr_eq_repr hy]
  simp only [aux]

  -- step 2: `s` read in trivialization `e` is `C^k`
  have h₁ : ContMDiffAt I 𝓘(𝕜, F) k (fun x ↦ (e (s x)).2) x := by
    rw [contMDiffAt_section_of_mem_baseSet hxe] at hs
    exact hs
  -- step 3: `b.repr` is a linear map, so the composition is smooth
  let bas := fun v ↦ b.repr v i
  let basl : F →ₗ[𝕜] 𝕜 := {
    toFun := bas
    map_add' m m' := by simp [bas]
    map_smul' m x := by simp [bas]
  }
  let basL : F →L[𝕜] 𝕜 := {
    toLinearMap := basl
    cont := basl.continuous_of_finiteDimensional
  }
  have hbas : ContMDiffAt 𝓘(𝕜, F) 𝓘(𝕜) k basL (e (s x)).2 :=
    contMDiffAt_iff_contDiffAt.mpr <| (basL.contDiff (n := k)).contDiffAt
  exact hbas.comp x h₁

omit [IsManifold I 0 M] [ContMDiffVectorBundle n F V I] in
/-- If `s` is `C^k` on `t ⊆ e.baseSet`, so is its coefficient `b.localFrame_repr e i`
in the local frame induced by `e` -/
lemma contMDiffOn_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} {t : Set M}
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet)
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) t) (i : ι) :
    ContMDiffOn I 𝓘(𝕜) k (b.localFrame_repr e i s) t :=
  fun _ hx ↦ (b.contMDiffAt_localFrame_repr (ht' hx)
    (hs.contMDiffAt (ht.mem_nhds hx)) i).contMDiffWithinAt

omit [IsManifold I 0 M] [ContMDiffVectorBundle n F V I] in
/-- If `s` is `C^k` on `e.baseSet`, so is its coefficient `b.localFrame_repr e i` in the local frame
induced by `e` -/
lemma contMDiffOn_baseSet_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞}
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) e.baseSet) (i : ι) :
    ContMDiffOn I 𝓘(𝕜) k (b.localFrame_repr e i s) e.baseSet :=
  contMDiffOn_localFrame_repr b e.open_baseSet (subset_refl _) hs _

/-- A section `s` of `V` is `C^k` at `x ∈ e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma contMDiffAt_iff_localFrame_repr [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] (b : Basis ι 𝕜 F)
    {s : Π x : M,  V x} {k : WithTop ℕ∞} {x' : M} (hx : x' ∈ e.baseSet) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) x' ↔
    ∀ i, ContMDiffAt I 𝓘(𝕜) k (b.localFrame_repr e i s) x' := by
  refine ⟨fun h i ↦ b.contMDiffAt_localFrame_repr hx h i, fun i ↦ ?_⟩
  -- needs two missing API lemmas, see below
  sorry

/-- A section `s` of `V` is `C^k` on `t ⊆ e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma contMDiffOn_iff_localFrame_repr [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} {t : Set M}
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) t ↔
    ∀ i, ContMDiffOn I 𝓘(𝕜) k (b.localFrame_repr e i s) t := by
  refine ⟨fun h i ↦ contMDiffOn_localFrame_repr b ht ht' h i, fun i ↦ ?_⟩

  have inner (i) : ContMDiffOn I (I.prod 𝓘(𝕜, F)) k (fun x ↦
      TotalSpace.mk' F x ((localFrame_repr e b i) s x • localFrame e b i x)) t := by
    -- lemma localFrame_repr is smooth, localFrame is smooth => scalar product is
    -- does this already exist? if not, missing API!
    sorry
  let rhs₀ (i) := fun x' ↦ (localFrame_repr e b i) s x' • localFrame e b i x'
  let rhs := fun x' ↦ ∑ i, rhs₀ i x'
  have almost : ContMDiffOn I (I.prod 𝓘(𝕜, F)) k
      (fun x ↦ TotalSpace.mk' F x (rhs x)) t := by
    unfold rhs
    -- TODO: add a dependent function version of contMDiffOn_finsum, for sections of a vector bundle
    -- have aux := contMDiffOn_finsum (I' := I) (I := I.prod 𝓘(𝕜, F)) (f := fun i x ↦ rhs₀ i x)
    sorry
  apply almost.congr
  intro y hy
  congr
  exact localFrame_repr_sum_eq s (ht' hy)

/-- A section `s` of `V` is `C^k` on a trivialisation domain `e.baseSet` iff each of its
coefficients `b.localFrame_repr e i s` in a local frame near `x` is -/
lemma contMDiffOn_baseSet_iff_localFrame_repr [Fintype ι] [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    (b : Basis ι 𝕜 F) {s : Π x : M,  V x} {k : WithTop ℕ∞} :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) k (fun x ↦ TotalSpace.mk' F x (s x)) e.baseSet ↔
    ∀ i, ContMDiffOn I 𝓘(𝕜) k (b.localFrame_repr e i s) e.baseSet := by
  rw [b.contMDiffOn_iff_localFrame_repr e.open_baseSet (subset_refl _)]

end Basis

-- local extension of a vector field in a trivialisation's base set
section extendLocally

variable {ι : Type*} [Fintype ι] {b : Basis ι 𝕜 F}
  {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
  [MemTrivializationAtlas e] {x : M}

open scoped Classical in
-- TODO: add longer docs!
-- a starting point (not fully updated any more) is this:
/- Extend a vector `v ∈ V x` to a section of the bundle `V`, whose value at `x` is `v`.
The details of the extension are mostly unspecified: for covariant derivatives, the value of
`s` at points other than `x` will not matter (except for shorter proofs).
Thus, we choose `s` to be somewhat nice: our chosen construction is linear in `v`.
-/

-- comment: need not be smooth (outside of e.baseSet), but this is a useful building block for
-- global smooth extensions of vector fields
-- the latter caps this with a smooth bump function, which need not exist if k=C
-- In contrast, this definition makes sense over any field
-- (for example, *locally* holomorphic sections always exist),

/--
Extend a vector `v ∈ V x` to a local section of `V`, w.r.t. a chosen local trivialisation.
This construction uses a choice of local frame near `x`, w.r.t. to a basis `b` of `F` and a
compatible local trivialisation `e` of `V` near `x`: the resulting extension has constant
coefficients on `e.baseSet` w.r.t. this trivialisation (and is zero otherwise).

In particular, our construction is smooth on `e.baseSet`, and linear in the input vector `v`.
-/
noncomputable def localExtensionOn (b : Basis ι 𝕜 F)
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (x : M) (v : V x) : (x' : M) → V x' :=
  fun x' ↦ if hx : x ∈ e.baseSet then
    letI bV := b.localFrame_toBasis_at e hx; ∑ i, bV.repr v i • b.localFrame e i x'
    else 0

variable (b e) in
@[simp]
lemma localExtensionOn_apply_self (hx : x ∈ e.baseSet) (v : V x) :
    ((localExtensionOn b e x v) x) = v := by
  simp [localExtensionOn, hx]
  nth_rw 2 [← (b.localFrame_toBasis_at e hx).sum_repr v]

/-- A local extension has constant frame coefficients within its defining trivialisation. -/
lemma localExtensionOn_localFrame_repr (b : Basis ι 𝕜 F)
    {e : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M)}
    [MemTrivializationAtlas e] {x : M} (hx : x ∈ e.baseSet) (v : V x) (i : ι)
    {x' : M} (hx' : x' ∈ e.baseSet):
    b.localFrame_repr e i (localExtensionOn b e x v) x' =
      b.localFrame_repr e i (localExtensionOn b e x v) x := by
  simp [localExtensionOn, hx, hx']

-- By construction, localExtensionOn is a linear map.

variable (b e) in
lemma localExtensionOn_add (v v' : V x) :
    localExtensionOn b e x (v + v') = localExtensionOn b e x v + localExtensionOn b e x v' := by
  ext x'
  by_cases hx: x ∈ e.baseSet; swap
  · simp [hx, localExtensionOn]
  · simp [hx, localExtensionOn, add_smul, Finset.sum_add_distrib]

variable (b e) in
lemma localExtensionOn_smul (a : 𝕜) (v : V x) :
    localExtensionOn b e x (a • v) = a • localExtensionOn b e x v := by
  ext x'
  by_cases hx: x ∈ e.baseSet; swap
  · simp [hx, localExtensionOn]
  · simp [hx, localExtensionOn, Finset.smul_sum]
    set B := Basis.localFrame_toBasis_at e b hx
    congr
    ext i
    rw [mul_smul a ((B.repr v) i)]

variable (F) in
omit [IsManifold I 0 M] in
lemma contMDiffOn_localExtensionOn [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜]
    {x : M} (hx : x ∈ e.baseSet) (v : V x) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) 1
    (fun x' ↦ TotalSpace.mk' F x' (localExtensionOn b e x v x')) e.baseSet := by
  -- The local frame coefficients of `localExtensionOn` w.r.t. the frame induced by `e` are
  -- constant, hence smoothness follows.
  rw [b.contMDiffOn_baseSet_iff_localFrame_repr]
  intro i
  apply (contMDiffOn_const (c := (b.localFrame_repr e i) (localExtensionOn b e x v) x)).congr
  intro y hy
  rw [localExtensionOn_localFrame_repr b hx v i hy]

end extendLocally
