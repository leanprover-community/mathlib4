/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Local diffeomorphisms between smooth manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism from `s` and `t`.
`f` is called a **local diffeomorphism** iff it is a local diffeomorphism at every `x ∈ M`.

## Main definitions
* `LocalDiffeomorphAt I J M N n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `LocalDiffeomorph I J M N n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `LocalDiffeomorph`, and `LocalDiffeomorphAt` implies the next condition.
* `LocalDiffeomorph.image`: the image of a local diffeomorphism is open

* `Diffeomorph.mfderiv_toContinuousLinearEquiv`: each differential of a `C^n` diffeomorphism
(`n ≥ 1`) is a linear equivalence.
* `LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv`: if `f` is a local diffeomorphism
at `x`, the differential `mfderiv I J n f x` is a continuous linear equivalence.
* `LocalDiffeomorph.differential_toContinuousLinearEquiv`: if `f` is a local diffeomorphism,
each differential `mfderiv I J n f x` is a continuous linear equivalence.

## TODO
* a local diffeomorphism is a diffeomorphism to its image
* a bijective local diffeomorphism is a diffeomorphism.
* if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
`f` is a local diffeomorphism at `x`.
* if `f` is `C^n` and each differential is a linear isomorphism, `f` is a local diffeomorphism.

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of local structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Tags
local diffeomorphism, manifold

-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace G N] (n : ℕ∞)

section LocalDiffeomorphAux
/-- A "diffeomorphism on" `s` is a function `f : M → N` such that `f` restricts to a diffeomorphism
`s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file. -/
structure LocalDiffeomorphAux extends LocalHomeomorph M N where
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

/-- Coercion of a `LocalDiffeomorphAux` to function.
Note that a `LocalDiffeomorphAux` is not `FunLike` (like `LocalHomeomorph`),
as `toFun` doesn't determine `invFun` outside of `target`. -/
instance : CoeFun (LocalDiffeomorphAux I J M N n) fun _ => M → N :=
  ⟨fun Φ => Φ.toFun'⟩

/-- A diffeomorphism is a local diffeomorphism. -/
def Diffeomorph.toLocalDiffeomorphAux (h : Diffeomorph I J M N n) : LocalDiffeomorphAux I J M N n :=
  {
    toLocalHomeomorph := h.toHomeomorph.toLocalHomeomorph
    contMDiffOn_toFun := fun x _ ↦ h.contMDiff_toFun x
    contMDiffOn_invFun := fun _ _ ↦ h.symm.contMDiffWithinAt
  }

-- Add the very basic API we need.
namespace LocalDiffeomorphAux
variable (Φ : LocalDiffeomorphAux I J M N n) (hn : 1 ≤ n)

/-- The inverse of a local diffeomorphism. -/
protected def symm : LocalDiffeomorphAux J I N M n := by
  exact {
    toLocalHomeomorph := Φ.toLocalHomeomorph.symm
    contMDiffOn_toFun := Φ.contMDiffOn_invFun
    contMDiffOn_invFun := Φ.contMDiffOn_toFun
  }

protected theorem contMDiffOn : ContMDiffOn I J n Φ Φ.source :=
  Φ.contMDiffOn_toFun

protected theorem contMDiffOn_symm : ContMDiffOn J I n Φ.invFun Φ.target :=
  Φ.contMDiffOn_invFun

protected theorem mdifferentiableOn : MDifferentiableOn I J Φ Φ.source :=
  (Φ.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableOn_symm : MDifferentiableOn J I Φ.invFun Φ.target :=
  (Φ.symm).mdifferentiableOn hn

protected theorem mdifferentiableAt {x : M} (hx : x ∈ Φ.source) : MDifferentiableAt I J Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

protected theorem mdifferentiableAt_symm {x : M} (hx : x ∈ Φ.source) :
    MDifferentiableAt J I Φ.invFun (Φ x) :=
  (Φ.symm).mdifferentiableAt hn (Φ.map_source hx)

/- We could add lots of additional API (following `Diffeomorph` and `LocalHomeomorph*), such as
* further continuity and differentiability lemmas
* refl and trans instances; lemmas between them.
As this declaration is meant for internal use only, we keep it simple. -/
end LocalDiffeomorphAux
end LocalDiffeomorphAux

variable {M N}

/-- `f : M → N` is called a **`C^n` local diffeomorphism at *x*** iff there exist
  open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = Φ` on `U`. -/
def IsLocalDiffeomorphAt (f : M → N) (x : M) : Prop :=
  ∃ Φ : LocalDiffeomorphAux I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source

/-- `f : M → N` is a **`C^n` local diffeomorphism** iff it is a local diffeomorphism
at each `x ∈ M`. -/
def IsLocalDiffeomorph (f : M → N) : Prop :=
  ∀ x : M, IsLocalDiffeomorphAt I J n f x

lemma isLocalDiffeomorph_iff {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J n f x := by rfl

variable {n}

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _ ↦ ⟨Φ.toLocalDiffeomorphAux, by trivial, eqOn_refl Φ _⟩

/-- The image of a local diffeomorphism is open. -/
def LocalDiffeomorph.image {f : M → N} (hf : IsLocalDiffeomorph I J n f) : Opens N := by
  refine ⟨range f, ?_⟩
  apply isOpen_iff_forall_mem_open.mpr
  intro y hy

  -- Given `y = f x ∈ range f`, we need to find `V ⊆ N` open containing `y`.
  rw [mem_range] at hy
  rcases hy with ⟨x, hxy⟩

  -- As f is a local diffeo at x, on some open set `U' ∋ x` it agrees with a diffeo `Φ : U' → V'`.
  choose Φ hyp using hf x
  rcases hyp with ⟨hxU, heq⟩
  -- Then `V:=Φ.target` has the desired properties.
  refine ⟨Φ.target, ?_, Φ.open_target, ?_⟩
  · rw [← LocalHomeomorph.image_source_eq_target, ← heq.image_eq]
    exact image_subset_range f Φ.source
  · rw [← hxy, heq hxU]
    exact Φ.toLocalHomeomorph.map_source hxU

lemma LocalDiffeomorph.image_coe {f : M → N} (hf : IsLocalDiffeomorph I J n f) :
    (LocalDiffeomorph.image I J hf).1 = range f := rfl

section helper -- FIXME: move to Algebra.Module.Basic
variable {R : Type*} [Ring R]
variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module R E]
variable {F : Type*} [TopologicalSpace F] [AddCommMonoid F] [Module R F]

/-- `g ∘ f = id` as `ContinuousLinearMap`s implies `g ∘ f = id` as functions. -/
lemma LeftInverse.of_composition {f : E →L[R] F} {g : F →L[R] E}
    (hinv : g.comp f = ContinuousLinearMap.id R E) : LeftInverse g f := by
  have : g ∘ f = id := calc g ∘ f
      _ = ↑(g.comp f) := by rw [ContinuousLinearMap.coe_comp']
      _ = ↑( ContinuousLinearMap.id R E) := by rw [hinv]
      _ = id := by rw [ContinuousLinearMap.coe_id']
  exact congrFun this

/-- `f ∘ g = id` as `ContinuousLinearMap`s implies `f ∘ g = id` as functions. -/
lemma RightInverse.of_composition {f : E →L[R] F} {g : F →L[R] E}
    (hinv : f.comp g = ContinuousLinearMap.id R F) : RightInverse g f :=
  LeftInverse.of_composition hinv
end helper

section Differential
variable {I J} {f : M → N} {x : M} (hn : 1 ≤ n)
variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]

/-- If `f` is a `C^n` local diffeomorphism at `x`, for `n ≥ 1`,
  the differential `df_x` is a linear equivalence. -/
noncomputable def LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : 1 ≤ n) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) := by
  choose Φ hyp using hf
  rcases hyp with ⟨hxU, heq⟩
  let A := mfderiv I J f x
  have hA : A = mfderiv I J Φ x := calc A
    _ = mfderivWithin I J f Φ.source x := (mfderivWithin_of_isOpen Φ.open_source hxU).symm
    _ = mfderivWithin I J Φ Φ.source x :=
      mfderivWithin_congr (Φ.open_source.uniqueMDiffWithinAt hxU) heq (heq hxU)
    _ = mfderiv I J Φ x := mfderivWithin_of_isOpen Φ.open_source hxU
  let B := mfderiv J I Φ.invFun (Φ x)
  have inv1 : B.comp A = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := calc B.comp A
    _ = B.comp (mfderiv I J Φ x) := by rw [hA]
    _ = mfderiv I I (Φ.invFun ∘ Φ) x :=
      (mfderiv_comp x (Φ.mdifferentiableAt_symm hn hxU) (Φ.mdifferentiableAt hn hxU)).symm
    _ = mfderivWithin I I (Φ.invFun ∘ Φ) Φ.source x :=
      (mfderivWithin_of_isOpen Φ.open_source hxU).symm
    _ = mfderivWithin I I id Φ.source x := by
      have : EqOn (Φ.invFun ∘ Φ) id Φ.source := fun _ hx ↦ Φ.left_inv' hx
      apply mfderivWithin_congr (Φ.open_source.uniqueMDiffWithinAt hxU) this (this hxU)
    _ = mfderiv I I id x := mfderivWithin_of_isOpen Φ.open_source hxU
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace I x) := mfderiv_id I
  have inv2 : A.comp B = ContinuousLinearMap.id 𝕜 (TangentSpace J (Φ x)) := calc A.comp B
    _ = (mfderiv I J Φ x).comp B := by rw [hA]
    _ = mfderiv J J (Φ ∘ Φ.invFun) (Φ x) := by
        -- Use the chain rule: need to rewrite both the base point Φ (Φ.invFun x)
        -- and the map Φ.invFun ∘ Φ.
        have hΦ : MDifferentiableAt I J Φ x := Φ.mdifferentiableAt hn hxU
        rw [← (Φ.left_inv hxU)] at hΦ
        let r := mfderiv_comp (Φ x) hΦ (Φ.mdifferentiableAt_symm hn hxU)
        rw [(Φ.left_inv hxU)] at r
        exact r.symm
    _ = mfderivWithin J J (Φ ∘ Φ.invFun) Φ.target (Φ x) :=
      (mfderivWithin_of_isOpen Φ.open_target (Φ.map_source hxU)).symm
    _ = mfderivWithin J J id Φ.target (Φ x) := by
      have : EqOn (Φ ∘ Φ.invFun) id Φ.target := fun _ hx ↦ Φ.right_inv' hx
      apply mfderivWithin_congr ?_ this (this (Φ.map_source hxU))
      exact (Φ.open_target.uniqueMDiffWithinAt (Φ.map_source hxU))
    _ = mfderiv J J id (Φ x) := mfderivWithin_of_isOpen Φ.open_target (Φ.map_source hxU)
    _ = ContinuousLinearMap.id 𝕜 (TangentSpace J (Φ x)) := mfderiv_id J
  exact {
    toFun := A
    invFun := B
    left_inv := LeftInverse.of_composition inv1
    right_inv := RightInverse.of_composition inv2
    continuous_toFun := A.cont
    continuous_invFun := B.cont
    map_add' := fun x_1 y ↦ ContinuousLinearMap.map_add A x_1 y
    map_smul' := by intros; simp
  }

-- FIXME: for some reason, "rfl" fails.
lemma LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorphAt I J n f x) :
    LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hf hn = mfderiv I J f x := by
  sorry

/-- Each differential of a `C^n` diffeomorphism (`n ≥ 1`) is a linear equivalence. -/
noncomputable def Diffeomorph.mfderiv_toContinuousLinearEquiv (hn : 1 ≤ n) (Φ : M ≃ₘ^n⟮I, J⟯ N)
    (x : M) : ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (Φ x)) :=
  LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (Φ.isLocalDiffeomorph x) hn

-- TODO: make `by rfl` work
lemma Diffeomorph.mfderiv_toContinuousLinearEquiv_coe (Φ : M ≃ₘ^n⟮I, J⟯ N) :
    (Φ.mfderiv_toContinuousLinearEquiv hn x).toFun = mfderiv I J Φ x := sorry

variable (x) in
/-- If `f` is a `C^n` local diffeomorphism (`n ≥ 1`), each differential is a linear equivalence. -/
noncomputable def LocalDiffeomorph.mfderiv_toContinuousLinearEquiv (hf : IsLocalDiffeomorph I J n f) :
    ContinuousLinearEquiv (RingHom.id 𝕜) (TangentSpace I x) (TangentSpace J (f x)) :=
  LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (hf x) hn

variable (x) in
lemma LocalDiffeomorph.mfderiv_toContinuousLinearEquiv_coe (hf : IsLocalDiffeomorph I J n f):
    LocalDiffeomorph.mfderiv_toContinuousLinearEquiv x hn hf = mfderiv I J f x := by
  let r := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn (hf x)
  have : (LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv (hf x) hn) =
    (LocalDiffeomorph.mfderiv_toContinuousLinearEquiv x hn hf) :=
    sorry -- TODO: why doesn't `rfl` work?
  exact this ▸ r

/-! # Differential under composition with a local diffeomorphism -/
variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']
  (I' : ModelWithCorners 𝕜 E' H') [SmoothManifoldWithCorners I' M'] [SmoothManifoldWithCorners I M]
  [SmoothManifoldWithCorners J N]

variable {φ : M → M'} (hφ : IsLocalDiffeomorphAt I I' n φ x)
  {f : M' → N} (hf : MDifferentiableAt I' J f (φ x))

-- TODO: add as basic lemma for local diffeos; also that local diffeos are contMDiffOn!
lemma fIsDifferentiableAt {φ : M → M'}  (hφ : IsLocalDiffeomorphAt I I' n φ x) :
    MDifferentiableAt I I' φ x := sorry

-- TODO: the next four to six lemmas all start the same -> can I refactor this somehow?

/-- If `φ` is a local diffeomorphism at `x` and `f` is differentiable at `φ x`,
  `mfderiv (f∘φ) x` is surjective iff `mfderiv f (φ x)` is. -/
lemma mfderiv_surjective_iff_comp_isLocalDiffeomorph : Surjective (mfderiv I' J f (φ x))
    ↔ Surjective (mfderiv I J (f ∘ φ) x) := by
  let dφ := mfderiv I I' φ x
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ' : HasMFDerivAt I I' φ x dφ := (fIsDifferentiableAt (hφ := hφ)).hasMFDerivAt
  rw [HasMFDerivAt.mfderiv ((hf.hasMFDerivAt).comp hφ' (x := x)), ← aux]
  rw [← dφiso.bijective.surjective.of_comp_iff]
  exact Iff.rfl

/-- If `φ` is a local diffeomorphism at `x` and `f` is differentiable at `φ x`,
  `mfderiv (f∘φ) x` is injective iff `mfderiv f (φ x)` is. -/
lemma mfderiv_injective_iff_comp_isLocalDiffeomorph :
    Injective (mfderiv I' J f (φ x)) ↔ Injective (mfderiv I J (f ∘ φ) x) := by
  let dφ := mfderiv I I' φ x
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ' : HasMFDerivAt I I' φ x dφ := (fIsDifferentiableAt (hφ := hφ)).hasMFDerivAt
  rw [HasMFDerivAt.mfderiv ((hf.hasMFDerivAt).comp hφ' (x := x)), ← aux]
  rw [← Injective.of_comp_iff' _ dφiso.bijective]
  exact Iff.rfl

/-- If `M` is finite-dimensional, then rk (df\cdot φ)_x = rk (df_φ(x)). -/
-- TODO: correct statement? rank, finrank, something else?
-- TODO: need the lemma about rank of linear isomorphisms; not searched yet
lemma mfderiv_rank_eq_comp_isLocalDiffeomorph [FiniteDimensional 𝕜 E] : 0 = 1 := by
  let dφ := mfderiv I I' φ x
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ' : HasMFDerivAt I I' φ x dφ := (fIsDifferentiableAt (hφ := hφ)).hasMFDerivAt
  -- rw [HasMFDerivAt.mfderiv ((hf.hasMFDerivAt).comp hφ' (x := x)), ← aux]
  sorry

variable {f : M → M'} (hf : MDifferentiableAt I I' f x)
  {φ : M' → N} (hφ : IsLocalDiffeomorphAt I' J n φ (f x))

/-- If `f` is differentiable at `x` and `φ` is a local diffeomorphism at `f x`,
  `mfderiv (φ∘f) x` is surjective iff `mfderiv φ (f x)` is. -/
lemma mfderiv_surjective_iff_comp_isLocalDiffeomorph' :
    Surjective (mfderiv I I' f x) ↔ Surjective (mfderiv I J (φ ∘ f) x) := by
  let dφ := mfderiv I' J φ (f x)
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ : HasMFDerivAt I' J φ (f x) dφ := (fIsDifferentiableAt (hφ := hφ)).hasMFDerivAt
  rw [HasMFDerivAt.mfderiv (hφ.comp (hf.hasMFDerivAt) (x := x)), ← aux]
  rw [← Surjective.of_comp_iff' dφiso.bijective]
  exact Iff.rfl

/-- If `f` is differentiable at `x` and `φ` is a local diffeomorphism at `f x`,
  `mfderiv (φ∘f) x` is injective iff `mfderiv φ (f x)` is. -/
lemma mfderiv_injective_iff_comp_isLocalDiffeomorph' :
    Injective (mfderiv I I' f x) ↔ Injective (mfderiv I J (φ ∘ f) x) := by
  let dφ := mfderiv I' J φ (f x)
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ : HasMFDerivAt I' J φ (f x) dφ := (fIsDifferentiableAt (hφ := hφ)).hasMFDerivAt
  rw [HasMFDerivAt.mfderiv (hφ.comp (hf.hasMFDerivAt) (x := x)), ← aux]
  rw [← Injective.of_comp_iff dφiso.bijective.injective]
  exact Iff.rfl

-- TODO: also insert statement about ranks of differential

end Differential


-- charts have isomorphic differentials: TODO move to different file!
section ChartsDifferentials
variable [I.Boundaryless] [SmoothManifoldWithCorners I M]

-- I have this on a branch already -> prove it!
theorem LocalHomeomorph.isOpen_extend_target (e : LocalHomeomorph M H) :
    IsOpen (e.extend I).target := sorry

-- xxx: basically copied from LocalHomeomomorph.isOpen_extend_target in the integral curves PR
lemma isOpen_extChartAt_target (x : M) : IsOpen (extChartAt I x).target := by
  sorry

def extChartAt_sourceToOpen (x : M) : Opens M :=
  ⟨(extChartAt I x).source, isOpen_extChartAt_source I x⟩

def extChartAt_targetToOpen (x : M) : Opens E :=
  ⟨(extChartAt I x).target, isOpen_extChartAt_target I x⟩

/-- If `I` is boundaryless, an extended local homeomorphism is a local homeomorph. -/
def LocalHomeomorph.extend_toLocalHomeomorph {e : LocalHomeomorph M H} : LocalHomeomorph M E :=
  {
    toLocalEquiv := e.extend I
    open_source := isOpen_extend_source e I
    open_target := isOpen_extend_target I e -- this uses boundarylessness!
    continuous_toFun := continuousOn_extend e I
    continuous_invFun := continuousOn_extend_symm e I
  }

variable (n)

-- add to ContMDiff, below contMDiffAt_extend
theorem contMDiffOn_extend {e : LocalHomeomorph M H} (he : e ∈ maximalAtlas I M) :
    ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) e.source :=
  fun _x' hx' => (contMDiffAt_extend he hx').contMDiffWithinAt

variable {e : LocalHomeomorph M H} (he : e ∈ maximalAtlas I M)

/-- If `M` has no boundary, every extended chart is a local diffeomorphism
between its source and target. -/
-- TODO: this holds for every interior point x --> this requires showing the interior is open
def extend_toLocalDiffeomorphAux : LocalDiffeomorphAux I 𝓘(𝕜, E) M E n :=
  {
    toLocalHomeomorph := e.extend_toLocalHomeomorph I
    contMDiffOn_toFun := by
      show ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) (e.extend I).source
      rw [e.extend_source]
      exact contMDiffOn_extend I n he
    contMDiffOn_invFun := by
      show ContMDiffOn 𝓘(𝕜, E) I n (e.extend I).symm (e.extend I).target
      -- should be a lemma! xxx think: why not the standard form for extend_target?
      have : (e.extend I).target = I '' e.target := by rw [e.extend_target, I.image_eq]
      exact this ▸ contMDiffOn_extend_symm he
  }

lemma LocalHomeomorph.extend_toLocalDiffeomorphAux_coe :
    (extend_toLocalDiffeomorphAux I n he).toFun = e.extend I := by
  rfl

lemma extend_toLocalDiffeomorphAux_source :
    (extend_toLocalDiffeomorphAux I n he).source = e.source := by
  rw [← e.extend_source I]
  rfl

-- this is currently unused -> is this useful to keep?
lemma extend_toLocalDiffeomorphAux_target :
    (extend_toLocalDiffeomorphAux I n he).target = (e.extend I).target := by
  rfl

/-- If `M` has no boundary, every inverse extended chart is a local diffeomorphism
between its source and target. -/
-- TODO: this holds for every interior point x --> this requires showing the interior is open
def extend_symm_toLocalDiffeomorphAux : LocalDiffeomorphAux 𝓘(𝕜, E) I E M n :=
  (extend_toLocalDiffeomorphAux I n he).symm

/- these lemmas are currently unused --- are they useful?
lemma LocalHomeomorph.extend_symm_toLocalDiffeomorphAux_coe :
    (extend_symm_toLocalDiffeomorphAux I n he).toFun = (e.extend I).symm := by
  rfl

lemma extend_symm_toLocalDiffeomorphAux_source :
    (extend_symm_toLocalDiffeomorphAux I n he).source = (e.extend I).target := by
  rfl

lemma extend_symm_toLocalDiffeomorphAux_target :
    (extend_symm_toLocalDiffeomorphAux I n he).target = e.source := by
    rw [← e.extend_source I]
    rfl
-/

variable {I} in
/-- If `M` has no boundary, each extended chart is a local diffeomorphism at each point
in its source. -/
lemma LocalHomeomorph.extend_isLocalDiffeomorphAt {x : M} (hx : x ∈ e.source) :
    IsLocalDiffeomorphAt I 𝓘(𝕜, E) n (e.extend I) x := by
  refine ⟨extend_toLocalDiffeomorphAux I n he,
    (extend_toLocalDiffeomorphAux_source I n he) ▸ hx, ?_⟩
  rw [extend_toLocalDiffeomorphAux_source I n he, ← extend_toLocalDiffeomorphAux_coe]
  exact eqOn_refl _ _

/-- If `M` has no boundary, each inverse extended chart is a local diffeomorphism
at each point of its source. -/
lemma LocalHomeomorph.extend_symm_isLocalDiffeomorphAt {y : E} (hy : y ∈ (e.extend I).target) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) I n (e.extend I).symm y :=
  ⟨(extend_toLocalDiffeomorphAux I n he).symm, hy, eqOn_refl _ _⟩

/-- If `M` has no boundary, `exChartAt I x` is a local diffeomorphism at `x`. -/
lemma extChartAt_isLocalDiffeomorphAt (x : M) :
    IsLocalDiffeomorphAt I 𝓘(𝕜, E) n (extChartAt I x) x := by
  rw [extChartAt]
  exact (chartAt H x).extend_isLocalDiffeomorphAt n (chart_mem_maximalAtlas I x)
    (mem_chart_source H x)

/-- If `M` has no boundary, each inverse extended chart is a local diffeomorphism
at each point of its source. -/
lemma extChartAt_symm_isLocalDiffeomorphAt {x : M} {y : E} (hy : y ∈ (extChartAt I x).target) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) I n (extChartAt I x).symm y := by
  rw [extChartAt]
  exact (chartAt H x).extend_symm_isLocalDiffeomorphAt I n (chart_mem_maximalAtlas I x) hy

variable {f : M → N} {x : M} (hf : MDifferentiableAt I J f x)
  {e : LocalHomeomorph M H} (hx : x ∈ e.source) {e' : LocalHomeomorph N G} (hx' : (f x) ∈ e'.source)
  (he : e ∈ maximalAtlas I M) (he' : e' ∈ maximalAtlas J N)
  [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]

/-- If `f : M → N` has surjective differential at `x` iff its local coordinate representation
  `φ ∘ f ∘ ψ.symm`, for any two charts φ, ψ around `x` and `f x`, does. -/
lemma mfderiv_surjective_iff_in_charts (hn : 1 ≤ n) : Surjective (mfderiv I J f x)
    ↔ Surjective (fderiv 𝕜 ((e'.extend J) ∘ f ∘ (e.extend I).symm) (e.extend I x)) := by
  rw [← mfderiv_eq_fderiv]
  have h0 : (e.extend I) x ∈ (e.extend I).target := sorry -- proven on another branch
  have h : (e.extend I) x ∈ (e.extend I).symm.source := by
    rw [LocalEquiv.symm_source]
    exact h0
  let x' := (e.extend I).symm ((e.extend I) x)
  have eqx' : x' = (e.extend I).symm ((e.extend I) x) := rfl
  have : x' = x := e.extend_left_inv I hx
  -- f ∘ e.symm is differentiable at eExt x
  have hf' : MDifferentiableAt 𝓘(𝕜, E) J (f ∘ (e.extend I).symm) ((e.extend I) x) := by
    rw [← this] at hf
    have aux : MDifferentiableAt 𝓘(𝕜, E) I (e.extend I).symm ((e.extend I) x) := by
      apply ContMDiffAt.mdifferentiableAt _ hn
      -- No boundary: this is true, but too strong for our last step: use a weaker version.
      -- apply ContMDiffOn.contMDiffAt _ ((e.isOpen_extend_target I).mem_nhds h0)--(mem_image_of_mem I (e.map_source hx)))
      have : IsOpen (I '' e.target) := sorry
      apply ContMDiffOn.contMDiffAt _ (this.mem_nhds (mem_image_of_mem I (e.map_source hx)))
      exact contMDiffOn_extend_symm he
    exact MDifferentiableAt.comp (hg := hf) (hf := aux) (M' := M) (M := E)

  -- Rewrite by the previous lemma twice.
  let r1 := e.extend_symm_isLocalDiffeomorphAt _ n he h
  let s1 := mfderiv_surjective_iff_comp_isLocalDiffeomorph hn _ _ r1 (this.symm ▸ hf)
  rw [e.extend_left_inv I hx] at s1
  rw [s1]

  let r2 := e'.extend_isLocalDiffeomorphAt n he' (this ▸ hx')
  rw [mfderiv_surjective_iff_comp_isLocalDiffeomorph' hn (hφ := this.symm ▸ r2) hf']
  rfl

-- corollary: f has injective/surjective/bijective differential iff its local coord rep has
-- for any two charts in that domain
-- corollary: if fin-dim, rank of differential is the same as local coord rep
-- xxx: introduce a definition for local coordinate rep?

end ChartsDifferentials
