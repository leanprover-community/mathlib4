/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.Dimension

/-!
# Local diffeomorphisms between smooth manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively such that `f` restricts to a diffeomorphism from `s` and `t`.
`f` is called a **local diffeomorphism** iff it is a local diffeomorphism at every `x ∈ M`.

## Main definitions
* `IsLocalDiffeomorphAt I J n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `IsLocalDiffeomorph I J n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `IsLocalDiffeomorph`, and `IsLocalDiffeomorphAt` implies the next.
* `LocalDiffeomorph.isOpen_range`: the image of a local diffeomorphism is open
* `Diffeomorph.of_bijective_isLocalDiffeomorph`:
  a bijective local diffeomorphism is a diffeomorphism.

* `Diffeomorph.mfderiv_toContinuousLinearEquiv`: each differential of a `C^n` diffeomorphism
(`n ≥ 1`) is a linear equivalence.
* `LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv`: if `f` is a local diffeomorphism
at `x`, the differential `mfderiv I J n f x` is a continuous linear equivalence.
* `LocalDiffeomorph.differential_toContinuousLinearEquiv`: if `f` is a local diffeomorphism,
each differential `mfderiv I J n f x` is a continuous linear equivalence.

## TODO
* an injective diffeomorphism is a diffeomorphism to its image
* each differential of a `C^n` diffeomorphism (`n ≥ 1`) is a linear equivalence.
* if `f` is a local diffeomorphism at `x`, the differential `mfderiv I J n f x`
is a continuous linear isomorphism.
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

section PartialDiffeomorph
/-- A partial diffeomorphism on `s` is a function `f : M → N` such that `f` restricts to a
diffeomorphism `s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file. -/
-- TODO: rename `LocalHomeomorph` to `PartialHomeomorph` to match this name.
structure PartialDiffeomorph extends LocalEquiv M N where
  open_source : IsOpen source
  open_target : IsOpen target
  contMDiffOn_toFun : ContMDiffOn I J n toFun source
  contMDiffOn_invFun : ContMDiffOn J I n invFun target

/-- Coercion of a `PartialDiffeomorph` to function.
Note that a `PartialDiffeomorph` is not `FunLike` (like `LocalHomeomorph`),
as `toFun` doesn't determine `invFun` outside of `target`. -/
instance : CoeFun (PartialDiffeomorph I J M N n) fun _ => M → N :=
  ⟨fun Φ => Φ.toFun⟩

-- Add the very basic API we need.
namespace PartialDiffeomorph
variable (Φ : PartialDiffeomorph I J M N n) (hn : 1 ≤ n)

/-- A partial diffeomorphism is also a local homeomorphism. -/
def toLocalHomeomorph : LocalHomeomorph M N :=
  {
    toLocalEquiv := Φ.toLocalEquiv
    open_source := Φ.open_source
    open_target := Φ.open_target
    continuous_toFun := Φ.contMDiffOn_toFun.continuousOn
    continuous_invFun := Φ.contMDiffOn_invFun.continuousOn
  }

/-- The inverse of a partial diffeomorphism. -/
protected def symm : PartialDiffeomorph J I N M n :=
  {
    toLocalEquiv := Φ.toLocalEquiv.symm
    open_source := Φ.open_target
    open_target := Φ.open_source
    contMDiffOn_toFun := Φ.contMDiffOn_invFun
    contMDiffOn_invFun := Φ.contMDiffOn_toFun
  }

protected theorem contMDiffOn : ContMDiffOn I J n Φ Φ.source :=
  Φ.contMDiffOn_toFun

protected theorem contMDiffOn_symm : ContMDiffOn J I n Φ.symm Φ.target :=
  Φ.contMDiffOn_invFun

protected theorem mdifferentiableOn : MDifferentiableOn I J Φ Φ.source :=
  (Φ.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableOn_symm : MDifferentiableOn J I Φ.invFun Φ.target :=
  (Φ.symm).mdifferentiableOn hn

protected theorem mdifferentiableAt {x : M} (hx : x ∈ Φ.source) : MDifferentiableAt I J Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

protected theorem mdifferentiableAt_symm {x : M} (hx : x ∈ Φ.source) :
    MDifferentiableAt J I Φ.symm (Φ x) :=
  (Φ.symm).mdifferentiableAt hn (Φ.map_source hx)

/- We could add lots of additional API (following `Diffeomorph` and `LocalHomeomorph*), such as
* further continuity and differentiability lemmas
* refl and trans instances; lemmas between them.
As this declaration is meant for internal use only, we keep it simple. -/
end PartialDiffeomorph
end PartialDiffeomorph

variable {M N}

/-- `f : M → N` is called a **`C^n` local diffeomorphism at *x*** iff there exist
  open sets `U ∋ x` and `V ∋ f x` and a diffeomorphism `Φ : U → V` such that `f = Φ` on `U`. -/
def IsLocalDiffeomorphAt (f : M → N) (x : M) : Prop :=
  ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source

/-- `f : M → N` is a **`C^n` local diffeomorphism** iff it is a local diffeomorphism
at each `x ∈ M`. -/
def IsLocalDiffeomorph (f : M → N) : Prop :=
  ∀ x : M, IsLocalDiffeomorphAt I J n f x

lemma isLocalDiffeomorph_iff {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J n f x := by rfl

variable {n}

/-! # Basic properties of local diffeomorphisms -/
section Basic
variable {f : M → N} {x : M}

/-- A `C^n` local diffeomorphism at `x` is `C^n` differentiable at `x`. -/
lemma contMDiffAt_of_isLocalDiffeomorphAt (hf : IsLocalDiffeomorphAt I J n f x) :
    ContMDiffAt I J n f x := by
  choose Φ hx heq using hf
  -- In fact, even `ContMDiffOn I J n f Φ.source`.
  exact ((Φ.contMDiffOn_toFun).congr heq).contMDiffAt (Φ.open_source.mem_nhds hx)

/-- A local diffeomorphism at `x` is differentiable at `x`. -/
lemma mdifferentiableAt_of_isLocalDiffeomorphAt (hn : 1 ≤ n) (hf : IsLocalDiffeomorphAt I J n f x) :
    MDifferentiableAt I J f x :=
  (contMDiffAt_of_isLocalDiffeomorphAt I J hf).mdifferentiableAt hn

/-- A `C^n` local diffeomorphism is `C^n`. -/
lemma contMDiff_of_isLocalDiffeomorph (hf : IsLocalDiffeomorph I J n f) : ContMDiff I J n f :=
  fun x ↦ contMDiffAt_of_isLocalDiffeomorphAt I J (hf x)

/-- A `C^n` local diffeomorphism is differentiable. -/
lemma mdifferentiable_of_isLocalDiffeomorph (hn : 1 ≤ n) (hf : IsLocalDiffeomorph I J n f) :
    MDifferentiable I J f :=
  fun x ↦ mdifferentiableAt_of_isLocalDiffeomorphAt I J hn (hf x)

/-- A diffeomorphism is a partial diffeomorphism. -/
def Diffeomorph.toPartialDiffeomorph (h : Diffeomorph I J M N n) : PartialDiffeomorph I J M N n :=
  {
    toLocalEquiv := h.toHomeomorph.toLocalEquiv
    open_source := isOpen_univ
    open_target := isOpen_univ
    contMDiffOn_toFun := fun x _ ↦ h.contMDiff_toFun x
    contMDiffOn_invFun := fun _ _ ↦ h.symm.contMDiffWithinAt
  }

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _x ↦ ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

/-- A local diffeomorphism has open range. -/
lemma LocalDiffeomorph.isOpen_range {f : M → N} (hf : IsLocalDiffeomorph I J n f) :
    IsOpen (range f) := by
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
  · rw [← LocalEquiv.image_source_eq_target, ← heq.image_eq]
    exact image_subset_range f Φ.source
  · rw [← hxy, heq hxU]
    exact Φ.map_source' hxU

/-- The image of a local diffeomorphism is open. -/
def LocalDiffeomorph.image {f : M → N} (hf : IsLocalDiffeomorph I J n f) : Opens N :=
  ⟨range f, isOpen_range I J hf⟩

lemma LocalDiffeomorph.image_coe {f : M → N} (hf : IsLocalDiffeomorph I J n f) :
    (LocalDiffeomorph.image I J hf).1 = range f := rfl

/-- A bijective local diffeomorphism is a diffeomorphism. -/
noncomputable def Diffeomorph.of_bijective_isLocalDiffeomorph {f : M → N}
    (hf' : Function.Bijective f) (hf : IsLocalDiffeomorph I J n f) : Diffeomorph I J M N n := by
  -- Choose a right inverse `g` of `f`.
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
   -- Choose diffeomorphisms φ_x which coincide which `f` near `x`.
  choose Φ hyp using (fun x ↦ hf x)
  -- Two such diffeomorphisms (and their inverses!) coincide on their sources:
  -- they're both inverses to g. In fact, the latter suffices for our proof.
  -- have : ∀ x y, EqOn (Φ x).symm (Φ y).symm ((Φ x).target ∩ (Φ y).target) := sorry
  have aux : ∀ x, EqOn g (Φ x).symm (Φ x).target :=
    fun x ↦ eqOn_of_leftInvOn_of_rightInvOn (fun x' _ ↦ hgInverse.1 x')
      (LeftInvOn.congr_left ((Φ x).toLocalHomeomorph).rightInvOn
        ((Φ x).toLocalHomeomorph).symm_mapsTo (hyp x).2.symm)
      (fun _y hy ↦(Φ x).map_target hy)
  exact {
    toFun := f
    invFun := g
    left_inv := hgInverse.1
    right_inv := hgInverse.2
    contMDiff_toFun := contMDiff_of_isLocalDiffeomorph I J hf
    contMDiff_invFun := by
      intro y
      let x := g y
      obtain ⟨hx, hfx⟩ := hyp x
      apply ((PartialDiffeomorph.contMDiffOn J I N M n (Φ x).symm).congr (aux x)).contMDiffAt
      apply (((Φ x).open_target).mem_nhds ?_)
      have : y = (Φ x) x := (Eq.congr (hgInverse.2 y) (hfx hx)).mp rfl
      exact this ▸ (Φ x).map_source hx
  }

end Basic

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

-- TODO: the next six lemmas all start the same way; can I refactor this somehow?

/-- If `φ` is a local diffeomorphism at `x` and `f` is differentiable at `φ x`,
  `mfderiv (f∘φ) x` is surjective iff `mfderiv f (φ x)` is. -/
lemma mfderiv_surjective_iff_comp_isLocalDiffeomorph : Surjective (mfderiv I' J f (φ x))
    ↔ Surjective (mfderiv I J (f ∘ φ) x) := by
  let dφ := mfderiv I I' φ x
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ' : HasMFDerivAt I I' φ x dφ :=
    (mdifferentiableAt_of_isLocalDiffeomorphAt _ _ hn hφ).hasMFDerivAt
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
  have hφ' : HasMFDerivAt I I' φ x dφ :=
    (mdifferentiableAt_of_isLocalDiffeomorphAt _ _ hn hφ).hasMFDerivAt
  rw [HasMFDerivAt.mfderiv ((hf.hasMFDerivAt).comp hφ' (x := x)), ← aux]
  rw [← Injective.of_comp_iff' _ dφiso.bijective]
  exact Iff.rfl

/-- If `f` is differentiable at `x` and `φ` is a local diffeomorphism at `f x`,
  `mfderiv (φ∘f) x` is bijective iff `mfderiv φ (f x)` is. -/
lemma mfderiv_bijective_iff_comp_isLocalDiffeomorph :
    Bijective (mfderiv I' J f (φ x)) ↔ Bijective (mfderiv I J (f ∘ φ) x) := by
  rw [Bijective, Bijective, and_congr]
  apply mfderiv_injective_iff_comp_isLocalDiffeomorph hn hφ (hf := hf)
  apply mfderiv_surjective_iff_comp_isLocalDiffeomorph hn hφ (hf := hf)

open LinearMap (rank)

/-- If `M` is finite-dimensional, then rk d(f∘φ)_x = rk (df_φ(x)). -/
-- xxx: is finite-dimensionality required, or obvious by Lean convention?
lemma mfderiv_rank_eq_comp_isLocalDiffeomorph [FiniteDimensional 𝕜 E] :
    rank (mfderiv I' J f (φ x)).toLinearMap = rank (mfderiv I J (f ∘ φ) x).toLinearMap := by

  let dφ := mfderiv I I' φ x
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ' : HasMFDerivAt I I' φ x dφ :=
    (mdifferentiableAt_of_isLocalDiffeomorphAt _ _ hn hφ).hasMFDerivAt
  rw [HasMFDerivAt.mfderiv ((hf.hasMFDerivAt).comp hφ' (x := x)), ← aux]

  set df := mfderiv I' J f (φ x)
  apply le_antisymm ?_ (LinearMap.rank_comp_le_left dφiso.toLinearMap df.toLinearMap)
  sorry -- this is the hard inclusion: why is rank df ≤ rank (df ∘ dφiso)
  -- probably doable, using LinearMap.le_rank_iff_exists_linearIndependent

variable {f : M → M'} (hf : MDifferentiableAt I I' f x)
  {φ : M' → N} (hφ : IsLocalDiffeomorphAt I' J n φ (f x))

/-- If `f` is differentiable at `x` and `φ` is a local diffeomorphism at `f x`,
  `mfderiv (φ∘f) x` is surjective iff `mfderiv φ (f x)` is. -/
lemma mfderiv_surjective_iff_comp_isLocalDiffeomorph' :
    Surjective (mfderiv I I' f x) ↔ Surjective (mfderiv I J (φ ∘ f) x) := by
  let dφ := mfderiv I' J φ (f x)
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ : HasMFDerivAt I' J φ (f x) dφ :=
    (mdifferentiableAt_of_isLocalDiffeomorphAt _ _ hn hφ).hasMFDerivAt
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
  have hφ : HasMFDerivAt I' J φ (f x) dφ :=
    (mdifferentiableAt_of_isLocalDiffeomorphAt _ _ hn hφ).hasMFDerivAt
  rw [HasMFDerivAt.mfderiv (hφ.comp (hf.hasMFDerivAt) (x := x)), ← aux]
  rw [← Injective.of_comp_iff dφiso.bijective.injective]
  exact Iff.rfl

/-- If `f` is differentiable at `x` and `φ` is a local diffeomorphism at `f x`,
  `mfderiv (φ∘f) x` is bijective iff `mfderiv φ (f x)` is. -/
lemma mfderiv_bijective_iff_comp_isLocalDiffeomorph' :
    Bijective (mfderiv I I' f x) ↔ Bijective (mfderiv I J (φ ∘ f) x) := by
  rw [Bijective, Bijective, and_congr]
  apply mfderiv_injective_iff_comp_isLocalDiffeomorph' hn hφ (hf := hf)
  apply mfderiv_surjective_iff_comp_isLocalDiffeomorph' hn hφ (hf := hf)

/-- If `M` is finite-dimensional, then rk d(φ ∘ f)_x = rk (dφ_f(x)). -/
lemma mfderiv_rank_eq_comp_isLocalDiffeomorph' [FiniteDimensional 𝕜 E] : 0 = 1 := by
  -- TODO. this doesn't typecheck, both sides live in different universes
  -- need to name levels explicitly, then use Cardinal.lift on e.g. the LHS
  -- rank (mfderiv I' J φ (f x)).toLinearMap = rank (mfderiv I I' f x).toLinearMap := by
  let dφ := mfderiv I' J φ (f x)
  let dφiso := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv hφ hn
  have aux : dφiso = dφ := LocalDiffeomorphAt.mfderiv_toContinuousLinearEquiv_coe hn hφ
  have hφ : HasMFDerivAt I' J φ (f x) dφ :=
    (mdifferentiableAt_of_isLocalDiffeomorphAt _ _ hn hφ).hasMFDerivAt
  -- rw [HasMFDerivAt.mfderiv (hφ.comp (hf.hasMFDerivAt) (x := x)), ← aux]
  -- set dφ := mfderiv I' J φ (f x)
  -- LinearEquiv.rank_map_eq should do the trick here
  sorry

end Differential


-- charts have isomorphic differentials: TODO move to different file!
section ChartsDifferentials
variable [I.Boundaryless] [SmoothManifoldWithCorners I M]

def extChartAt_sourceToOpen (x : M) : Opens M :=
  ⟨(extChartAt I x).source, isOpen_extChartAt_source I x⟩

def extChartAt_targetToOpen (x : M) : Opens E :=
  ⟨(extChartAt I x).target, isOpen_extChartAt_target I x⟩

/-- If `I` is boundaryless, an extended local homeomorphism is a local homeomorph. -/
def LocalHomeomorph.extend_toLocalHomeomorph {e : LocalHomeomorph M H} : LocalHomeomorph M E :=
  {
    toLocalEquiv := e.extend I
    open_source := isOpen_extend_source e I
    open_target := isOpen_extend_target e I
    continuous_toFun := continuousOn_extend e I
    continuous_invFun := continuousOn_extend_symm e I
  }

variable (n) {e : LocalHomeomorph M H} (he : e ∈ maximalAtlas I M)

/-- If `M` has no boundary, every extended chart is a local diffeomorphism
between its source and target. -/
-- TODO: show this for every interior point x (once we know the interior is open)
def extend_toPartialDiffeomorph : PartialDiffeomorph I 𝓘(𝕜, E) M E n :=
  {
    toLocalEquiv := e.extend I
    open_source := e.isOpen_extend_source I
    open_target := e.isOpen_extend_target I
    contMDiffOn_toFun := by
      show ContMDiffOn I 𝓘(𝕜, E) n (e.extend I) (e.extend I).source
      rw [e.extend_source]
      exact contMDiffOn_extend he
    contMDiffOn_invFun := by
      show ContMDiffOn 𝓘(𝕜, E) I n (e.extend I).symm (e.extend I).target
      -- should be a lemma! xxx think: why not the standard form for extend_target?
      have : (e.extend I).target = I '' e.target := by rw [e.extend_target, I.image_eq]
      exact this ▸ contMDiffOn_extend_symm he
  }

lemma LocalHomeomorph.extend_toPartialDiffeomorph_coe :
    (extend_toPartialDiffeomorph I n he).toFun = e.extend I := by
  rfl

lemma extend_toPartialDiffeomorph_source :
    (extend_toPartialDiffeomorph I n he).source = e.source := by
  rw [← e.extend_source I]
  rfl

-- this is currently unused -> is this useful to keep?
lemma extend_toPartialDiffeomorph_target :
    (extend_toPartialDiffeomorph I n he).target = (e.extend I).target := by
  rfl

/-- If `M` has no boundary, every inverse extended chart is a local diffeomorphism
between its source and target. -/
-- TODO: show this for every interior point x (once we know the interior is open)
def extend_symm_toPartialDiffeomorph : PartialDiffeomorph 𝓘(𝕜, E) I E M n :=
  (extend_toPartialDiffeomorph I n he).symm

/- these lemmas are currently unused --- are they useful?
lemma LocalHomeomorph.extend_symm_toPartialDiffeomorph_coe :
    (extend_symm_toPartialDiffeomorph I n he).toFun = (e.extend I).symm := by
  rfl

lemma extend_symm_toPartialDiffeomorph_source :
    (extend_symm_toPartialDiffeomorph I n he).source = (e.extend I).target := by
  rfl

lemma extend_symm_toPartialDiffeomorph_target :
    (extend_symm_toPartialDiffeomorph I n he).target = e.source := by
    rw [← e.extend_source I]
    rfl
-/

variable {I}

/-- If `M` has no boundary, each extended chart is a local diffeomorphism at each point
in its source. -/
-- TODO: show this for every interior point x (once we know the interior is open)
lemma LocalHomeomorph.extend_isLocalDiffeomorphAt {x : M} (hx : x ∈ e.source) :
    IsLocalDiffeomorphAt I 𝓘(𝕜, E) n (e.extend I) x := by
  refine ⟨extend_toPartialDiffeomorph I n he,
    (extend_toPartialDiffeomorph_source I n he) ▸ hx, ?_⟩
  rw [extend_toPartialDiffeomorph_source I n he, ← extend_toPartialDiffeomorph_coe]
  exact eqOn_refl _ _

/-- If `M` has no boundary, each inverse extended chart is a local diffeomorphism
at each point of its source. -/
-- TODO: show this for every interior point x (once we know the interior is open)
lemma LocalHomeomorph.extend_symm_isLocalDiffeomorphAt {y : E} (hy : y ∈ (e.extend I).target) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) I n (e.extend I).symm y :=
  ⟨(extend_toPartialDiffeomorph I n he).symm, hy, eqOn_refl _ _⟩

/-- If `M` has no boundary, `extChartAt I x` is a local diffeomorphism at `x`. -/
-- TODO: show this for every interior point x (once we know the interior is open)
lemma extChartAt_isLocalDiffeomorphAt (x : M) :
    IsLocalDiffeomorphAt I 𝓘(𝕜, E) n (extChartAt I x) x := by
  rw [extChartAt]
  exact (chartAt H x).extend_isLocalDiffeomorphAt n (chart_mem_maximalAtlas I x)
    (mem_chart_source H x)

/-- If `M` has no boundary, `(extChartAt I x).symm` is a local diffeomorphism at `x`. -/
-- TODO: show this for every interior point x (once we know the interior is open)
lemma extChartAt_symm_isLocalDiffeomorphAt {x : M} {y : E} (hy : y ∈ (extChartAt I x).target) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) I n (extChartAt I x).symm y := by
  rw [extChartAt]
  exact (chartAt H x).extend_symm_isLocalDiffeomorphAt n (chart_mem_maximalAtlas I x) hy

variable {f : M → N} {x : M} (hf : MDifferentiableAt I J f x)
  {e : LocalHomeomorph M H} (hx : x ∈ e.source) {e' : LocalHomeomorph N G} (hx' : (f x) ∈ e'.source)
  (he : e ∈ maximalAtlas I M) (he' : e' ∈ maximalAtlas J N)
  [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N] [J.Boundaryless]

variable {J n}

/-- If `f : M → N` has surjective differential at `x` iff its local coordinate representation
  `φ ∘ f ∘ ψ.symm`, for any two charts φ, ψ around `x` and `f x`, does. -/
lemma mfderiv_surjective_iff_in_charts (hn : 1 ≤ n) : Surjective (mfderiv I J f x)
    ↔ Surjective (fderiv 𝕜 ((e'.extend J) ∘ f ∘ (e.extend I).symm) (e.extend I x)) := by
  rw [← mfderiv_eq_fderiv]
  have h : (e.extend I) x ∈ (e.extend I).symm.source := by
    rw [← e.extend_source I] at hx
    exact e.mapsTo_extend' I hx
  let x' := (e.extend I).symm ((e.extend I) x)
  have eqx' : x' = (e.extend I).symm ((e.extend I) x) := rfl
  have : x' = x := e.extend_left_inv I hx
  -- f ∘ e.symm is differentiable at eExt x
  have hf' : MDifferentiableAt 𝓘(𝕜, E) J (f ∘ (e.extend I).symm) ((e.extend I) x) := by
    rw [← this] at hf
    have aux : MDifferentiableAt 𝓘(𝕜, E) I (e.extend I).symm ((e.extend I) x) := by
      apply ContMDiffAt.mdifferentiableAt _ hn
      -- No boundary: this is true, but too strong for our last step: use a weaker version.
      -- apply ContMDiffOn.contMDiffAt _ ((e.isOpen_extend_target I).mem_nhds h0)
      have : IsOpen (I '' e.target) := sorry -- have this on a branch also
      apply ContMDiffOn.contMDiffAt _ (this.mem_nhds (mem_image_of_mem I (e.map_source hx)))
      exact contMDiffOn_extend_symm he
    exact hf.comp _ aux (M := E)

  let r1 := e.extend_symm_isLocalDiffeomorphAt n he h
  let s1 := mfderiv_surjective_iff_comp_isLocalDiffeomorph hn _ _ r1 (this.symm ▸ hf)
  rw [e.extend_left_inv I hx] at s1
  rw [s1]

  let r2 := e'.extend_isLocalDiffeomorphAt n he' (this ▸ hx')
  rw [mfderiv_surjective_iff_comp_isLocalDiffeomorph' hn (hφ := this.symm ▸ r2) hf']
  rfl

/-- If `f : M → N` has injective differential at `x` iff its local coordinate representation
  `φ ∘ f ∘ ψ.symm`, for any two charts φ, ψ around `x` and `f x`, does. -/
lemma mfderiv_injective_iff_in_charts (hn : 1 ≤ n) : Injective (mfderiv I J f x)
    ↔ Injective (fderiv 𝕜 ((e'.extend J) ∘ f ∘ (e.extend I).symm) (e.extend I x)) := by
  -- TODO: reduce this duplication somehow!
  rw [← mfderiv_eq_fderiv]
  have h : (e.extend I) x ∈ (e.extend I).symm.source := by
    rw [← e.extend_source I] at hx
    exact e.mapsTo_extend' I hx
  let x' := (e.extend I).symm ((e.extend I) x)
  have eqx' : x' = (e.extend I).symm ((e.extend I) x) := rfl
  have : x' = x := e.extend_left_inv I hx
  -- f ∘ e.symm is differentiable at eExt x
  have hf' : MDifferentiableAt 𝓘(𝕜, E) J (f ∘ (e.extend I).symm) ((e.extend I) x) := by
    rw [← this] at hf
    have aux : MDifferentiableAt 𝓘(𝕜, E) I (e.extend I).symm ((e.extend I) x) := by
      apply ContMDiffAt.mdifferentiableAt _ hn
      -- No boundary: this is true, but too strong for our last step: use a weaker version.
      -- apply ContMDiffOn.contMDiffAt _ ((e.isOpen_extend_target I).mem_nhds h0)
      have : IsOpen (I '' e.target) := sorry -- have this on a branch also
      apply ContMDiffOn.contMDiffAt _ (this.mem_nhds (mem_image_of_mem I (e.map_source hx)))
      exact contMDiffOn_extend_symm he
    exact hf.comp _ aux (M := E)
  let r1 := e.extend_symm_isLocalDiffeomorphAt n he h
  let s1 := mfderiv_injective_iff_comp_isLocalDiffeomorph hn _ _ r1 (this.symm ▸ hf)
  rw [e.extend_left_inv I hx] at s1
  rw [s1]
  let r2 := e'.extend_isLocalDiffeomorphAt n he' (this ▸ hx')
  rw [mfderiv_injective_iff_comp_isLocalDiffeomorph' hn (hφ := this.symm ▸ r2) hf']
  rfl

/-- If `f : M → N` has bijective differential at `x` iff its local coordinate representation
  `φ ∘ f ∘ ψ.symm`, for any two charts φ, ψ around `x` and `f x`, does. -/
-- this proof is just the chart application of the other statements... can I reuse this?
lemma mfderiv_bijective_iff_in_charts (hn : 1 ≤ n) : Bijective (mfderiv I J f x) ↔
    Bijective (fderiv 𝕜 ((e'.extend J) ∘ f ∘ (e.extend I).symm) (e.extend I x)) := by
  rw [Bijective, Bijective, and_congr]
  apply mfderiv_injective_iff_in_charts hf hx hx' he he' hn
  apply mfderiv_surjective_iff_in_charts hf hx hx' he he' hn

-- corollary: if M is finite-dimensional, rank of differential df_x equals the rank of d(f_loc),
-- where f_loc is the local coordinate representation
-- xxx: introduce a definition for local coordinate rep?

-- Sample application of the lemmas above.
lemma cor (hn : 1 ≤ n) : Bijective (mfderiv I J f x) ↔
    Bijective (fderiv 𝕜 ((extChartAt J (f x)) ∘ f ∘ (extChartAt I x).symm) (extChartAt I x x)) := by
  rw [extChartAt]
  apply mfderiv_bijective_iff_in_charts hf (mem_chart_source H x) (mem_chart_source G (f x))
    (chart_mem_maximalAtlas I x) (chart_mem_maximalAtlas J (f x)) hn

end ChartsDifferentials
