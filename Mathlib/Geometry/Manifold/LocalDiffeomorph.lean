/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Local diffeomorphisms between manifolds

In this file, we define `C^n` local diffeomorphisms between manifolds.

A `C^n` map `f : M → N` is a **local diffeomorphism at `x`** iff there are neighbourhoods `s`
and `t` of `x` and `f x`, respectively, such that `f` restricts to a diffeomorphism
between `s` and `t`. `f` is called a **local diffeomorphism on `s`** iff it is a local
diffeomorphism at every `x ∈ s`, and a **local diffeomorphism** iff it is a local diffeomorphism on
`univ`.

## Main definitions
* `IsLocalDiffeomorphAt I J n f x`: `f` is a `C^n` local diffeomorphism at `x`
* `IsLocalDiffeomorphOn I J n f s`: `f` is a `C^n` local diffeomorphism on `s`
* `IsLocalDiffeomorph I J n f`: `f` is a `C^n` local diffeomorphism

## Main results
* Each of `Diffeomorph`, `IsLocalDiffeomorph`, `IsLocalDiffeomorphOn` and `IsLocalDiffeomorphAt`
  implies the next condition.
* `IsLocalDiffeomorph.isLocalHomeomorph`: a local diffeomorphism is a local homeomorphism,
  and similarly for a local diffeomorphism on `s`.
* `IsLocalDiffeomorph.isOpen_range`: the image of a local diffeomorphism is open
* `IsLocalDiffeomorph.diffeomorphOfBijective`:
  a bijective local diffeomorphism is a diffeomorphism

* `Diffeomorph.mfderivToContinuousLinearEquiv`: each differential of a `C^n` diffeomorphism
  (`n ≠ 0`) is a linear equivalence.
* `LocalDiffeomorphAt.mfderivToContinuousLinearEquiv`: if `f` is a local diffeomorphism
  at `x`, the differential `mfderiv I J n f x` is a continuous linear equivalence.
* `LocalDiffeomorph.mfderivToContinuousLinearEquiv`: if `f` is a local diffeomorphism,
  each differential `mfderiv I J n f x` is a continuous linear equivalence.

## TODO
* an injective local diffeomorphism is a diffeomorphism to its image
* if `f` is `C^n` at `x` and `mfderiv I J n f x` is a linear isomorphism,
  `f` is a local diffeomorphism at `x` (using the inverse function theorem).

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of local structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

## Tags
local diffeomorphism, manifold

-/

@[expose] public section

open Manifold Set TopologicalSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (N : Type*) [TopologicalSpace N] [ChartedSpace G N] (n : WithTop ℕ∞)

section PartialDiffeomorph
/-- A partial diffeomorphism on `s` is a function `f : M → N` such that `f` restricts to a
diffeomorphism `s → t` between open subsets of `M` and `N`, respectively.
This is an auxiliary definition and should not be used outside of this file. -/
structure PartialDiffeomorph extends PartialEquiv M N where
  open_source : IsOpen source
  open_target : IsOpen target
  contMDiffOn_toFun : CMDiff[source] n toFun
  contMDiffOn_invFun : CMDiff[target] n invFun

/-- Coercion of a `PartialDiffeomorph` to function.
Note that a `PartialDiffeomorph` is not `DFunLike` (like `OpenPartialHomeomorph`),
as `toFun` doesn't determine `invFun` outside of `target`. -/
instance : CoeFun (PartialDiffeomorph I J M N n) fun _ => M → N :=
  ⟨fun Φ => Φ.toFun⟩

variable {I J M N n}

/-- A diffeomorphism is a partial diffeomorphism. -/
def Diffeomorph.toPartialDiffeomorph (h : Diffeomorph I J M N n) :
    PartialDiffeomorph I J M N n where
  toPartialEquiv := h.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := h.contMDiff_toFun x
  contMDiffOn_invFun _ _ := h.symm.contMDiffWithinAt

-- Add the very basic API we need.
namespace PartialDiffeomorph
variable (Φ : PartialDiffeomorph I J M N n)

/-- A partial diffeomorphism is also a local homeomorphism. -/
def toOpenPartialHomeomorph : OpenPartialHomeomorph M N where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  continuousOn_toFun := Φ.contMDiffOn_toFun.continuousOn
  continuousOn_invFun := Φ.contMDiffOn_invFun.continuousOn

/-- The inverse of a local diffeomorphism. -/
protected def symm : PartialDiffeomorph J I N M n where
  toPartialEquiv := Φ.toPartialEquiv.symm
  open_source := Φ.open_target
  open_target := Φ.open_source
  contMDiffOn_toFun := Φ.contMDiffOn_invFun
  contMDiffOn_invFun := Φ.contMDiffOn_toFun

protected theorem contMDiffOn : CMDiff[Φ.source] n Φ := Φ.contMDiffOn_toFun

protected theorem mdifferentiableOn (hn : n ≠ 0) : MDiff[Φ.source] Φ :=
  (Φ.contMDiffOn).mdifferentiableOn hn

protected theorem mdifferentiableAt (hn : n ≠ 0) {x : M} (hx : x ∈ Φ.source) :
    MDiffAt Φ x :=
  (Φ.mdifferentiableOn hn x hx).mdifferentiableAt (Φ.open_source.mem_nhds hx)

/- We could add lots of additional API (following `Diffeomorph` and `OpenPartialHomeomorph`),
such as
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

lemma PartialDiffeomorph.isLocalDiffeomorphAt (φ : PartialDiffeomorph I J M N n)
    {x : M} (hx : x ∈ φ.source) : IsLocalDiffeomorphAt I J n φ x :=
  ⟨φ, hx, Set.eqOn_refl _ _⟩

namespace IsLocalDiffeomorphAt

variable {f : M → N} {x : M}

variable {I I' J n}

/-- An arbitrary choice of local inverse of `f` near `x`. -/
noncomputable def localInverse (hf : IsLocalDiffeomorphAt I J n f x) :
    PartialDiffeomorph J I N M n := (Classical.choose hf).symm

lemma localInverse_open_source (hf : IsLocalDiffeomorphAt I J n f x) :
    IsOpen hf.localInverse.source :=
  PartialDiffeomorph.open_source _

lemma localInverse_mem_source (hf : IsLocalDiffeomorphAt I J n f x) :
    f x ∈ hf.localInverse.source := by
  rw [(hf.choose_spec.2 hf.choose_spec.1)]
  exact (Classical.choose hf).map_source hf.choose_spec.1

lemma localInverse_mem_target (hf : IsLocalDiffeomorphAt I J n f x) :
    x ∈ hf.localInverse.target :=
  hf.choose_spec.1

lemma contmdiffOn_localInverse (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiff[hf.localInverse.source] n hf.localInverse :=
  hf.localInverse.contMDiffOn_toFun

lemma localInverse_right_inv (hf : IsLocalDiffeomorphAt I J n f x) {y : N}
    (hy : y ∈ hf.localInverse.source) : f (hf.localInverse y) = y := by
  have : hf.localInverse y ∈ hf.choose.source := by
    rw [← hf.choose.symm_target]
    exact hf.choose.symm.map_source hy
  rw [hf.choose_spec.2 this]
  exact hf.choose.right_inv hy

lemma localInverse_eqOn_right (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn (f ∘ hf.localInverse) id hf.localInverse.source :=
  fun _y hy ↦ hf.localInverse_right_inv hy

lemma localInverse_eventuallyEq_right (hf : IsLocalDiffeomorphAt I J n f x) :
    f ∘ hf.localInverse =ᶠ[nhds (f x)] id :=
  Filter.eventuallyEq_of_mem
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)
    hf.localInverse_eqOn_right

lemma localInverse_left_inv (hf : IsLocalDiffeomorphAt I J n f x) {x' : M}
    (hx' : x' ∈ hf.localInverse.target) : hf.localInverse (f x') = x' := by
  rw [hf.choose_spec.2 (hf.choose.symm_target ▸ hx')]
  exact hf.choose.left_inv hx'

lemma localInverse_eqOn_left (hf : IsLocalDiffeomorphAt I J n f x) :
    EqOn (hf.localInverse ∘ f) id hf.localInverse.target :=
  fun _ hx ↦ hf.localInverse_left_inv hx

lemma localInverse_eventuallyEq_left (hf : IsLocalDiffeomorphAt I J n f x) :
    hf.localInverse ∘ f =ᶠ[nhds x] id :=
  Filter.eventuallyEq_of_mem
    (hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target) hf.localInverse_eqOn_left

lemma localInverse_isLocalDiffeomorphAt (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphAt J I n (hf.localInverse) (f x) :=
  hf.localInverse.isLocalDiffeomorphAt _ _ _ hf.localInverse_mem_source

lemma localInverse_contMDiffOn (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiff[hf.localInverse.source] n hf.localInverse :=
  hf.localInverse.contMDiffOn_toFun

lemma localInverse_contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiffAt n hf.localInverse (f x) :=
  hf.localInverse_contMDiffOn.contMDiffAt
    (hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source)

lemma localInverse_mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    MDiffAt hf.localInverse (f x) :=
  hf.localInverse_contMDiffAt.mdifferentiableAt hn

end IsLocalDiffeomorphAt

/-- `f : M → N` is called a **`C^n` local diffeomorphism on *s*** iff it is a local diffeomorphism
at each `x : s`. -/
def IsLocalDiffeomorphOn (f : M → N) (s : Set M) : Prop :=
  ∀ x : s, IsLocalDiffeomorphAt I J n f x

/-- `f : M → N` is a **`C^n` local diffeomorphism** iff it is a local diffeomorphism
at each `x ∈ M`. -/
def IsLocalDiffeomorph (f : M → N) : Prop :=
  ∀ x : M, IsLocalDiffeomorphAt I J n f x

variable {I J n} in
lemma isLocalDiffeomorphOn_iff {f : M → N} (s : Set M) :
    IsLocalDiffeomorphOn I J n f s ↔ ∀ x : s, IsLocalDiffeomorphAt I J n f x := by rfl

variable {I J n} in
lemma isLocalDiffeomorph_iff {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ ∀ x : M, IsLocalDiffeomorphAt I J n f x := by rfl

variable {I J n} in
theorem isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ {f : M → N} :
    IsLocalDiffeomorph I J n f ↔ IsLocalDiffeomorphOn I J n f Set.univ :=
  ⟨fun hf x ↦ hf x, fun hf x ↦ hf ⟨x, trivial⟩⟩

variable {I J n} in
lemma IsLocalDiffeomorph.isLocalDiffeomorphOn
    {f : M → N} (hf : IsLocalDiffeomorph I J n f) (s : Set M) : IsLocalDiffeomorphOn I J n f s :=
  fun x ↦ hf x

/-! ### Basic properties of local diffeomorphisms -/
section Basic
variable {f : M → N} {s : Set M} {x : M}
variable {I J n}

/-- A `C^n` local diffeomorphism at `x` is `C^n` differentiable at `x`. -/
lemma IsLocalDiffeomorphAt.contMDiffAt (hf : IsLocalDiffeomorphAt I J n f x) :
    CMDiffAt n f x := by
  choose Φ hx heq using hf
  -- In fact, even `CMDiff[Φ.source] n f`.
  exact ((Φ.contMDiffOn_toFun).congr heq).contMDiffAt (Φ.open_source.mem_nhds hx)

/-- A local diffeomorphism at `x` is differentiable at `x`. -/
lemma IsLocalDiffeomorphAt.mdifferentiableAt (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    MDiffAt f x :=
  hf.contMDiffAt.mdifferentiableAt hn

/-- A `C^n` local diffeomorphism on `s` is `C^n` on `s`. -/
lemma IsLocalDiffeomorphOn.contMDiffOn (hf : IsLocalDiffeomorphOn I J n f s) :
    CMDiff[s] n f :=
  fun x hx ↦ (hf ⟨x, hx⟩).contMDiffAt.contMDiffWithinAt

/-- A local diffeomorphism on `s` is differentiable on `s`. -/
lemma IsLocalDiffeomorphOn.mdifferentiableOn (hf : IsLocalDiffeomorphOn I J n f s) (hn : n ≠ 0) :
    MDiff[s] f :=
  hf.contMDiffOn.mdifferentiableOn hn

/-- A `C^n` local diffeomorphism is `C^n`. -/
lemma IsLocalDiffeomorph.contMDiff (hf : IsLocalDiffeomorph I J n f) : CMDiff n f :=
  fun x ↦ (hf x).contMDiffAt

/-- A `C^n` local diffeomorphism is differentiable. -/
lemma IsLocalDiffeomorph.mdifferentiable (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) :
    MDiff f :=
  fun x ↦ (hf x).mdifferentiableAt hn

/-- A `C^n` diffeomorphism is a local diffeomorphism. -/
lemma Diffeomorph.isLocalDiffeomorph (Φ : M ≃ₘ^n⟮I, J⟯ N) : IsLocalDiffeomorph I J n Φ :=
  fun _x ↦ ⟨Φ.toPartialDiffeomorph, by trivial, eqOn_refl Φ _⟩

-- FUTURE: if useful, also add "a `PartialDiffeomorph` is a local diffeomorphism on its source"

/-- A local diffeomorphism on `s` is a local homeomorphism on `s`. -/
theorem IsLocalDiffeomorphOn.isLocalHomeomorphOn {s : Set M} (hf : IsLocalDiffeomorphOn I J n f s) :
    IsLocalHomeomorphOn f s := by
  apply IsLocalHomeomorphOn.mk
  intro x hx
  choose U hyp using hf ⟨x, hx⟩
  exact ⟨U.toOpenPartialHomeomorph, hyp⟩

/-- A local diffeomorphism is a local homeomorphism. -/
theorem IsLocalDiffeomorph.isLocalHomeomorph (hf : IsLocalDiffeomorph I J n f) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ] at hf
  exact hf.isLocalHomeomorphOn

/-- A local diffeomorphism is an open map. -/
lemma IsLocalDiffeomorph.isOpenMap (hf : IsLocalDiffeomorph I J n f) : IsOpenMap f :=
  (hf.isLocalHomeomorph).isOpenMap

/-- A local diffeomorphism has open range. -/
lemma IsLocalDiffeomorph.isOpen_range (hf : IsLocalDiffeomorph I J n f) : IsOpen (range f) :=
  (hf.isOpenMap).isOpen_range

/-- The image of a local diffeomorphism is open. -/
def IsLocalDiffeomorph.image (hf : IsLocalDiffeomorph I J n f) : Opens N :=
  ⟨range f, hf.isOpen_range⟩

lemma IsLocalDiffeomorph.image_coe (hf : IsLocalDiffeomorph I J n f) : hf.image.1 = range f :=
  rfl

-- TODO: this result holds more generally for (local) structomorphisms
-- This argument implies a `LocalDiffeomorphOn f s` for `s` open is a `PartialDiffeomorph`

/-- A bijective local diffeomorphism is a diffeomorphism. -/
noncomputable def IsLocalDiffeomorph.diffeomorphOfBijective
    (hf : IsLocalDiffeomorph I J n f) (hf' : Function.Bijective f) : Diffeomorph I J M N n := by
  -- Choose a right inverse `g` of `f`.
  choose g hgInverse using (Function.bijective_iff_has_inverse).mp hf'
  -- Choose diffeomorphisms φ_x which coincide with `f` near `x`.
  choose Φ hyp using (fun x ↦ hf x)
  -- Two such diffeomorphisms (and their inverses!) coincide on their sources:
  -- they're both inverses to g. In fact, the latter suffices for our proof.
  -- have (x y) : EqOn (Φ x).symm (Φ y).symm ((Φ x).target ∩ (Φ y).target) := sorry
  have aux (x) : EqOn g (Φ x).symm (Φ x).target :=
    eqOn_of_leftInvOn_of_rightInvOn (fun x' _ ↦ hgInverse.1 x')
      (LeftInvOn.congr_left ((Φ x).toOpenPartialHomeomorph).rightInvOn
        ((Φ x).toOpenPartialHomeomorph).symm_mapsTo (hyp x).2.symm)
      (fun _y hy ↦ (Φ x).map_target hy)
  exact {
    toFun := f
    invFun := g
    left_inv := hgInverse.1
    right_inv := hgInverse.2
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := by
      intro y
      let x := g y
      obtain ⟨hx, hfx⟩ := hyp x
      apply ((Φ x).symm.contMDiffOn.congr (aux x)).contMDiffAt (((Φ x).open_target).mem_nhds ?_)
      have : y = (Φ x) x := ((hgInverse.2 y).congr (hfx hx)).mp rfl
      exact this ▸ (Φ x).map_source hx }

@[deprecated (since := "2025-12-19")]
alias IsLocalDiffeomorph.diffeomorph_of_bijective := IsLocalDiffeomorph.diffeomorphOfBijective

end Basic

section Differential

variable {f : M → N} {s : Set M} {x : M}

variable {I I' J n}

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is a `C^n` local diffeomorphism at `x`, for `n ≠ 0`, the differential `df_x`
is a linear equivalence. -/
noncomputable def IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (f x) where
  toFun := mfderiv% f x
  invFun := mfderiv% hf.localInverse (f x)
  left_inv := by
    apply ContinuousLinearMap.leftInverse_of_comp
    rw [← mfderiv_id, ← hf.localInverse_eventuallyEq_left.mfderiv_eq]
    exact (mfderiv_comp _ (hf.localInverse_mdifferentiableAt hn) (hf.mdifferentiableAt hn)).symm
  right_inv := by
    apply ContinuousLinearMap.rightInverse_of_comp
    rw [← mfderiv_id, ← hf.localInverse_eventuallyEq_right.mfderiv_eq]
    -- We need to rewrite the base point hf.localInverse (f x) = x twice,
    -- in the differentiability hypothesis and for applying the chain rule.
    have hf' : MDifferentiableAt I J f (hf.localInverse (f x)) := by
      rw [hf.localInverse_left_inv hf.localInverse_mem_target]
      exact hf.mdifferentiableAt hn
    rw [mfderiv_comp _ hf' (hf.localInverse_mdifferentiableAt hn),
      hf.localInverse_left_inv hf.localInverse_mem_target]
  continuous_toFun := (mfderiv% f x).cont
  continuous_invFun := (mfderiv% hf.localInverse (f x)).cont
  map_add' := fun x_1 y ↦ map_add _ x_1 y
  map_smul' := by intros; simp

@[simp, mfld_simps]
lemma IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorphAt I J n f x) (hn : n ≠ 0) :
    hf.mfderivToContinuousLinearEquiv hn = mfderiv% f x := rfl

/-- Each differential of a `C^n` diffeomorphism of Banach manifolds (`n ≠ 0`)
is a linear equivalence. -/
noncomputable def Diffeomorph.mfderivToContinuousLinearEquiv
    (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (Φ x) :=
  (Φ.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv hn

lemma Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) :
    Φ.mfderivToContinuousLinearEquiv hn x = mfderiv% Φ x := by rfl

/-- If `f` is a `C^n` local diffeomorphism of Banach manifolds (`n ≠ 0`),
each differential is a linear equivalence. -/
noncomputable def IsLocalDiffeomorph.mfderivToContinuousLinearEquiv
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) (x : M) :
    TangentSpace I x ≃L[𝕜] TangentSpace J (f x) :=
  (hf x).mfderivToContinuousLinearEquiv hn

lemma IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (hf : IsLocalDiffeomorph I J n f) (hn : n ≠ 0) (x : M) :
    hf.mfderivToContinuousLinearEquiv hn x = mfderiv% f x :=
  (hf x).mfderivToContinuousLinearEquiv_coe hn

end Differential
