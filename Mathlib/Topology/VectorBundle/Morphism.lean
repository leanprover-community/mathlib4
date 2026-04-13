/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Vector Bundle Homomorphisms and Equivalences

This file defines bundled continuous, fiberwise-linear maps between vector bundles over possibly
different base spaces.

A `VectorBundleHom` bundles a continuous map of total spaces with a family of linear maps between
fibers, covering a base map `baseMap : B₁ → B₂`. A `VectorBundleEquiv` strengthens this to a
homeomorphism of total spaces with fiberwise linear equivalences.

## Design notes

The base map `baseMap : B₁ → B₂` is stored as a field, even though it is determined by the total
space map (recovered by `baseMap_eq`). This is because `fiberLinearMap` has type
`∀ x, E₁ x →ₗ[𝕜] E₂ (baseMap x)`, which would become `∀ x, E₁ x →ₗ[𝕜] E₂ ((toFun ⟨x, 0⟩).proj)`
without the field — an unwieldy dependent type. The constructor `mk'` derives the base map
automatically for users who prefer not to supply it.

## Main Definitions

* `VectorBundleHom 𝕜 F₁ E₁ F₂ E₂` : a continuous, fiberwise-linear map between vector bundles,
  covering a base map `baseMap : B₁ → B₂`.
* `VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂` : a homeomorphism of total spaces with fiberwise linear
  equivalences, covering a bijection of base spaces.
* `VectorBundleEquiv.ofMutualInverseHoms` : assemble an equivalence from two mutually-inverse
  homomorphisms.
* `VectorBundleEquiv.ofFiberwiseLinearEquiv` : construct an equivalence from a family of fiberwise
  linear equivalences, given continuity of the induced total-space maps.
* `VectorBundleHom.toVectorBundleEquiv` : promote a bijective homomorphism to an equivalence,
  given that the base map is a homeomorphism.

## References

* [J. M. Lee, *Introduction to Smooth Manifolds*][lee2012] p. 261

## Tags
vector bundle, homomorphism, equivalence, isomorphism
-/

@[expose] public section

open Bundle

/-! ## Vector bundle homomorphisms -/

/-- A vector bundle homomorphism from `E₁` over `B₁` to `E₂` over `B₂`. -/
structure VectorBundleHom
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B₁ B₂ : Type*}
    [TopologicalSpace B₁] [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where
  /-- The base map covered by this bundle homomorphism. -/
  baseMap : B₁ → B₂
  /-- The underlying continuous map between total spaces. -/
  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂
  /-- The total space map is continuous. -/
  continuous_toFun : Continuous toFun
  /-- A family of linear maps between the fibers. -/
  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)
  /-- The map acts fiberwise via `fiberLinearMap`. -/
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace VectorBundleHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B₁ B₂ B₃ : Type*}
  [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommMonoid (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]

/-- Construct a `VectorBundleHom` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk' (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂) (hΦ : Continuous Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x), Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  continuous_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

/-- The base map equals the projection of the total space map on the zero section. -/
theorem baseMap_eq (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    Φ.baseMap x = (Φ.toFun ⟨x, 0⟩).proj := by
  simp [Φ.fiber_compat, map_zero]

@[ext]
theorem ext (Φ Ψ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (h : Φ.toFun = Ψ.toFun) : Φ = Ψ := by
  have hb : Φ.baseMap = Ψ.baseMap := by ext x; rw [Φ.baseMap_eq, Ψ.baseMap_eq, h]
  obtain ⟨_, _, _, _, hΦ⟩ := Φ; obtain ⟨_, _, _, _, hΨ⟩ := Ψ
  dsimp at h hb; subst h; subst hb; congr 1
  exact funext fun x => LinearMap.ext fun v => TotalSpace.mk_inj.mp ((hΦ x v).symm.trans (hΨ x v))

instance : FunLike (VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  coe := toFun
  coe_injective' f g h := ext f g h

instance : ContinuousMapClass (VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  map_continuous Φ := Φ.continuous_toFun

/-- The underlying `ContinuousMap` of a `VectorBundleHom`. -/
@[simps]
def toContinuousMap (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) : C(TotalSpace F₁ E₁, TotalSpace F₂ E₂) :=
  ⟨Φ, Φ.continuous_toFun⟩

/-- The base map of a vector bundle homomorphism is continuous, since it factors as
`π₂ ∘ Φ ∘ zeroSection` and the zero section is continuous. -/
theorem continuous_baseMap [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) : Continuous Φ.baseMap :=
  ((FiberBundle.continuous_proj F₂ E₂).comp
    (Φ.continuous_toFun.comp (continuous_zeroSection 𝕜))).congr (fun x => (Φ.baseMap_eq x).symm)

@[simp]
theorem proj_eq (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (Φ.toFun p).proj = Φ.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [Φ.fiber_compat]

@[simp]
theorem toFun_apply (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    Φ.toFun ⟨x, v⟩ = ⟨Φ.baseMap x, Φ.fiberLinearMap x v⟩ := Φ.fiber_compat x v

/-- The identity vector bundle homomorphism. -/
@[simps baseMap fiberLinearMap]
def id : VectorBundleHom 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  continuous_toFun := continuous_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

/-- Composition of vector bundle homomorphisms. -/
@[simps baseMap fiberLinearMap]
def comp (Ψ : VectorBundleHom 𝕜 F₂ E₂ F₃ E₃) (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := Ψ.baseMap ∘ Φ.baseMap
  toFun := Ψ.toFun ∘ Φ.toFun
  continuous_toFun := Ψ.continuous_toFun.comp Φ.continuous_toFun
  fiberLinearMap x := (Ψ.fiberLinearMap (Φ.baseMap x)).comp (Φ.fiberLinearMap x)
  fiber_compat x v := (congrArg Ψ.toFun (Φ.fiber_compat x v)).trans (Ψ.fiber_compat _ _)

@[simp]
theorem comp_id (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) : Φ.comp id = Φ := ext _ _ rfl

@[simp]
theorem id_comp (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) : id.comp Φ = Φ := ext _ _ rfl

@[simp]
theorem coe_id : ⇑(id : VectorBundleHom 𝕜 F₁ E₁ F₁ E₁) = _root_.id := rfl

@[simp]
theorem coe_comp (Ψ : VectorBundleHom 𝕜 F₂ E₂ F₃ E₃) (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    ⇑(Ψ.comp Φ) = ⇑Ψ ∘ ⇑Φ := rfl

/-- If `Ψ ∘ Φ = id` on total spaces, then `Ψ.baseMap ∘ Φ.baseMap = id` on base spaces. -/
theorem baseMap_leftInverse (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (Ψ : VectorBundleHom 𝕜 F₂ E₂ F₁ E₁) (h : ∀ p, Ψ.toFun (Φ.toFun p) = p) :
    Function.LeftInverse Ψ.baseMap Φ.baseMap := fun x => by
  simpa [Ψ.proj_eq, Φ.proj_eq] using congrArg TotalSpace.proj (h ⟨x, 0⟩)

end VectorBundleHom

/-! ## Vector bundle equivalences -/

/-- A vector bundle equivalence between bundles `E₁` over `B₁` and `E₂` over `B₂`. -/
structure VectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜] {B₁ B₂ : Type*}
    [TopologicalSpace B₁] [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where
  /-- The base map covered by this bundle equivalence. -/
  baseMap : B₁ → B₂
  /-- The underlying homeomorphism between total spaces. -/
  toHomeomorph : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂
  /-- A family of linear equivalences between the fibers. -/
  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)
  /-- The homeomorphism acts fiberwise via `fiberLinearEquiv`. -/
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toHomeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

/-! ## Algebraic lemmas for fiberwise maps -/

section FiberwiseMapLemmas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {B₁ B₂ : Type*}
  {F₁ : Type*} {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  {F₂ : Type*} {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂} {baseMap : B₁ → B₂}
  {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}

/-- A fiberwise-compatible injection of total spaces induces an injective base map. -/
theorem baseMap_injective_of_injective (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hinj : Function.Injective Φ) : Function.Injective baseMap := fun x₁ x₂ h => by
  have h₁ := hcompat x₁ 0; have h₂ := hcompat x₂ 0
  simp only [map_zero] at h₁ h₂
  exact congrArg TotalSpace.proj (hinj (h₁.trans (h ▸ rfl) |>.trans h₂.symm))

/-- A fiberwise-compatible surjection of total spaces induces a surjective base map. -/
theorem baseMap_surjective_of_surjective (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hsurj : Function.Surjective Φ) : Function.Surjective baseMap := fun y =>
  have ⟨⟨x, _⟩, hx⟩ := hsurj ⟨y, 0⟩
  ⟨x, congrArg TotalSpace.proj ((hcompat x _).symm.trans hx)⟩

/-- A fiberwise-compatible bijection of total spaces induces a bijective base map. -/
theorem baseMap_bijective_of_bijective (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) : Function.Bijective baseMap :=
  ⟨baseMap_injective_of_injective hcompat hbij.1,
   baseMap_surjective_of_surjective hcompat hbij.2⟩

/-- If a fiberwise-linear bijection of total spaces covers a base map and acts as
`⟨x, v⟩ ↦ ⟨baseMap x, φ x v⟩`, then each fiber map `φ x` is bijective. -/
theorem fiberBijective_of_bijective (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (x : B₁) : Function.Bijective (φ x) :=
  ⟨fun v w hvw => TotalSpace.mk_inj.mp (hbij.1 (by rw [hcompat, hcompat, hvw])),
   fun w => by
    obtain ⟨⟨y, v⟩, hv⟩ := hbij.2 ⟨baseMap x, w⟩; rw [hcompat] at hv
    have := baseMap_injective_of_injective hcompat hbij.1 (congrArg TotalSpace.proj hv); subst this
    exact ⟨v, TotalSpace.mk_inj.mp hv⟩⟩

/-- Applying `baseMap` to the projection of `Φ⁻¹ p` recovers `p.proj`. -/
lemma baseMap_proj_symm_ofBijective (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (p : TotalSpace F₂ E₂) :
    baseMap ((Equiv.ofBijective Φ hbij).symm p).proj = p.proj := by
  have h : Φ _ = p := (Equiv.ofBijective Φ hbij).apply_symm_apply p
  rw [hcompat] at h; exact congrArg TotalSpace.proj h

end FiberwiseMapLemmas

namespace VectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommMonoid (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]

/-- Construct a `VectorBundleEquiv` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk' (Φ : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂) (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x), Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toHomeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

/-- The base map equals the projection of the total space map on the zero section. -/
theorem baseMap_eq (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    Φ.baseMap x = (Φ.toHomeomorph ⟨x, 0⟩).proj := by
  simp [Φ.fiber_compat, map_zero]

@[simp]
theorem toHomeomorph_zeroSection (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    Φ.toHomeomorph (zeroSection F₁ E₁ x) = zeroSection F₂ E₂ (Φ.baseMap x) := by
  simp [zeroSection, Φ.fiber_compat]

@[simp]
theorem proj_eq (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (Φ.toHomeomorph p).proj = Φ.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [Φ.fiber_compat]

@[simp]
theorem toHomeomorph_apply (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    Φ.toHomeomorph ⟨x, v⟩ = ⟨Φ.baseMap x, Φ.fiberLinearEquiv x v⟩ := Φ.fiber_compat x v

@[ext]
theorem ext (Φ Ψ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (h : Φ.toHomeomorph = Ψ.toHomeomorph) :
    Φ = Ψ := by
  have hb : Φ.baseMap = Ψ.baseMap := by ext x; rw [Φ.baseMap_eq, Ψ.baseMap_eq, h]
  obtain ⟨_, _, _, hΦ⟩ := Φ; obtain ⟨_, _, _, hΨ⟩ := Ψ
  dsimp at h hb; subst h; subst hb; congr 1
  exact funext fun x => LinearEquiv.ext fun v =>
    TotalSpace.mk_inj.mp ((hΦ x v).symm.trans (hΨ x v))

instance : FunLike (VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  coe Φ := Φ.toHomeomorph
  coe_injective' Φ Ψ h := ext Φ Ψ (Homeomorph.ext (congrFun h))

instance : ContinuousMapClass (VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  map_continuous Φ := Φ.toHomeomorph.continuous

/-- The underlying `ContinuousMap` of a `VectorBundleEquiv`. -/
@[simps]
def toContinuousMap (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : C(TotalSpace F₁ E₁, TotalSpace F₂ E₂) :=
  ⟨Φ, Φ.toHomeomorph.continuous⟩

/-- The base map of a vector bundle equivalence is bijective. -/
theorem baseMap_bijective (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : Function.Bijective Φ.baseMap :=
  ⟨fun x₁ x₂ h => congrArg TotalSpace.proj (Φ.toHomeomorph.injective
      ((Φ.toHomeomorph_zeroSection x₁).trans (h ▸ rfl)
        |>.trans (Φ.toHomeomorph_zeroSection x₂).symm)),
   fun y => have ⟨⟨x, v⟩, hxv⟩ := Φ.toHomeomorph.surjective ⟨y, 0⟩
    ⟨x, congrArg TotalSpace.proj ((Φ.fiber_compat x v).symm.trans hxv)⟩⟩

@[simp]
theorem toHomeomorph_fiberLinearEquiv_symm (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₂ (Φ.baseMap x)) :
    Φ.toHomeomorph ⟨x, (Φ.fiberLinearEquiv x).symm v⟩ = ⟨Φ.baseMap x, v⟩ := by
  simp [Φ.fiber_compat, LinearEquiv.apply_symm_apply]

/-- A `VectorBundleEquiv` gives a `VectorBundleHom` in the forward direction. -/
@[simps baseMap fiberLinearMap]
def toVectorBundleHom (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := Φ.baseMap
  toFun := Φ.toHomeomorph
  continuous_toFun := Φ.toHomeomorph.continuous
  fiberLinearMap x := (Φ.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := Φ.fiber_compat x v

instance : Coe (VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :=
  ⟨toVectorBundleHom⟩

/-- The identity vector bundle equivalence. -/
@[simps baseMap toHomeomorph fiberLinearEquiv]
def refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toHomeomorph := Homeomorph.refl _
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

/-- The inverse of a vector bundle equivalence. -/
@[simps baseMap toHomeomorph]
def symm (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : VectorBundleEquiv 𝕜 F₂ E₂ F₁ E₁ where
  baseMap y := (Φ.toHomeomorph.symm ⟨y, 0⟩).proj
  toHomeomorph := Φ.toHomeomorph.symm
  fiberLinearEquiv y := ((Φ.proj_eq _).symm.trans
      (congrArg TotalSpace.proj (Φ.toHomeomorph.apply_symm_apply ⟨y, 0⟩))
      ▸ Φ.fiberLinearEquiv (Φ.toHomeomorph.symm ⟨y, 0⟩).proj).symm
  fiber_compat y v := by
    have key : ∀ (x : B₁) (hx : Φ.baseMap x = y), (⟨y, v⟩ : TotalSpace F₂ E₂) =
        Φ.toHomeomorph ⟨x, (hx ▸ Φ.fiberLinearEquiv x).symm v⟩ :=
      fun x hx => by subst hx; exact (Φ.toHomeomorph_fiberLinearEquiv_symm x v).symm
    exact Φ.toHomeomorph.symm_apply_eq.mpr (key _ _)

/-- Composition of vector bundle equivalences. -/
@[simps baseMap toHomeomorph]
def trans (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (Ψ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := Ψ.baseMap ∘ Φ.baseMap
  toHomeomorph := Φ.toHomeomorph.trans Ψ.toHomeomorph
  fiberLinearEquiv x := (Φ.fiberLinearEquiv x).trans (Ψ.fiberLinearEquiv (Φ.baseMap x))
  fiber_compat x v := (congrArg Ψ.toHomeomorph (Φ.fiber_compat x v)).trans (Ψ.fiber_compat _ _)

@[simp]
theorem refl_apply (p : TotalSpace F₁ E₁) :
    (refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁) p = p := rfl

@[simp]
theorem symm_apply_apply (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    Φ.symm (Φ p) = p := Φ.toHomeomorph.symm_apply_apply p

@[simp]
theorem apply_symm_apply (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₂ E₂) :
    Φ (Φ.symm p) = p := Φ.toHomeomorph.apply_symm_apply p

@[simp]
theorem symm_symm (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : Φ.symm.symm = Φ :=
  ext _ _ (Homeomorph.ext (Φ.toHomeomorph.symm_symm ▸ fun _ => rfl))

@[simp]
theorem symm_trans_self (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : Φ.symm.trans Φ = refl :=
  ext _ _ (Homeomorph.ext fun p => Φ.toHomeomorph.apply_symm_apply p)

@[simp]
theorem self_trans_symm (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : Φ.trans Φ.symm = refl :=
  ext _ _ (Homeomorph.ext fun p => Φ.toHomeomorph.symm_apply_apply p)

@[simp]
theorem trans_apply (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (Ψ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃)
    (p : TotalSpace F₁ E₁) : (Φ.trans Ψ) p = Ψ (Φ p) := rfl

@[simp]
theorem symm_apply (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₂ E₂) :
    Φ.symm p = Φ.toHomeomorph.symm p := rfl

theorem toVectorBundleHom_comp (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (Ψ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃) :
    (Φ.trans Ψ).toVectorBundleHom = Ψ.toVectorBundleHom.comp Φ.toVectorBundleHom :=
  VectorBundleHom.ext _ _ rfl

@[simp]
theorem trans_refl (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : Φ.trans refl = Φ :=
  ext _ _ (Homeomorph.ext fun _ => rfl)

@[simp]
theorem refl_trans (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : refl.trans Φ = Φ :=
  ext _ _ (Homeomorph.ext fun _ => rfl)

theorem injective (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : Function.Injective Φ :=
  Φ.toHomeomorph.injective

theorem surjective (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : Function.Surjective Φ :=
  Φ.toHomeomorph.surjective

theorem bijective (Φ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) : Function.Bijective Φ :=
  Φ.toHomeomorph.bijective

@[simp]
theorem toVectorBundleHom_id :
    toVectorBundleHom (refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁) = VectorBundleHom.id :=
  VectorBundleHom.ext _ _ rfl

/-- Assemble a `VectorBundleEquiv` from two mutually-inverse `VectorBundleHom`s over possibly
different base spaces. -/
noncomputable def ofMutualInverseHoms
    (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (Ψ : VectorBundleHom 𝕜 F₂ E₂ F₁ E₁)
    (hΨΦ : ∀ p, Ψ.toFun (Φ.toFun p) = p) (hΦΨ : ∀ p, Φ.toFun (Ψ.toFun p) = p) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := Φ.baseMap
  toHomeomorph :=
    { toEquiv := ⟨Φ.toFun, Ψ.toFun, hΨΦ, hΦΨ⟩
      continuous_toFun := Φ.continuous_toFun
      continuous_invFun := Ψ.continuous_toFun }
  fiberLinearEquiv x :=
    LinearEquiv.ofBijective (Φ.fiberLinearMap x)
      (fiberBijective_of_bijective Φ.fiber_compat
        ⟨Function.LeftInverse.injective hΨΦ, Function.RightInverse.surjective hΦΨ⟩ x)
  fiber_compat := Φ.fiber_compat

end VectorBundleEquiv

/-! ## Building equivalences from fiberwise data -/

section FiberwiseEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

/-- Given a family of linear maps `φ x : E₁ x →ₗ[𝕜] E₂ (f x)` covering a base map `f : B → B₂`, and
a continuity proof for the induced total-space map, construct a `VectorBundleHom`. -/
def VectorBundleHom.ofFiberwiseLinearMap {B₂ : Type*} [TopologicalSpace B₂] {E₂ : B₂ → Type*}
    [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
    (f : B → B₂) (φ : ∀ x : B, E₁ x →ₗ[𝕜] E₂ (f x))
    (h_cont : Continuous (fun p : TotalSpace F₁ E₁ => (⟨f p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂))) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := f
  toFun p := ⟨f p.1, φ p.1 p.2⟩
  continuous_toFun := h_cont
  fiberLinearMap := φ
  fiber_compat _ _ := rfl

/-- Given a family of linear equivalences `φ x : E₁ x ≃ₗ[𝕜] E₂ x` whose induced total-space maps are
continuous in both directions, construct a `VectorBundleEquiv` covering the identity. -/
noncomputable def VectorBundleEquiv.ofFiberwiseLinearEquiv (φ : ∀ x : B, E₁ x ≃ₗ[𝕜] E₂ x)
    (h_cont : Continuous (fun p : TotalSpace F₁ E₁ =>  (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂)))
    (h_cont_inv : Continuous (fun p : TotalSpace F₂ E₂ =>
        (⟨p.1, (φ p.1).symm p.2⟩ : TotalSpace F₁ E₁))) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := _root_.id
  toHomeomorph :=
    { toEquiv :=
        { toFun := fun p => ⟨p.1, φ p.1 p.2⟩
          invFun := fun p => ⟨p.1, (φ p.1).symm p.2⟩
          left_inv := fun ⟨_, _⟩ => by simp
          right_inv := fun ⟨_, _⟩ => by simp }
      continuous_toFun := h_cont
      continuous_invFun := h_cont_inv }
  fiberLinearEquiv := φ
  fiber_compat _ _ := rfl

end FiberwiseEquiv

/-! ## Trivialization Coordinates -/

section TrivializationCoord

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

omit [CompleteSpace 𝕜] in
/-- Given a family of fiberwise linear maps `φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)`
covering a base map `baseMap : B₁ → B₂`, and a base point `x : B₁`, the local representative
through the trivializations at `x` in `E₁` and at `baseMap x` in `E₂`: a continuous linear map
`F₁ →L[𝕜] F₂` defined on the overlap of base sets (and `0` otherwise). -/
noncomputable def trivializationCoord (baseMap : B₁ → B₂)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x))
    (x : B₁) : B₁ → (F₁ →L[𝕜] F₂) :=
  open Classical in fun q =>
  if hq : q ∈ (trivializationAt F₁ E₁ x).baseSet ∧
      baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet
  then
    let e₁ := (trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 q hq.1
    let e₂ := (trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt 𝕜 (baseMap q) hq.2
    LinearMap.toContinuousLinearMap
      (e₂.toLinearMap.comp ((φ q).comp e₁.symm.toLinearMap))
  else 0

/-- The trivialization coordinate at `q` applied to `v` equals the fiber coordinate of `Φ` on
`e₁⁻¹ (q, v)` read through `e₂`. -/
lemma trivializationCoord_apply {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂} {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)} (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (x q : B₁)
    (hq₁ : q ∈ (trivializationAt F₁ E₁ x).baseSet)
    (hq₂ : baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet)
    (v : F₁) :
    trivializationCoord baseMap φ x q v =
      ((trivializationAt F₂ E₂ (baseMap x))
        (Φ ((trivializationAt F₁ E₁ x).toOpenPartialHomeomorph.symm (q, v)))).2 := by
  unfold trivializationCoord
  rw [dif_pos (show q ∈ _ ∧ baseMap q ∈ _ from ⟨hq₁, hq₂⟩)]
  conv_rhs => rw [
    (trivializationAt F₁ E₁ x).symm_apply_eq_mk_continuousLinearEquivAt_symm (R := 𝕜) q hq₁ v,
    hcompat,
    congrArg Prod.snd ((trivializationAt F₂ E₂ (baseMap x)).apply_eq_prod_continuousLinearEquivAt
      𝕜 (baseMap q) hq₂ _)]
  rfl

/-- `trivializationCoord baseMap φ x q` is invertible on the overlap of the base sets
whenever each fiber map `φ q` is bijective. -/
lemma trivializationCoord_isInvertible {baseMap : B₁ → B₂} {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hφ_bij : ∀ x, Function.Bijective (φ x)) (x q : B₁)
    (hq₁ : q ∈ (trivializationAt F₁ E₁ x).baseSet)
    (hq₂ : baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet) :
    (trivializationCoord baseMap φ x q : F₁ →L[𝕜] F₂).IsInvertible := by
  unfold trivializationCoord
  rw [dif_pos (show q ∈ _ ∧ baseMap q ∈ _ from ⟨hq₁, hq₂⟩)]
  exact ⟨(((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 q hq₁).symm.toLinearEquiv.trans
    (LinearEquiv.ofBijective (φ q) (hφ_bij q)) |>.trans
    ((trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt
      𝕜 (baseMap q) hq₂).toLinearEquiv).toContinuousLinearEquiv, by ext; rfl⟩

/-- On a neighborhood of `e₂ ⟨baseMap x, w⟩`, inverting `trivializationCoord baseMap φ x` pointwise
computes the second coordinate of `e₁ ∘ Φ⁻¹ ∘ e₂⁻¹`, provided the base map is a homeomorphism. -/
lemma trivializationCoord_inverse_eventuallyEq {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (baseMap : B₁ ≃ₜ B₂) {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩) (hbij : Function.Bijective Φ)
    (hφ_bij : ∀ x, Function.Bijective (φ x)) (x : B₁) (w : E₂ (baseMap x)) :
    (fun p : B₂ × F₂ => ContinuousLinearMap.inverse
        (trivializationCoord baseMap φ x (baseMap.symm p.1)) p.2)
      =ᶠ[nhds ((trivializationAt F₂ E₂ (baseMap x)) ⟨baseMap x, w⟩)]
    (fun p : B₂ × F₂ => ((trivializationAt F₁ E₁ x) ((Equiv.ofBijective Φ hbij).symm
        ((trivializationAt F₂ E₂ (baseMap x)).toOpenPartialHomeomorph.symm p))).2) := by
  set e₁ := trivializationAt F₁ E₁ x
  set e₂ := trivializationAt F₂ E₂ (baseMap x)
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hx₂ := mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
  have he₂_source : (⟨baseMap x, w⟩ : TotalSpace F₂ E₂) ∈ e₂.source := e₂.mem_source.mpr hx₂
  filter_upwards [IsOpen.mem_nhds
      (((baseMap.isOpenMap _ e₁.open_baseSet).inter e₂.open_baseSet).prod isOpen_univ)
      ⟨⟨⟨x, mem_baseSet_trivializationAt F₁ E₁ x, (e₂.coe_fst he₂_source).symm⟩,
        e₂.coe_fst he₂_source ▸ hx₂⟩, Set.mem_univ _⟩]
    with ⟨q', v⟩ ⟨⟨⟨q, hq₁, hq_eq⟩, hq₂'⟩, _⟩
  dsimp at hq_eq hq₂'
  have hq : baseMap.symm q' = q := hq_eq ▸ baseMap.symm_apply_apply q
  have hq₂ : baseMap (baseMap.symm q') ∈ e₂.baseSet := (baseMap.apply_symm_apply q').symm ▸ hq₂'
  set p := Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm (q', v))
  have hAG : trivializationCoord baseMap φ x (baseMap.symm q') ((e₁ p).2) = v := by
    have hp_proj : p.proj = baseMap.symm q' :=
      baseMap_injective_of_injective hcompat hbij.1
        ((baseMap_proj_symm_ofBijective hcompat hbij _).trans
          (e₂.proj_symm_apply (show (q', v) ∈ e₂.target from e₂.mem_target.mpr hq₂'))
          |>.trans (baseMap.apply_symm_apply q').symm)
    rw [trivializationCoord_apply hcompat x (baseMap.symm q') (hq ▸ hq₁) hq₂,
        ← hp_proj, e₁.symm_apply_mk_proj (e₁.mem_source.mpr (hp_proj ▸ hq ▸ hq₁)),
        Equiv.ofBijective_apply_symm_apply Φ hbij _,
        congrArg Prod.snd (e₂.apply_symm_apply' hq₂')]
  exact (trivializationCoord_isInvertible (baseMap := baseMap) hφ_bij x
    (baseMap.symm q') (hq ▸ hq₁) hq₂).inverse_apply_eq.mpr hAG.symm

end TrivializationCoord

/-! ## Bijective bundle homomorphisms are equivalences -/

section ToVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- The trivialization coordinate `trivializationCoord baseMap φ x` is continuous at `x` when `Φ`
is continuous and acts fiberwise via `φ`. -/
lemma continuousAt_trivializationCoord {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_cont : Continuous Φ) {baseMap : B₁ → B₂} {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩) (x : B₁) :
    ContinuousAt (trivializationCoord (F₁ := F₁) (F₂ := F₂) baseMap φ x) x := by
  set e₁ := trivializationAt F₁ E₁ x
  set e₂ := trivializationAt F₂ E₂ (baseMap x)
  have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
  have hx₂ := mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
  apply continuousAt_clm_apply.mpr; intro v
  have he₁_tgt : (x, v) ∈ e₁.target := e₁.mem_target.mpr hx₁
  exact (((e₂.continuousOn.continuousAt (e₂.open_source.mem_nhds (by
      simp only [Function.comp, e₂.mem_source, hcompat,
        e₁.proj_symm_apply he₁_tgt]; exact hx₂))).comp
    (hΦ_cont.continuousAt.comp
      (Trivialization.continuousAt_symm_prodMk_left e₁ he₁_tgt))).snd).congr
    (Filter.eventually_of_mem
      (IsOpen.mem_nhds (e₁.open_baseSet.inter
        (((FiberBundle.continuous_proj F₂ E₂).comp (hΦ_cont.comp (continuous_zeroSection 𝕜))).congr
          (fun x => by simp [hcompat]) |>.isOpen_preimage _ e₂.open_baseSet)) ⟨hx₁, hx₂⟩)
      fun q ⟨hq₁, hq₂⟩ => (trivializationCoord_apply hcompat x q hq₁ hq₂ v).symm)

/-- The inverse of a fiberwise-linear, fiberwise-bijective continuous bijection between
vector bundles over different bases is continuous, provided the base map is a homeomorphism. -/
lemma continuous_symm_of_fiberBijective {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_cont : Continuous Φ) (baseMap : B₁ ≃ₜ B₂) {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩) (hbij : Function.Bijective Φ) :
    Continuous (Equiv.ofBijective Φ hbij).symm := by
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hφ_bij := fiberBijective_of_bijective hcompat hbij
  have hproj (p : TotalSpace F₂ E₂) : (Φ_equiv.symm p).proj = baseMap.symm p.proj :=
    baseMap_injective_of_injective hcompat hbij.1
      ((baseMap_proj_symm_ofBijective hcompat hbij p).trans (baseMap.apply_symm_apply p.proj).symm)
  rw [continuous_iff_continuousAt]
  rintro ⟨y, w⟩
  obtain ⟨x, rfl⟩ := baseMap.surjective y
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact ((baseMap.symm.continuous.comp (FiberBundle.continuous_proj F₂ E₂)).continuousAt).congr
      (.of_forall fun p => (hproj p).symm)
  · rw [(hproj _).trans (baseMap.symm_apply_apply x)]
    set e₂ := trivializationAt F₂ E₂ (baseMap x)
    have hx₂ := mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
    have he₂_source : (⟨baseMap x, w⟩ : TotalSpace F₂ E₂) ∈ e₂.source := e₂.mem_source.mpr hx₂
    set A : B₁ → (F₁ →L[𝕜] F₂) := trivializationCoord baseMap φ x
    haveI : CompleteSpace F₁ := FiniteDimensional.complete 𝕜 F₁
    have hNice_cont := by
      have : ContinuousAt ((ContinuousLinearMap.inverse ∘ A) ∘ (baseMap.symm ∘ Prod.fst))
          (e₂ ⟨baseMap x, w⟩) := by
        refine ContinuousAt.comp ?_ (baseMap.symm.continuous.continuousAt.comp continuousAt_fst)
        convert ((trivializationCoord_isInvertible (baseMap := baseMap) hφ_bij x x
          (mem_baseSet_trivializationAt F₁ E₁ x) hx₂).contDiffAt_map_inverse
            (n := 0)).continuousAt.comp
          (continuousAt_trivializationCoord hΦ_cont hcompat x) using 1
        simp [e₂.coe_fst he₂_source]
      exact this.clm_apply continuousAt_snd
    exact ((hNice_cont.congr
      (trivializationCoord_inverse_eventuallyEq
        baseMap hcompat hbij hφ_bij x w)).comp
      (e₂.toOpenPartialHomeomorph.continuousAt
        he₂_source)).congr
      (by filter_upwards [e₂.open_source.mem_nhds
            he₂_source] with p hp
          exact congrArg (fun q => (trivializationAt F₁ E₁ x (Φ_equiv.symm q)).2)
            (e₂.toOpenPartialHomeomorph.left_inv hp))

/-- A bijective vector bundle homomorphism whose base map is a homeomorphism is a vector
bundle equivalence. The base map being a homeomorphism cannot be derived from bijectivity of
the total-space map alone. See `toVectorBundleEquivId` for the identity-base special case. -/
noncomputable def VectorBundleHom.toVectorBundleEquiv (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (baseMap : B₁ ≃ₜ B₂) (hbase : Φ.baseMap = baseMap) (hbij : Function.Bijective Φ.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ :=
  match Φ, hbase, hbij with
  | ⟨_, Φ', hΦ_cont, φ, hcompat⟩, rfl, hbij =>
    let hφ_bij := fiberBijective_of_bijective hcompat hbij
    { baseMap := baseMap
      toHomeomorph := ⟨Equiv.ofBijective Φ' hbij, hΦ_cont,
        continuous_symm_of_fiberBijective hΦ_cont baseMap hcompat hbij⟩
      fiberLinearEquiv := fun x =>
        LinearEquiv.ofBijective (φ x) (hφ_bij x)
      fiber_compat := hcompat }

end ToVectorBundleEquiv

section ToVectorBundleEquivId

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- The inverse of a fiberwise-linear, fiberwise-bijective continuous bijection between
vector bundles over the same base (with identity base map) is continuous. This is the
special case of `continuous_symm_of_fiberBijective` with `Homeomorph.refl B`. -/
lemma continuous_symm_of_fiberBijective_id {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_cont : Continuous Φ) {φ : ∀ x, E₁ x →ₗ[𝕜] E₂ x} (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩)
    (hbij : Function.Bijective Φ) : Continuous (Equiv.ofBijective Φ hbij).symm :=
  continuous_symm_of_fiberBijective hΦ_cont (Homeomorph.refl B) hcompat hbij

/-- Special case of `VectorBundleHom.toVectorBundleEquiv` for the identity base map. -/
noncomputable def VectorBundleHom.toVectorBundleEquivId (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (hid : Φ.baseMap = _root_.id) (hbij : Function.Bijective Φ.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ :=
  Φ.toVectorBundleEquiv (Homeomorph.refl B) hid hbij

end ToVectorBundleEquivId

end
