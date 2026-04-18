/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.Localization.TensorProduct

/-! # Homogeneous localization of tensor product of graded algebra

Let `𝒜` be a graded `R`-algebra, and `S` be an `R`-algebra. Then `S ⊗[R] 𝒜` is a graded
`S`-algebra with the same grading.

Let `W` be a homogeneous submonoid of `𝒜`. Then `(S⊗[R]𝒜)[(1⊗W)⁻¹]₀ ≅ S ⊗[R] (𝒜[W⁻¹]₀)`.
-/

@[expose] public section

local notation3:max "(at " W ")" => Localization W
local notation3:max 𝒜"["W"⁻¹]₀" => HomogeneousLocalization 𝒜 W

open TensorProduct

namespace HomogeneousLocalization

variable {R A S : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
  {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  {B T : Type*} [CommRing B] [Algebra R B] {ℬ : ι → Submodule R B} [GradedAlgebra ℬ]

/-- Custom induction lemma for `HomogeneousLocalization (𝒜 · |>.baseChange S) W₂`:

every element can be written as `n / (1 ⊗ₜ d)` where `n : S ⊗ 𝒜 i` and `d : 𝒜 i ∩ W₁`. -/
theorem baseChange_induction
    (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
    (hw : W₁.map Algebra.TensorProduct.includeRight = W₂)
    (homog : W₁ ≤ SetLike.homogeneousSubmonoid 𝒜)
    (x : (𝒜 · |>.baseChange S)[W₂⁻¹]₀) :
    ∃ (i : ι) (n : S ⊗[R] ↥(𝒜 i)) (d : 𝒜 i) (hd : ↑d ∈ W₁),
      .mk ⟨i, (𝒜 i).toBaseChange _ n, (𝒜 i).toBaseChange _ (1 ⊗ₜ[R] d),
        hw ▸ ⟨_, hd, rfl⟩⟩ = x := by
  by_cases hw₂ : 0 ∈ W₂
  · use 0, 0, 1, one_mem _
    subsingleton [subsingleton _ hw₂]
  subst hw
  obtain ⟨⟨i, n, ⟨d, hd⟩, ⟨e, he, (rfl : _ = d)⟩⟩, rfl⟩ := x.mk_surjective
  obtain ⟨j, hej⟩ := homog he
  obtain rfl := DirectSum.degree_eq_of_mem_mem (𝒜 · |>.baseChange S) hd
    (Submodule.tmul_mem_baseChange_of_mem (1 : S) hej) (by aesop)
  obtain ⟨n, rfl⟩ := (𝒜 i).toBaseChange_surjective _ n
  exact ⟨i, n, ⟨e, hej⟩, he, rfl⟩

/-- A special version of `ext_mkₗ` just for the case of
`HomogeneousLocalization (𝒜 · |>.baseChange S) W₂`. -/
theorem ext_mkₗ_baseChange (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
    (hw : W₁.map Algebra.TensorProduct.includeRight = W₂)
    (homog : W₁ ≤ SetLike.homogeneousSubmonoid 𝒜)
    {M : Type*} [AddCommGroup M] [Module S M]
    {f g : (𝒜 · |>.baseChange S)[W₂⁻¹]₀ →ₗ[S] M}
    (ih : ∀ {i : ι} (den : 𝒜 i), den.val ∈ W₁ →
      f ∘ₗ mkₗ (𝒜 · |>.baseChange S) W₂ ((𝒜 i).toBaseChange S (1 ⊗ₜ[R] den)) =
      g ∘ₗ mkₗ (𝒜 · |>.baseChange S) W₂ ((𝒜 i).toBaseChange S (1 ⊗ₜ[R] den))) : f = g := by
  ext x
  obtain ⟨i, n, d, hd, hx⟩ := baseChange_induction 𝒜 W₁ W₂ hw homog x
  rw [← hx, ← mkₗ_apply]
  exact congr($(ih _ hd) _)

-- NB: aux defs extracted for performance concerns
section aux_defs

variable (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
  (hw : W₁.map Algebra.TensorProduct.includeRight = W₂)
  (homog : W₁ ≤ SetLike.homogeneousSubmonoid 𝒜)

/-- The forward direction of `baseChange`, here as only a linear map.

This is an auxiliary definition. -/
noncomputable def baseChange.forwards : (𝒜 · |>.baseChange S)[W₂⁻¹]₀ →ₗ[S] S ⊗[R] 𝒜[W₁⁻¹]₀ :=
  let f₁ : (𝒜 · |>.baseChange S)[W₂⁻¹]₀ →ₐ[S] (at W₂) := Algebra.algHom _ _ _
  let f₂ : (at W₂) ≃ₐ[S] S ⊗[R] (at W₁) := Localization.tensorEquiv _ _ hw
  let f₃ : S ⊗[R] (at W₁) →ₗ[S] S ⊗[R] 𝒜[W₁⁻¹]₀ :=
    ((ofLocalization 𝒜 W₁ homog).restrictScalars R).baseChange S
  f₃ ∘ₗ f₂.toLinearMap ∘ₗ f₁.toLinearMap

/-- The backward direction of `baseChange` as an algebra map.

This is an auxiliary definition. -/
noncomputable def baseChange.backwards : S ⊗[R] 𝒜[W₁⁻¹]₀ →ₐ[S] (𝒜 · |>.baseChange S)[W₂⁻¹]₀ :=
  AlgHom.liftEquiv R S 𝒜[W₁⁻¹]₀ (𝒜 · |>.baseChange S)[W₂⁻¹]₀ <|
    .comp (equivRestrictScalars (𝒜 · |>.baseChange S) W₂ R).symm.toAlgHom <|
      mapₐ (.includeRight _ _) _ _ <| hw ▸ Submonoid.le_comap_map _

@[simp] theorem baseChange.forwards_mk_tmul
    {i : ι} {s : S} {n : 𝒜 i} {d : 𝒜 i} (hd : d.val ∈ W₁) :
    forwards 𝒜 W₁ W₂ hw homog (.mk ⟨i, (𝒜 i).toBaseChange _ (s ⊗ₜ[R] n),
      (𝒜 i).toBaseChange _ (1 ⊗ₜ[R] d), hw ▸ ⟨_, hd, rfl⟩⟩) = s ⊗ₜ[R] .mk ⟨i, n, d, hd⟩ := by
  simp [forwards, Algebra.algHom, hd]

@[simp] theorem baseChange.backwards_mk_tmul
    {i : ι} {s : S} {n : 𝒜 i} {d : 𝒜 i} {hd : d.val ∈ W₁} :
    backwards 𝒜 W₁ W₂ hw (s ⊗ₜ[R] .mk ⟨i, n, d, hd⟩) =
      .mk ⟨i, (𝒜 i).toBaseChange _ (s ⊗ₜ[R] n),
        (𝒜 i).toBaseChange _ (1 ⊗ₜ[R] d), hw ▸ ⟨_, hd, rfl⟩⟩ := by
  simpa [backwards, mapₐ_mk] using mk_congr rfl (by simp [Submodule.coe_smul, smul_tmul']) rfl

set_option maxHeartbeats 999999 in
-- This is slow for some reason.
theorem baseChange.left_inv :
    (backwards 𝒜 W₁ W₂ hw).toLinearMap ∘ₗ forwards 𝒜 W₁ W₂ hw homog = .id := by
  refine ext_mkₗ_baseChange 𝒜 W₁ W₂ hw homog fun {i} d hd ↦
    ((𝒜 i).toBaseChange_surjective S).injective_linearMapComp_right ?_
  subst hw
  have key : ∃ x ∈ W₁, (1 : S) ⊗ₜ[R] x = 1 ⊗ₜ[R] ↑d := by grind
  ext
  simp [hd, key]

theorem baseChange.right_inv :
    forwards 𝒜 W₁ W₂ hw homog ∘ₗ (backwards 𝒜 W₁ W₂ hw).toLinearMap = .id := by
  ext x
  obtain ⟨⟨i, n, d, hd⟩, rfl⟩ := x.mk_surjective
  simp [hd]

end aux_defs

/-- `(S ⊗[R] 𝒜)[(1 ⊗ W₁)⁻¹]₀ ≃ₐ[S] S ⊗[R] 𝒜[W₁⁻¹]₀` -/
noncomputable def baseChange
    (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
    (hw : W₁.map Algebra.TensorProduct.includeRight = W₂)
    (homog : W₁ ≤ SetLike.homogeneousSubmonoid 𝒜) :
    (𝒜 · |>.baseChange S)[W₂⁻¹]₀ ≃ₐ[S] S ⊗[R] 𝒜[W₁⁻¹]₀ := .symm
  { __ := baseChange.backwards 𝒜 W₁ W₂ hw
    invFun := baseChange.forwards 𝒜 W₁ W₂ hw homog
    left_inv _ := congr($(baseChange.right_inv ..) _)
    right_inv _ := congr($(baseChange.left_inv ..) _) }

@[simp] theorem baseChange_mk_tmul
    (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
    (hw : W₁.map Algebra.TensorProduct.includeRight = W₂)
    (homog : W₁ ≤ SetLike.homogeneousSubmonoid 𝒜)
    {i : ι} {s : S} {n : 𝒜 i} {d : 𝒜 i} (hd : d.val ∈ W₁) :
    baseChange 𝒜 W₁ W₂ hw homog (.mk ⟨i, (𝒜 i).toBaseChange _ (s ⊗ₜ[R] n),
      (𝒜 i).toBaseChange _ (1 ⊗ₜ[R] d), hw ▸ ⟨_, hd, rfl⟩⟩) = s ⊗ₜ[R] .mk ⟨i, n, d, hd⟩ :=
  baseChange.forwards_mk_tmul ..

@[simp] theorem baseChange_symm_mk_tmul
    (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
    (hw : W₁.map Algebra.TensorProduct.includeRight = W₂)
    (homog : W₁ ≤ SetLike.homogeneousSubmonoid 𝒜)
    {i : ι} {s : S} {n : 𝒜 i} {d : 𝒜 i} (hd : d.val ∈ W₁) :
    (baseChange 𝒜 W₁ W₂ hw homog).symm (s ⊗ₜ[R] .mk ⟨i, n, d, hd⟩) =
      .mk ⟨i, (𝒜 i).toBaseChange _ (s ⊗ₜ[R] n),
        (𝒜 i).toBaseChange _ (1 ⊗ₜ[R] d), hw ▸ ⟨_, hd, rfl⟩⟩ :=
  baseChange.backwards_mk_tmul 𝒜 W₁ W₂ hw ..

end HomogeneousLocalization

-- TODO: add simp to Algebra.algHom
