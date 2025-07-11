/-
Copyright (c) 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Prod

/-!
# Standard constructions on vector bundles

This file contains several standard constructions on vector bundles:

* `Bundle.Trivial.vectorBundle 𝕜 B F`: the trivial vector bundle with scalar field `𝕜` and model
  fiber `F` over the base `B`

* `VectorBundle.prod`: for vector bundles `E₁` and `E₂` with scalar field `𝕜` over a common base,
  a vector bundle structure on their direct sum `E₁ ×ᵇ E₂` (the notation stands for
  `fun x ↦ E₁ x × E₂ x`).

* `VectorBundle.pullback`: for a vector bundle `E` over `B`, a vector bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags
Vector bundle, direct sum, pullback
-/

noncomputable section

open Bundle Set FiberBundle

/-! ### The trivial vector bundle -/

namespace Bundle.Trivial

variable (𝕜 : Type*) (B : Type*) (F : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [TopologicalSpace B]

instance trivialization.isLinear : (trivialization B F).IsLinear 𝕜 where
  linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩

variable {𝕜} in
theorem trivialization.coordChangeL (b : B) :
    (trivialization B F).coordChangeL 𝕜 (trivialization B F) b =
      ContinuousLinearEquiv.refl 𝕜 F := by
  ext v
  rw [Trivialization.coordChangeL_apply']
  exacts [rfl, ⟨mem_univ _, mem_univ _⟩]

instance vectorBundle : VectorBundle 𝕜 F (Bundle.Trivial B F) where
  trivialization_linear' e he := by
    rw [eq_trivialization B F e]
    infer_instance
  continuousOn_coordChange' e e' he he' := by
    obtain rfl := eq_trivialization B F e
    obtain rfl := eq_trivialization B F e'
    simp only [trivialization.coordChangeL]
    exact continuous_const.continuousOn

@[simp] lemma linearMapAt_trivialization (x : B) :
    (trivialization B F).linearMapAt 𝕜 x = LinearMap.id := by
  ext v
  rw [Trivialization.coe_linearMapAt_of_mem _ (by simp)]
  rfl

@[simp] lemma continuousLinearMapAt_trivialization (x : B) :
    (trivialization B F).continuousLinearMapAt 𝕜 x = ContinuousLinearMap.id 𝕜 F := by
  ext; simp

@[simp] lemma symmₗ_trivialization (x : B) :
    (trivialization B F).symmₗ 𝕜 x = LinearMap.id := by
  ext; simp [Trivialization.coe_symmₗ, trivialization_symm_apply B F]

@[simp] lemma symmL_trivialization (x : B) :
    (trivialization B F).symmL 𝕜 x = ContinuousLinearMap.id 𝕜 F := by
  ext; simp [trivialization_symm_apply B F]

@[simp] lemma continuousLinearEquivAt_trivialization (x : B) :
    (trivialization B F).continuousLinearEquivAt 𝕜 x (mem_univ _) =
      ContinuousLinearEquiv.refl 𝕜 F := by
  ext; simp

end Bundle.Trivial

/-! ### Direct sum of two vector bundles -/

section

variable (𝕜 : Type*) {B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] (F₁ : Type*)
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type*) [TopologicalSpace (TotalSpace F₁ E₁)]
  (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)]

namespace Trivialization

variable {F₁ E₁ F₂ E₂}
variable [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

instance prod.isLinear [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] : (e₁.prod e₂).IsLinear 𝕜 where
  linear := fun _ ⟨h₁, h₂⟩ =>
    (((e₁.linear 𝕜 h₁).mk' _).prodMap ((e₂.linear 𝕜 h₂).mk' _)).isLinear

@[simp]
theorem coordChangeL_prod [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜] ⦃b⦄
    (hb : (b ∈ e₁.baseSet ∧ b ∈ e₂.baseSet) ∧ b ∈ e₁'.baseSet ∧ b ∈ e₂'.baseSet) :
    ((e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b : F₁ × F₂ →L[𝕜] F₁ × F₂) =
      (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁).prodMap (e₂.coordChangeL 𝕜 e₂' b) := by
  rw [ContinuousLinearMap.ext_iff, ContinuousLinearMap.coe_prodMap']
  rintro ⟨v₁, v₂⟩
  change
    (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
      (e₁.coordChangeL 𝕜 e₁' b v₁, e₂.coordChangeL 𝕜 e₂' b v₂)
  rw [e₁.coordChangeL_apply e₁', e₂.coordChangeL_apply e₂', (e₁.prod e₂).coordChangeL_apply']
  exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]

variable {e₁ e₂} [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

theorem prod_apply' [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B} (hx₁ : x ∈ e₁.baseSet)
    (hx₂ : x ∈ e₂.baseSet) (v₁ : E₁ x) (v₂ : E₂ x) :
    prod e₁ e₂ ⟨x, (v₁, v₂)⟩ =
      ⟨x, e₁.continuousLinearEquivAt 𝕜 x hx₁ v₁, e₂.continuousLinearEquivAt 𝕜 x hx₂ v₂⟩ :=
  rfl

end Trivialization

open Trivialization

variable [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, AddCommMonoid (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

/-- The product of two vector bundles is a vector bundle. -/
instance VectorBundle.prod [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] :
    VectorBundle 𝕜 (F₁ × F₂) (E₁ ×ᵇ E₂) where
  trivialization_linear' := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine (((continuousOn_coordChange 𝕜 e₁ e₁').mono ?_).prod_mapL 𝕜
      ((continuousOn_coordChange 𝕜 e₂ e₂').mono ?_)).congr ?_ <;>
      dsimp only [prod_baseSet, mfld_simps]
    · mfld_set_tac
    · mfld_set_tac
    · rintro b hb
      rw [ContinuousLinearMap.ext_iff]
      rintro ⟨v₁, v₂⟩
      change (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
        (e₁.coordChangeL 𝕜 e₁' b v₁, e₂.coordChangeL 𝕜 e₂' b v₂)
      rw [e₁.coordChangeL_apply e₁', e₂.coordChangeL_apply e₂', (e₁.prod e₂).coordChangeL_apply']
      exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]

variable {𝕜 F₁ E₁ F₂ E₂}

@[simp]
theorem Trivialization.continuousLinearEquivAt_prod {e₁ : Trivialization F₁ (π F₁ E₁)}
    {e₂ : Trivialization F₂ (π F₂ E₂)} [e₁.IsLinear 𝕜] [e₂.IsLinear 𝕜] {x : B}
    (hx : x ∈ (e₁.prod e₂).baseSet) :
    (e₁.prod e₂).continuousLinearEquivAt 𝕜 x hx =
      (e₁.continuousLinearEquivAt 𝕜 x hx.1).prodCongr (e₂.continuousLinearEquivAt 𝕜 x hx.2) := by
  ext v : 2
  obtain ⟨v₁, v₂⟩ := v
  rw [(e₁.prod e₂).continuousLinearEquivAt_apply 𝕜, Trivialization.prod]
  exact (congr_arg Prod.snd (prod_apply' 𝕜 hx.1 hx.2 v₁ v₂) :)

end

/-! ### Pullbacks of vector bundles -/

section

variable (R 𝕜 : Type*) {B : Type*} (F : Type*) (E : B → Type*) {B' : Type*} (f : B' → B)

instance [i : ∀ x : B, AddCommMonoid (E x)] (x : B') : AddCommMonoid ((f *ᵖ E) x) := i _

instance [Semiring R] [∀ x : B, AddCommMonoid (E x)] [i : ∀ x, Module R (E x)] (x : B') :
    Module R ((f *ᵖ E) x) := i _

variable {E F} [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module 𝕜 (E x)] {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B]

instance Trivialization.pullback_linear (e : Trivialization F (π F E)) [e.IsLinear 𝕜] (f : K) :
    (Trivialization.pullback (B' := B') e f).IsLinear 𝕜 where
  linear _ h := e.linear 𝕜 h

instance VectorBundle.pullback [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (f : K) : VectorBundle 𝕜 F ((f : B' → B) *ᵖ E) where
  trivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    infer_instance
  continuousOn_coordChange' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    refine ((continuousOn_coordChange 𝕜 e e').comp
      (map_continuous f).continuousOn fun b hb => hb).congr ?_
    rintro b (hb : f b ∈ e.baseSet ∩ e'.baseSet); ext v
    change ((e.pullback f).coordChangeL 𝕜 (e'.pullback f) b) v = (e.coordChangeL 𝕜 e' (f b)) v
    rw [e.coordChangeL_apply e' hb, (e.pullback f).coordChangeL_apply' _]
    exacts [rfl, hb]

end
