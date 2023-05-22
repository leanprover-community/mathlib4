/-
Copyright © 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn

! This file was ported from Lean 3 source module topology.vector_bundle.constructions
! leanprover-community/mathlib commit be2c24f56783935652cefffb4bfca7e4b25d167e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.FiberBundle.Constructions
import Mathbin.Topology.VectorBundle.Basic

/-!
# Standard constructions on vector bundles

This file contains several standard constructions on vector bundles:

* `bundle.trivial.vector_bundle 𝕜 B F`: the trivial vector bundle with scalar field `𝕜` and model
  fiber `F` over the base `B`

* `vector_bundle.prod`: for vector bundles `E₁` and `E₂` with scalar field `𝕜` over a common base,
  a vector bundle structure on their direct sum `E₁ ×ᵇ E₂` (the notation stands for
  `λ x, E₁ x × E₂ x`).

* `vector_bundle.pullback`: for a vector bundle `E` over `B`, a vector bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags
Vector bundle, direct sum, pullback
-/


noncomputable section

open Bundle Set FiberBundle

open Classical Bundle

/-! ### The trivial vector bundle -/


namespace Bundle.Trivial

variable (𝕜 : Type _) (B : Type _) (F : Type _) [NontriviallyNormedField 𝕜] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [TopologicalSpace B]

instance trivialization.isLinear : (trivialization B F).isLinear 𝕜
    where linear x hx := ⟨fun y z => rfl, fun c y => rfl⟩
#align bundle.trivial.trivialization.is_linear Bundle.Trivial.trivialization.isLinear

variable {𝕜}

theorem trivialization.coordChangeL (b : B) :
    (trivialization B F).coordChangeL 𝕜 (trivialization B F) b = ContinuousLinearEquiv.refl 𝕜 F :=
  by
  ext v
  rw [Trivialization.coordChangeL_apply']
  exacts[rfl, ⟨mem_univ _, mem_univ _⟩]
#align bundle.trivial.trivialization.coord_changeL Bundle.Trivial.trivialization.coordChangeL

variable (𝕜)

instance vectorBundle : VectorBundle 𝕜 F (Bundle.Trivial B F)
    where
  trivialization_linear' := by
    intro e he
    rw [eq_trivialization B F e]
    infer_instance
  continuousOn_coord_change' := by
    intro e e' he he'
    obtain rfl := eq_trivialization B F e
    obtain rfl := eq_trivialization B F e'
    simp_rw [Trivialization.coordChangeL]
    exact continuous_const.continuous_on
#align bundle.trivial.vector_bundle Bundle.Trivial.vectorBundle

end Bundle.Trivial

/-! ### Direct sum of two vector bundles -/


section

variable (𝕜 : Type _) {B : Type _} [NontriviallyNormedField 𝕜] [TopologicalSpace B] (F₁ : Type _)
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] (E₁ : B → Type _) [TopologicalSpace (TotalSpace E₁)]
  (F₂ : Type _) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] (E₂ : B → Type _)
  [TopologicalSpace (TotalSpace E₂)]

namespace Trivialization

variable {F₁ E₁ F₂ E₂} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] (e₁ e₁' : Trivialization F₁ (π E₁))
  (e₂ e₂' : Trivialization F₂ (π E₂))

instance prod.isLinear [e₁.isLinear 𝕜] [e₂.isLinear 𝕜] : (e₁.Prod e₂).isLinear 𝕜
    where linear := fun x ⟨h₁, h₂⟩ =>
    (((e₁.linear 𝕜 h₁).mk' _).Prod_map ((e₂.linear 𝕜 h₂).mk' _)).isLinear
#align trivialization.prod.is_linear Trivialization.prod.isLinear

@[simp]
theorem coordChangeL_prod [e₁.isLinear 𝕜] [e₁'.isLinear 𝕜] [e₂.isLinear 𝕜] [e₂'.isLinear 𝕜] ⦃b⦄
    (hb : b ∈ (e₁.Prod e₂).baseSet ∩ (e₁'.Prod e₂').baseSet) :
    ((e₁.Prod e₂).coordChangeL 𝕜 (e₁'.Prod e₂') b : F₁ × F₂ →L[𝕜] F₁ × F₂) =
      (e₁.coordChangeL 𝕜 e₁' b : F₁ →L[𝕜] F₁).Prod_map (e₂.coordChangeL 𝕜 e₂' b) :=
  by
  rw [ContinuousLinearMap.ext_iff, ContinuousLinearMap.coe_prodMap']
  rintro ⟨v₁, v₂⟩
  show
    (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
      (e₁.coord_changeL 𝕜 e₁' b v₁, e₂.coord_changeL 𝕜 e₂' b v₂)
  rw [e₁.coord_changeL_apply e₁', e₂.coord_changeL_apply e₂', (e₁.prod e₂).coordChangeL_apply']
  exacts[rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]
#align trivialization.coord_changeL_prod Trivialization.coordChangeL_prod

variable {e₁ e₂} [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

theorem prod_apply [e₁.isLinear 𝕜] [e₂.isLinear 𝕜] {x : B} (hx₁ : x ∈ e₁.baseSet)
    (hx₂ : x ∈ e₂.baseSet) (v₁ : E₁ x) (v₂ : E₂ x) :
    prod e₁ e₂ ⟨x, (v₁, v₂)⟩ =
      ⟨x, e₁.continuousLinearEquivAt 𝕜 x hx₁ v₁, e₂.continuousLinearEquivAt 𝕜 x hx₂ v₂⟩ :=
  rfl
#align trivialization.prod_apply Trivialization.prod_apply

end Trivialization

open Trivialization

variable [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, AddCommMonoid (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

/-- The product of two vector bundles is a vector bundle. -/
instance VectorBundle.prod [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂] :
    VectorBundle 𝕜 (F₁ × F₂) (E₁ ×ᵇ E₂)
    where
  trivialization_linear' := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩; skip
    infer_instance
  continuousOn_coord_change' :=
    by
    rintro _ _ ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨e₁', e₂', he₁', he₂', rfl⟩; skip
    refine'
        (((continuousOn_coord_change 𝕜 e₁ e₁').mono _).prodMapL 𝕜
              ((continuousOn_coord_change 𝕜 e₂ e₂').mono _)).congr
          _ <;>
      dsimp only [base_set_prod, mfld_simps]
    · mfld_set_tac
    · mfld_set_tac
    · rintro b hb
      rw [ContinuousLinearMap.ext_iff]
      rintro ⟨v₁, v₂⟩
      show
        (e₁.prod e₂).coordChangeL 𝕜 (e₁'.prod e₂') b (v₁, v₂) =
          (e₁.coord_changeL 𝕜 e₁' b v₁, e₂.coord_changeL 𝕜 e₂' b v₂)
      rw [e₁.coord_changeL_apply e₁', e₂.coord_changeL_apply e₂', (e₁.prod e₂).coordChangeL_apply']
      exacts[rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩]
#align vector_bundle.prod VectorBundle.prod

variable {𝕜 F₁ E₁ F₂ E₂}

@[simp]
theorem Trivialization.continuousLinearEquivAt_prod {e₁ : Trivialization F₁ (π E₁)}
    {e₂ : Trivialization F₂ (π E₂)} [e₁.isLinear 𝕜] [e₂.isLinear 𝕜] {x : B} (hx₁ : x ∈ e₁.baseSet)
    (hx₂ : x ∈ e₂.baseSet) :
    (e₁.Prod e₂).continuousLinearEquivAt 𝕜 x ⟨hx₁, hx₂⟩ =
      (e₁.continuousLinearEquivAt 𝕜 x hx₁).Prod (e₂.continuousLinearEquivAt 𝕜 x hx₂) :=
  by
  ext1
  funext v
  obtain ⟨v₁, v₂⟩ := v
  rw [(e₁.prod e₂).continuousLinearEquivAt_apply 𝕜, Trivialization.prod]
  exact (congr_arg Prod.snd (prod_apply 𝕜 hx₁ hx₂ v₁ v₂) : _)
#align trivialization.continuous_linear_equiv_at_prod Trivialization.continuousLinearEquivAt_prod

end

/-! ### Pullbacks of vector bundles -/


section

variable (R 𝕜 : Type _) {B : Type _} (F : Type _) (E : B → Type _) {B' : Type _} (f : B' → B)

instance [∀ x : B, AddCommMonoid (E x)] : ∀ x : B', AddCommMonoid ((f *ᵖ E) x) := by
  delta_instance bundle.pullback

instance [Semiring R] [∀ x : B, AddCommMonoid (E x)] [∀ x, Module R (E x)] :
    ∀ x : B', Module R ((f *ᵖ E) x) := by delta_instance bundle.pullback

variable {E F} [TopologicalSpace B'] [TopologicalSpace (TotalSpace E)] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module 𝕜 (E x)] {K : Type _} [ContinuousMapClass K B' B]

instance Trivialization.pullback_linear (e : Trivialization F (π E)) [e.isLinear 𝕜] (f : K) :
    (@Trivialization.pullback _ _ _ B' _ _ _ _ _ _ _ e f).isLinear 𝕜
    where linear x h := e.linear 𝕜 h
#align trivialization.pullback_linear Trivialization.pullback_linear

instance VectorBundle.pullback [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
    (f : K) : VectorBundle 𝕜 F ((f : B' → B) *ᵖ E)
    where
  trivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩; skip
    infer_instance
  continuousOn_coord_change' :=
    by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩; skip
    refine'
      ((continuousOn_coord_change 𝕜 e e').comp (map_continuous f).ContinuousOn fun b hb => hb).congr
        _
    rintro b (hb : f b ∈ e.base_set ∩ e'.base_set); ext v
    show ((e.pullback f).coordChangeL 𝕜 (e'.pullback f) b) v = (e.coord_changeL 𝕜 e' (f b)) v
    rw [e.coord_changeL_apply e' hb, (e.pullback f).coordChangeL_apply' _]
    exacts[rfl, hb]
#align vector_bundle.pullback VectorBundle.pullback

end

