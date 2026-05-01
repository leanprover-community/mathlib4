/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Homology

/-!
# Right t-exact functors

-/

@[expose] public section

namespace CategoryTheory

open Limits Triangulated Pretriangulated

variable {C D : Type*}
  [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [CategoryTheory.IsTriangulated C]
  [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [CategoryTheory.IsTriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  (t₁ : TStructure C) (t₂ : TStructure D)
  (H₁ : Type*) [Category H₁] [Abelian H₁]
  (H₂ : Type*) [Category H₂] [Abelian H₂]
  [t₁.Heart H₁] [t₂.Heart H₂] [t₂.HasHomology₀ H₂]
  [(t₂.homology₀ (H := H₂)).ShiftSequence ℤ]

namespace Functor

variable {H₁ H₂} in
def homologyRightTExact (n : ℕ) : H₁ ⥤ H₂ := t₁.ιHeart (H := H₁) ⋙ F ⋙ t₂.homology (H := H₂) n

instance (n : ℕ) : (F.homologyRightTExact t₁ t₂ (H₁ := H₁) (H₂ := H₂) n).Additive := by
  dsimp [homologyRightTExact]
  infer_instance

section

variable (S : ShortComplex H₁) (hS : S.ShortExact) (n₀ n₁ : ℕ) (hn₁ : n₀ + 1 = n₁)

variable {H₁ H₂} in
noncomputable def homologyRightTExactδ :
    (F.homologyRightTExact t₁ t₂ (H₂ := H₂) n₀).obj S.X₃ ⟶
      (F.homologyRightTExact t₁ t₂ n₁).obj S.X₁ :=
  t₂.homologyδ (H := H₂) (F.mapTriangle.obj (t₁.heartShortExactTriangle S hS)) n₀ n₁
    (by simp [← hn₁])

variable {H₁ H₂} in
@[reassoc (attr := simp)]
lemma homologyRightTExactδ_comp :
    F.homologyRightTExactδ t₁ t₂ (H₁ := H₁) (H₂ := H₂) S hS n₀ n₁ hn₁ ≫
      (F.homologyRightTExact t₁ t₂ n₁).map S.f = 0 :=
  t₂.homologyδ_comp _ (F.map_distinguished _ (t₁.heartShortExactTriangle_distinguished S hS)) _ _ _

variable {H₁ H₂} in
@[reassoc (attr := simp)]
lemma homologyRightTExact_comp_δ :
     (F.homologyRightTExact t₁ t₂ n₀).map S.g ≫
      F.homologyRightTExactδ t₁ t₂ (H₂ := H₂) S hS n₀ n₁ hn₁ = 0 :=
  t₂.comp_homologyδ _ (F.map_distinguished _ (t₁.heartShortExactTriangle_distinguished S hS)) _ _ _

variable {H₁ H₂} in
lemma homologyRightTExact_exact₁ :
    (ShortComplex.mk _ _ (F.homologyRightTExactδ_comp t₁ t₂ (H₂ := H₂) S hS n₀ n₁ hn₁)).Exact :=
  t₂.homology_exact₁ _ (F.map_distinguished _ (t₁.heartShortExactTriangle_distinguished S hS)) _ _ _

include hS in
variable {H₁ H₂} in
lemma homologyRightTExact_exact₂ (n : ℕ) :
    (S.map (F.homologyRightTExact t₁ t₂ (H₂ := H₂) n)).Exact :=
  t₂.homology_exact₂ _ (F.map_distinguished _ (t₁.heartShortExactTriangle_distinguished S hS)) _

variable {H₁ H₂} in
lemma homologyRightTExact_exact₃ :
    (ShortComplex.mk _ _ (F.homologyRightTExact_comp_δ t₁ t₂ (H₂ := H₂) S hS n₀ n₁ hn₁)).Exact :=
  t₂.homology_exact₃ _ (F.map_distinguished _ (t₁.heartShortExactTriangle_distinguished S hS)) _ _ _

variable [Functor.RightTExact F t₁ t₂]

instance (X : H₁) :
  t₂.IsGE (F.obj (t₁.ιHeart.obj X)) 0 := F.isGE_obj t₁ t₂ _ 0

instance :
    (F.homologyRightTExact t₁ t₂ (H₁ := H₁) (H₂ := H₂) 0).PreservesMonomorphisms where
  preserves {X Y} f _ := by
    let S := ShortComplex.mk _ _ (cokernel.condition f)
    have hS : S.ShortExact :=
      { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f) }
    apply (t₂.homology_exact₁ _ (F.map_distinguished _
      (t₁.heartShortExactTriangle_distinguished S hS)) (-1) 0 (by linarith)).mono_g
    apply IsZero.eq_of_src
    dsimp
    exact t₂.isZero_homology_of_isGE _ _ 0 (by linarith)

variable {H₁ H₂} in
lemma homologyRightTExact₀_map_exact (h : S.Exact) [hf : Mono S.f] :
    (S.map (F.homologyRightTExact t₁ t₂ (H₁ := H₁) (H₂ := H₂) 0)).Exact := by
  let S' := ShortComplex.mk _ _ S.f_pOpcycles
  let φ : S' ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := S.fromOpcycles }
  have : Mono φ.τ₃ := h.mono_fromOpcycles
  have hS' : S'.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h }
  let ψ := (F.homologyRightTExact t₁ t₂ (H₁ := H₁) (H₂ := H₂) 0).mapShortComplex.map φ
  have : IsIso ψ.τ₁ := by dsimp [ψ]; infer_instance
  have : IsIso ψ.τ₂ := by dsimp [ψ]; infer_instance
  have : Mono ψ.τ₃ := by dsimp [ψ]; infer_instance
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1
  exact F.homologyRightTExact_exact₂ t₁ t₂ S' hS' 0

end

end Functor

end CategoryTheory
