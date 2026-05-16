/-
Copyright (c) 2026 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib

/-!
# Categorical PBW

## References

* This is from the preprint: https://arxiv.org/pdf/1804.06485

-/

namespace CategoryTheory

namespace Monad

open Limits

universe v u

variable {C : Type u} [Category.{v} C]

instance {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂) [HasReflexiveCoequalizers (Algebra T₂)] :
    (algebraFunctorOfMonadHom h).IsRightAdjoint :=
  have : (algebraFunctorOfMonadHom h ⋙ T₁.forget).IsRightAdjoint :=
    algebra_equiv_of_iso_monads_comp_forget h ▸ instIsRightAdjointAlgebraForget T₂
  isRightAdjoint_triangle_lift_monadic T₁.forget

noncomputable def directImageFunctor {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂)
    [HasReflexiveCoequalizers T₂.Algebra] : Algebra T₁ ⥤ Algebra T₂ :=
  (algebraFunctorOfMonadHom h).leftAdjoint

noncomputable def directImageFunctor_adj_algebraFunctorOfMonadHom {T₁ T₂ : Monad C} (h : T₁ ⟶ T₂)
    [HasReflexiveCoequalizers T₂.Algebra] : directImageFunctor h ⊣ algebraFunctorOfMonadHom h :=
  Adjunction.ofIsRightAdjoint (algebraFunctorOfMonadHom h)

structure RightModule (T : Monad C) where
  F : C ⥤ C
  ρ : F ⋙ T.toFunctor ⟶ F
  assoc : (ρ ◫ 𝟙 _) ≫ ρ = (Functor.associator _ _ _).hom ≫ (𝟙 _ ◫ T.μ) ≫ ρ := by cat_disch
  unit : ((𝟙 _) ◫ T.η) ≫ ρ = (Functor.rightUnitor _).hom := by cat_disch

def FreeRightModule (T : Monad C) (X : C ⥤ C) : RightModule T where
  F := X ⋙ T.toFunctor
  ρ := (Functor.associator _ _ _).hom ≫ (𝟙 _ ◫ T.μ)
  assoc := by
    ext
    simpa using assoc _ _
  unit := by
    ext
    simpa using left_unit _ _

namespace RightModule

structure Hom {T : Monad C} (M₁ M₂ : RightModule T) where
  τ : M₁.F ⟶ M₂.F
  comm : (τ ◫ 𝟙 _) ≫ M₂.ρ = M₁.ρ ≫ τ

structure Iso {T : Monad C} (M₁ M₂ : RightModule T) where
  hom : Hom M₁ M₂
  inv : Hom M₂ M₁
  hom_inv_id : hom.τ ≫ inv.τ = 𝟙 _
  inv_hom_id : inv.τ ≫ hom.τ = 𝟙 _

def IsFree {T : Monad C} (M : RightModule T) : Prop :=
  ∃ X : C ⥤ C, Nonempty (Iso M (FreeRightModule T X))

end RightModule

def inducedRightModule {M N : Monad C} (φ : M ⟶ N) : RightModule M where
  F := N.toFunctor
  ρ := ((𝟙 _) ◫ φ.toNatTrans) ≫ N.μ
  assoc := by
    ext x
    simpa using φ.app (M.obj (N.obj x)) ≫= N.map (φ.app (N.obj x)) ≫= assoc _ _
  unit := by
    ext
    simpa using left_unit _ _

def HasPBW {M N : Monad C} (φ : M ⟶ N) [HasReflexiveCoequalizers (Algebra N)] :=
  ∃ X : C ⥤ C, Nonempty (directImageFunctor φ ⋙ N.forget ≅ M.forget ⋙ X)

instance {M N : Monad C} (φ : M ⟶ N) (c : M.Algebra) :
    IsReflexivePair (N.map (φ.app c.A) ≫ N.μ.app c.A) (N.map c.a) := by
  refine ⟨N.map (M.η.app c.A), ?_, ?_⟩
  · have h := φ.app_η c.A
    simp_rw [Functor.id_obj] at h
    rw [← Category.assoc, ← N.map_comp, h]
    exact N.right_unit c.A
  · have h := c.unit
    simp_rw [Functor.id_obj] at h
    rw [← N.map_comp, h, Functor.map_id]

-- i believe this can be done assuming `[HasReflexiveCoequalizers N.Algebra]` alone but it needs
-- some extra work

variable {M N : Monad C} [∀ M : Monad C, HasReflexiveCoequalizers M.Algebra]

instance : HasReflexiveCoequalizers C := by
  sorry

instance (φ : M ⟶ N) (c : M.Algebra) :
    HasCoequalizer (N.map (φ.app c.A) ≫ N.μ.app c.A) (N.map c.a) := by
  infer_instance

/-- This is the left adjoint diagram corresponding to `algebra_equiv_of_iso_monads_comp_forget`. -/
noncomputable def directImageFunctor_preserves_free {M N : Monad C} (φ : M ⟶ N) :
    free _ ⋙ directImageFunctor φ ≅ free _ := by
  apply M.adj.leftAdjointCompIso (directImageFunctor_adj_algebraFunctorOfMonadHom φ) N.adj
  rfl

instance {N : Monad C} [HasReflexiveCoequalizers C] :
    HasReflexiveCoequalizers N.Algebra where
  has_coeq A B f g h := by
    obtain ⟨s, hsf, hsg⟩ := h.common_section'
    have : IsReflexivePair f.f g.f := ⟨s.f, congr_arg Monad.Algebra.Hom.f hsf, congr_arg
      Monad.Algebra.Hom.f hsg⟩
    have : HasCoequalizer f.f g.f := HasReflexiveCoequalizers.has_coeq f.f g.f
    sorry

noncomputable def directImageCofork {M N : Monad C} (φ : M ⟶ N) (c : M.Algebra)
    [HasReflexiveCoequalizers C] :
    Cofork (N.map (φ.app c.A) ≫ N.μ.app c.A) (N.map c.a) :=
  Cofork.ofπ (coequalizer.π _ _) (coequalizer.condition _ _)

-- we will probably need an instance proving `algerba N` has reflexive coequalizers if `C` does,
-- until we prove the previous lemmas using `HasReflexiveCoequalizers (Algebra N)`.
theorem hasPBW_iff {M N : Monad C} (φ : M ⟶ N) [HasReflexiveCoequalizers (Algebra N)] :
    HasPBW φ ↔ (inducedRightModule φ).IsFree := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨X, h⟩ := h
    sorry
  · sorry

end Monad

end CategoryTheory
