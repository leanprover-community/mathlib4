/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Base-change in `CommAlgCat` -/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TensorProduct

universe w u v

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- `Under.pushout` in `CommRingCat` is isomorphic to `ModuleCat.extendScalars` after
composing with suitable forgetful functors. -/
def CommRingCat.pushoutIsoExtendScalars : (((Under.pushout φ ⋙ (commAlgCatEquivUnder S).inverse) ⋙
    forget₂ (CommAlgCat ↑S) (AlgCat ↑S)) ⋙ forget₂ (AlgCat ↑S) (ModuleCat ↑S)) ≅
      (commAlgCatEquivUnder R).inverse ⋙ forget₂ (CommAlgCat R) (AlgCat R) ⋙
        forget₂ (AlgCat R) (ModuleCat R) ⋙ ModuleCat.extendScalars φ.hom := by
  letI := φ.hom.toAlgebra
  letI e (A : Under R) : pushout A.hom φ ≅ .of (S ⊗[R] A.right) :=
    pushoutSymmetry _ _ ≪≫ (colimit.isColimit _).coconePointUniqueUpToIso
      (CommRingCat.pushoutCoconeIsColimit R _ _)
  haveI hel (A : Under R) : pushout.inl _ _ ≫ (e A).hom =
      CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom := by
    simpa [e, -IsColimit.comp_coconePointUniqueUpToIso_hom] using
      (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ _
  haveI her (A : Under R) : pushout.inr _ _ ≫ (e A).hom =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (S := R)).toRingHom := by
    simpa [e, -IsColimit.comp_coconePointUniqueUpToIso_hom] using
      (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom _ _
  refine NatIso.ofComponents (fun A ↦
    LinearEquiv.toModuleIso
      { __ := (e A).commRingCatIsoToRingEquiv.toAddEquiv, map_smul' s m := ?_ }) ?_
  · dsimp [Iso.commRingCatIsoToRingEquiv, ModuleCat.restrictScalars] at m ⊢
    simp only [Algebra.smul_def, map_mul,
      RingHom.algebraMap_toAlgebra, Under.mk_hom]
    rw [@Algebra.smul_def S (↑S ⊗[↑R] ↑A.right)]
    change (pushout.inr A.hom φ ≫ (e A).hom) s * _ =
      (CommRingCat.ofHom (algebraMap S (S ⊗[R] A.right))) s * _
    congr 3
    simp only [Functor.const_obj_obj, Functor.id_obj, her]
    rfl
  · intros X Y f
    ext x
    change (pushout.desc (f.right ≫ pushout.inl Y.hom φ) (pushout.inr Y.hom φ) _ ≫ (e Y).hom) _ =
      ((e X).hom ≫ CommRingCat.ofHom
        (Algebra.TensorProduct.map (.id R S) (CommRingCat.toAlgHom f))) _
    congr 2
    ext1
    · rw [reassoc_of% hel]
      simp [hel, ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom]
      rfl
    · rw [reassoc_of% her]
      simp [her, ← CommRingCat.ofHom_comp, ← AlgHom.comp_toRingHom]
