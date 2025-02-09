/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# Effective epimorphisms in `CompHausLike`

In any category of compact Hausdorff spaces, continuous surjections are effective epimorphisms.

We deduce that if the converse holds and explicit pullbacks exist, then `CompHausLike P` is
preregular.

If furthermore explicit finite coproducts exist, then `CompHausLike P` is precoherent.
-/

universe u

open CategoryTheory Limits Topology

namespace CompHausLike

variable {P : TopCat.{u} → Prop}

/--
If `π` is a surjective morphism in `CompHausLike P`, then it is an effective epi.
-/
noncomputable
def effectiveEpiStruct {B X : CompHausLike P} (π : X ⟶ B) (hπ : Function.Surjective π) :
    EffectiveEpiStruct π where
  desc e h := ofHom _ ((IsQuotientMap.of_surjective_continuous hπ π.hom.continuous).lift e.hom
    fun a b hab ↦
      CategoryTheory.congr_fun (h
        (ofHom _ ⟨fun _ ↦ a, continuous_const⟩)
        (ofHom _ ⟨fun _ ↦ b, continuous_const⟩)
      (by ext; exact hab)) a)
  fac e h := TopCat.hom_ext ((IsQuotientMap.of_surjective_continuous hπ π.hom.continuous).lift_comp
    e.hom
    fun a b hab ↦ CategoryTheory.congr_fun (h
      (ofHom _ ⟨fun _ ↦ a, continuous_const⟩)
      (ofHom _ ⟨fun _ ↦ b, continuous_const⟩)
    (by ext; exact hab)) a)
  uniq e h g hm := by
    suffices g = ofHom _ ((IsQuotientMap.of_surjective_continuous hπ π.hom.continuous).liftEquiv
      ⟨e.hom,
      fun a b hab ↦ CategoryTheory.congr_fun
        (h
          (ofHom _ ⟨fun _ ↦ a, continuous_const⟩)
          (ofHom _ ⟨fun _ ↦ b, continuous_const⟩)
          (by ext; exact hab))
        a⟩) by assumption
    apply ConcreteCategory.ext
    rw [hom_ofHom,
      ← Equiv.symm_apply_eq (IsQuotientMap.of_surjective_continuous hπ π.hom.continuous).liftEquiv]
    ext
    simp only [IsQuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

theorem preregular [HasExplicitPullbacks P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f) :
    Preregular (CompHausLike P) where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ⟨⟨effectiveEpiStruct _ ?_⟩⟩, pullback.snd f π,
      (pullback.condition _ _).symm⟩
    intro y
    obtain ⟨z, hz⟩ := hs π hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

theorem precoherent [HasExplicitPullbacks P] [HasExplicitFiniteCoproducts.{0} P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f) :
    Precoherent (CompHausLike P) := by
  have : Preregular (CompHausLike P) := preregular hs
  infer_instance

end CompHausLike
