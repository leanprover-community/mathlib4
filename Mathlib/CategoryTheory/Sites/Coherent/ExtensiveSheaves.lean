/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Preserves
/-!

# Sheaves for the extensive topology

This file characterises sheaves for the extensive topology.

## Main result

* `isSheaf_iff_preservesFiniteProducts`: In a finitary extensive category, the sheaves for the
  extensive topology are precisely those preserving finite products.
-/

universe w

namespace CategoryTheory

open Limits Presieve Opposite

variable {C : Type*} [Category C] {D : Type*} [Category D]

variable [FinitaryPreExtensive C]

/-- A presieve is *extensive* if it is finite and its arrows induce an isomorphism from the
coproduct to the target. -/
class Presieve.Extensive {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a finite collection of arrows that together induce an isomorphism from the
  coproduct of their sources. -/
  arrows_nonempty_isColimit : ∃ (α : Type) (_ : Finite α) (Z : α → C) (π : (a : α) → (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ Nonempty (IsColimit (Cofan.mk X π))

instance {X : C} (S : Presieve X) [S.Extensive] : S.hasPullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, rfl, ⟨hc⟩⟩ := Presieve.Extensive.arrows_nonempty_isColimit (R := S)
    intro _ _ _ _ _ hg
    cases hg
    apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct hc

/--
A finite product preserving presheaf is a sheaf for the extensive topology on a category which is
`FinitaryPreExtensive`.
-/
theorem isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.Extensive]
    (F : Cᵒᵖ ⥤ Type w) [PreservesFiniteProducts F] : S.IsSheafFor F  := by
  obtain ⟨α, _, Z, π, rfl, ⟨hc⟩⟩ := Extensive.arrows_nonempty_isColimit (R := S)
  have : (ofArrows Z (Cofan.mk X π).inj).hasPullbacks :=
    (inferInstance : (ofArrows Z π).hasPullbacks)
  cases nonempty_fintype α
  exact isSheafFor_of_preservesProduct _ _ hc

instance {α : Type} [Finite α] (Z : α → C) : (ofArrows Z (fun i ↦ Sigma.ι Z i)).Extensive :=
  ⟨⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ⟨coproductIsCoproduct _⟩⟩⟩

/-- Every Yoneda-presheaf is a sheaf for the extensive topology. -/
theorem extensiveTopology.isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (extensiveTopology C)
    (yoneda.obj W) := by
  erw [isSheaf_coverage]
  intro X R ⟨Y, α, Z, π, hR, hi⟩
  have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
  have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
  exact isSheafFor_extensive_of_preservesFiniteProducts _ _

/-- The extensive topology on a finitary pre-extensive category is subcanonical. -/
theorem extensiveTopology.subcanonical : Sheaf.Subcanonical (extensiveTopology C) :=
  Sheaf.Subcanonical.of_yoneda_isSheaf _ isSheaf_yoneda_obj

variable [FinitaryExtensive C]

/--
A presheaf of sets on a category which is `FinitaryExtensive` is a sheaf iff it preserves finite
products.
-/
theorem Presieve.isSheaf_iff_preservesFiniteProducts (F : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (extensiveTopology C) F ↔
    Nonempty (PreservesFiniteProducts F) := by
  refine ⟨fun hF ↦ ⟨⟨fun α _ ↦ ⟨fun {K} ↦ ?_⟩⟩⟩, fun hF ↦ ?_⟩
  · erw [Presieve.isSheaf_coverage] at hF
    let Z : α → C := fun i ↦ unop (K.obj ⟨i⟩)
    have : (Presieve.ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).hasPullbacks :=
      (inferInstance : (Presieve.ofArrows Z (Sigma.ι Z)).hasPullbacks)
    have : ∀ (i : α), Mono (Cofan.inj (Cofan.mk (∐ Z) (Sigma.ι Z)) i) :=
      (inferInstance : ∀ (i : α), Mono (Sigma.ι Z i))
    let i : K ≅ Discrete.functor (fun i ↦ op (Z i)) := Discrete.natIsoFunctor
    let _ : PreservesLimit (Discrete.functor (fun i ↦ op (Z i))) F :=
        Presieve.preservesProductOfIsSheafFor F ?_ initialIsInitial _ (coproductIsCoproduct Z)
        (FinitaryExtensive.isPullback_initial_to_sigma_ι Z)
        (hF (Presieve.ofArrows Z (fun i ↦ Sigma.ι Z i)) ?_)
    · exact preservesLimitOfIsoDiagram F i.symm
    · apply hF
      refine ⟨Empty, inferInstance, Empty.elim, IsEmpty.elim inferInstance, rfl, ⟨default,?_, ?_⟩⟩
      · ext b
        cases b
      · simp only [eq_iff_true_of_subsingleton]
    · refine ⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ?_⟩
      suffices Sigma.desc (fun i ↦ Sigma.ι Z i) = 𝟙 _ by rw [this]; infer_instance
      ext
      simp
  · let _ := hF.some
    erw [Presieve.isSheaf_coverage]
    intro X R ⟨Y, α, Z, π, hR, hi⟩
    have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
    have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts R F

/--
A presheaf on a category which is `FinitaryExtensive` is a sheaf iff it preserves finite products.
-/
theorem Presheaf.isSheaf_iff_preservesFiniteProducts (F : Cᵒᵖ ⥤ D) :
    IsSheaf (extensiveTopology C) F ↔ Nonempty (PreservesFiniteProducts F) := by
  constructor
  · intro h
    rw [IsSheaf] at h
    refine ⟨⟨fun J _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩⟩
    apply coyonedaJointlyReflectsLimits
    intro ⟨E⟩
    specialize h E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts] at h
    have : PreservesLimit K (F.comp (coyoneda.obj ⟨E⟩)) := (h.some.preserves J).preservesLimit
    change IsLimit ((F.comp (coyoneda.obj ⟨E⟩)).mapCone c)
    apply this.preserves
    exact hc
  · intro ⟨_⟩ E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts]
    exact ⟨inferInstance⟩

noncomputable instance (F : Sheaf (extensiveTopology C) D) : PreservesFiniteProducts F.val :=
  ((Presheaf.isSheaf_iff_preservesFiniteProducts F.val).mp F.cond).some

end CategoryTheory
