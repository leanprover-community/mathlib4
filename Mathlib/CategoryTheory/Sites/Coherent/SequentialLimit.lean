/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Subcanonical
/-!

# Limits of epimorphisms in coherent topoi

This file proves that a sequential limit of epimorphisms is epimorphic in the category of sheaves
for the coherent topology on a preregular finitary extensive concrete category where the effective
epimorphisms are precisely the surjective ones.

In other words, given epimorphisms of sheaves

`⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀`,

the projection map `lim Xₙ ⟶ X₀` is an epimorphism (see `coherentTopology.epi_π_app_zero_of_epi`).

This is deduced from the corresponding statement about locally surjective morphisms of sheaves
(see `coherentTopology.isLocallySurjective_π_app_zero_of_isLocallySurjective_map`).
-/

universe w v u

open CategoryTheory Limits Opposite

attribute [local instance] ConcreteCategory.instFunLike

namespace CategoryTheory.coherentTopology

variable {C : Type u} [Category.{v} C] [Preregular C] [FinitaryExtensive C]
    {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)} {c : Cone F}
    (hc : IsLimit c)
    (hF : ∀ n, Sheaf.IsLocallySurjective (F.map (homOfLE (Nat.le_succ n)).op))

private noncomputable def preimage (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) :
    (n : ℕ) → ((Y : C) × (F.obj ⟨n⟩).val.obj ⟨Y⟩)
  | 0 => ⟨X, y⟩
  | (n+1) => by
    have := hF n
    rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
    specialize this (preimage X y n).1 (preimage X y n).2
    exact ⟨this.choose, this.choose_spec.choose_spec.choose_spec.choose⟩

private noncomputable def preimageTransitionMap (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    (preimage hF X y (n + 1)).1 ⟶ (preimage hF X y n).1 := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose

private lemma preimageTransitionMap_effectiveEpi (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    EffectiveEpi (preimageTransitionMap hF X y n) := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose_spec.choose

private lemma preimage_w (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) (n : ℕ) :
    (F.map (homOfLE (n.le_add_right 1)).op).val.app ⟨(preimage hF X y (n+1)).1⟩
      (preimage hF X y (n+1)).2 = ((F.obj ⟨n⟩).val.map (preimageTransitionMap hF X y n).op)
        (preimage hF X y n).2 := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  specialize this (preimage hF X y n).1 (preimage hF X y n).2
  exact this.choose_spec.choose_spec.choose_spec.choose_spec

private noncomputable def preimageDiagram (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n ↦ (preimage hF X y n).1)
    fun n ↦ preimageTransitionMap hF X y n

variable [HasLimitsOfShape ℕᵒᵖ C]

private noncomputable def auxCone (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : Cone F where
  pt := ((coherentTopology C).yoneda).obj (limit (preimageDiagram hF X y))
  π := NatTrans.ofOpSequence
    (fun n ↦ (coherentTopology C).yoneda.map
      (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm (preimage hF X y n).2) (by
    intro n
    simp only [Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, Category.id_comp,
      Category.assoc, ← limit.w (preimageDiagram hF X y) (homOfLE (n.le_add_right 1)).op,
      Nat.succ_eq_add_one, homOfLE_leOfHom, Functor.map_comp]
    rw [GrothendieckTopology.yonedaEquiv_symm_naturality_left,
      GrothendieckTopology.yonedaEquiv_symm_naturality_right]
    erw [preimage_w hF X y n]
    simp [preimageDiagram] )

variable [ConcreteCategory C] (h : ∀ {X Y : C} (f : X ⟶ Y), EffectiveEpi f ↔ Function.Surjective f)

variable [PreservesLimitsOfShape ℕᵒᵖ (forget C)]

include hF h hc in
lemma isLocallySurjective_π_app_zero_of_isLocallySurjective_map :
    Sheaf.IsLocallySurjective (c.π.app ⟨0⟩) := by
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff]
  intro X y
  have hh : EffectiveEpi (limit.π (preimageDiagram hF X y) ⟨0⟩) := by
    rw [h]
    refine Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit _) fun n ↦ ?_
    simpa [preimageDiagram, ← h] using preimageTransitionMap_effectiveEpi hF X y n
  refine ⟨limit (preimageDiagram hF X y), limit.π (preimageDiagram hF X y) ⟨0⟩, hh,
    (coherentTopology C).yonedaEquiv (hc.lift (auxCone hF X y )),
    (?_ : (c.π.app (op 0)).val.app _ _ = _)⟩
  simp only [← (coherentTopology C).yonedaEquiv_comp, Functor.const_obj_obj, auxCone,
    IsLimit.fac, NatTrans.ofOpSequence_app, (coherentTopology C).yonedaEquiv_comp,
    (coherentTopology C).yonedaEquiv_yoneda_map]
  rfl

include h in
lemma epi_π_app_zero_of_epi [HasSheafify (coherentTopology C) (Type v)]
    [Balanced (Sheaf (coherentTopology C) (Type v))]
    [(coherentTopology C).WEqualsLocallyBijective (Type v)]
    {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)}
    {c : Cone F} (hc : IsLimit c)
    (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op)) : Epi (c.π.app ⟨0⟩) := by
  simp_rw [← Sheaf.isLocallySurjective_iff_epi'] at hF ⊢
  exact isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF h

end CategoryTheory.coherentTopology
