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
for the coherent topology on a preregular finitary extensive category where sequential limits of
effective epimorphisms are effective epimorphisms.

In other words, given epimorphisms of sheaves

`⋯ ⟶ Xₙ₊₁ ⟶ Xₙ ⟶ ⋯ ⟶ X₀`,

the projection map `lim Xₙ ⟶ X₀` is an epimorphism (see `coherentTopology.epi_π_app_zero_of_epi`).

This is deduced from the corresponding statement about locally surjective morphisms of sheaves
(see `coherentTopology.isLocallySurjective_π_app_zero_of_isLocallySurjective_map`).
-/

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.coherentTopology

variable {C : Type u} [Category.{v} C] [Preregular C] [FinitaryExtensive C]

attribute [local instance] Types.instFunLike Types.instConcreteCategory
variable {F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)} {c : Cone F}
    (hc : IsLimit c)
    (hF : ∀ n, Sheaf.IsLocallySurjective (F.map (homOfLE (Nat.le_succ n)).op))

private structure struct (F : ℕᵒᵖ ⥤ Sheaf (coherentTopology C) (Type v)) where
  X (n : ℕ) : C
  x (n : ℕ) : (F.obj ⟨n⟩).val.obj ⟨X n⟩
  map (n : ℕ) : X (n + 1) ⟶ X n
  effectiveEpi (n : ℕ) : EffectiveEpi (map n)
  w (n : ℕ) : (F.map (homOfLE (n.le_add_right 1)).op).val.app (op (X (n + 1))) (x (n + 1)) =
      (F.obj (op n)).val.map (map n).op (x n)

include hF in
private lemma exists_effectiveEpi (n : ℕ) (X : C) (y : (F.obj ⟨n⟩).val.obj ⟨X⟩) :
    ∃ (X' : C) (φ : X' ⟶ X) (_ : EffectiveEpi φ) (x : (F.obj ⟨n + 1⟩).val.obj ⟨X'⟩),
      ((F.map (homOfLE (n.le_add_right 1)).op).val.app ⟨X'⟩) x = ((F.obj ⟨n⟩).val.map φ.op) y := by
  have := hF n
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff] at this
  exact this X y

private noncomputable def preimage (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) :
    (n : ℕ) → ((Y : C) × (F.obj ⟨n⟩).val.obj ⟨Y⟩)
  | 0 => ⟨X, y⟩
  | (n + 1) => ⟨(exists_effectiveEpi hF n (preimage X y n).1 (preimage X y n).2).choose,
      (exists_effectiveEpi hF n
        (preimage X y n).1 (preimage X y n).2).choose_spec.choose_spec.choose_spec.choose⟩

private noncomputable def preimageStruct (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : struct F where
  X n := (preimage hF X y n).1
  x n := (preimage hF X y n).2
  map n := (exists_effectiveEpi hF n _ _).choose_spec.choose
  effectiveEpi n := (exists_effectiveEpi hF n _ _).choose_spec.choose_spec.choose
  w n := (exists_effectiveEpi hF n _ _).choose_spec.choose_spec.choose_spec.choose_spec

private noncomputable def preimageDiagram (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (preimageStruct hF X y).map

variable [HasLimitsOfShape ℕᵒᵖ C]

private noncomputable def cone (X : C) (y : (F.obj ⟨0⟩).val.obj ⟨X⟩) : Cone F where
  pt := ((coherentTopology C).yoneda).obj (limit (preimageDiagram hF X y))
  π := NatTrans.ofOpSequence
    (fun n ↦ (coherentTopology C).yoneda.map
      (limit.π _ ⟨n⟩) ≫ ((coherentTopology C).yonedaEquiv).symm ((preimageStruct hF X y).x n)) (by
    intro n
    simp only [Functor.const_obj_obj, homOfLE_leOfHom, Functor.const_obj_map, Category.id_comp,
      Category.assoc, ← limit.w (preimageDiagram hF X y) (homOfLE (n.le_add_right 1)).op,
      homOfLE_leOfHom, Functor.map_comp]
    simp [GrothendieckTopology.yonedaEquiv_symm_naturality_left,
      GrothendieckTopology.yonedaEquiv_symm_naturality_right,
      preimageDiagram, (preimageStruct hF X y).w n])

variable (h : ∀ (G : ℕᵒᵖ ⥤ C),
  (∀ n, EffectiveEpi (G.map (homOfLE (Nat.le_succ n)).op)) → EffectiveEpi (limit.π G ⟨0⟩))

include hF h hc in
lemma isLocallySurjective_π_app_zero_of_isLocallySurjective_map :
    Sheaf.IsLocallySurjective (c.π.app ⟨0⟩) := by
  rw [coherentTopology.isLocallySurjective_iff, regularTopology.isLocallySurjective_iff]
  intro X y
  have hh : EffectiveEpi (limit.π (preimageDiagram hF X y) ⟨0⟩) :=
    h _ fun n ↦ by simpa [preimageDiagram] using (preimageStruct hF X y).effectiveEpi n
  refine ⟨limit (preimageDiagram hF X y), limit.π (preimageDiagram hF X y) ⟨0⟩, hh,
    (coherentTopology C).yonedaEquiv (hc.lift (cone hF X y)),
    (?_ : (c.π.app (op 0)).val.app _ _ = _)⟩
  simp only [← (coherentTopology C).yonedaEquiv_comp, Functor.const_obj_obj, cone,
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
