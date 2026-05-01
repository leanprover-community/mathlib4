/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Normal subgroup objects

In this file we define normal subgroups of group objects in a cartesian monoidal category as
a predicate on morphisms. A morphism `φ : H ⟶ G` of group objects is normal if it is mono, a
monoid morphism and the conjugation map `(g, h) ↦ g * h * g⁻¹` factors through `φ`.

## Main declarations

- `CategoryTheory.IsMonHom.Normal`: The predicate on morphisms to be a normal monoid morphism.
- `CategoryTheory.IsMonHom.normal_iff_normal_monoidHom`: A monoid morphism `H ⟶ G` that is mono
  is normal if and only if for every `X`, the image of `H(X)` in `G(X)` is a normal subgroup.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

open MonObj GrpObj MonoidalCategory CartesianMonoidalCategory

/-- A morphism `φ : H ⟶ G` of additive group objects is a normal monoid homomorphism if it is a
monoid homomorphism that is mono and such that the conjugation map `(g, h) ↦ g + h - g`
factors through `φ`. -/
class IsAddMonHom.Normal {G H : C} [AddGrpObj G] [AddGrpObj H] (φ : H ⟶ G) : Prop where
  mono : Mono φ := by infer_instance
  isAddMonHom : IsAddMonHom φ := by infer_instance
  exists_comp_eq_addConj : ∃ ψ : G ⊗ H ⟶ H, ψ ≫ φ = G ◁ φ ≫ AddGrpObj.addConj G

attribute [instance] IsAddMonHom.Normal.mono IsAddMonHom.Normal.isAddMonHom

namespace IsMonHom

variable {G H K : C} [GrpObj G] [GrpObj H] [GrpObj K] {φ : H ⟶ G}

/-- A morphism `φ : H ⟶ G` of group objects is a normal monoid homomorphism if it is a
monoid homomorphism that is mono and such that the conjugation map `(g, h) ↦ g * h * g⁻¹`
factors through `φ`. -/
@[to_additive]
class Normal (φ : H ⟶ G) : Prop where
  mono : Mono φ := by infer_instance
  isMonHom : IsMonHom φ := by infer_instance
  exists_comp_eq_conj (φ) : ∃ ψ : G ⊗ H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G

attribute [instance] Normal.mono Normal.isMonHom

@[to_additive]
instance : Normal (𝟙 G) where
  exists_comp_eq_conj := by cat_disch

@[to_additive]
instance : Normal η[G] where
  exists_comp_eq_conj := by
    use toUnit _
    simp [conj, comp_mul, comp_inv, toUnit_unique _ (toUnit _), ← Hom.one_def]

@[to_additive]
lemma isNormalHom_iff [IsMonHom φ] [Mono φ] : Normal φ ↔ ∃ ψ : G ⊗ H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G :=
  ⟨fun h ↦ h.exists_comp_eq_conj, fun h ↦ ⟨‹_›, ‹_›, h⟩⟩

/-- If `φ` is mono, it is a normal group homomorphism if and only if for all `X` the image of
`H(X)` in `G(X)` is a normal subgroup. -/
@[to_additive]
theorem normal_iff_normal_monoidHom [IsMonHom φ] [Mono φ] :
    Normal φ ↔ ∀ (X : C), (monoidHom φ X).range.Normal := by
  rw [isNormalHom_iff]
  refine ⟨?_, ?_⟩
  · intro ⟨ψ, hψ⟩ X
    constructor
    rintro - ⟨x, rfl⟩ z
    use lift z x ≫ ψ
    simp [hψ]
  · intro hnormal
    have (X : C) (g : X ⟶ G) (h : X ⟶ H) : ∃ (h' : X ⟶ H), h' ≫ φ = g * h ≫ φ * g⁻¹ :=
      (hnormal X).conj_mem (h ≫ φ) (by simp) g
    choose h' hh' using this
    refine ⟨Yoneda.fullyFaithful.preimage ?_, ?_⟩
    · refine ⟨fun X ↦ ↾fun x ↦ h' _ (x ≫ fst _ _) (x ≫ snd _ _), fun X Y f ↦ ?_⟩
      ext
      rw [← cancel_mono φ]
      simp [hh', comp_mul, comp_inv]
    · refine yoneda.map_injective ?_
      ext
      simp [hh', conj, comp_mul, comp_inv]

instance (priority := low) [BraidedCategory C] [IsCommMonObj G] [IsMonHom φ] [Mono φ] :
    Normal φ := by
  simp [isNormalHom_iff, conj_eq_snd_of_isCommMonObj]

end CategoryTheory.IsMonHom
