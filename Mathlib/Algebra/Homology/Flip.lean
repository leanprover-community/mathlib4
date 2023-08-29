/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.HomologicalComplex

#align_import algebra.homology.flip from "leanprover-community/mathlib"@"ff511590476ef357b6132a45816adc120d5d7b1d"

/-!
# Flip a complex of complexes

For now we don't have double complexes as a distinct thing,
but we can model them as complexes of complexes.

Here we show how to flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.

-/


universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {ι : Type*} {c : ComplexShape ι} {ι' : Type*} {c' : ComplexShape ι'}

/-- Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
def flipObj (C : HomologicalComplex (HomologicalComplex V c) c') :
    HomologicalComplex (HomologicalComplex V c') c where
  X i :=
    { X := fun j => (C.X j).X i
      d := fun j j' => (C.d j j').f i
      shape := fun j j' w => by
        simp_all only [shape, zero_f]
        -- 🎉 no goals
      d_comp_d' := fun j₁ j₂ j₃ _ _ => congr_hom (C.d_comp_d j₁ j₂ j₃) i }
  d i i' :=
    { f := fun j => (C.X j).d i i'
      comm' := fun j j' _ => ((C.d j j').comm i i').symm }
  shape i i' w := by
    ext j
    -- ⊢ Hom.f ((fun i i' => Hom.mk fun j => d (X C j) i i') i i') j = Hom.f 0 j
    exact (C.X j).shape i i' w
    -- 🎉 no goals
#align homological_complex.flip_obj HomologicalComplex.flipObj

variable (V c c')

/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
def flip :
    HomologicalComplex (HomologicalComplex V c) c' ⥤ HomologicalComplex (HomologicalComplex V c') c
    where
  obj C := flipObj C
  map {C D} f :=
    { f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := fun j j' _ => congr_hom (f.comm j j') i } }
#align homological_complex.flip HomologicalComplex.flip

/-- Auxiliary definition for `HomologicalComplex.flipEquivalence`. -/
@[simps!]
def flipEquivalenceUnitIso :
    𝟭 (HomologicalComplex (HomologicalComplex V c) c') ≅ flip V c c' ⋙ flip V c' c :=
  NatIso.ofComponents
    (fun C =>
      { hom :=
          { f := fun i => { f := fun j => 𝟙 ((C.X i).X j) }
            comm' := fun i j _ => by
              ext
              -- ⊢ Hom.f ((fun i => Hom.mk fun j => 𝟙 (X (X C i) j)) i ≫ d ((flip V c c' ⋙ flip …
              dsimp
              -- ⊢ 𝟙 (X (X C i) i✝) ≫ Hom.f (d C i j) i✝ = Hom.f (d C i j) i✝ ≫ 𝟙 (X (X C j) i✝)
              simp only [Category.id_comp, Category.comp_id] }
              -- 🎉 no goals
        inv :=
          { f := fun i => { f := fun j => 𝟙 ((C.X i).X j) }
            comm' := fun i j _ => by
              ext
              -- ⊢ Hom.f ((fun i => Hom.mk fun j => 𝟙 (X (X C i) j)) i ≫ d ((𝟭 (HomologicalComp …
              dsimp
              -- ⊢ 𝟙 (X (X C i) i✝) ≫ Hom.f (d C i j) i✝ = Hom.f (d C i j) i✝ ≫ 𝟙 (X (X C j) i✝)
              simp only [Category.id_comp, Category.comp_id] } })
              -- 🎉 no goals
    fun {X Y} f => by
      ext
      -- ⊢ Hom.f (Hom.f ((𝟭 (HomologicalComplex (HomologicalComplex V c) c')).map f ≫ ( …
      dsimp
      -- ⊢ Hom.f (Hom.f f i✝¹) i✝ ≫ 𝟙 (HomologicalComplex.X (HomologicalComplex.X Y i✝¹ …
      simp only [Category.id_comp, Category.comp_id]
      -- 🎉 no goals
#align homological_complex.flip_equivalence_unit_iso HomologicalComplex.flipEquivalenceUnitIso

/-- Auxiliary definition for `HomologicalComplex.flipEquivalence`. -/
@[simps!]
def flipEquivalenceCounitIso :
    flip V c' c ⋙ flip V c c' ≅ 𝟭 (HomologicalComplex (HomologicalComplex V c') c) :=
  NatIso.ofComponents
    (fun C =>
      { hom :=
          { f := fun i => { f := fun j => 𝟙 ((C.X i).X j) }
            comm' := fun i j _ => by
              ext
              -- ⊢ Hom.f ((fun i => Hom.mk fun j => 𝟙 (X (X C i) j)) i ≫ d ((𝟭 (HomologicalComp …
              dsimp
              -- ⊢ 𝟙 (X (X C i) i✝) ≫ Hom.f (d C i j) i✝ = Hom.f (d C i j) i✝ ≫ 𝟙 (X (X C j) i✝)
              simp only [Category.id_comp, Category.comp_id] }
              -- 🎉 no goals
        inv :=
          { f := fun i => { f := fun j => 𝟙 ((C.X i).X j) }
            comm' := fun i j _ => by
              ext
              -- ⊢ Hom.f ((fun i => Hom.mk fun j => 𝟙 (X (X C i) j)) i ≫ d ((flip V c' c ⋙ flip …
              dsimp
              -- ⊢ 𝟙 (X (X C i) i✝) ≫ Hom.f (d C i j) i✝ = Hom.f (d C i j) i✝ ≫ 𝟙 (X (X C j) i✝)
              simp only [Category.id_comp, Category.comp_id] } })
              -- 🎉 no goals
    fun {X Y} f => by
      ext
      -- ⊢ Hom.f (Hom.f ((flip V c' c ⋙ flip V c c').map f ≫ ((fun C => Iso.mk (Hom.mk  …
      dsimp
      -- ⊢ Hom.f (Hom.f f i✝¹) i✝ ≫ 𝟙 (HomologicalComplex.X (HomologicalComplex.X Y i✝¹ …
      simp only [Category.id_comp, Category.comp_id]
      -- 🎉 no goals
#align homological_complex.flip_equivalence_counit_iso HomologicalComplex.flipEquivalenceCounitIso

/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
def flipEquivalence :
    HomologicalComplex (HomologicalComplex V c) c' ≌ HomologicalComplex (HomologicalComplex V c') c
    where
  functor := flip V c c'
  inverse := flip V c' c
  unitIso := flipEquivalenceUnitIso V c c'
  counitIso := flipEquivalenceCounitIso V c c'
#align homological_complex.flip_equivalence HomologicalComplex.flipEquivalence

end HomologicalComplex
