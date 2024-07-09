/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Idempotents.Karoubi

#align_import category_theory.idempotents.biproducts from "leanprover-community/mathlib"@"362c2263e25ed3b9ed693773f32f91243612e1da"

/-!

# Biproducts in the idempotent completion of a preadditive category

In this file, we define an instance expressing that if `C` is an additive category
(i.e. is preadditive and has finite biproducts), then `Karoubi C` is also an additive category.

We also obtain that for all `P : Karoubi C` where `C` is a preadditive category `C`, there
is a canonical isomorphism `P ⊞ P.complement ≅ (toKaroubi C).obj P.X` in the category
`Karoubi C` where `P.complement` is the formal direct factor of `P.X` corresponding to
the idempotent endomorphism `𝟙 P.X - P.p`.

-/


noncomputable section

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

universe v

namespace CategoryTheory

namespace Idempotents

namespace Karoubi

variable {C : Type*} [Category.{v} C] [Preadditive C]

namespace Biproducts

/-- The `Bicone` used in order to obtain the existence of
the biproduct of a functor `J ⥤ Karoubi C` when the category `C` is additive. -/
@[simps]
def bicone [HasFiniteBiproducts C] {J : Type} [Finite J] (F : J → Karoubi C) : Bicone F where
  pt :=
    { X := biproduct fun j => (F j).X
      p := biproduct.map fun j => (F j).p
      idem := by
        ext
        simp only [assoc, biproduct.map_π, biproduct.map_π_assoc, idem] }
  π j :=
    { f := (biproduct.map fun j => (F j).p) ≫ Bicone.π _ j
      comm := by
        simp only [assoc, biproduct.bicone_π, biproduct.map_π, biproduct.map_π_assoc, (F j).idem] }
  ι j :=
    { f := biproduct.ι (fun j => (F j).X) j ≫ biproduct.map fun j => (F j).p
      comm := by simp only [biproduct.ι_map, assoc, idem_assoc] }
  ι_π j j' := by
    split_ifs with h
    · subst h
      simp only [biproduct.ι_map, biproduct.bicone_π, biproduct.map_π, eqToHom_refl,
        id_eq, hom_ext_iff, comp_f, assoc, bicone_ι_π_self_assoc, idem]
    · dsimp
      simp only [biproduct.ι_map, biproduct.map_π, hom_ext_iff, comp_f,
        assoc, biproduct.ι_π_ne_assoc _ h, zero_comp, comp_zero, instZero_zero]
#align category_theory.idempotents.karoubi.biproducts.bicone CategoryTheory.Idempotents.Karoubi.Biproducts.bicone

end Biproducts

theorem karoubi_hasFiniteBiproducts [HasFiniteBiproducts C] : HasFiniteBiproducts (Karoubi C) :=
  { out := fun n =>
      { has_biproduct := fun F => by
          apply hasBiproduct_of_total (Biproducts.bicone F)
          simp only [hom_ext_iff]
          refine biproduct.hom_ext' _ _ (fun j => ?_)
          simp only [Biproducts.bicone_pt_X, sum_hom, comp_f, Biproducts.bicone_π_f,
            biproduct.bicone_π, biproduct.map_π, Biproducts.bicone_ι_f, biproduct.ι_map, assoc,
            idem_assoc, id_eq, Biproducts.bicone_pt_p, comp_sum]
          rw [Finset.sum_eq_single j]
          · simp only [bicone_ι_π_self_assoc]
          · intro b _ hb
            simp only [biproduct.ι_π_ne_assoc _ hb.symm, zero_comp]
          · intro hj
            simp only [Finset.mem_univ, not_true] at hj } }
#align category_theory.idempotents.karoubi.karoubi_has_finite_biproducts CategoryTheory.Idempotents.Karoubi.karoubi_hasFiniteBiproducts

attribute [instance] karoubi_hasFiniteBiproducts

/-- `P.complement` is the formal direct factor of `P.X` given by the idempotent
endomorphism `𝟙 P.X - P.p` -/
@[simps]
def complement (P : Karoubi C) : Karoubi C where
  X := P.X
  p := 𝟙 _ - P.p
  idem := idem_of_id_sub_idem P.p P.idem
#align category_theory.idempotents.karoubi.complement CategoryTheory.Idempotents.Karoubi.complement

instance (P : Karoubi C) : HasBinaryBiproduct P P.complement :=
  hasBinaryBiproduct_of_total
    { pt := P.X
      fst := P.decompId_p
      snd := P.complement.decompId_p
      inl := P.decompId_i
      inr := P.complement.decompId_i
      inl_fst := P.decompId.symm
      inl_snd := by
        simp only [instZero_zero, hom_ext_iff, complement_X, comp_f,
          decompId_i_f, decompId_p_f, complement_p, comp_sub, comp_id, idem, sub_self]
      inr_fst := by
        simp only [instZero_zero, hom_ext_iff, complement_X, comp_f,
          decompId_i_f, complement_p, decompId_p_f, sub_comp, id_comp, idem, sub_self]
      inr_snd := P.complement.decompId.symm }
    (by
      simp only [id_eq, complement_X, comp_f,
        decompId_i_f, decompId_p_f, complement_p, instAdd_add, idem,
        comp_sub, comp_id, sub_comp, id_comp, sub_self, sub_zero, add_sub_cancel])

attribute [-simp] hom_ext_iff

/-- A formal direct factor `P : Karoubi C` of an object `P.X : C` in a
preadditive category is actually a direct factor of the image `(toKaroubi C).obj P.X`
of `P.X` in the category `Karoubi C` -/
def decomposition (P : Karoubi C) : P ⊞ P.complement ≅ (toKaroubi _).obj P.X where
  hom := biprod.desc P.decompId_i P.complement.decompId_i
  inv := biprod.lift P.decompId_p P.complement.decompId_p
  hom_inv_id := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, comp_id, biprod.lift_eq, comp_add, ← decompId_assoc,
        add_right_eq_self, ← assoc]
      refine (?_ =≫ _).trans zero_comp
      ext
      simp only [comp_f, toKaroubi_obj_X, decompId_i_f, decompId_p_f,
        complement_p, comp_sub, comp_id, idem, sub_self, instZero_zero]
    · rw [biprod.inr_desc_assoc, comp_id, biprod.lift_eq, comp_add, ← decompId_assoc,
        add_left_eq_self, ← assoc]
      refine (?_ =≫ _).trans zero_comp
      ext
      simp only [complement_X, comp_f, decompId_i_f, complement_p,
        decompId_p_f, sub_comp, id_comp, idem, sub_self, instZero_zero]
  inv_hom_id := by
    simp only [biprod.lift_desc, instAdd_add, toKaroubi_obj_X, comp_f,
      decompId_p_f, decompId_i_f, idem, complement_X, complement_p, comp_sub, comp_id,
      sub_comp, id_comp, sub_self, sub_zero, add_sub_cancel,
      id_eq, toKaroubi_obj_p]
#align category_theory.idempotents.karoubi.decomposition CategoryTheory.Idempotents.Karoubi.decomposition

end Karoubi

end Idempotents

end CategoryTheory
