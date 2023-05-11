/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.idempotents.biproducts
! leanprover-community/mathlib commit 362c2263e25ed3b9ed693773f32f91243612e1da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!

# Biproducts in the idempotent completion of a preadditive category

In this file, we define an instance expressing that if `C` is an additive category
(i.e. is preadditive and has finite biproducts), then `karoubi C` is also an additive category.

We also obtain that for all `P : karoubi C` where `C` is a preadditive category `C`, there
is a canonical isomorphism `P ⊞ P.complement ≅ (to_karoubi C).obj P.X` in the category
`karoubi C` where `P.complement` is the formal direct factor of `P.X` corresponding to
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

variable {C : Type _} [Category.{v} C] [Preadditive C]

namespace Biproducts

/-- The `bicone` used in order to obtain the existence of
the biproduct of a functor `J ⥤ karoubi C` when the category `C` is additive. -/
@[simps]
def bicone [HasFiniteBiproducts C] {J : Type} [Fintype J] (F : J → Karoubi C) : Bicone F
    where
  pt :=
    { pt := biproduct fun j => (F j).pt
      p := biproduct.map fun j => (F j).p
      idem := by
        ext j
        simp only [biproduct.ι_map_assoc, biproduct.ι_map]
        slice_lhs 1 2 => rw [(F j).idem] }
  π j :=
    { f := (biproduct.map fun j => (F j).p) ≫ Bicone.π _ j
      comm := by
        simp only [assoc, biproduct.bicone_π, biproduct.map_π, biproduct.map_π_assoc, (F j).idem] }
  ι j :=
    { f := bicone.ι _ j ≫ biproduct.map fun j => (F j).p
      comm := by
        rw [biproduct.ι_map, ← assoc, ← assoc, (F j).idem, assoc, biproduct.ι_map, ← assoc,
          (F j).idem] }
  ι_π j j' := by
    split_ifs
    · subst h
      simp only [assoc, idem, biproduct.map_π, biproduct.map_π_assoc, eq_to_hom_refl, id_eq,
        hom_ext, comp_f, biproduct.ι_π_self_assoc]
    ·
      simp only [biproduct.ι_π_ne_assoc _ h, assoc, biproduct.map_π, biproduct.map_π_assoc, hom_ext,
        comp_f, zero_comp, quiver.hom.add_comm_group_zero_f]
#align category_theory.idempotents.karoubi.biproducts.bicone CategoryTheory.Idempotents.Karoubi.Biproducts.bicone

end Biproducts

theorem karoubi_hasFiniteBiproducts [HasFiniteBiproducts C] : HasFiniteBiproducts (Karoubi C) :=
  {
    out := fun n =>
      {
        HasBiproduct := fun F => by
          classical
            apply has_biproduct_of_total (biproducts.bicone F)
            ext1
            ext1
            simp only [id_eq, comp_id, biproducts.bicone_X_p, biproduct.ι_map]
            rw [sum_hom, comp_sum, Finset.sum_eq_single j]
            rotate_left
            · intro j' h1 h2
              simp only [biproduct.ι_map, biproducts.bicone_ι_f, biproducts.bicone_π_f, assoc,
                comp_f, biproduct.map_π]
              slice_lhs 1 2 => rw [biproduct.ι_π]
              split_ifs
              · exfalso
                exact h2 h.symm
              · simp only [zero_comp]
            · intro h
              exfalso
              simpa only [Finset.mem_univ, not_true] using h
            · simp only [biproducts.bicone_π_f, comp_f, biproduct.ι_map, assoc,
                biproducts.bicone_ι_f, biproduct.map_π]
              slice_lhs 1 2 => rw [biproduct.ι_π]
              split_ifs
              swap
              · exfalso
                exact h rfl
              simp only [eq_to_hom_refl, id_comp, (F j).idem] } }
#align category_theory.idempotents.karoubi.karoubi_has_finite_biproducts CategoryTheory.Idempotents.Karoubi.karoubi_hasFiniteBiproducts

attribute [instance] karoubi_has_finite_biproducts

/-- `P.complement` is the formal direct factor of `P.X` given by the idempotent
endomorphism `𝟙 P.X - P.p` -/
@[simps]
def complement (P : Karoubi C) : Karoubi C
    where
  pt := P.pt
  p := 𝟙 _ - P.p
  idem := idem_of_id_sub_idem P.p P.idem
#align category_theory.idempotents.karoubi.complement CategoryTheory.Idempotents.Karoubi.complement

instance (P : Karoubi C) : HasBinaryBiproduct P P.complement :=
  hasBinaryBiproduct_of_total
    { pt := P.pt
      fst := P.decompId_p
      snd := P.complement.decompId_p
      inl := P.decompId_i
      inr := P.complement.decompId_i
      inl_fst := P.decompId.symm
      inl_snd :=
        by
        simp only [decomp_id_i_f, decomp_id_p_f, complement_p, comp_sub, comp_f, hom_ext,
          quiver.hom.add_comm_group_zero_f, P.idem]
        erw [comp_id, sub_self]
      inr_fst :=
        by
        simp only [decomp_id_i_f, complement_p, decomp_id_p_f, sub_comp, comp_f, hom_ext,
          quiver.hom.add_comm_group_zero_f, P.idem]
        erw [id_comp, sub_self]
      inr_snd := P.complement.decompId.symm }
    (by
      simp only [hom_ext, ← decomp_p, quiver.hom.add_comm_group_add_f, to_karoubi_map_f, id_eq,
        coe_p, complement_p, add_sub_cancel'_right])

/-- A formal direct factor `P : karoubi C` of an object `P.X : C` in a
preadditive category is actually a direct factor of the image `(to_karoubi C).obj P.X`
of `P.X` in the category `karoubi C` -/
def decomposition (P : Karoubi C) : P ⊞ P.complement ≅ (toKaroubi _).obj P.pt
    where
  Hom := biprod.desc P.decompId_i P.complement.decompId_i
  inv := biprod.lift P.decompId_p P.complement.decompId_p
  hom_inv_id' := by
    ext1
    · simp only [← assoc, biprod.inl_desc, comp_id, biprod.lift_eq, comp_add, ← decomp_id, id_comp,
        add_right_eq_self]
      convert zero_comp
      ext
      simp only [decomp_id_i_f, decomp_id_p_f, complement_p, comp_sub, comp_f,
        quiver.hom.add_comm_group_zero_f, P.idem]
      erw [comp_id, sub_self]
    · simp only [← assoc, biprod.inr_desc, biprod.lift_eq, comp_add, ← decomp_id, comp_id, id_comp,
        add_left_eq_self]
      convert zero_comp
      ext
      simp only [decomp_id_i_f, decomp_id_p_f, complement_p, sub_comp, comp_f,
        quiver.hom.add_comm_group_zero_f, P.idem]
      erw [id_comp, sub_self]
  inv_hom_id' := by
    rw [biprod.lift_desc]
    simp only [← decomp_p]
    ext
    dsimp only [complement, to_karoubi]
    simp only [quiver.hom.add_comm_group_add_f, add_sub_cancel'_right, id_eq]
#align category_theory.idempotents.karoubi.decomposition CategoryTheory.Idempotents.Karoubi.decomposition

end Karoubi

end Idempotents

end CategoryTheory

