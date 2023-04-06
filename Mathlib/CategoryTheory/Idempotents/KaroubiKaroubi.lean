/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.idempotents.karoubi_karoubi
! leanprover-community/mathlib commit 31019c2504b17f85af7e0577585fad996935a317
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotence of the Karoubi envelope

In this file, we construct the equivalence of categories
`karoubi_karoubi.equivalence C : karoubi C ≌ karoubi (karoubi C)` for any category `C`.

-/


open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

namespace Idempotents

namespace KaroubiKaroubi

variable (C : Type _) [Category C]

/-- The canonical functor `karoubi (karoubi C) ⥤ karoubi C` -/
@[simps]
def inverse : Karoubi (Karoubi C) ⥤ Karoubi C
    where
  obj P := ⟨P.pt.pt, P.p.f, by simpa only [hom_ext] using P.idem⟩
  map P Q f := ⟨f.f.f, by simpa only [hom_ext] using f.comm⟩
#align category_theory.idempotents.karoubi_karoubi.inverse CategoryTheory.Idempotents.KaroubiKaroubi.inverse

instance [Preadditive C] : Functor.Additive (inverse C) where

/-- The unit isomorphism of the equivalence -/
@[simps]
def unitIso : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C :=
  eqToIso (Functor.ext (by tidy) (by tidy))
#align category_theory.idempotents.karoubi_karoubi.unit_iso CategoryTheory.Idempotents.KaroubiKaroubi.unitIso

/-- The counit isomorphism of the equivalence -/
@[simps]
def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C))
    where
  Hom :=
    { app := fun P =>
        { f :=
            { f := P.p.1
              comm := by
                have h := P.idem
                simp only [hom_ext, comp_f] at h
                erw [← assoc, h, comp_p] }
          comm := by
            have h := P.idem
            simp only [hom_ext, comp_f] at h⊢
            erw [h, h] }
      naturality' := fun P Q f => by simpa only [hom_ext] using (p_comm f).symm }
  inv :=
    { app := fun P =>
        { f :=
            { f := P.p.1
              comm := by
                have h := P.idem
                simp only [hom_ext, comp_f] at h
                erw [h, p_comp] }
          comm := by
            have h := P.idem
            simp only [hom_ext, comp_f] at h⊢
            erw [h, h] }
      naturality' := fun P Q f => by simpa only [hom_ext] using (p_comm f).symm }
  hom_inv_id' := by
    ext P
    simpa only [hom_ext, id_eq] using P.idem
  inv_hom_id' := by
    ext P
    simpa only [hom_ext, id_eq] using P.idem
#align category_theory.idempotents.karoubi_karoubi.counit_iso CategoryTheory.Idempotents.KaroubiKaroubi.counitIso

/-- The equivalence `karoubi C ≌ karoubi (karoubi C)` -/
@[simps]
def equivalence : Karoubi C ≌ Karoubi (Karoubi C)
    where
  Functor := toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C
#align category_theory.idempotents.karoubi_karoubi.equivalence CategoryTheory.Idempotents.KaroubiKaroubi.equivalence

instance equivalence.additive_functor [Preadditive C] : Functor.Additive (equivalence C).Functor :=
  by
  dsimp
  infer_instance
#align category_theory.idempotents.karoubi_karoubi.equivalence.additive_functor CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_functor

instance equivalence.additive_inverse [Preadditive C] : Functor.Additive (equivalence C).inverse :=
  by
  dsimp
  infer_instance
#align category_theory.idempotents.karoubi_karoubi.equivalence.additive_inverse CategoryTheory.Idempotents.KaroubiKaroubi.equivalence.additive_inverse

end KaroubiKaroubi

end Idempotents

end CategoryTheory

