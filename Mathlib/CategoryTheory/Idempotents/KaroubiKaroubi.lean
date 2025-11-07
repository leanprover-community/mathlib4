/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotence of the Karoubi envelope

In this file, we construct the equivalence of categories
`KaroubiKaroubi.equivalence C : Karoubi C ≌ Karoubi (Karoubi C)` for any category `C`.

-/


open CategoryTheory.Category

open CategoryTheory.Idempotents.Karoubi

namespace CategoryTheory

namespace Idempotents

namespace KaroubiKaroubi

variable (C : Type*) [Category C]

@[reassoc (attr := simp)]
lemma idem_f (P : Karoubi (Karoubi C)) : P.p.f ≫ P.p.f = P.p.f := by
  simpa only [hom_ext_iff, comp_f] using P.idem

@[reassoc]
lemma p_comm_f {P Q : Karoubi (Karoubi C)} (f : P ⟶ Q) : P.p.f ≫ f.f.f = f.f.f ≫ Q.p.f := by
  simpa only [hom_ext_iff, comp_f] using p_comm f

/-- The canonical functor `Karoubi (Karoubi C) ⥤ Karoubi C` -/
@[simps]
def inverse : Karoubi (Karoubi C) ⥤ Karoubi C where
  obj P := ⟨P.X.X, P.p.f, by simpa only [hom_ext_iff] using P.idem⟩
  map f := ⟨f.f.f, by simpa only [hom_ext_iff] using f.comm⟩

instance [Preadditive C] : Functor.Additive (inverse C) where

/-- The unit isomorphism of the equivalence -/
@[simps!]
def unitIso : 𝟭 (Karoubi C) ≅ toKaroubi (Karoubi C) ⋙ inverse C :=
  eqToIso (Functor.ext (by cat_disch) (by simp))

attribute [local simp] p_comm_f in
/-- The counit isomorphism of the equivalence -/
@[simps]
def counitIso : inverse C ⋙ toKaroubi (Karoubi C) ≅ 𝟭 (Karoubi (Karoubi C)) where
  hom := { app := fun P => { f := { f := P.p.1 } } }
  inv := { app := fun P => { f := { f := P.p.1 }  } }

/-- The equivalence `Karoubi C ≌ Karoubi (Karoubi C)` -/
@[simps]
def equivalence : Karoubi C ≌ Karoubi (Karoubi C) where
  functor := toKaroubi (Karoubi C)
  inverse := KaroubiKaroubi.inverse C
  unitIso := KaroubiKaroubi.unitIso C
  counitIso := KaroubiKaroubi.counitIso C

instance equivalence.additive_functor [Preadditive C] :
    Functor.Additive (equivalence C).functor where

instance equivalence.additive_inverse [Preadditive C] :
    Functor.Additive (equivalence C).inverse where

end KaroubiKaroubi

end Idempotents

end CategoryTheory
