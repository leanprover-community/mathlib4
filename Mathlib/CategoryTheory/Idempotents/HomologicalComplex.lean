/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Idempotent completeness and homological complexes

This file contains simplifications lemmas for categories
`Karoubi (HomologicalComplex C c)` and the construction of an equivalence
of categories `Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`.

When the category `C` is idempotent complete, it is shown that
`HomologicalComplex (Karoubi C) c` is also idempotent complete.

-/


namespace CategoryTheory

open Category

variable {C : Type*} [Category C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}

namespace Idempotents

namespace Karoubi

namespace HomologicalComplex

variable {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) (n : ι)

@[simp, reassoc]
theorem p_comp_d : P.p.f n ≫ f.f.f n = f.f.f n :=
  HomologicalComplex.congr_hom (p_comp f) n

@[simp, reassoc]
theorem comp_p_d : f.f.f n ≫ Q.p.f n = f.f.f n :=
  HomologicalComplex.congr_hom (comp_p f) n

@[reassoc]
theorem p_comm_f : P.p.f n ≫ f.f.f n = f.f.f n ≫ Q.p.f n :=
  HomologicalComplex.congr_hom (p_comm f) n

variable (P)

@[simp, reassoc]
theorem p_idem : P.p.f n ≫ P.p.f n = P.p.f n :=
  HomologicalComplex.congr_hom P.idem n

end HomologicalComplex

end Karoubi

open Karoubi

namespace KaroubiHomologicalComplexEquivalence

namespace Functor

/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`,
on objects. -/
@[simps]
def obj (P : Karoubi (HomologicalComplex C c)) : HomologicalComplex (Karoubi C) c where
  X n :=
    ⟨P.X.X n, P.p.f n, by
      simpa only [HomologicalComplex.comp_f] using HomologicalComplex.congr_hom P.idem n⟩
  d i j := { f := P.p.f i ≫ P.X.d i j }
  shape i j hij := by simp only [hom_eq_zero_iff, P.X.shape i j hij, Limits.comp_zero]; aesop_cat

/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`,
on morphisms. -/
@[simps]
def map {P Q : Karoubi (HomologicalComplex C c)} (f : P ⟶ Q) : obj P ⟶ obj Q where
  f n :=
    { f := f.f.f n }

end Functor

/-- The functor `Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c`. -/
@[simps]
def functor : Karoubi (HomologicalComplex C c) ⥤ HomologicalComplex (Karoubi C) c where
  obj := Functor.obj
  map f := Functor.map f

namespace Inverse

/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`,
on objects -/
@[simps]
def obj (K : HomologicalComplex (Karoubi C) c) : Karoubi (HomologicalComplex C c) where
  X :=
    { X := fun n => (K.X n).X
      d := fun i j => (K.d i j).f
      shape := fun i j hij => hom_eq_zero_iff.mp (K.shape i j hij)
      d_comp_d' := fun i j k _ _ => by
        simpa only [comp_f] using hom_eq_zero_iff.mp (K.d_comp_d i j k) }
  p := { f := fun n => (K.X n).p }

/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`,
on morphisms -/
@[simps]
def map {K L : HomologicalComplex (Karoubi C) c} (f : K ⟶ L) : obj K ⟶ obj L where
  f :=
    { f := fun n => (f.f n).f
      comm' := fun i j hij => by simpa only [comp_f] using hom_ext_iff.mp (f.comm' i j hij) }

end Inverse

/-- The functor `HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c)`. -/
@[simps]
def inverse : HomologicalComplex (Karoubi C) c ⥤ Karoubi (HomologicalComplex C c) where
  obj := Inverse.obj
  map f := Inverse.map f

/-- The counit isomorphism of the equivalence
`Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps!]
def counitIso : inverse ⋙ functor ≅ 𝟭 (HomologicalComplex (Karoubi C) c) :=
  eqToIso (Functor.ext (fun P => HomologicalComplex.ext (by aesop_cat) (by simp))
    (by aesop_cat))

/-- The unit isomorphism of the equivalence
`Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps]
def unitIso : 𝟭 (Karoubi (HomologicalComplex C c)) ≅ functor ⋙ inverse where
  hom :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, HomologicalComplex.Hom.comm_assoc,
                  HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_p_d, Inverse.map_f_f,
          Functor.map_f_f, HomologicalComplex.p_comp_d] }
  inv :=
    { app := fun P =>
        { f :=
            { f := fun n => P.p.f n
              comm' := fun i j _ => by
                dsimp
                simp only [HomologicalComplex.Hom.comm, assoc, HomologicalComplex.p_idem] }
          comm := by
            ext n
            dsimp
            simp only [HomologicalComplex.p_idem] }
      naturality := fun P Q φ => by
        ext
        dsimp
        simp only [comp_f, HomologicalComplex.comp_f, Inverse.map_f_f, Functor.map_f_f,
          HomologicalComplex.comp_p_d, HomologicalComplex.p_comp_d] }
  hom_inv_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem, comp_f, HomologicalComplex.comp_f, _root_.id_eq]
  inv_hom_id := by
    ext
    dsimp
    simp only [HomologicalComplex.p_idem, comp_f, HomologicalComplex.comp_f, _root_.id_eq,
      Inverse.obj_p_f, Functor.obj_X_p]

end KaroubiHomologicalComplexEquivalence

variable (C) (c)

/-- The equivalence `Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c`. -/
@[simps]
def karoubiHomologicalComplexEquivalence :
    Karoubi (HomologicalComplex C c) ≌ HomologicalComplex (Karoubi C) c where
  functor := KaroubiHomologicalComplexEquivalence.functor
  inverse := KaroubiHomologicalComplexEquivalence.inverse
  unitIso := KaroubiHomologicalComplexEquivalence.unitIso
  counitIso := KaroubiHomologicalComplexEquivalence.counitIso

variable (α : Type*) [AddRightCancelSemigroup α] [One α]

/-- The equivalence `Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α`. -/
@[simps!]
def karoubiChainComplexEquivalence : Karoubi (ChainComplex C α) ≌ ChainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.down α)

/-- The equivalence `Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α`. -/
@[simps!]
def karoubiCochainComplexEquivalence :
    Karoubi (CochainComplex C α) ≌ CochainComplex (Karoubi C) α :=
  karoubiHomologicalComplexEquivalence C (ComplexShape.up α)

instance [IsIdempotentComplete C] : IsIdempotentComplete (HomologicalComplex C c) := by
  rw [isIdempotentComplete_iff_of_equivalence
      ((toKaroubiEquivalence C).mapHomologicalComplex c),
    ← isIdempotentComplete_iff_of_equivalence (karoubiHomologicalComplexEquivalence C c)]
  infer_instance

end Idempotents

end CategoryTheory
