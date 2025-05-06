/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.CochainComplexMinus
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Filtration of a cochain complex

-/

open CategoryTheory Category Limits

namespace CochainComplex

variable {C : Type*} [Category C] [Abelian C]
  (K L : CochainComplex C ℤ)

instance (n : ℤ) : Mono (K.ιTruncLE n) := by
  dsimp only [ιTruncLE]
  infer_instance

namespace truncLELEIsoOfLE

lemma isIso (n m : ℤ) (h : n ≤ m := by omega) :
    IsIso ((K.truncLE n).ιTruncLE m) := by
  rw [isIso_ιTruncLE_iff]
  exact isStrictlyLE_of_le _ _ _ h

end truncLELEIsoOfLE

@[simps! hom]
noncomputable def truncLELEIsoOfLE (n m : ℤ) (h : n ≤ m := by omega) :
    (K.truncLE n).truncLE m ≅ K.truncLE n :=
  have := truncLELEIsoOfLE.isIso K n m h
  asIso ((K.truncLE n).ιTruncLE m)

noncomputable def truncLEMapOfLE (n m : ℤ) (h : n ≤ m := by omega) :
    K.truncLE n ⟶ K.truncLE m :=
  (K.truncLELEIsoOfLE n m h).inv ≫
    HomologicalComplex.truncLEMap
      (K.ιTruncLE n) (ComplexShape.embeddingUpIntLE m)

@[reassoc (attr := simp)]
lemma truncLEMapOfLE_ι (n m : ℤ) (h : n ≤ m) :
    K.truncLEMapOfLE n m h ≫ K.ιTruncLE m = K.ιTruncLE n := by
  dsimp only [truncLEMapOfLE]
  rw [← cancel_epi (K.truncLELEIsoOfLE n m h).hom, assoc,
    ιTruncLE_naturality, Iso.hom_inv_id_assoc]
  simp only [truncLELEIsoOfLE_hom]

variable {K L} in
@[reassoc (attr := simp)]
lemma truncLEMapOfLE_naturality (f : K ⟶ L) (n m : ℤ) (h : n ≤ m) :
    truncLEMap f n ≫ L.truncLEMapOfLE n m h =
      K.truncLEMapOfLE n m h ≫ truncLEMap f m := by
  simp [← cancel_mono (L.ιTruncLE _)]

@[simps]
noncomputable def filtrationLE : ℤ ⥤ CochainComplex C ℤ where
  obj n := K.truncLE n
  map f := K.truncLEMapOfLE _ _ (leOfHom f)
  map_id _ := by simp [← cancel_mono (K.ιTruncLE _)]
  map_comp _ _ := by simp [← cancel_mono (K.ιTruncLE _), assoc]

noncomputable def filtrationLEMinus : ℤ ⥤ CochainComplex.Minus C :=
  ObjectProperty.lift _ K.filtrationLE
    (fun n ↦ ⟨n, by dsimp; infer_instance⟩)

@[simp]
lemma ι_obj_filtrationLEMinus_obj (n : ℤ) :
    (Minus.ι _).obj (K.filtrationLEMinus.obj n) = K.truncLE n := rfl

@[simp]
lemma ι_map_filtrationLEMinus_map {n m : ℤ} (h : n ⟶ m) :
    (Minus.ι _).map (K.filtrationLEMinus.map h) =
      K.filtrationLE.map h := rfl

@[simps!]
noncomputable def filtrationLEMinusCompιIso :
    K.filtrationLEMinus ⋙ Minus.ι _ ≅ K.filtrationLE := Iso.refl _

@[simps]
noncomputable def filtrationLECocone :
    Cocone K.filtrationLE where
  pt := K
  ι := { app := K.ιTruncLE }

noncomputable def isColimitFiltrationLECocone :
    IsColimit K.filtrationLECocone :=
  HomologicalComplex.isColimitOfEval _ _ (fun n ↦
    isColimitOfIsEventuallyConstant _ (n + 1) (by
      intro m h
      replace h := leOfHom h
      exact isIso_ιTruncLE_f _ _ _ (by omega)))

variable (C) in
@[simps]
noncomputable def filtrationLEFunctor :
    CochainComplex C ℤ ⥤ ℤ ⥤ CochainComplex C ℤ where
  obj K := K.filtrationLE
  map {K L} f := { app n := truncLEMap f n }

variable {K L} in
noncomputable def mapFiltrationLEMinus (f : K ⟶ L) :
    K.filtrationLEMinus ⟶ L.filtrationLEMinus :=
  ((Minus.fullyFaithfulι C).whiskeringRight ℤ).preimage ((filtrationLEFunctor C).map f)

variable {K L} in
@[simp]
lemma ι_map_mapFiltrationLEMinus_app (f : K ⟶ L) (n : ℤ) :
    (Minus.ι _).map ((mapFiltrationLEMinus f).app n) = truncLEMap f n := rfl

variable (C)

@[simps]
noncomputable def filtrationLEMinusFunctor :
    CochainComplex C ℤ ⥤ ℤ ⥤ Minus C where
  obj K := K.filtrationLEMinus
  map {K L} f := mapFiltrationLEMinus f
  map_id K := by
    ext n : 2
    apply (Minus.ι _).map_injective
    simp
  map_comp _ _ := by
    ext n : 2
    apply (Minus.ι _).map_injective
    simp

@[simps!]
noncomputable def filtrationLEMinusFunctorCompWhiskeringRightObjιIso :
  filtrationLEMinusFunctor C ⋙ (whiskeringRight _ _ _).obj (Minus.ι C) ≅
    filtrationLEFunctor C := Iso.refl _

noncomputable def filtrationLEFunctorCompColimIso [HasColimitsOfShape ℤ C] :
    filtrationLEFunctor C ⋙ colim ≅ 𝟭 (CochainComplex C ℤ) :=
  NatIso.ofComponents
    (fun K ↦ IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      K.isColimitFiltrationLECocone) (fun f ↦ colimit.hom_ext (by simp))

@[reassoc (attr := simp)]
lemma ι_filtrationLEFunctorCompColimIso_hom_app (n : ℤ) [HasColimitsOfShape ℤ C] :
    colimit.ι K.filtrationLE n ≫ (filtrationLEFunctorCompColimIso C).hom.app K =
      K.ιTruncLE n := by
  simp [filtrationLEFunctorCompColimIso]

end CochainComplex
