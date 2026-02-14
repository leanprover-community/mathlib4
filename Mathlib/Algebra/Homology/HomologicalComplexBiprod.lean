/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

/-!
# TODO: Mathlib.Algebra.Homology.HomologicalComplexBiprod
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Additive

/-! Binary biproducts of homological complexes

In this file, it is shown that if two homological complex `K` and `L` in
a preadditive category are such that for all `i : ι`, the binary biproduct
`K.X i ⊞ L.X i` exists, then `K ⊞ L` exists, and there is an isomorphism
`biprodXIso K L i : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`.

-/

@[expose] public section
open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

instance (i : ι) : HasBinaryBiproduct ((eval C c i).obj K) ((eval C c i).obj L) := by
  dsimp [eval]
  infer_instance

instance (i : ι) : HasLimit ((pair K L) ⋙ (eval C c i)) := by
  have e : _ ≅ pair (K.X i) (L.X i) := diagramIsoPair (pair K L ⋙ eval C c i)
  exact hasLimit_of_iso e.symm

instance (i : ι) : HasColimit ((pair K L) ⋙ (eval C c i)) := by
  have e : _ ≅ pair (K.X i) (L.X i) := diagramIsoPair (pair K L ⋙ eval C c i)
  exact hasColimit_of_iso e

instance : HasBinaryBiproduct K L := HasBinaryBiproduct.of_hasBinaryProduct _ _

instance (i : ι) : PreservesBinaryBiproduct K L (eval C c i) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

/-- The canonical isomorphism `(K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`. -/
noncomputable def biprodXIso (i : ι) : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i) :=
  (eval C c i).mapBiprod K L

@[reassoc (attr := simp)]
lemma inl_biprodXIso_inv (i : ι) :
    biprod.inl ≫ (biprodXIso K L i).inv = (biprod.inl : K ⟶ K ⊞ L).f i := by
  simp [biprodXIso]

@[reassoc (attr := simp)]
lemma inr_biprodXIso_inv (i : ι) :
    biprod.inr ≫ (biprodXIso K L i).inv = (biprod.inr : L ⟶ K ⊞ L).f i := by
  simp [biprodXIso]

@[reassoc (attr := simp)]
lemma biprodXIso_hom_fst (i : ι) :
    (biprodXIso K L i).hom ≫ biprod.fst = (biprod.fst : K ⊞ L ⟶ K).f i := by
  simp [biprodXIso]

@[reassoc (attr := simp)]
lemma biprodXIso_hom_snd (i : ι) :
    (biprodXIso K L i).hom ≫ biprod.snd = (biprod.snd : K ⊞ L ⟶ L).f i := by
  simp [biprodXIso]

@[reassoc (attr := simp)]
lemma biprod_inl_fst_f (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = 𝟙 _ := by
  rw [← comp_f, biprod.inl_fst, id_f]

@[reassoc (attr := simp)]
lemma biprod_inl_snd_f (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = 0 := by
  rw [← comp_f, biprod.inl_snd, zero_f]

@[reassoc (attr := simp)]
lemma biprod_inr_fst_f (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = 0 := by
  rw [← comp_f, biprod.inr_fst, zero_f]

@[reassoc (attr := simp)]
lemma biprod_inr_snd_f (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = 𝟙 _ := by
  rw [← comp_f, biprod.inr_snd, id_f]

variable {K L}
variable {M : HomologicalComplex C c}

@[reassoc (attr := simp)]
lemma biprod_inl_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.desc α β).f i = α.f i := by
  rw [← comp_f, biprod.inl_desc]

@[reassoc (attr := simp)]
lemma biprod_inr_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.desc α β).f i = β.f i := by
  rw [← comp_f, biprod.inr_desc]

@[reassoc (attr := simp)]
lemma biprod_lift_fst_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) :
    (biprod.lift α β).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = α.f i := by
  rw [← comp_f, biprod.lift_fst]

@[reassoc (attr := simp)]
lemma biprod_lift_snd_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) :
    (biprod.lift α β).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = β.f i := by
  rw [← comp_f, biprod.lift_snd]

end HomologicalComplex
