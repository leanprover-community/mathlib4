import Mathlib.Algebra.Homology.DerivedCategory.Basic

open CategoryTheory Category Limits

variable {C : Type _} [Category C] [Abelian C]

namespace CochainComplex

open HomologicalComplex

variable (K L : CochainComplex C ℤ) (e : K ≅ L) (n : ℤ)

class IsStrictlyLE where
  isZero (i : ℤ) (hi : n < i) : IsZero (K.X i)

lemma isZero_of_isStrictlyLE (n i : ℤ) (hi : n < i) [K.IsStrictlyLE n] :
    IsZero (K.X i) := IsStrictlyLE.isZero i hi

class IsStrictlyGE where
  isZero (i : ℤ) (hi : i < n) : IsZero (K.X i)

lemma isZero_of_isStrictlyGE (i : ℤ) (hi : i < n) [K.IsStrictlyGE n] :
    IsZero (K.X i) := IsStrictlyGE.isZero i hi

class IsLE where
  isZero (i : ℤ) (hi : n < i) : IsZero (K.newHomology i)

lemma isZero_of_isLE (i : ℤ) (hi : n < i) [K.IsLE n] :
    IsZero (K.newHomology i) := IsLE.isZero i hi

class IsGE where
  isZero (i : ℤ) (hi : i < n) : IsZero (K.newHomology i)

lemma isZero_of_isGE (i : ℤ) (hi : i < n) [K.IsGE n] :
    IsZero (K.newHomology i) := IsGE.isZero i hi

instance (K : CochainComplex C ℤ) [K.IsStrictlyLE n] : K.IsLE n := ⟨fun i hi =>
  K.isZero_homology_of_isZero _ (K.isZero_of_isStrictlyLE n i hi)⟩

instance (K : CochainComplex C ℤ) [K.IsStrictlyGE n] : K.IsGE n := ⟨fun i hi =>
  K.isZero_homology_of_isZero _ (K.isZero_of_isStrictlyGE n i hi)⟩

lemma isStrictLE_of_LE (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyLE p] :
  K.IsStrictlyLE q := ⟨fun i hi => K.isZero_of_isStrictlyLE p i (by linarith)⟩

lemma isStrictLE_of_GE (p q : ℤ) (hpq : p ≤ q) [K.IsStrictlyGE q] :
  K.IsStrictlyGE p := ⟨fun i hi => K.isZero_of_isStrictlyGE q i (by linarith)⟩

lemma isLE_of_LE (p q : ℤ) (hpq : p ≤ q) [K.IsLE p] :
  K.IsLE q := ⟨fun i hi => K.isZero_of_isLE p i (by linarith)⟩

lemma isGE_of_GE (p q : ℤ) (hpq : p ≤ q) [K.IsGE q] :
  K.IsGE p := ⟨fun i hi => K.isZero_of_isGE q i (by linarith)⟩

variable {K L}

lemma isStrictlyLE_of_iso [K.IsStrictlyLE n] : L.IsStrictlyLE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isStrictlyLE n i hi)
    ((eval _ _ i).mapIso e.symm)⟩

lemma isStrictlyGE_of_iso [K.IsStrictlyGE n] : L.IsStrictlyGE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isStrictlyGE n i hi)
    ((eval _ _ i).mapIso e.symm)⟩

lemma isLE_of_iso [K.IsLE n] : L.IsLE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isLE n i hi)
    ((newHomologyFunctor _ _ i).mapIso e.symm)⟩

lemma isGE_of_iso [K.IsGE n] : L.IsGE n := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isGE n i hi)
    ((newHomologyFunctor _ _ i).mapIso e.symm)⟩

variable (K)

lemma isStrictlyLE_shift [K.IsStrictlyLE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyLE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isStrictlyLE n _ (by linarith)) (K.shiftFunctorObjXIso a i _ rfl)⟩

lemma isStrictlyGE_shift [K.IsStrictlyGE n] (a n' : ℤ) (h : a + n' = n) :
    (K⟦a⟧).IsStrictlyGE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isStrictlyGE n _ (by linarith)) (K.shiftFunctorObjXIso a i _ rfl)⟩

lemma isLE_shift [K.IsLE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsLE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isLE n (a+i) (by linarith))
    (((newHomologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)⟩

lemma isGE_shift [K.IsGE n] (a n' : ℤ) (h : a + n' = n) : (K⟦a⟧).IsGE n' := ⟨fun i hi =>
  IsZero.of_iso (K.isZero_of_isGE n (a+i) (by linarith))
    (((newHomologyFunctor C _ (0 : ℤ)).shiftIso a i _ rfl).app K)⟩

end CochainComplex


namespace DerivedCategory

variable (K L : DerivedCategory C) (n : ℤ)

class IsLE where
  isZero (i : ℤ) (hi : n < i) : IsZero ((homologyFunctor _ i).obj K)

lemma isZero_of_isLE (i : ℤ) (hi : n < i) [K.IsLE n] :
    IsZero ((homologyFunctor _ i).obj K) := IsLE.isZero i hi

class IsGE where
  isZero (i : ℤ) (hi : i < n) : IsZero ((homologyFunctor _ i).obj K)

lemma isZero_of_isGE (i : ℤ) (hi : i < n) [K.IsGE n] :
    IsZero ((homologyFunctor _ i).obj K) := IsGE.isZero i hi

instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsLE n] :
    (Q.obj K).IsLE n :=
  ⟨fun i hi => IsZero.of_iso (K.isZero_of_isLE n i hi) ((homologyFunctorFactors C i).app K)⟩

instance (K : CochainComplex C ℤ) (n : ℤ) [K.IsGE n] :
    (Q.obj K).IsGE n :=
  ⟨fun i hi => IsZero.of_iso (K.isZero_of_isGE n i hi) ((homologyFunctorFactors C i).app K)⟩

end DerivedCategory
