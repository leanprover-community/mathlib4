import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.Algebra.Homology.HomotopyCategory

open CategoryTheory Category Limits


namespace HomologicalComplex

section

variable (C : Type _) [Category C] [HasZeroMorphisms C] {ι : Type _} (c : ComplexShape ι)

@[simps]
def shortComplexFunctor' (i j k : ι) : HomologicalComplex C c ⥤ ShortComplex C where
  obj K := ShortComplex.mk (K.d i j) (K.d j k) (K.d_comp_d i j k)
  map f :=
    { τ₁ := f.f i
      τ₂ := f.f j
      τ₃ := f.f k }

@[simps!]
noncomputable def shortComplexFunctor (i : ι) :=
  shortComplexFunctor' C c (c.prev i) i (c.next i)

variable {C c}
variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (ψ : L ⟶ M)

abbrev sc' (i j k : ι) := (shortComplexFunctor' C c i j k).obj K
noncomputable abbrev sc (i : ι) := (shortComplexFunctor C c i).obj K

abbrev HasHomology (i : ι) := (K.sc i).HasHomology

variable (i : ι) [K.HasHomology i] [L.HasHomology i] [M.HasHomology i]

noncomputable def newHomology := (K.sc i).homology
noncomputable def newCycles := (K.sc i).cycles
noncomputable def homologyπ : K.newCycles i ⟶ K.newHomology i := (K.sc i).homologyπ
noncomputable def iCycles : K.newCycles i ⟶ K.X i := (K.sc i).iCycles

variable {i}

noncomputable def liftCycles {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.newCycles i :=
  (K.sc i).liftCycles k (by subst hj ; exact hk)

@[reducible]
noncomputable def liftCycles' {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.Rel i j)
    (hk : k ≫ K.d i j = 0) : A ⟶ K.newCycles i :=
  K.liftCycles k j (c.next_eq' hj) hk

@[reassoc (attr := simp)]
lemma liftCycles_i {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) : K.liftCycles k j hj hk ≫ K.iCycles i = k := by
  dsimp [liftCycles, iCycles]
  simp

noncomputable def toCycles (i j : ι) [K.HasHomology j] :
  K.X i ⟶ K.newCycles j :=
  K.liftCycles (K.d i j) (c.next j) rfl (K.d_comp_d _ _ _)

variable (i)

@[reassoc (attr := simp)]
lemma iCycles_d (j : ι) : K.iCycles i ≫ K.d i j = 0 := by
  by_cases hij : c.Rel i j
  . obtain rfl := c.next_eq' hij
    exact (K.sc i).iCycles_g
  . rw [K.shape _ _ hij, comp_zero]

@[reassoc (attr := simp)]
lemma toCycles_i (i j : ι) [K.HasHomology j] :
    K.toCycles i j ≫ K.iCycles j = K.d i j :=
  liftCycles_i _ _ _ _ _

instance [K.HasHomology i] : Mono (K.iCycles i) := by
  dsimp only [iCycles]
  infer_instance

instance [K.HasHomology i] : Epi (K.homologyπ i) := by
  dsimp only [homologyπ]
  infer_instance

variable {i}

@[reassoc]
lemma liftCycles_homologyπ_eq_zero_of_boundary {A : C} (k : A ⟶ K.X i) (j : ι)
    (hj : c.next i = j) {i' : ι} (x : A ⟶ K.X i') (hx : k = x ≫ K.d i' i) :
    K.liftCycles k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) ≫ K.homologyπ i = 0 := by
  by_cases c.Rel i' i
  . obtain rfl := c.prev_eq' h
    exact (K.sc i).liftCycles_homologyπ_eq_zero_of_boundary _ x hx
  . have : liftCycles K k j hj (by rw [hx, assoc, K.d_comp_d, comp_zero]) = 0 := by
      rw [K.shape _ _ h, comp_zero] at hx
      rw [← cancel_mono (K.iCycles i), zero_comp, liftCycles_i, hx]
    rw [this, zero_comp]

@[reassoc (attr := simp)]
lemma toCycles_comp_homology_π (i j : ι) [K.HasHomology j]:
    K.toCycles i j ≫ K.homologyπ j = 0 :=
  K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

variable {K L M} (i)

noncomputable def homologyMap : K.newHomology i ⟶ L.newHomology i :=
  ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

variable (K)

@[simp]
lemma homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.homologyMap_id _

variable {K}

@[reassoc]
lemma homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i := by
  dsimp [homologyMap]
  rw [Functor.map_comp, ShortComplex.homologyMap_comp]

variable (K L)

@[simp]
lemma homologyMap_zero : homologyMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.homologyMap_zero _ _

variable {K L}

attribute [simp] homologyMap_comp

variable (C c)

@[simps]
noncomputable def newHomologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.newHomology i
  map f := homologyMap f i

/- TODO : adapt more of the homology of ShortComplex API to this situation, including the
dual versions cyclesCo, etc... -/

end

end HomologicalComplex

section

open HomologicalComplex CategoryTheory

variable {C : Type _} [Category C] [Preadditive C] {ι : Type _} {c : ComplexShape ι}
  [DecidableRel c.Rel] {K L : HomologicalComplex C c} {f g : K ⟶ L}

noncomputable def Homotopy.toShortComplex (ho : Homotopy f g) (i : ι) :
    ShortComplex.Homotopy ((shortComplexFunctor C c i).map f)
      ((shortComplexFunctor C c i).map g) where
  h₀ :=
    if c.Rel (c.prev i) i
    then ho.hom _ (c.prev (c.prev i)) ≫ L.d _ _
    else f.f _ - g.f _ - K.d _ i ≫ ho.hom i _
  h₁ := ho.hom _ _
  h₂ := ho.hom _ _
  h₃ :=
    if c.Rel i (c.next i)
    then K.d _ _ ≫ ho.hom (c.next (c.next i)) _
    else f.f _ - g.f _ - ho.hom _ i ≫ L.d _ _
  h₀_f := by
    split_ifs with h
    . dsimp
      simp only [assoc, d_comp_d, comp_zero]
    . dsimp
      rw [L.shape _ _ h, comp_zero]
  g_h₃ := by
    split_ifs with h
    . dsimp
      simp
    . dsimp
      rw [K.shape _ _ h, zero_comp]
  comm₁ := by
    dsimp
    split_ifs with h
    . rw [ho.comm (c.prev i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => d K (c.prev i) j ≫ ho.hom j (c.prev i)) (c.next_eq' h)]
    . abel
  comm₂ := ho.comm i
  comm₃ := by
    dsimp
    split_ifs with h
    . rw [ho.comm (c.next i)]
      dsimp [dFrom, dTo, fromNext, toPrev]
      rw [congr_arg (fun j => ho.hom (c.next i) j ≫ L.d j (c.next i)) (c.prev_eq' h)]
    . abel

lemma Homotopy.homologyMap_eq (ho : Homotopy f g) (i : ι) [K.HasHomology i] [L.HasHomology i] :
    homologyMap f i = homologyMap g i :=
  ShortComplex.Homotopy.congr_homologyMap (ho.toShortComplex i)

noncomputable def HomotopyEquiv.toHomologyIso (h : HomotopyEquiv K L) (i : ι)
  [K.HasHomology i] [L.HasHomology i] : K.newHomology i ≅ L.newHomology i where
  hom := homologyMap h.hom i
  inv := homologyMap h.inv i
  hom_inv_id := by rw [← homologyMap_comp, h.homotopyHomInvId.homologyMap_eq, homologyMap_id]
  inv_hom_id := by rw [← homologyMap_comp, h.homotopyInvHomId.homologyMap_eq, homologyMap_id]

namespace HomologicalComplex

variable (φ ψ : K ⟶ L) (i : ι) [K.HasHomology i] [L.HasHomology i]

@[simp]
lemma homologyMap_neg : homologyMap (-φ) i = -homologyMap φ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_neg]
  rfl

@[simp]
lemma homologyMap_add : homologyMap (φ + ψ) i = homologyMap φ i + homologyMap ψ i := by
  dsimp [homologyMap]
  rw [← ShortComplex.homologyMap_add]
  rfl

instance [CategoryWithHomology C] : (newHomologyFunctor C c i).Additive where

end HomologicalComplex

namespace HomotopyCategory

variable (C) (c)
variable [CategoryWithHomology C]

noncomputable def newHomologyFunctor (i : ι) : HomotopyCategory C c ⥤ C :=
  CategoryTheory.Quotient.lift _ (HomologicalComplex.newHomologyFunctor C c i) (by
    rintro K L f g ⟨h⟩
    exact h.homologyMap_eq i)

noncomputable def newHomologyFunctorFactors (i : ι) :
    quotient C c ⋙ newHomologyFunctor C c i ≅
      HomologicalComplex.newHomologyFunctor C c i :=
  Quotient.lift.isLift _ _ _

-- this is to prevent any abuse of defeq
attribute [irreducible] newHomologyFunctor newHomologyFunctorFactors

instance : (newHomologyFunctor C c i).Additive := by
  have := Functor.additive_of_iso (newHomologyFunctorFactors C c i).symm
  exact Functor.additive_of_full_essSurj_comp (quotient C c) _

end HomotopyCategory

end
