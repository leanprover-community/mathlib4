import Mathlib.Algebra.Homology.ShortComplex.Exact
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
lemma comp_liftCycles {A' A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (α : A' ⟶ A) :
    α ≫ K.liftCycles k j hj hk = K.liftCycles (α ≫ k) j hj (by rw [assoc, hk, comp_zero]) := by
  simp only [← cancel_mono (K.iCycles i), assoc, liftCycles_i]

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
lemma toCycles_comp_homologyπ (i j : ι) [K.HasHomology j]:
    K.toCycles i j ≫ K.homologyπ j = 0 :=
  K.liftCycles_homologyπ_eq_zero_of_boundary (K.d i j) (c.next j) rfl (𝟙 _) (by simp)

noncomputable def homologyIsCokernel (i j : ι) (hi : c.prev j = i) [K.HasHomology j] :
    IsColimit (CokernelCofork.ofπ (K.homologyπ j) (K.toCycles_comp_homologyπ i j)) := by
  subst hi
  exact IsColimit.ofIsoColimit ((K.sc j).homologyIsCokernel)
    (Cofork.ext (Iso.refl _) (by dsimp [homologyπ] ; simp))

variable (i)

noncomputable def cyclesCo := (K.sc i).cyclesCo
noncomputable def homologyι : K.newHomology i ⟶ K.cyclesCo i := (K.sc i).homologyι
noncomputable def pCyclesCo : K.X i ⟶ K.cyclesCo i := (K.sc i).pCyclesCo

variable {i}

noncomputable def descCyclesCo {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.cyclesCo i ⟶ A :=
  (K.sc i).descCyclesCo k (by subst hj; exact hk)

@[reducible]
noncomputable def descCyclesCo' {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.Rel j i)
    (hk : K.d j i ≫ k = 0) : K.cyclesCo i ⟶ A :=
  K.descCyclesCo k j (c.prev_eq' hj) hk

@[reassoc (attr := simp)]
lemma p_descCyclesCo {A : C} (k : K.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : K.d j i ≫ k = 0) : K.pCyclesCo i ≫ K.descCyclesCo k j hj hk = k := by
  dsimp [descCyclesCo, pCyclesCo]
  simp

noncomputable def fromCyclesCo (i j : ι) [K.HasHomology i] :
  K.cyclesCo i ⟶ K.X j  :=
  K.descCyclesCo (K.d i j) (c.prev i) rfl (K.d_comp_d _ _ _)

variable (i)

@[reassoc (attr := simp)]
lemma d_pCyclesCo (X : HomologicalComplex C c) (i j : ι) [X.HasHomology j] : X.d i j ≫ X.pCyclesCo j = 0 := by
  by_cases hij : c.Rel i j
  . obtain rfl := c.prev_eq' hij
    exact (X.sc j).f_pCyclesCo
  . rw [X.shape _ _ hij, zero_comp]

@[reassoc (attr := simp)]
lemma p_fromCyclesCo (i j : ι) [K.HasHomology i] :
    K.pCyclesCo i ≫ K.fromCyclesCo i j = K.d i j :=
  p_descCyclesCo _ _ _ _ _

instance [K.HasHomology i] : Epi (K.pCyclesCo i) := by
  dsimp only [pCyclesCo]
  infer_instance

instance [K.HasHomology i] : Mono (K.homologyι i) := by
  dsimp only [homologyι]
  infer_instance

variable {K L M}

noncomputable def homologyMap : K.newHomology i ⟶ L.newHomology i :=
  ShortComplex.homologyMap ((shortComplexFunctor C c i).map φ)

noncomputable def cyclesMap : K.newCycles i ⟶ L.newCycles i :=
  ShortComplex.cyclesMap ((shortComplexFunctor C c i).map φ)

noncomputable def cyclesCoMap : K.cyclesCo i ⟶ L.cyclesCo i :=
  ShortComplex.cyclesCoMap ((shortComplexFunctor C c i).map φ)

@[reassoc (attr := simp)]
lemma cyclesMap_i : cyclesMap φ i ≫ L.iCycles i = K.iCycles i ≫ φ.f i :=
  ShortComplex.cyclesMap_i _

@[reassoc (attr := simp)]
lemma p_cyclesCoMap : K.pCyclesCo i ≫ cyclesCoMap φ i = φ.f i ≫ L.pCyclesCo i :=
  ShortComplex.p_cyclesCoMap _

variable (K)

@[simp]
lemma homologyMap_id : homologyMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.homologyMap_id _

@[simp]
lemma cyclesMap_id : cyclesMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.cyclesMap_id _

@[simp]
lemma cyclesCoMap_id : cyclesCoMap (𝟙 K) i = 𝟙 _ :=
  ShortComplex.cyclesCoMap_id _

variable {K}

@[reassoc]
lemma homologyMap_comp : homologyMap (φ ≫ ψ) i = homologyMap φ i ≫ homologyMap ψ i := by
  dsimp [homologyMap]
  rw [Functor.map_comp, ShortComplex.homologyMap_comp]

@[reassoc]
lemma cyclesMap_comp : cyclesMap (φ ≫ ψ) i = cyclesMap φ i ≫ cyclesMap ψ i := by
  dsimp [cyclesMap]
  rw [Functor.map_comp, ShortComplex.cyclesMap_comp]

@[reassoc]
lemma cyclesCoMap_comp : cyclesCoMap (φ ≫ ψ) i = cyclesCoMap φ i ≫ cyclesCoMap ψ i := by
  dsimp [cyclesCoMap]
  rw [Functor.map_comp, ShortComplex.cyclesCoMap_comp]

variable (K L)

@[simp]
lemma homologyMap_zero : homologyMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.homologyMap_zero _ _

@[simp]
lemma cyclesMap_zero : cyclesMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.cyclesMap_zero _ _

@[simp]
lemma cyclesCoMap_zero : cyclesCoMap (0 : K ⟶ L) i = 0 :=
  ShortComplex.cyclesCoMap_zero _ _

variable {K L}

@[reassoc (attr := simp)]
lemma homologyπ_naturality :
    K.homologyπ i ≫ homologyMap φ i = cyclesMap φ i ≫ L.homologyπ i :=
  ShortComplex.homologyπ_naturality _

@[reassoc (attr := simp)]
lemma liftCycles_comp_cyclesMap {A : C} (k : A ⟶ K.X i) (j : ι) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (φ : K ⟶ L) :
    K.liftCycles k j hj hk ≫ cyclesMap φ i = L.liftCycles (k ≫ φ.f i) j hj
      (by rw [assoc, φ.comm, reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_mono (L.iCycles i), assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i]

@[reassoc (attr := simp)]
lemma homologyι_naturality :
    homologyMap φ i ≫ L.homologyι i = K.homologyι i ≫ cyclesCoMap φ i :=
  ShortComplex.homologyι_naturality _

@[reassoc (attr := simp)]
lemma cyclesCoMap_comp_descCyclesCo {A : C} (k : L.X i ⟶ A) (j : ι) (hj : c.prev i = j)
    (hk : L.d j i ≫ k = 0) (φ : K ⟶ L) :
    cyclesCoMap φ i ≫ L.descCyclesCo k j hj hk = K.descCyclesCo (φ.f i ≫ k) j hj
      (by rw [← φ.comm_assoc, hk, comp_zero]) := by
  simp only [← cancel_epi (K.pCyclesCo i), p_cyclesCoMap_assoc, p_descCyclesCo]

variable (C c)

section

attribute [local simp] homologyMap_comp

@[simps]
noncomputable def newHomologyFunctor [CategoryWithHomology C] : HomologicalComplex C c ⥤ C where
  obj K := K.newHomology i
  map f := homologyMap f i

end

@[simps!]
noncomputable def newHomologyFunctorIso [CategoryWithHomology C] :
    newHomologyFunctor C c i ≅ shortComplexFunctor C c i ⋙ ShortComplex.homologyFunctor C :=
  NatIso.ofComponents (fun T => Iso.refl _) (by aesop_cat)

/- TODO : adapt more of the homology of ShortComplex API to this situation, including the
dual versions cyclesCo, etc... -/


@[simps!]
noncomputable def natIsoSc' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    shortComplexFunctor C c j ≅ shortComplexFunctor' C c i j k :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk (K.XIsoOfEq hi) (Iso.refl _) (K.XIsoOfEq hk)
    (by aesop_cat) (by aesop_cat)) (by aesop_cat)

variable {C c} (K L)

lemma isZero_homology_iff (i : ι) [K.HasHomology i] :
    IsZero (K.newHomology i) ↔ (K.sc i).Exact := by
  dsimp only [newHomology]
  rw [← ShortComplex.exact_iff_isZero_homology]

lemma isZero_homology_iff' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] :
    IsZero (K.newHomology j) ↔ (K.sc' i j k).Exact := by
  rw [isZero_homology_iff]
  exact ShortComplex.exact_iff_of_iso ((natIsoSc' C c i j k hi hk).app K)

lemma isIso_iCycles (i j : ι) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i] :
    IsIso (K.iCycles i) := by
  subst hj
  exact ShortComplex.isIso_iCycles _ h

lemma isIso_pCyclesCo (i j : ι) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j] :
    IsIso (K.pCyclesCo j) := by
  subst hi
  exact ShortComplex.isIso_pCyclesCo _ h

lemma isIso_liftCycles (i j : ι) (hj : c.next i = j) (h : K.d i j = 0) [K.HasHomology i] :
    IsIso (K.liftCycles (𝟙 (K.X i)) j hj (by rw [h, comp_zero])) := by
  have := K.isIso_iCycles i j hj h
  exact IsIso.of_isIso_fac_right (K.liftCycles_i _ _ _ _)

lemma isIso_descCyclesCo (i j : ι) (hi : c.prev j = i) (h : K.d i j = 0) [K.HasHomology j] :
    IsIso (K.descCyclesCo (𝟙 (K.X j)) i hi (by rw [h, zero_comp])) := by
  have := K.isIso_pCyclesCo i j hi h
  exact IsIso.of_isIso_fac_left (K.p_descCyclesCo _ _ _ _)

variable {K L}

noncomputable def homologyMapArrowIso (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [((shortComplexFunctor' C _ i j k).obj K).HasHomology]
    [((shortComplexFunctor' C _ i j k).obj L).HasHomology] :
    Arrow.mk (homologyMap φ j) ≅
      Arrow.mk (ShortComplex.homologyMap ((shortComplexFunctor' C _ i j k ).map φ)) := by
  refine' Arrow.isoMk
    (ShortComplex.homologyMapIso ((natIsoSc' C c i j k hi hk).app K))
    (ShortComplex.homologyMapIso ((natIsoSc' C c i j k hi hk).app L)) _
  dsimp [homologyMap]
  simp only [← ShortComplex.homologyMap_comp]
  congr 1
  exact ((natIsoSc' C c i j k hi hk).hom.naturality φ).symm

lemma isIso_homologyMap_iff' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [((shortComplexFunctor' C _ i j k).obj K).HasHomology]
    [((shortComplexFunctor' C _ i j k).obj L).HasHomology] :
  IsIso (homologyMap φ j) ↔
    IsIso (ShortComplex.homologyMap ((shortComplexFunctor' C _ i j k ).map φ)) := by
  exact MorphismProperty.RespectsIso.arrow_mk_iso_iff
    (MorphismProperty.RespectsIso.isomorphisms C) (homologyMapArrowIso φ i j k hi hk)

lemma mono_homologyMap_iff' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [((shortComplexFunctor' C _ i j k).obj K).HasHomology]
    [((shortComplexFunctor' C _ i j k).obj L).HasHomology] :
  Mono (homologyMap φ j) ↔
    Mono (ShortComplex.homologyMap ((shortComplexFunctor' C _ i j k ).map φ)) := by
  exact MorphismProperty.RespectsIso.arrow_mk_iso_iff
    (MorphismProperty.RespectsIso.monomorphisms C) (homologyMapArrowIso φ i j k hi hk)

lemma epi_homologyMap_iff' (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [((shortComplexFunctor' C _ i j k).obj K).HasHomology]
    [((shortComplexFunctor' C _ i j k).obj L).HasHomology] :
  Epi (homologyMap φ j) ↔
    Epi (ShortComplex.homologyMap ((shortComplexFunctor' C _ i j k ).map φ)) := by
  exact MorphismProperty.RespectsIso.arrow_mk_iso_iff
    (MorphismProperty.RespectsIso.epimorphisms C) (homologyMapArrowIso φ i j k hi hk)

lemma isIso_homologyMap_of_isIso_cyclesMap_of_epi (i j : ι) (hi : c.prev j = i)
    [K.HasHomology j] [L.HasHomology j]
    (h₁ : IsIso (cyclesMap φ j)) (h₂ : Epi (φ.f i)) :
    IsIso (homologyMap φ j) := by
  subst hi
  exact ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi _ h₁ h₂

lemma isIso_homologyMap_of_isIso_cyclesCoMap_of_mono (i j : ι) (hj : c.next i = j)
    [K.HasHomology i] [L.HasHomology i]
    (h₁ : IsIso (cyclesCoMap φ i)) (h₂ : Mono (φ.f j)) :
    IsIso (homologyMap φ i) := by
  subst hj
  exact ShortComplex.isIso_homologyMap_of_isIso_cyclesCoMap_of_mono _ h₁ h₂

lemma isZero_homology_of_isZero (i : ι) (hi : IsZero (K.X i)) [K.HasHomology i]:
    IsZero (K.newHomology i) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (by exact hi)

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

variable (C c)

def qis [CategoryWithHomology C] : MorphismProperty (HomologicalComplex C c) :=
  fun _ _ f => ∀ (i : ι), IsIso (homologyMap f i)

lemma homotopyEquivalences_subset_qis [CategoryWithHomology C] :
    homotopyEquivalences C c ⊆ qis C c := by
  rintro X Y _ ⟨e, rfl⟩ i
  exact IsIso.of_iso (e.toHomologyIso i)

section single

variable {C}
variable [HasZeroObject C] [DecidableEq ι]

instance (A : C) : ((single C c i).obj A).HasHomology i :=
  ⟨⟨ShortComplex.HomologyData.ofZeros _ rfl rfl⟩⟩

noncomputable def singleHomologyIso (A : C) : ((single C c i).obj A).newHomology i ≅ A :=
  (ShortComplex.HomologyData.ofZeros (sc ((single C c i).obj A) i) rfl rfl).left.homologyIso ≪≫
    singleObjXSelf C c i A

@[reassoc (attr := simp)]
lemma singleHomologyIso_hom_naturality {A B : C} (f : A ⟶ B) :
    homologyMap ((single C c i).map f) i ≫ (singleHomologyIso c i B).hom =
      (singleHomologyIso c i A).hom ≫ f := by
  dsimp only [singleHomologyIso, Iso.trans, homologyMap]
  simp [(ShortComplex.HomologyMapData.ofZeros
    ((shortComplexFunctor C c i).map ((single C c i).map f)) rfl rfl rfl rfl).left.homologyMap_eq]

variable (C)

@[simps!]
noncomputable def singleCompHomologyFunctorIso [CategoryWithHomology C] :
    single C c i ⋙ newHomologyFunctor C c i ≅ 𝟭 C :=
  NatIso.ofComponents (singleHomologyIso c i) (by aesop_cat)

end single

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
