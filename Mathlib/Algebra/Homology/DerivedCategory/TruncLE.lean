import Mathlib.Algebra.Homology.DerivedCategory.IsLE

open CategoryTheory Category Limits Preadditive ZeroObject

variable {C : Type u} [Category C] [Abelian C]
  [HasDerivedCategory C]

namespace CochainComplex

open HomologicalComplex

variable (K L M : CochainComplex C ℤ) (φ : K ⟶ L) (ψ : L ⟶ M)

noncomputable def truncLEX (n i : ℤ) : C :=
  if n < i then 0
  else if i = n then K.newCycles i
    else K.X i

lemma isZero_truncLEX (n i : ℤ) (hi : n < i) : IsZero (K.truncLEX n i) := by
  dsimp [truncLEX]
  rw [if_pos hi]
  exact isZero_zero C

noncomputable def truncLEXIsoX (n i : ℤ) (hi : i < n) :
    K.truncLEX n i ≅ K.X i := eqToIso (by
  dsimp [truncLEX]
  rw [if_neg, if_neg]
  all_goals linarith)

noncomputable def truncLEXIsoCycles (n i : ℤ) (hi : i = n) :
    K.truncLEX n i ≅ K.newCycles i := eqToIso (by
  dsimp [truncLEX]
  rw [if_neg, if_pos hi]
  linarith)

variable {K L}

noncomputable def truncLEXmap (n i : ℤ) : K.truncLEX n i ⟶ L.truncLEX n i := by
  by_cases hi : n < i
  . exact 0
  . by_cases hi' : i < n
    . exact (K.truncLEXIsoX n i hi').hom ≫ φ.f i ≫ (L.truncLEXIsoX n i hi').inv
    . have hi'' : i = n := le_antisymm (by simpa using hi) (by simpa using hi')
      exact (K.truncLEXIsoCycles n i hi'').hom ≫ cyclesMap φ i ≫
        (L.truncLEXIsoCycles n i hi'').inv

lemma truncLEXmap_eq_zero (n i : ℤ) (hi : n < i) :
    truncLEXmap φ n i = 0 := by
  dsimp [truncLEXmap]
  rw [dif_pos hi]

lemma truncLEXmap_eq_f (n i : ℤ) (hi : i < n) :
    truncLEXmap φ n i =
      (K.truncLEXIsoX n i hi).hom ≫ φ.f i ≫ (L.truncLEXIsoX n i hi).inv := by
  dsimp [truncLEXmap]
  rw [dif_neg (show ¬ n < i by linarith), dif_pos hi]

lemma truncLEXmap_eq_cyclesMap (n i : ℤ) (hi : i = n) :
    truncLEXmap φ n i =
      (K.truncLEXIsoCycles n i hi).hom ≫ cyclesMap φ i ≫ (L.truncLEXIsoCycles n i hi).inv := by
  dsimp [truncLEXmap]
  rw [dif_neg (show ¬ (n < i) by linarith), dif_neg (show ¬ (i < n) by linarith)]

variable (K)

noncomputable def truncLEιf (n i : ℤ) : K.truncLEX n i ⟶ K.X i := by
  by_cases hi : n < i
  . exact 0
  . by_cases hn : i = n
    . exact (K.truncLEXIsoCycles n i hn).hom ≫ K.iCycles i
    . exact (K.truncLEXIsoX n i (by cases (not_lt.1 hi).lt_or_eq <;> tauto)).hom

instance (n i : ℤ) : Mono (K.truncLEιf n i) := by
  dsimp [truncLEιf]
  split_ifs with h₁ h₂
  . rw [mono_iff_cancel_zero]
    intros
    apply (K.isZero_truncLEX n i h₁).eq_of_tgt
  . apply mono_comp
  . infer_instance

lemma truncLEιf_eq_zero (n i : ℤ) (hi : n < i) :
    K.truncLEιf n i = 0 := by
  dsimp [truncLEιf]
  rw [dif_pos hi]

lemma truncLEιf_eq_of_eq (n i : ℤ) (hi : i = n) :
    K.truncLEιf n i = (truncLEXIsoCycles K n i hi).hom ≫ K.iCycles i := by
  dsimp [truncLEιf]
  rw [dif_neg, dif_pos hi]
  all_goals linarith

lemma truncLEιf_eq_truncLEXIso_hom (n i : ℤ) (hi : i < n) :
    K.truncLEιf n i = (truncLEXIsoX K n i hi).hom := by
  dsimp [truncLEιf]
  rw [dif_neg, dif_neg]
  all_goals linarith

variable {K}

@[reassoc (attr := simp)]
lemma truncLEmap_ιf (n i : ℤ) : truncLEXmap φ n i ≫ L.truncLEιf n i =
    K.truncLEιf n i ≫ φ.f i := by
  by_cases hi : n < i
  . simp only [truncLEιf_eq_zero _ _ _ hi, zero_comp, comp_zero]
  . obtain (hi'|hi') := (not_lt.1 hi).lt_or_eq
    . simp only [truncLEιf_eq_truncLEXIso_hom _ _ _ hi', K.truncLEXmap_eq_f _ _ _ hi', assoc,
        Iso.inv_hom_id, comp_id]
    . simp only [truncLEιf_eq_of_eq _ _ _ hi', truncLEXmap_eq_cyclesMap _ _ _ hi',
        truncLEXmap_eq_cyclesMap, assoc, Iso.inv_hom_id_assoc, cyclesMap_i]

variable (K)

noncomputable def truncLEd (n i j : ℤ) : K.truncLEX n i ⟶ K.truncLEX n j := by
  by_cases hij : i + 1 = j
  . by_cases hj₀ : n < j
    . exact 0
    . by_cases hj : j = n
      . exact K.liftCycles ((K.truncLEXIsoX n i (by linarith)).hom ≫ K.d i j) (j+1)
          (by simp) (by simp) ≫ (K.truncLEXIsoCycles n j hj).inv
      . refine' (K.truncLEXIsoX n i _).hom ≫ K.d i j ≫ (K.truncLEXIsoX n j _).inv
        . linarith
        . cases (not_lt.1 hj₀).lt_or_eq <;> tauto
  . exact 0

lemma truncLE_shape (n i j : ℤ) (hij : i + 1 ≠ j) :
    K.truncLEd n i j = 0 := by
  dsimp [truncLEd]
  rw [dif_neg hij]

lemma truncLEd_eq_zero (n i j : ℤ) (hi : n ≤ i) :
    K.truncLEd n i j = 0 := by
  by_cases hij : i + 1 = j
  . dsimp only [truncLEd]
    rw [dif_pos hij, dif_pos]
    linarith
  . rw [truncLE_shape _ _ _ _ hij]

@[simp]
lemma truncLEd_eq_zero' (n j : ℤ) :
    K.truncLEd n n j = 0 :=
  K.truncLEd_eq_zero _ _ _ (by rfl)

lemma truncLEd_eq_d (n i j : ℤ) (hij : i + 1 = j) (hj : j < n) :
    K.truncLEd n i j =
      (K.truncLEXIsoX n i (by rw [← hij] at hj ; exact (lt_add_one i).trans hj)).hom ≫
        K.d i j ≫ (K.truncLEXIsoX n j hj).inv := by
  dsimp [truncLEd]
  rw [dif_pos hij, dif_neg, dif_neg]
  all_goals linarith

lemma trunceLEd_eq_liftCycles_comp (n i j : ℤ) (hij : i + 1 = j) (hj : j = n) :
    K.truncLEd n i j = K.liftCycles ((K.truncLEXIsoX n i (by linarith)).hom ≫ K.d i j) (j+1)
          (by simp) (by simp) ≫ (K.truncLEXIsoCycles n j hj).inv := by
  dsimp [truncLEd]
  rw [dif_pos hij, dif_neg (show ¬n < j by linarith), dif_pos hj]

lemma truncLEι_d_eq_zero (n i j : ℤ) (hi : n ≤ i) :
    K.truncLEιf n i ≫ K.d i j = 0 := by
  obtain (hi|hi) := hi.lt_or_eq
  . rw [K.truncLEιf_eq_zero _ _ hi, zero_comp]
  . simp [K.truncLEιf_eq_of_eq _ _ hi.symm]

@[reassoc (attr := simp)]
lemma truncLEd_comm (n i j : ℤ) :
    K.truncLEd n i j ≫ K.truncLEιf n j =
      K.truncLEιf n i ≫ K.d i j := by
  by_cases hij : i + 1 = j
  . by_cases hi : n ≤ i
    . rw [K.truncLEd_eq_zero _ _ _ hi, zero_comp, K.truncLEι_d_eq_zero _ _ _ hi]
    . simp only [not_le] at hi
      by_cases hj : j < n
      . simp only [K.truncLEιf_eq_truncLEXIso_hom _ _ hi, K.truncLEιf_eq_truncLEXIso_hom _ _ hj,
          K.truncLEd_eq_d _ _ _ hij hj, assoc, Iso.inv_hom_id, comp_id]
      . have hj' : j = n := by cases (not_lt.1 hj).lt_or_eq <;> linarith
        simp only [K.trunceLEd_eq_liftCycles_comp _ _ _ hij hj', K.truncLEιf_eq_of_eq _ _ hj',
          K.truncLEιf_eq_truncLEXIso_hom _ _ hi, assoc, Iso.inv_hom_id_assoc,
          HomologicalComplex.liftCycles_i]
  . rw [K.shape _ _ hij, K.truncLE_shape _ _ _ hij, zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma truncLEd_comp_d (n i j k : ℤ) :
    K.truncLEd n i j ≫ K.truncLEd n j k = 0 := by
  simp only [← cancel_mono (K.truncLEιf n k), zero_comp, assoc,
          truncLEd_comm, truncLEd_comm_assoc, K.d_comp_d, comp_zero]

@[simp]
lemma truncLEXmap_id (n i : ℤ) : truncLEXmap (𝟙 K) n i = 𝟙 _ := by
  simp only [← cancel_mono (K.truncLEιf n i), truncLEmap_ιf, id_f, comp_id, id_comp]

variable {K M}

@[reassoc]
lemma truncLEXmap_comp (n i : ℤ) :
  truncLEXmap (φ ≫ ψ) n i = truncLEXmap φ n i ≫ truncLEXmap ψ n i := by
  simp only [← cancel_mono (M.truncLEιf n i), truncLEmap_ιf, comp_f,
    assoc, truncLEmap_ιf_assoc]

attribute [simp] truncLEXmap_comp

@[reassoc (attr := simp)]
lemma truncLEmap_d (n i j : ℤ) : truncLEXmap φ n i ≫ L.truncLEd n i j =
  K.truncLEd n i j ≫ truncLEXmap φ n j := by
  simp only [← cancel_mono (L.truncLEιf n j), assoc, truncLEd_comm,
    truncLEmap_ιf_assoc, Hom.comm, truncLEmap_ιf, truncLEd_comm_assoc]

variable (K L)

@[simps]
noncomputable def truncLE (n : ℤ) : CochainComplex C ℤ where
  X := K.truncLEX n
  d := K.truncLEd n
  shape := fun i j hij => K.truncLE_shape n i j hij

variable {K L}

@[simps]
noncomputable def truncLEmap (n : ℤ) : K.truncLE n ⟶ L.truncLE n where
  f := truncLEXmap φ n

variable (K L)

@[simps]
noncomputable def truncLEι (n : ℤ) : K.truncLE n ⟶ K where
  f i := K.truncLEιf n i

variable {K L}

@[reassoc (attr := simp)]
lemma truncLEι_naturality (n : ℤ) :
  truncLEmap φ n ≫ L.truncLEι n = K.truncLEι n ≫ φ := by aesop_cat

variable (K L)

lemma isZero_homology_truncLE (n i : ℤ) (hi : n < i) :
    IsZero ((K.truncLE n).newHomology i) := by
  rw [isZero_homology_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_truncLEX _ _ hi)

lemma isIso_homologyMap_truncLEι (n i : ℤ) (hi : i ≤ n) :
    IsIso (homologyMap (K.truncLEι n) i) := by
  obtain (hi'|rfl) := hi.lt_or_eq
  . let α := (shortComplexFunctor' C (ComplexShape.up ℤ) (i - 1) i (i + 1)).map (truncLEι K n)
    rw [isIso_homologyMap_iff' _ (i-1) i (i+1) (by simp) (by simp)]
    change IsIso (ShortComplex.homologyMap α)
    have : IsIso α.τ₁ := by
      dsimp
      rw [K.truncLEιf_eq_truncLEXIso_hom _ _ (by linarith)]
      infer_instance
    have : IsIso α.τ₂ := by
      dsimp
      rw [K.truncLEιf_eq_truncLEXIso_hom _ _ hi']
      infer_instance
    have : Mono α.τ₃ := by dsimp ; infer_instance
    apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono
  . apply isIso_homologyMap_of_isIso_cyclesMap_of_epi _ (i-1) i (by simp)
    . refine' ⟨⟨(K.truncLE i).liftCycles (K.truncLEXIsoCycles i i rfl).inv (i+1) (by simp) _,
        _, _⟩⟩
      . dsimp
        rw [K.truncLEd_eq_zero _ _ _ (by rfl), comp_zero]
      . dsimp
        have := (K.truncLE i).isIso_liftCycles i (i+1) (by simp) (by simp)
        simp only [← cancel_epi ((K.truncLE i).liftCycles (𝟙 ((K.truncLE i).X i)) (i+1)
          (by simp) (by simp)), ← cancel_mono ((K.truncLE i).iCycles i),
          truncLE_X, liftCycles_comp_cyclesMap_assoc, truncLEι_f, id_comp,
          assoc, liftCycles_i, comp_id]
        simp only [← cancel_mono ((K.truncLEXIsoCycles i i rfl).hom), assoc, Iso.inv_hom_id,
          comp_id, id_comp, ← cancel_mono (K.iCycles i), liftCycles_i, truncLEιf_eq_of_eq]
      . simp only [← cancel_mono (K.iCycles i), liftCycles_comp_cyclesMap,
          truncLE_X, truncLEι_f, liftCycles_i, id_comp,
          K.truncLEιf_eq_of_eq i i rfl, Iso.inv_hom_id_assoc]
    . dsimp
      rw [K.truncLEιf_eq_truncLEXIso_hom _ _ (by linarith)]
      infer_instance

variable {K L}

lemma isIso_homologyMap_truncLEmap_iff (n i : ℤ) (hi : i ≤ n) :
    IsIso (homologyMap (truncLEmap φ n) i) ↔ IsIso (homologyMap φ i):= by
  have := K.isIso_homologyMap_truncLEι _ _ hi
  have := L.isIso_homologyMap_truncLEι _ _ hi
  apply isIso_iff_of_arrow_mk_iso
  refine' Arrow.isoMk (asIso (homologyMap (K.truncLEι n) i))
    (asIso (homologyMap (L.truncLEι n) i)) _
  dsimp
  simp only [← homologyMap_comp, truncLEι_naturality]

lemma qis_truncLEmap_iff :
    qis _ _ (truncLEmap φ n) ↔ ∀ (i : ℤ) (_ : i ≤ n), IsIso (homologyMap φ i) := by
  constructor
  . intro h i hi
    rw [← isIso_homologyMap_truncLEmap_iff φ n i hi]
    apply h
  . intro h i
    by_cases hi : i ≤ n
    . rw [isIso_homologyMap_truncLEmap_iff φ n i hi]
      exact h _ hi
    . simp only [not_le] at hi
      refine' ⟨⟨0, _, _⟩⟩
      . apply (K.isZero_homology_truncLE n i hi).eq_of_src
      . apply (L.isZero_homology_truncLE n i hi).eq_of_src

variable (K)

lemma qis_truncLEι_iff (n : ℤ) :
    qis _ _ (K.truncLEι n) ↔ K.IsLE n := by
  constructor
  . intro h
    constructor
    intro i hi
    have h' := h i
    exact IsZero.of_iso (K.isZero_homology_truncLE _ _ hi)
      (asIso (homologyMap (truncLEι K n) i)).symm
  . intro h i
    by_cases hi : i ≤ n
    . exact K.isIso_homologyMap_truncLEι n i hi
    . simp only [not_le] at hi
      refine' ⟨⟨0, _, _⟩⟩
      . apply (K.isZero_homology_truncLE n i hi).eq_of_src
      . apply (K.isZero_of_isLE n i hi).eq_of_src

instance (n : ℤ) [K.IsLE n] : IsIso (DerivedCategory.Q.map (K.truncLEι n)) := by
  apply Localization.inverts DerivedCategory.Q (qis C _)
  rw [qis_truncLEι_iff]
  infer_instance

variable (C)

@[simps]
noncomputable def functorTruncLE (n : ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := K.truncLE n
  map φ := truncLEmap φ n

@[simps]
noncomputable def natTransTruncLEι (n : ℤ) : functorTruncLE C n ⟶ 𝟭 _ where
  app K := K.truncLEι n

lemma qis_isInvertedBy_functorTruncLE_comp_Q (n : ℤ) :
    (qis C _).IsInvertedBy (functorTruncLE C n ⋙ DerivedCategory.Q) := fun K L f hf => by
  dsimp
  rw [DerivedCategory.isIso_Q_map_iff', qis_truncLEmap_iff]
  intro i _
  exact hf i

instance : (K.truncLE n).IsStrictlyLE n := ⟨K.isZero_truncLEX n⟩

instance (i : ℤ) [K.IsStrictlyLE i] : (K.truncLE n).IsStrictlyLE i := ⟨fun j hj => by
  by_cases hj' : n < j
  . exact K.isZero_truncLEX _ _ hj'
  . rw [IsZero.iff_id_eq_zero, ← cancel_mono (K.truncLEιf n j)]
    apply IsZero.eq_of_tgt
    exact K.isZero_of_isStrictlyLE i j (by linarith)⟩

instance (i : ℤ) [K.IsStrictlyGE i] : (K.truncLE n).IsStrictlyGE i := ⟨fun j hj => by
  by_cases hj' : n < j
  . exact K.isZero_truncLEX _ _ hj'
  . rw [IsZero.iff_id_eq_zero, ← cancel_mono (K.truncLEιf n j)]
    apply IsZero.eq_of_tgt
    exact K.isZero_of_isStrictlyGE i j (by linarith)⟩

lemma isIso_truncLEι_iff (n : ℤ) : IsIso (K.truncLEι n) ↔ K.IsStrictlyLE n := by
  constructor
  . intro hK
    constructor
    intro i hi
    exact IsZero.of_iso (isZero_truncLEX _ _ _ hi)
      ((eval _ _ i).mapIso (asIso (K.truncLEι n)).symm)
  . intro hK
    suffices ∀ (i : ℤ), IsIso ((K.truncLEι n).f i) by
      apply HomologicalComplex.Hom.isIso_of_components
    intro i
    dsimp
    by_cases hi : i < n
    . rw [truncLEιf_eq_truncLEXIso_hom _ _ _ hi]
      infer_instance
    . obtain (hi'|rfl) := (not_lt.1 hi).lt_or_eq
      . exact ⟨0, (K.isZero_truncLEX n i hi').eq_of_src _ _,
          (K.isZero_of_isStrictlyLE n i hi').eq_of_src _ _⟩
      . have := K.isIso_iCycles n (n+1) (by simp)
          (((K.isZero_of_isStrictlyLE n (n+1) (by simp))).eq_of_tgt _ _)
        rw [K.truncLEιf_eq_of_eq n n rfl]
        infer_instance


instance (n : ℤ) [K.IsStrictlyLE n] : IsIso (K.truncLEι n) := by
  rw [K.isIso_truncLEι_iff]
  infer_instance

variable {C}

end CochainComplex

namespace DerivedCategory

variable (C)

noncomputable def functorTruncLE (n : ℤ) : DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift _ (CochainComplex.qis_isInvertedBy_functorTruncLE_comp_Q C n) Q

noncomputable def functorTruncLEFactors (n : ℤ) :
    Q ⋙ functorTruncLE C n ≅ CochainComplex.functorTruncLE C n ⋙ Q :=
  Localization.fac _ _ _

noncomputable instance : Localization.Lifting Q (HomologicalComplex.qis C _)
    (CochainComplex.functorTruncLE C n ⋙ Q) (functorTruncLE C n) :=
  ⟨functorTruncLEFactors C n⟩

noncomputable def natTransTruncLEι (n : ℤ) : functorTruncLE C n ⟶ 𝟭 _  :=
  Localization.liftNatTrans Q (HomologicalComplex.qis C _)
    (CochainComplex.functorTruncLE C n ⋙ Q) Q _ _
      (whiskerRight (CochainComplex.natTransTruncLEι C n) Q)

noncomputable def QCompFunctorTruncLECompHomologyFunctorIso (n i : ℤ) :
    Q ⋙ functorTruncLE C n ⋙ homologyFunctor C i ≅
      CochainComplex.functorTruncLE C n ⋙
        HomologicalComplex.newHomologyFunctor _ _ i :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (functorTruncLEFactors C n) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (homologyFunctorFactors _ i)

variable {C}

noncomputable abbrev truncLE (X : DerivedCategory C) (n : ℤ) := (functorTruncLE C n).obj X

lemma isZero_homology_truncLE (X : DerivedCategory C) (n i : ℤ) (hi : n < i) :
    IsZero ((homologyFunctor C i).obj (X.truncLE n)) := by
  revert n i hi X
  apply induction_Q_obj
  . intro K n i hi
    exact IsZero.of_iso (K.isZero_homology_truncLE n i hi)
      ((QCompFunctorTruncLECompHomologyFunctorIso C n i).app K)
  . intros X Y e hX n i hi
    exact IsZero.of_iso (hX n i hi) ((homologyFunctor _ _).mapIso
      ((functorTruncLE C n).mapIso e.symm))

noncomputable abbrev truncLEι (X : DerivedCategory C) (n : ℤ) :=
  (natTransTruncLEι C n).app X

@[reassoc]
lemma truncLEι_naturality {X Y : DerivedCategory C} (f : X ⟶ Y) (n : ℤ) :
    (functorTruncLE C n).map f ≫ Y.truncLEι n = X.truncLEι n ≫ f :=
  (natTransTruncLEι C n).naturality f

lemma truncLEι_app (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).truncLEι n =
      (functorTruncLEFactors C n).hom.app K ≫ Q.map (K.truncLEι n) := by
  dsimp [truncLEι, natTransTruncLEι]
  rw [Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso, Localization.Lifting.iso']
  simp

lemma isIso_homologyMap_truncLEι (X : DerivedCategory C) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((homologyFunctor C i).map (X.truncLEι n)) := by
  revert n i hi X
  apply induction_Q_obj
  . intro K n i hi
    rw [truncLEι_app, Functor.map_comp]
    have : IsIso ((homologyFunctor C i).map ((functorTruncLEFactors C n).hom.app K)) := inferInstance
    have : IsIso ((homologyFunctor C i).map (Q.map (K.truncLEι n))) := by
      erw [NatIso.isIso_map_iff (homologyFunctorFactors C i) (K.truncLEι n)]
      exact K.isIso_homologyMap_truncLEι n i hi
    apply IsIso.comp_isIso
  . intros X Y e hX n i hi
    exact ((MorphismProperty.RespectsIso.isomorphisms C).arrow_iso_iff
      ((homologyFunctor C i).mapArrow.mapIso
        ((NatTrans.functorArrow (natTransTruncLEι C n)).mapIso e))).1 (hX n i hi)

lemma isIso_truncLEι_iff (X : DerivedCategory C) (n : ℤ) :
    IsIso (X.truncLEι n) ↔ X.IsLE n := by
  constructor
  . intro hX
    constructor
    intro i hi
    exact IsZero.of_iso (isZero_homology_truncLE _ _ _ hi)
      ((homologyFunctor C i).mapIso (asIso (truncLEι X n)).symm)
  . intro hX
    rw [isIso_iff]
    intro i
    by_cases hi : i ≤ n
    . exact X.isIso_homologyMap_truncLEι _ _ hi
    . simp only [not_le] at hi
      refine' ⟨0, _, _⟩
      . apply (X.isZero_homology_truncLE n i hi).eq_of_src
      . apply (X.isZero_of_isLE n i hi).eq_of_src

lemma isZero_truncLE_iff (X : DerivedCategory C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsZero (X.truncLE n₀) ↔ X.IsGE n₁ := by
  have h : ∀ (i : ℤ) (_ : i < n₁), (homologyFunctor C i).obj (X.truncLE n₀) ≅
      (homologyFunctor C i).obj X:= fun i hi => by
    have := X.isIso_homologyMap_truncLEι n₀ i (by linarith)
    exact asIso ((homologyFunctor C i).map (X.truncLEι n₀))
  constructor
  . intro hX
    constructor
    intro i hi
    refine' IsZero.of_iso _ (h i hi).symm
    rw [IsZero.iff_id_eq_zero] at hX ⊢
    rw [← (homologyFunctor C i).map_id, hX, Functor.map_zero]
  . intro hX
    rw [isZero_iff]
    intro i
    by_cases hi : i < n₁
    . exact IsZero.of_iso (X.isZero_of_isGE n₁ i hi) (h i hi)
    . exact X.isZero_homology_truncLE _ _ (by linarith)

instance (X : DerivedCategory C) (n : ℤ) [X.IsLE n] : IsIso (X.truncLEι n) := by
  rw [isIso_truncLEι_iff]
  infer_instance

instance (X : DerivedCategory C) (n : ℤ) : (X.truncLE n).IsLE n := by
  revert X
  apply induction_Q_obj
  . intro K
    have e : _ ≅ Q.obj (K.truncLE n) := (functorTruncLEFactors C n).app K
    apply isLE_of_iso e.symm n
  . intros X Y e hX
    exact isLE_of_iso ((functorTruncLE C n).mapIso e) n

lemma right_fac_of_isStrictlyLE (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) (n : ℤ)
    [X.IsStrictlyLE n] :
    ∃ (X' : CochainComplex C ℤ) (_ : X'.IsStrictlyLE n) (s : X' ⟶ X) (hs : IsIso (Q.map s))
      (g : X' ⟶ Y), f = inv (Q.map s) ≫ Q.map g := by
  obtain ⟨X', s, hs, g, rfl⟩ := right_fac X Y f
  have : IsIso (Q.map (CochainComplex.truncLEmap s n)) := by
    rw [isIso_Q_map_iff', CochainComplex.qis_truncLEmap_iff]
    rw [isIso_Q_map_iff'] at hs
    intro i _
    exact hs i
  refine' ⟨X'.truncLE n, inferInstance, CochainComplex.truncLEmap s n ≫ X.truncLEι n, _,
      CochainComplex.truncLEmap g n ≫ Y.truncLEι n, _⟩
  . rw [Q.map_comp]
    infer_instance
  . have eq := Q.congr_map (CochainComplex.truncLEι_naturality s n)
    have eq' := Q.congr_map (CochainComplex.truncLEι_naturality g n)
    simp only [Functor.map_comp] at eq eq'
    simp only [Functor.map_comp, ← cancel_epi (Q.map (CochainComplex.truncLEmap s n) ≫
      Q.map (CochainComplex.truncLEι X n)), IsIso.hom_inv_id_assoc, assoc, reassoc_of% eq, eq']

end DerivedCategory
