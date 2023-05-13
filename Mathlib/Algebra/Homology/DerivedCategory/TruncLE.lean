import Mathlib.Algebra.Homology.DerivedCategory.Basic

open CategoryTheory Category Limits Preadditive ZeroObject

variable {C : Type _} [Category C] [Abelian C]

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

@[reassoc (attr := simp)]
lemma truncLEι_naturality : truncLEmap φ n ≫ truncLEι L n = truncLEι K n ≫ φ := by aesop_cat

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
        have := (K.truncLE i).isIso_liftCycles_of_zero i (i+1) (by simp) (by simp)
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

lemma qis_truncLEι_iff :
    qis _ _ (K.truncLEι n) ↔ ∀ (i : ℤ) (_ : n < i), IsZero (K.newHomology i) := by
  constructor
  . intro h i hi
    have h' := h i
    exact IsZero.of_iso (K.isZero_homology_truncLE _ _ hi)
      (asIso (homologyMap (truncLEι K n) i)).symm
  . intro h i
    by_cases hi : i ≤ n
    . exact K.isIso_homologyMap_truncLEι n i hi
    . simp only [not_le] at hi
      refine' ⟨⟨0, _, _⟩⟩
      . apply (K.isZero_homology_truncLE n i hi).eq_of_src
      . apply (h i hi).eq_of_src

variable (C)

@[simps]
noncomputable def functorTruncLE (n : ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := K.truncLE n
  map φ := truncLEmap φ n

@[simps]
noncomputable def functorTruncLEι (n : ℤ) : functorTruncLE C n ⟶ 𝟭 _ where
  app K := K.truncLEι n

lemma qis_isInvertedBy_functorTruncLE_comp_Q (n : ℤ) :
    (qis C _).IsInvertedBy (functorTruncLE C n ⋙ DerivedCategory.Q) := fun K L f hf => by
  dsimp
  rw [DerivedCategory.isIso_Q_map_iff', qis_truncLEmap_iff]
  intro i _
  exact hf i

variable {C}

end CochainComplex

namespace DerivedCategory

variable (C)

noncomputable def functorTruncLE (n : ℤ) : DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift _ (CochainComplex.qis_isInvertedBy_functorTruncLE_comp_Q C n) Q

noncomputable def functorTruncLEFactors (n : ℤ) :
    Q ⋙ functorTruncLE C n ≅ CochainComplex.functorTruncLE C n ⋙ Q :=
  Localization.fac _ _ _

end DerivedCategory
