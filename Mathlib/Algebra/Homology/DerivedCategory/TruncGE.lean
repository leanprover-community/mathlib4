import Mathlib.Algebra.Homology.DerivedCategory.IsLE

open CategoryTheory Category Limits Preadditive ZeroObject

variable {C : Type _} [Category C] [Abelian C]
  [HasDerivedCategory C]

namespace CochainComplex

open HomologicalComplex

variable (K L M : CochainComplex C ℤ) (φ : K ⟶ L) (ψ : L ⟶ M)

noncomputable def truncGEX (n i : ℤ) : C :=
  if i < n then 0
  else if i = n then K.opcycles i
    else K.X i

lemma isZero_truncGEX (n i : ℤ) (hi : i < n) : IsZero (K.truncGEX n i) := by
  dsimp [truncGEX]
  rw [if_pos hi]
  exact isZero_zero C

noncomputable def truncGEXIsoX (n i : ℤ) (hi : n < i) :
    K.truncGEX n i ≅ K.X i := eqToIso (by
  dsimp [truncGEX]
  rw [if_neg, if_neg]
  all_goals linarith)

noncomputable def truncGEXIsoOpcycles (n i : ℤ) (hi : i = n) :
    K.truncGEX n i ≅ K.opcycles i := eqToIso (by
  dsimp [truncGEX]
  rw [if_neg, if_pos hi]
  linarith)

variable {K L}

noncomputable def truncGEXmap (n i : ℤ) : K.truncGEX n i ⟶ L.truncGEX n i := by
  by_cases hi : i < n
  . exact 0
  . by_cases hi' : n < i
    . exact (K.truncGEXIsoX n i hi').hom ≫ φ.f i ≫ (L.truncGEXIsoX n i hi').inv
    . have hi'' : i = n := le_antisymm (by simpa using hi') (by simpa using hi)
      exact (K.truncGEXIsoOpcycles n i hi'').hom ≫ opcyclesMap φ i≫
        (L.truncGEXIsoOpcycles n i hi'').inv

lemma truncGEXmap_eq_zero (n i : ℤ) (hi : i < n) :
    truncGEXmap φ n i = 0 := by
  dsimp [truncGEXmap]
  rw [dif_pos hi]

lemma truncGEXmap_eq_f (n i : ℤ) (hi : n < i) :
    truncGEXmap φ n i =
      (K.truncGEXIsoX n i hi).hom ≫ φ.f i ≫ (L.truncGEXIsoX n i hi).inv := by
  dsimp [truncGEXmap]
  rw [dif_neg (show ¬ i < n by linarith), dif_pos hi]

lemma truncGEXmap_eq_opcyclesMap (n i : ℤ) (hi : i = n) :
    truncGEXmap φ n i =
      (K.truncGEXIsoOpcycles n i hi).hom ≫ opcyclesMap φ i ≫
        (L.truncGEXIsoOpcycles n i hi).inv := by
  dsimp [truncGEXmap]
  rw [dif_neg (show ¬ (i < n) by linarith), dif_neg (show ¬ (n < i) by linarith)]

variable (K)

noncomputable def truncGEπf (n i : ℤ) : K.X i ⟶ K.truncGEX n i := by
  by_cases hi : i < n
  . exact 0
  . by_cases hn : i = n
    . exact K.pOpcycles i ≫ (K.truncGEXIsoOpcycles n i hn).inv
    . exact (K.truncGEXIsoX n i (by cases (not_lt.1 hi).lt_or_eq <;> tauto)).inv

instance (n i : ℤ) : Epi (K.truncGEπf n i) := by
  dsimp [truncGEπf]
  split_ifs with h₁ h₂
  . rw [epi_iff_cancel_zero]
    intros
    apply (K.isZero_truncGEX n i h₁).eq_of_src
  . apply epi_comp
  . infer_instance

lemma truncGEπf_eq_zero (n i : ℤ) (hi : i < n) :
    K.truncGEπf n i = 0 := by
  dsimp [truncGEπf]
  rw [dif_pos hi]

lemma truncGEπf_eq_of_eq (n i : ℤ) (hi : i = n) :
    K.truncGEπf n i = K.pOpcycles i ≫ (truncGEXIsoOpcycles K n i hi).inv := by
  dsimp [truncGEπf]
  rw [dif_neg, dif_pos hi]
  all_goals linarith

lemma truncGEπf_eq_truncGEXIso_inv (n i : ℤ) (hi : n < i) :
    K.truncGEπf n i = (truncGEXIsoX K n i hi).inv := by
  dsimp [truncGEπf]
  rw [dif_neg, dif_neg]
  all_goals linarith

variable {K}

@[reassoc (attr := simp)]
lemma truncGEπ_map_f (n i : ℤ) : K.truncGEπf n i ≫ truncGEXmap φ n i =
    φ.f i ≫ L.truncGEπf n i := by
  by_cases hi : i < n
  . simp only [truncGEπf_eq_zero _ _ _ hi, zero_comp, comp_zero]
  . obtain (hi'|hi') := (not_lt.1 hi).lt_or_eq
    . simp only [truncGEπf_eq_truncGEXIso_inv _ _ _ hi',
        K.truncGEXmap_eq_f _ _ _ hi', Iso.inv_hom_id_assoc]
    . simp only [truncGEπf_eq_of_eq _ _ _ hi'.symm, truncGEXmap_eq_opcyclesMap _ _ _ hi'.symm,
        assoc, Iso.inv_hom_id_assoc, p_opcyclesMap_assoc]

variable (K)

noncomputable def truncGEd (n i j : ℤ) : K.truncGEX n i ⟶ K.truncGEX n j := by
  by_cases hij : i + 1 = j
  . by_cases hi₀ : i < n
    . exact 0
    . by_cases hi : i = n
      . exact (K.truncGEXIsoOpcycles n i hi).hom ≫ K.descOpcycles (K.d i j ≫
          (K.truncGEXIsoX n j (by linarith)).inv) (i-1) (by simp) (by simp)
      . refine' (K.truncGEXIsoX n i _).hom ≫ K.d i j ≫ (K.truncGEXIsoX n j _).inv
        . cases (not_lt.1 hi₀).lt_or_eq <;> tauto
        . linarith
  . exact 0

lemma truncGE_shape (n i j : ℤ) (hij : i + 1 ≠ j) :
    K.truncGEd n i j = 0 := by
  dsimp [truncGEd]
  rw [dif_neg hij]

lemma truncGEd_eq_zero (n i j : ℤ) (hi : j ≤ n) :
    K.truncGEd n i j = 0 := by
  by_cases hij : i + 1 = j
  . dsimp only [truncGEd]
    rw [dif_pos hij, dif_pos]
    linarith
  . rw [truncGE_shape _ _ _ _ hij]

@[simp]
lemma truncGEd_eq_zero' (n j : ℤ) :
    K.truncGEd n j n = 0 :=
  K.truncGEd_eq_zero _ _ _ (by rfl)

lemma truncGEd_eq_d (n i j : ℤ) (hij : i + 1 = j) (hj : n < i) :
    K.truncGEd n i j =
      (K.truncGEXIsoX n i hj).hom ≫
        K.d i j ≫ (K.truncGEXIsoX n j (by rw [← hij] ; exact hj.trans (lt_add_one i))).inv := by
  dsimp [truncGEd]
  rw [dif_pos hij, dif_neg, dif_neg]
  all_goals linarith

lemma trunceGEd_eq_comp_descOpcycles (n i j : ℤ) (hij : i + 1 = j) (hi : i = n) :
    K.truncGEd n i j = (K.truncGEXIsoOpcycles n i hi).hom ≫
      K.descOpcycles (K.d i j ≫
        (K.truncGEXIsoX n j (by linarith)).inv) (i-1) (by simp) (by simp) := by
  dsimp [truncGEd]
  rw [dif_pos hij, dif_neg (show ¬i < n by linarith), dif_pos hi]

lemma d_truncGEπ_eq_zero (n i j : ℤ) (hj : j ≤ n) :
    K.d i j ≫ K.truncGEπf n j = 0 := by
  obtain (hj|hj) := hj.lt_or_eq
  . rw [K.truncGEπf_eq_zero _ _ hj, comp_zero]
  . simp [K.truncGEπf_eq_of_eq _ _ hj]

@[reassoc (attr := simp)]
lemma truncGEd_comm (n i j : ℤ) :
    K.truncGEπf n i ≫ K.truncGEd n i j  =
      K.d i j ≫ K.truncGEπf n j := by
  by_cases hij : i + 1 = j
  . by_cases hj : j ≤ n
    . rw [K.truncGEd_eq_zero _ _ _ hj, comp_zero, K.d_truncGEπ_eq_zero _ _ _ hj]
    . simp only [not_le] at hj
      by_cases hi : n < i
      . rw [K.truncGEπf_eq_truncGEXIso_inv _ _ hi, K.truncGEπf_eq_truncGEXIso_inv _ _ hj,
          K.truncGEd_eq_d _ _ _ hij hi, Iso.inv_hom_id_assoc]
      . have hi' : i = n := by linarith
        rw [K.trunceGEd_eq_comp_descOpcycles _ _ _ hij hi', K.truncGEπf_eq_of_eq _ _ hi',
          K.truncGEπf_eq_truncGEXIso_inv _ _ hj, assoc, Iso.inv_hom_id_assoc,
          p_descOpcycles]
  . rw [K.shape _ _ hij, K.truncGE_shape _ _ _ hij, zero_comp, comp_zero]

@[reassoc (attr := simp)]
lemma truncGEd_comp_d (n i j k : ℤ) :
    K.truncGEd n i j ≫ K.truncGEd n j k = 0 := by
  simp only [← cancel_epi (K.truncGEπf n i), comp_zero, truncGEd_comm_assoc,
    truncGEd_comm, K.d_comp_d_assoc, zero_comp]

@[simp]
lemma truncGEXmap_id (n i : ℤ) : truncGEXmap (𝟙 K) n i = 𝟙 _ := by
  simp only [← cancel_epi (K.truncGEπf n i), truncGEπ_map_f, id_f, comp_id, id_comp]

variable {K M}

@[reassoc]
lemma truncGEXmap_comp (n i : ℤ) :
  truncGEXmap (φ ≫ ψ) n i = truncGEXmap φ n i ≫ truncGEXmap ψ n i := by
  simp only [← cancel_epi (K.truncGEπf n i), truncGEπ_map_f, comp_f,
    assoc, truncGEπ_map_f_assoc]

attribute [simp] truncGEXmap_comp

@[reassoc (attr := simp)]
lemma truncGEmap_d (n i j : ℤ) : truncGEXmap φ n i ≫ L.truncGEd n i j =
  K.truncGEd n i j ≫ truncGEXmap φ n j := by
  simp only [← cancel_epi (K.truncGEπf n i), assoc, truncGEd_comm,
    truncGEπ_map_f_assoc, Hom.comm_assoc, truncGEπ_map_f, truncGEd_comm_assoc]

variable (K L)

@[simps]
noncomputable def truncGE (n : ℤ) : CochainComplex C ℤ where
  X := K.truncGEX n
  d := K.truncGEd n
  shape := fun i j hij => K.truncGE_shape n i j hij

variable {K L}

@[simps]
noncomputable def truncGEmap (n : ℤ) : K.truncGE n ⟶ L.truncGE n where
  f := truncGEXmap φ n

variable (K L)

@[simps]
noncomputable def truncGEπ (n : ℤ) : K ⟶ K.truncGE n where
  f i := K.truncGEπf n i

variable {K L}

@[reassoc (attr := simp)]
lemma truncGEπ_naturality (n : ℤ) :
  K.truncGEπ n ≫ truncGEmap φ n = φ ≫ L.truncGEπ n  := by aesop_cat

variable (K L)

lemma isZero_homology_truncGE (n i : ℤ) (hi : i < n) :
    IsZero ((K.truncGE n).newHomology i) := by
  rw [isZero_homology_iff]
  exact ShortComplex.exact_of_isZero_X₂ _ (K.isZero_truncGEX _ _ hi)

lemma isIso_homologyMap_truncGEπ (n i : ℤ) (hi : n ≤ i) :
    IsIso (homologyMap (K.truncGEπ n) i) := by
  obtain (hi'|rfl) := hi.lt_or_eq
  . let α := (shortComplexFunctor' C (ComplexShape.up ℤ) (i - 1) i (i + 1)).map (truncGEπ K n)
    rw [isIso_homologyMap_iff' _ (i-1) i (i+1) (by simp) (by simp)]
    change IsIso (ShortComplex.homologyMap α)
    have : Epi α.τ₁ := by dsimp ; infer_instance
    have : IsIso α.τ₂ := by
      dsimp
      rw [K.truncGEπf_eq_truncGEXIso_inv _ _ hi']
      infer_instance
    have : IsIso α.τ₃ := by
      dsimp
      rw [K.truncGEπf_eq_truncGEXIso_inv _ _ (by linarith)]
      infer_instance
    apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono
  . apply isIso_homologyMap_of_isIso_opcyclesMap_of_mono _ n (n+1) (by simp)
    . refine' ⟨⟨(K.truncGE n).descOpcycles (K.truncGEXIsoOpcycles n n rfl).hom (n-1) (by simp) _,
        _, _⟩⟩
      . dsimp
        rw [K.truncGEd_eq_zero _ _ _ (by rfl), zero_comp]
      . simp only [← cancel_epi (K.pOpcycles n), opcyclesMap_comp_descOpcycles,
          truncGEπ_f, p_descOpcycles, K.truncGEπf_eq_of_eq, assoc, Iso.inv_hom_id]
      . dsimp
        have := (K.truncGE n).isIso_descOpcycles (n-1) n (by simp) (by simp)
        simp only [← cancel_mono ((K.truncGE n).descOpcycles (𝟙 ((K.truncGE n).X n)) (n-1)
          (by simp) (by simp)), assoc, opcyclesMap_comp_descOpcycles, truncGEπ_f,
          comp_id, id_comp, ← cancel_epi ((K.truncGE n).pOpcycles n)]
        dsimp
        simp only [← cancel_epi ((K.truncGEXIsoOpcycles n n rfl).inv),
          p_descOpcycles_assoc, p_descOpcycles, Iso.inv_hom_id_assoc,
          ← cancel_epi (K.pOpcycles n), comp_id, truncGEπf_eq_of_eq]
    . dsimp
      rw [K.truncGEπf_eq_truncGEXIso_inv _ _ (by linarith)]
      infer_instance

variable {K L}

lemma isIso_homologyMap_truncGEmap_iff (n i : ℤ) (hi : n ≤ i) :
    IsIso (homologyMap (truncGEmap φ n) i) ↔ IsIso (homologyMap φ i):= by
  symm
  have := K.isIso_homologyMap_truncGEπ _ _ hi
  have := L.isIso_homologyMap_truncGEπ _ _ hi
  apply isIso_iff_of_arrow_mk_iso
  refine' Arrow.isoMk (asIso (homologyMap (K.truncGEπ n) i))
    (asIso (homologyMap (L.truncGEπ n) i)) _
  dsimp
  simp only [← homologyMap_comp, truncGEπ_naturality]

lemma qis_truncGEmap_iff :
    qis _ _ (truncGEmap φ n) ↔ ∀ (i : ℤ) (_ : n ≤ i), IsIso (homologyMap φ i) := by
  constructor
  . intro h i hi
    rw [← isIso_homologyMap_truncGEmap_iff φ n i hi]
    apply h
  . intro h i
    by_cases hi : n ≤ i
    . rw [isIso_homologyMap_truncGEmap_iff φ n i hi]
      exact h _ hi
    . simp only [not_le] at hi
      refine' ⟨⟨0, _, _⟩⟩
      . apply (K.isZero_homology_truncGE n i hi).eq_of_src
      . apply (L.isZero_homology_truncGE n i hi).eq_of_src

variable (K)

lemma qis_truncGEπ_iff :
    qis _ _ (K.truncGEπ n) ↔ K.IsGE n := by
  constructor
  . intro h
    constructor
    intro i hi
    have h' := h i
    exact IsZero.of_iso (K.isZero_homology_truncGE _ _ hi)
      (asIso (homologyMap (truncGEπ K n) i))
  . intro h i
    by_cases hi : n ≤ i
    . exact K.isIso_homologyMap_truncGEπ n i hi
    . simp only [not_le] at hi
      refine' ⟨⟨0, _, _⟩⟩
      . apply (K.isZero_of_isGE n i hi).eq_of_src
      . apply (K.isZero_homology_truncGE n i hi).eq_of_src

instance (n : ℤ) [K.IsGE n] : IsIso (DerivedCategory.Q.map (K.truncGEπ n)) := by
  apply Localization.inverts DerivedCategory.Q (qis C _)
  rw [qis_truncGEπ_iff]
  infer_instance

variable (C)

@[simps]
noncomputable def functorTruncGE (n : ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := K.truncGE n
  map φ := truncGEmap φ n

@[simps]
noncomputable def natTransTruncGEπ (n : ℤ) : 𝟭 _ ⟶ functorTruncGE C n where
  app K := K.truncGEπ n

lemma qis_isInvertedBy_functorTruncGE_comp_Q (n : ℤ) :
    (qis C _).IsInvertedBy (functorTruncGE C n ⋙ DerivedCategory.Q) := fun K L f hf => by
  dsimp
  rw [DerivedCategory.isIso_Q_map_iff', qis_truncGEmap_iff]
  intro i _
  exact hf i

instance : (K.truncGE n).IsStrictlyGE n := ⟨K.isZero_truncGEX n⟩

instance (i : ℤ) [K.IsStrictlyLE i] : (K.truncGE n).IsStrictlyLE i := ⟨fun j hj => by
  by_cases hj' : j < n
  . exact K.isZero_truncGEX _ _ hj'
  . rw [IsZero.iff_id_eq_zero, ← cancel_epi (K.truncGEπf n j)]
    apply IsZero.eq_of_src
    exact K.isZero_of_isStrictlyLE i j (by linarith)⟩

instance (i : ℤ) [K.IsStrictlyGE i] : (K.truncGE n).IsStrictlyGE i := ⟨fun j hj => by
  by_cases hj' : j < n
  . exact K.isZero_truncGEX _ _ hj'
  . rw [IsZero.iff_id_eq_zero, ← cancel_epi (K.truncGEπf n j)]
    apply IsZero.eq_of_src
    exact K.isZero_of_isStrictlyGE i j (by linarith)⟩

lemma isIso_truncGEπ_iff (n : ℤ) : IsIso (K.truncGEπ n) ↔ K.IsStrictlyGE n := by
  constructor
  . intro hK
    constructor
    intro i hi
    exact IsZero.of_iso (isZero_truncGEX _ _ _ hi)
      ((eval _ _ i).mapIso (asIso (K.truncGEπ n)))
  . intro hK
    suffices ∀ (i : ℤ), IsIso ((K.truncGEπ n).f i) by
      apply HomologicalComplex.Hom.isIso_of_components
    intro i
    dsimp
    by_cases hi : n < i
    . rw [truncGEπf_eq_truncGEXIso_inv _ _ _ hi]
      infer_instance
    . obtain (hi'|rfl) := (not_lt.1 hi).lt_or_eq
      . exact ⟨0, (K.isZero_of_isStrictlyGE n i hi').eq_of_src _ _,
          (K.isZero_truncGEX n i hi').eq_of_src _ _⟩
      . have := K.isIso_pOpcycles (i-1) i (by simp)
          ((K.isZero_of_isStrictlyGE i (i-1) (by simp)).eq_of_src _ _)
        rw [K.truncGEπf_eq_of_eq i i rfl]
        infer_instance

instance (n : ℤ) [K.IsStrictlyGE n] : IsIso (K.truncGEπ n) := by
  rw [K.isIso_truncGEπ_iff]
  infer_instance

variable {C}

end CochainComplex

namespace DerivedCategory

variable (C)

noncomputable def functorTruncGE (n : ℤ) : DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift _ (CochainComplex.qis_isInvertedBy_functorTruncGE_comp_Q C n) Q

noncomputable def functorTruncGEFactors (n : ℤ) :
    Q ⋙ functorTruncGE C n ≅ CochainComplex.functorTruncGE C n ⋙ Q :=
  Localization.fac _ _ _

noncomputable instance : Localization.Lifting Q (HomologicalComplex.qis C _)
    (CochainComplex.functorTruncGE C n ⋙ Q) (functorTruncGE C n) :=
  ⟨functorTruncGEFactors C n⟩

noncomputable def natTransTruncGEπ (n : ℤ) : 𝟭 _ ⟶ functorTruncGE C n :=
  Localization.liftNatTrans Q (HomologicalComplex.qis C _)
    Q (CochainComplex.functorTruncGE C n ⋙ Q) _ _
      (whiskerRight (CochainComplex.natTransTruncGEπ C n) Q)

noncomputable def QCompFunctorTruncGECompHomologyFunctorIso (n i : ℤ) :
    Q ⋙ functorTruncGE C n ⋙ homologyFunctor C i ≅
      CochainComplex.functorTruncGE C n ⋙
        HomologicalComplex.newHomologyFunctor _ _ i :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (functorTruncGEFactors C n) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (homologyFunctorFactors _ i)

variable {C}

noncomputable abbrev truncGE (X : DerivedCategory C) (n : ℤ) := (functorTruncGE C n).obj X

lemma isZero_homology_truncGE (X : DerivedCategory C) (n i : ℤ) (hi : i < n) :
    IsZero ((homologyFunctor C i).obj (X.truncGE n)) := by
  revert n i hi X
  apply induction_Q_obj
  . intro K n i hi
    exact IsZero.of_iso (K.isZero_homology_truncGE n i hi)
      ((QCompFunctorTruncGECompHomologyFunctorIso C n i).app K)
  . intros X Y e hX n i hi
    exact IsZero.of_iso (hX n i hi) ((homologyFunctor _ _).mapIso
      ((functorTruncGE C n).mapIso e.symm))

noncomputable abbrev truncGEπ (X : DerivedCategory C) (n : ℤ) :=
  (natTransTruncGEπ C n).app X

@[reassoc (attr := simp)]
lemma truncGEπ_naturality {X Y : DerivedCategory C} (f : X ⟶ Y) (n : ℤ) :
    X.truncGEπ n ≫ (functorTruncGE C n).map f = f ≫ Y.truncGEπ n :=
  ((natTransTruncGEπ C n).naturality f).symm

lemma truncGEπ_app (K : CochainComplex C ℤ) (n : ℤ) :
    (Q.obj K).truncGEπ n =
      Q.map (K.truncGEπ n) ≫ (functorTruncGEFactors C n).inv.app K := by
  dsimp [truncGEπ, natTransTruncGEπ]
  rw [Localization.liftNatTrans_app]
  dsimp only [Localization.Lifting.iso, Localization.Lifting.iso']
  simp

lemma isIso_homologyMap_truncGEπ (X : DerivedCategory C) (n i : ℤ) (hi : n ≤ i) :
    IsIso ((homologyFunctor C i).map (X.truncGEπ n)) := by
  revert n i hi X
  apply induction_Q_obj
  . intro K n i hi
    rw [truncGEπ_app, Functor.map_comp]
    have : IsIso ((homologyFunctor C i).map ((functorTruncGEFactors C n).inv.app K)) := inferInstance
    have : IsIso ((homologyFunctor C i).map (Q.map (K.truncGEπ n))) := by
      erw [NatIso.isIso_map_iff (homologyFunctorFactors C i) (K.truncGEπ n)]
      exact K.isIso_homologyMap_truncGEπ n i hi
    apply IsIso.comp_isIso
  . intros X Y e hX n i hi
    exact ((MorphismProperty.RespectsIso.isomorphisms C).arrow_iso_iff
      ((homologyFunctor C i).mapArrow.mapIso
        ((NatTrans.functorArrow (natTransTruncGEπ C n)).mapIso e))).1 (hX n i hi)

lemma isIso_truncGEπ_iff (X : DerivedCategory C) (n : ℤ) :
    IsIso (X.truncGEπ n) ↔ X.IsGE n := by
  constructor
  . intro hX
    constructor
    intro i hi
    exact IsZero.of_iso (isZero_homology_truncGE _ _ _ hi)
      ((homologyFunctor C i).mapIso (asIso (truncGEπ X n)))
  . intro hX
    rw [isIso_iff]
    intro i
    by_cases hi : n ≤ i
    . exact X.isIso_homologyMap_truncGEπ _ _ hi
    . simp only [not_le] at hi
      refine' ⟨0, _, _⟩
      . apply (X.isZero_of_isGE n i hi).eq_of_src
      . apply (X.isZero_homology_truncGE n i hi).eq_of_src

lemma isZero_truncGE_iff (X : DerivedCategory C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsZero (X.truncGE n₁) ↔ X.IsLE n₀ := by
  have h : ∀ (i : ℤ) (_ : n₀ < i), (homologyFunctor C i).obj X ≅
      (homologyFunctor C i).obj (X.truncGE n₁) := fun i hi => by
    have := X.isIso_homologyMap_truncGEπ n₁ i (by linarith)
    exact (asIso ((homologyFunctor C i).map (X.truncGEπ n₁)))
  constructor
  . intro hX
    constructor
    intro i hi
    refine' IsZero.of_iso _ (h i hi)
    rw [IsZero.iff_id_eq_zero] at hX ⊢
    rw [← (homologyFunctor C i).map_id, hX, Functor.map_zero]
  . intro hX
    rw [isZero_iff]
    intro i
    by_cases hi : n₀ < i
    . exact IsZero.of_iso (X.isZero_of_isLE n₀ i hi) (h i hi).symm
    . exact X.isZero_homology_truncGE _ _ (by linarith)

instance (X : DerivedCategory C) (n : ℤ) [X.IsGE n] : IsIso (X.truncGEπ n) := by
  rw [isIso_truncGEπ_iff]
  infer_instance

instance (X : DerivedCategory C) (n : ℤ) : (X.truncGE n).IsGE n := by
  revert X
  apply induction_Q_obj
  . intro K
    have e : _ ≅ Q.obj (K.truncGE n) := (functorTruncGEFactors C n).app K
    apply isGE_of_iso e.symm n
  . intros X Y e hX
    exact isGE_of_iso ((functorTruncGE C n).mapIso e) n

lemma left_fac_of_isStrictlyGE (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) (n : ℤ)
    [Y.IsStrictlyGE n] :
    ∃ (Y' : CochainComplex C ℤ) (_ : Y'.IsStrictlyGE n) (g : X ⟶ Y') (s : Y ⟶ Y')
      (hs : IsIso (Q.map s)), f = Q.map g ≫ inv (Q.map s) := by
  obtain ⟨Y', g, s, hs, rfl⟩ := left_fac X Y f
  have : IsIso (Q.map (CochainComplex.truncGEmap s n)) := by
    rw [isIso_Q_map_iff', CochainComplex.qis_truncGEmap_iff]
    rw [isIso_Q_map_iff'] at hs
    intro i _
    exact hs i
  refine' ⟨Y'.truncGE n, inferInstance, X.truncGEπ n ≫ CochainComplex.truncGEmap g n,
    Y.truncGEπ n ≫ CochainComplex.truncGEmap s n, _, _⟩
  . rw [Q.map_comp]
    infer_instance
  . have eq := Q.congr_map (CochainComplex.truncGEπ_naturality s n)
    have eq' := Q.congr_map (CochainComplex.truncGEπ_naturality g n)
    simp only [Functor.map_comp] at eq eq'
    simp only [Functor.map_comp, ← cancel_mono (Q.map (CochainComplex.truncGEπ Y n)
      ≫ Q.map (CochainComplex.truncGEmap s n)), assoc, IsIso.inv_hom_id, comp_id]
    simp only [eq, IsIso.inv_hom_id_assoc, eq']

end DerivedCategory
