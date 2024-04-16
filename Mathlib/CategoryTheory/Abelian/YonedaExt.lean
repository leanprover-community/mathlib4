import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.DerivedCategory.LargeExt
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type _} [Category C] [Abelian C] [HasDerivedCategory C]

namespace Abelian

structure IteratedExtCategory (X₁ X₂ : C) (n : ℕ) where
  K : CochainComplex C ℤ
  hK₀ : K.IsStrictlyGE 0
  hK₁ : K.IsStrictlyLE (n+2)
  hK (i : ℤ) : K.ExactAt i --IsZero (K.homology n)
  iso₁ : K.X (n+2) ≅ X₁
  iso₂ : K.X 0 ≅ X₂

attribute [instance] IteratedExtCategory.hK₀ IteratedExtCategory.hK₁

inductive YonedaExt' (X₁ X₂ : C) : ℕ → Type _
  | ofHom (f : X₁ ⟶ X₂) : YonedaExt' X₁ X₂ 0
  | ofExt {n : ℕ} (E : IteratedExtCategory X₁ X₂ n) : YonedaExt' X₁ X₂ (n+1)

namespace IteratedExtCategory

variable {X₁ X₂ : C} {n : ℕ} (E : IteratedExtCategory X₁ X₂ n)

lemma hK' (i : ℤ) : IsZero (E.K.homology i) := by
  rw [← E.K.exactAt_iff_isZero_homology i]
  exact E.hK i

lemma epi_d (i j : ℤ) (hij : i + 1 = j) (hm : i = n + 1) :
    Epi (E.K.d i j) := by
  have h := E.hK j
  rw [E.K.exactAt_iff' i j (j+1) (by simp; linarith) (by simp),
    ShortComplex.exact_iff_epi] at h; swap
  · exact (E.K.isZero_of_isStrictlyLE (n+2) _ (by linarith)).eq_of_tgt _ _
  exact h

lemma mono_d : Mono (E.K.d 0 1) := by
  have h := E.hK 0
  rw [E.K.exactAt_iff' (-1) 0 1 (by simp) (by simp),
    ShortComplex.exact_iff_mono] at h; swap
  · exact (E.K.isZero_of_isStrictlyGE 0 _ (by linarith)).eq_of_src _ _
  exact h

--X₂                                                    X₁
--K.X 0 ⟶ K.X 1 ⟶ K.X 2 ⟶ ..... ⟶ K.X n ⟶ K.X (n+1) ⟶ K.X (n+2)

noncomputable def Z.X (d : ℤ) : C := if d = 1 then 0 else E.K.X (d+n+1)

--Z.X (-(n+1)) = X₂
--Z.X (-n) = K.X 1
--Z.X (-1) = K.X n
--Z.X 0 = K.X (n+1)

noncomputable def Z.XIso (d i : ℤ) (hi : d + n + 1 = i) (hd : d ≠ 1) :
    Z.X E d ≅ E.K.X i := eqToIso (by
  dsimp [Z.X]
  rw [if_neg hd]
  congr)

noncomputable def Z.d (a b : ℤ) : Z.X E a ⟶ Z.X E b :=
  if ha : a = 1 then 0
    else if hb : b = 1 then 0
      else
        (Z.XIso E a _ rfl ha).hom ≫ E.K.d _ _ ≫ (Z.XIso E b _ rfl hb).inv

@[pp_dot]
noncomputable def Z : CochainComplex C ℤ where
  X := Z.X E
  d := Z.d E
  shape i j hij := by
    dsimp [Z.d]
    split_ifs
    · rfl
    · rfl
    · rw [E.K.shape, zero_comp, comp_zero]
      dsimp at hij ⊢
      intro
      apply hij
      linarith
  d_comp_d' i j k _ _ := by
    dsimp [Z.d]
    split_ifs <;> simp

noncomputable abbrev ZXIso (d i : ℤ) (hi : d + n + 1 = i) (hd : d ≠ 1) :
    E.Z.X d ≅ E.K.X i := Z.XIso E d i hi hd

noncomputable def ZXIso₂ (d : ℤ) (hi : d + n + 1 = 0) : E.Z.X d ≅ X₂ :=
  Z.XIso E d 0 hi (fun hd => by linarith) ≪≫ E.iso₂

lemma Z_d_eq (a b : ℤ) (i j : ℤ) (hi : a + n + 1 = i)
    (hj : b + n + 1 = j) (ha : a ≠ 1) (hb : b ≠ 1): E.Z.d a b =
    (Z.XIso E a i hi ha).hom ≫ E.K.d i j ≫ (Z.XIso E b j hj hb).inv := by
  subst hi hj
  dsimp [Z, Z.d]
  rw [dif_neg ha, dif_neg hb]

lemma isZero_Z_X_of_le (a : ℤ) (ha : a ≤ -n-2) : IsZero (E.Z.X a) := by
  dsimp [Z, Z.X]
  rw [if_neg] ; swap
  · rintro rfl
    have hn : 0 ≤ (n : ℤ) := Nat.cast_nonneg n
    linarith
  exact E.K.isZero_of_isStrictlyGE 0 _ (by linarith)

lemma isZero_Z_X_of_ge (a : ℤ) (ha : 1 ≤ a) : IsZero (E.Z.X a) := by
  dsimp [Z, Z.X]
  obtain (ha'|rfl) := ha.lt_or_eq
  · rw [if_neg (by linarith)]
    exact E.K.isZero_of_isStrictlyLE (n+2) _ (by linarith)
  · simp only [ite_true]
    exact isZero_zero _

instance : E.Z.IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro a ha
  exact E.isZero_Z_X_of_ge a (by omega)

instance : E.Z.IsStrictlyGE (-n-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro a ha
  exact E.isZero_Z_X_of_le a (by omega)

noncomputable def ZToX₁ : E.Z ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X₁ :=
  (HomologicalComplex.toSingleEquiv X₁ E.Z (-1) 0 (by simp)).symm
    ⟨(Z.XIso E 0 (n+1) (by linarith) (by linarith)).hom ≫ E.K.d (n+1) (n+2) ≫ E.iso₁.hom, by
      simp [E.Z_d_eq (-1) 0 n (n+1) (by linarith) (by linarith) (by linarith) (by linarith)]⟩

@[simp]
lemma ZToX₁_f_0 : E.ZToX₁.f 0 =
    (Z.XIso E 0 (n+1) (by linarith) (by linarith)).hom ≫ E.K.d (n+1) (n+2) ≫ E.iso₁.hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X₁).inv := by
  dsimp [ZToX₁, HomologicalComplex.toSingleEquiv]
  simp

noncomputable def ZToX₂ (n' : ℤ) (hn' : n' + n + 1 = 0) :
    E.Z ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) n').obj X₂ :=
  (HomologicalComplex.toSingleEquiv X₂ E.Z (n'-1) n' (by simp)).symm
    ⟨(Z.XIso E n' 0 hn' (by linarith)).hom ≫ E.iso₂.hom, by
      apply IsZero.eq_of_src
      apply E.isZero_Z_X_of_le
      linarith⟩

lemma ZToX₂_f_self (n' : ℤ) (hn' : n' + n + 1 = 0) :
    (E.ZToX₂ n' hn').f n' = (Z.XIso E n' 0 hn' (by linarith)).hom ≫ E.iso₂.hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n' X₂).inv := by
  dsimp [ZToX₂, HomologicalComplex.toSingleEquiv]
  simp

lemma isZero_homology_ZToX₁ (d : ℤ) (hd : d ≠ 0) :
    IsZero (E.Z.homology d) := by
  by_cases h : 0 < d
  · apply ShortComplex.isZero_homology_of_isZero_X₂
    dsimp
    apply isZero_Z_X_of_ge
    linarith
  · have hd' : d + 1 ≠ 1 := fun _ => hd (by linarith)
    refine' IsZero.of_iso (E.hK' (d+n+1)) (ShortComplex.homologyMapIso
      ((HomologicalComplex.natIsoSc' C (ComplexShape.up ℤ) (d-1) d (d+1)
        (by simp) (by simp)).app E.Z ≪≫ _ ≪≫
        ((HomologicalComplex.natIsoSc' C (ComplexShape.up ℤ) (d+n) (d+n+1) (d+n+2)
          (by simp) (by simp only [CochainComplex.next] ; linarith)).app E.K).symm))
    refine' ShortComplex.isoMk (Z.XIso E _ _ (by linarith) (by linarith))
      (Z.XIso E _ _ rfl (by linarith)) (Z.XIso E _ _ (by linarith) hd') _ _
    · simp [E.Z_d_eq (d-1) d (d+n) (d+n+1) (by linarith) (by linarith) (by linarith) (by linarith)]
    · simp [E.Z_d_eq d (d+1) (d+n+1) (d+n+2) (by linarith) (by linarith) (by linarith) hd']

@[simps]
noncomputable def shortComplex : ShortComplex C where
  X₁ := E.Z.X (-1)
  X₂ := E.Z.X 0
  X₃ := X₁
  f := E.Z.d (-1) 0
  g := (Z.XIso E 0 (n+1) (by linarith) (by linarith)).hom ≫ E.K.d (n+1) (n+2) ≫ E.iso₁.hom
  zero := by
    simp [E.Z_d_eq (-1) 0 n (n+1) (by linarith) (by linarith) (by linarith) (by linarith)]

lemma shortComplex_exact : E.shortComplex.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine' IsZero.of_iso (E.hK' (n+1)) (ShortComplex.homologyMapIso
    (_ ≪≫ (HomologicalComplex.natIsoSc' C (ComplexShape.up ℤ) n (n+1) (n+2)
      (by simp) (by simp ; linarith)).symm.app _))
  refine' ShortComplex.isoMk (by exact Z.XIso E (-1) n (by linarith) (by linarith))
    (Z.XIso E 0 (n+1) (by linarith) (by linarith)) E.iso₁.symm _ _
  · simp [E.Z_d_eq (-1) 0 n (n+1) (by linarith) (by linarith) (by linarith) (by linarith)]
  · simp

attribute [local instance] epi_comp

instance : Epi E.shortComplex.g := by
  suffices Epi (E.K.d (n+1) (n+2)) by
    dsimp
    infer_instance
  have h : (E.K.sc' (n+1) (n+2) (n+3)).Exact := by
    refine' ShortComplex.exact_of_iso
      ((HomologicalComplex.natIsoSc' C (ComplexShape.up ℤ) (n+1) (n+2) (n+3)
        (by simp only [CochainComplex.prev] ; linarith)
        (by simp only [CochainComplex.next] ; linarith)).app E.K) _
    rw [ShortComplex.exact_iff_isZero_homology]
    apply E.hK'
  rw [ShortComplex.exact_iff_epi _
    (IsZero.eq_of_tgt (E.K.isZero_of_isStrictlyLE  (n+2) _ (by linarith)) _ _)] at h
  exact h

@[simps!]
noncomputable def leftHomologyData : (E.Z.sc' (-1) 0 1).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork (E.Z.sc' (-1) 0 1)
    (IsZero.eq_of_tgt (E.isZero_Z_X_of_ge 1 (by rfl)) _ _) _ E.shortComplex_exact.gIsCokernel

@[simp]
lemma leftHomologyData_f' : E.leftHomologyData.f' = E.Z.d (-1) 0 := by
  rw [← cancel_mono (E.leftHomologyData.i), ShortComplex.LeftHomologyData.f'_i]
  dsimp
  rw [comp_id]

@[simps]
noncomputable def leftHomologyMapData : ShortComplex.LeftHomologyMapData
    ((HomologicalComplex.shortComplexFunctor' _ _ (-1) 0 1).map E.ZToX₁) E.leftHomologyData
    (ShortComplex.LeftHomologyData.ofZeros _ (by simp) (by simp)) where
  φK := (Z.XIso E 0 (n+1) (by linarith) (by linarith)).hom ≫ E.K.d (n+1) (n+2) ≫ E.iso₁.hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X₁).hom
  φH := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X₁).hom
  commf' := by
    dsimp
    simp only [leftHomologyData_f', ShortComplex.LeftHomologyData.ofZeros_f', comp_zero,
      E.Z_d_eq (-1) 0 n (n+1) (by linarith) (by linarith) (by linarith) (by linarith), assoc,
      Iso.inv_hom_id_assoc, E.K.d_comp_d_assoc, zero_comp]
  commi := by
    simp [ZToX₁, HomologicalComplex.toSingleEquiv]
    erw [comp_id]

instance : QuasiIso E.ZToX₁ where
  quasiIsoAt n := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases h : n = 0
    · subst h
      suffices IsIso (ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' _ _ (-1) 0 1).map E.ZToX₁)) from
        (NatIso.isIso_map_iff (isoWhiskerRight
          (HomologicalComplex.natIsoSc' C (ComplexShape.up ℤ) (-1) 0 1 (by simp) (by simp))
          (ShortComplex.homologyFunctor _ )) E.ZToX₁).2 this
      rw [E.leftHomologyMapData.homologyMap_eq]
      dsimp
      erw [id_comp]
      infer_instance
    · refine' ⟨0, IsZero.eq_of_src (E.isZero_homology_ZToX₁ n h) _ _,
        IsZero.eq_of_src (ShortComplex.isZero_homology_of_isZero_X₂ _ _) _ _⟩
      dsimp [HomologicalComplex.single]
      rw [if_neg h]
      exact isZero_zero _

noncomputable def shiftedHom (m : ℕ) (hm : n + 1 = m) :
    ShiftedHom ℤ ((DerivedCategory.singleFunctor C 0).obj X₁)
      ((DerivedCategory.singleFunctor C 0).obj X₂) ↑m :=
    (SingleFunctors.evaluationIso (DerivedCategory.singleFunctorsPostCompQIso C) 0).hom.app X₁ ≫
      inv (DerivedCategory.Q.map E.ZToX₁) ≫
      DerivedCategory.Q.map (E.ZToX₂ (-m) (by simp [← hm])) ≫
      (SingleFunctors.evaluationIso (DerivedCategory.singleFunctorsPostCompQIso C) (-m)).inv.app X₂ ≫
      ((DerivedCategory.singleFunctors C).shiftIso m (-m) 0 (add_right_neg _)).inv.app X₂

noncomputable def largeExtClass (m : ℕ) (hm : n + 1 = m) : LargeExt X₁ X₂ m :=
  LargeExt.mk (shiftedHom E m hm)

section composition

variable {X₃ : C} {n' : ℕ} (E' : IteratedExtCategory X₂ X₃ n') {n'' : ℕ} (hn'' : n + n' +1 = n'')

def compKX (i : ℤ) : C :=
  if i ≤ n' + 1
    then E'.K.X i
    else E.K.X (i - n' - 1)

def compKXIso' (i : ℤ) (hi : i ≤ n'+1) :
  compKX E E' i ≅ E'.K.X i := eqToIso (by
    dsimp [compKX]
    rw [if_pos hi])

def compKXIso (i : ℤ) (j : ℤ) (hi : n'+2 ≤ i) (hij : j + n' + 1 = i) :
  compKX E E' i ≅ E.K.X j := eqToIso (by
    dsimp [compKX]
    obtain rfl : j = i - n' - 1 := by linarith
    rw [if_neg]
    intro
    linarith)

def compKd (i j : ℤ) : compKX E E' i ⟶ compKX E E' j :=
  if hij : i + 1 = j then
    if h₁ : i ≤ n' then
      (compKXIso' E E' i (by linarith)).hom ≫ E'.K.d i j ≫
        (compKXIso' E E' j (by linarith)).inv
    else
      if h₂ : n'+2 ≤ i then
        (compKXIso E E' i (i - n' - 1) h₂ (by linarith)).hom ≫ E.K.d _ _ ≫
          (compKXIso E E' j (j - n' - 1) (by linarith) (by linarith)).inv
      else
        (compKXIso' E E' i (by linarith)).hom ≫
          E'.K.d i (n'+2) ≫ E'.iso₁.hom ≫ E.iso₂.inv ≫ E.K.d 0 1 ≫
          (compKXIso E E' j 1 (by linarith) (by linarith)).inv
  else 0

lemma compKd_shape (i j : ℤ) (hij : ¬ i+1=j) :
    compKd E E' i j = 0 := by
  dsimp only [compKd]
  rw [dif_neg hij]

lemma compKd_eq_d' (i j : ℤ) (hij : i + 1 = j) (hi : i ≤ n') :
    compKd E E' i j = (compKXIso' E E' i (by linarith)).hom ≫ E'.K.d i j ≫
      (compKXIso' E E' j (by linarith)).inv := by
  dsimp [compKd]
  rw [dif_pos hij, dif_pos hi]

lemma compKd_eq_d (i j : ℤ) (hij : i + 1 = j) (hi : n'+2 ≤ i) (i' j' : ℤ) (hi' : i' + n' + 1 = i) (hj' : j' + n' + 1 = j) :
    compKd E E' i j = (compKXIso E E' i i' hi (by linarith)).hom ≫ E.K.d _ _ ≫
      (compKXIso E E' j j' (by linarith) (by linarith)).inv := by
  obtain rfl : i' = i - n' -1 := by linarith
  obtain rfl : j' = j - n' -1 := by linarith
  dsimp [compKd]
  rw [dif_pos hij, dif_neg (by linarith), dif_pos hi]

lemma compKd_eq_d'_comp_d (i j : ℤ) (hij : i + 1 = j) (hi : i = n' + 1) :
    compKd E E' i j = (compKXIso' E E' i (by linarith)).hom ≫
      E'.K.d i (n'+2) ≫ E'.iso₁.hom ≫ E.iso₂.inv ≫ E.K.d 0 1 ≫
      (compKXIso E E' j 1 (by linarith) (by linarith)).inv := by
  dsimp [compKd]
  rw [dif_pos (by linarith), dif_neg (by linarith), dif_neg (by linarith)]

lemma compKd_comp_d' (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    compKd E E' i j ≫ compKd E E' j k = 0 := by
  by_cases hj : j ≤ n'
  · rw [compKd_eq_d' E E' i j hij (by linarith), compKd_eq_d' E E' j k hjk (by linarith)]
    simp
  · by_cases hi : n'+2 ≤ i
    · rw [compKd_eq_d E E' i j hij (by linarith) (i - n' -1) (j - n' -1)
          (by linarith) (by linarith),
        compKd_eq_d E E' j k hjk (by linarith) (j - n' -1) (k - n' -1)
          (by linarith) (by linarith)]
      simp
    · have hi₁ : i ≤ n' + 1 := by linarith
      cases (show n' ≤ i by linarith).eq_or_lt
      · rw [compKd_eq_d' E E' i j hij (by linarith),
          compKd_eq_d'_comp_d E E' j k hjk (by linarith)]
        simp
      · rw [compKd_eq_d'_comp_d E E' i j hij (by linarith),
          compKd_eq_d E E' j k hjk (by linarith) 1 2 (by linarith) (by linarith)]
        simp

@[simps]
def compK : CochainComplex C ℤ where
  X := compKX E E'
  d := compKd E E'
  shape := compKd_shape E E'
  d_comp_d' := compKd_comp_d' E E'

@[simps]
def compShortComplex₄ : ShortComplex₄ C where
  f := (compK E E').d n' (n'+1)
  g := (compK E E').d (n'+1) (n'+2)
  h := (compK E E').d (n'+2) (n'+3)
  zero₁ := compKd_comp_d' _ _ _ _ _ (by linarith) (by linarith)
  zero₂ := compKd_comp_d' _ _ _ _ _ (by linarith) (by linarith)

def compShortComplex₄Iso :
  (compShortComplex₄ E E') ≅
    ShortComplex₄.connectShortComplex
      (E'.K.sc' n' (n'+1) (n'+2)) (E.K.sc' 0 1 2) (E'.iso₁ ≪≫ E.iso₂.symm) _ rfl := by
  refine' ShortComplex₄.isoMk
    (compKXIso' E E' n' (by linarith))
    (compKXIso' E E' (n'+1) (by linarith))
    (compKXIso E E' (n'+2) 1 (by linarith) (by linarith))
    (compKXIso E E' (n'+3) 2 (by linarith) (by linarith)) _ _ _
  · simp [compKd_eq_d' E E' n' (n'+1) (by linarith) (by linarith)]
  · simp [compKd_eq_d'_comp_d E E' (n'+1) (n'+2) (by linarith) (by linarith)]
  · simp [compKd_eq_d E E' (n'+2) (n'+3) (by linarith) (by linarith)
      1 2 (by linarith) (by linarith)]

lemma compShortComplex₄_exact :
    (compShortComplex₄ E E').Exact := by
  rw [ShortComplex₄.exact_iff_of_iso (compShortComplex₄Iso E E')]
  have : Epi (E'.K.sc' n' (n' + 1) (n' + 2)).g :=
    E'.epi_d (n'+1) (n'+2) (by linarith) (by linarith)
  have : Mono (E.K.sc' 0 1 2).f := E.mono_d
  apply ShortComplex₄.connectShortComplex_exact
  · rw [← E'.K.exactAt_iff' n' (n'+1) (n'+2) (by simp) (by simp; linarith)]
    exact E'.hK _
  · rw [← E.K.exactAt_iff' 0 1 2 (by simp) (by simp)]
    exact E.hK _

def comp : IteratedExtCategory X₁ X₃ n'' where
  K := compK E E'
  hK₀ := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact IsZero.of_iso (E'.K.isZero_of_isStrictlyGE 0 i hi)
      (compKXIso' E E' i (by linarith))
  hK₁ := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact IsZero.of_iso (E.K.isZero_of_isStrictlyLE (n+2) (i - n' - 1) (by linarith))
      (compKXIso E E' i (i - n' - 1) (by linarith) (by linarith))
  hK i := by
    by_cases i ≤ n'
    · have e : (compK E E').sc' (i-1) i (i+1) ≅ E'.K.sc' (i-1) i (i+1) := by
        refine' ShortComplex.isoMk (compKXIso' E E' (i-1) (by linarith))
          (compKXIso' E E' i (by linarith))
          (compKXIso' E E' (i+1) (by linarith)) _ _
        · simp [compKd_eq_d' E E' (i-1) i (by linarith) (by linarith)]
        · simp [compKd_eq_d' E E' i (i+1) (by linarith) (by linarith)]
      rw [(compK E E').exactAt_iff' (i-1) i (i+1) (by simp) (by simp),
        ShortComplex.exact_iff_of_iso e,
        ← E'.K.exactAt_iff' (i-1) i (i+1) (by simp) (by simp)]
      exact E'.hK i
    · by_cases n' + 3 ≤ i
      · obtain ⟨j, hj⟩ : ∃ (j : ℤ), j = i-n'-1 := ⟨_, rfl⟩
        have e : (compK E E').sc' (i-1) i (i+1) ≅ E.K.sc' (j-1) j (j+1) := by
          refine' ShortComplex.isoMk
            (compKXIso E E' (i-1) (j-1) (by linarith) (by linarith))
            (compKXIso E E' i j (by linarith) (by linarith))
            (compKXIso E E' (i+1) (j+1) (by linarith) (by linarith)) _ _
          · simp [compKd_eq_d E E' (i-1) i (by linarith) (by linarith)
              (j-1) j (by linarith) (by linarith)]
          · simp [compKd_eq_d E E' i (i+1) (by linarith) (by linarith)
              j (j+1) (by linarith) (by linarith)]
        rw [(compK E E').exactAt_iff' (i-1) i (i+1) (by simp) (by simp),
          ShortComplex.exact_iff_of_iso e,
          ← E.K.exactAt_iff' (j-1) j (j+1) (by simp) (by simp)]
        exact E.hK j
      · obtain rfl | _ := (show n' +1 ≤ i by linarith).eq_or_lt
        · rw [(compK E E').exactAt_iff' n' (n'+1) (n'+2) (by simp) (by simp; linarith)]
          exact (compShortComplex₄_exact E E').exact₂
        · obtain rfl : i = n' + 2 := by linarith
          rw [(compK E E').exactAt_iff' (n'+1) (n'+2) (n'+3) (by simp; linarith) (by simp; linarith)]
          exact (compShortComplex₄_exact E E').exact₃
  iso₁ := compKXIso E E' (n'' + 2) (n+2) (by linarith) (by
      simp only [← hn'', Nat.cast_add, Nat.cast_one]
      linarith) ≪≫ E.iso₁
  iso₂ := compKXIso' E E' 0 (by linarith) ≪≫ E'.iso₂


lemma comp_K_d_eq_d' (i j : ℤ) (hij : i + 1 = j) (hi : i ≤ n') :
    (comp E E' hn'').K.d i j = (compKXIso' E E' i (by linarith)).hom ≫ E'.K.d i j ≫
      (compKXIso' E E' j (by linarith)).inv :=
  compKd_eq_d' E E' i j hij hi

lemma comp_K_d_eq_d (i j : ℤ) (hij : i + 1 = j) (hi : n'+2 ≤ i) (i' j' : ℤ) (hi' : i' + n' + 1 = i) (hj' : j' + n' + 1 = j) :
    (comp E E' hn'').K.d i j = (compKXIso E E' i i' hi (by linarith)).hom ≫ E.K.d _ _ ≫
      (compKXIso E E' j j' (by linarith) (by linarith)).inv :=
  compKd_eq_d E E' i j hij hi i' j' hi' hj'

lemma comp_K_d_eq_d'_comp_d (i j : ℤ) (hij : i + 1 = j) (hi : i = n' + 1) :
    (comp E E' hn'').K.d i j = (compKXIso' E E' i (by linarith)).hom ≫
      E'.K.d i (n'+2) ≫ E'.iso₁.hom ≫ E.iso₂.inv ≫ E.K.d 0 1 ≫
      (compKXIso E E' j 1 (by linarith) (by linarith)).inv :=
  compKd_eq_d'_comp_d E E' i j hij hi

variable (m m' m'' : ℕ) (hm : n + 1 = m) (hm' : n' + 1 = m') (hm'' : n'' + 1 = m'')
  (k : ℤ) (hk : k + m = 0) (k' : ℤ) (hk' : k' + m' = 0) (k'' : ℤ) (hk'' : k'' + m'' = 0)

noncomputable def compZToZf (i : ℤ) : (comp E E' hn'').Z.X i ⟶ E.Z.X i :=
  if hi' : 0 ≤ i + n then
    if hi : i ≠ 1 then
      ((comp E E' hn'').ZXIso i (i + n'' + 1) rfl hi).hom ≫
        (compKXIso E E' (i + n'' + 1) (i + n + 1) (by
          simp only [← hn'', Nat.cast_add, Nat.cast_one]
          linarith) (by linarith)).hom ≫
        (E.ZXIso i (i + n + 1) rfl hi).inv
    else 0
  else if hi' : i = -n - 1 then
      ((comp E E' hn'').ZXIso i (n'+1) (by linarith) (by linarith)).hom ≫
        (compKXIso' E E' (n'+1) (by linarith)).hom ≫
        E'.K.d (n'+1) (n'+2) ≫ E'.iso₁.hom ≫ E.iso₂.inv ≫ (E.ZXIso i 0 (by linarith) (by linarith)).inv
    else
      0

lemma compZToZf_eq (i j k : ℤ) (hi : i ≤ 0) (hi' : 0 ≤ i + n)
    (hij : i + n + 1 = j) (hjk : j + n' + 1 = k) :
  compZToZf E E' hn'' i =
    ((comp E E' hn'').ZXIso i k (by linarith) (by linarith)).hom ≫
      (compKXIso E E' k j (by linarith) hjk).hom ≫ (E.ZXIso i j hij (by linarith)).inv := by
  dsimp only [compZToZf]
  rw [dif_pos hi', dif_pos (by linarith)]
  obtain rfl : k = i + n'' + 1 := by linarith
  obtain rfl : j = i + n + 1 := by linarith
  rfl

lemma compZToZf_eq' :
    compZToZf E E' hn'' (-n-1) =
      ((comp E E' hn'').ZXIso (-n -1) (n'+1) (by linarith) (by linarith)).hom ≫
      (compKXIso' E E' (n'+1) (by linarith)).hom ≫ E'.K.d (n'+1) (n'+2) ≫
      E'.iso₁.hom ≫E.iso₂.inv ≫  (E.ZXIso (-n-1) 0 (by linarith) (by linarith)).inv := by
  dsimp [compZToZf]
  rw [dif_neg (by linarith), dif_pos rfl]

lemma compZToZf_eq_zero_of_le (i : ℤ) (hi : i ≤ - n - 2) :
    compZToZf E E' hn'' i = 0 := by
  dsimp only [compZToZf]
  rw [dif_neg (by linarith), dif_neg (by linarith)]

set_option maxHeartbeats 400000 in
noncomputable def compZToZ : (comp E E' hn'').Z ⟶ E.Z where
  f := compZToZf E E' hn''
  comm' := by
    rintro i j (hij : i + 1 = j)
    by_cases hi : i ≤ -1
    · by_cases hi' : 0 ≤ i + n
      · subst hij
        rw [compZToZf_eq E E' hn'' i (i+n+1) (i+n''+1) (by linarith) (by linarith) rfl (by linarith),
          compZToZf_eq E E' hn'' (i+1) (i+n+2) (i+n''+2) (by linarith) (by linarith) (by linarith) (by linarith),
          (comp E E' hn'').Z_d_eq i (i+1) (i+n''+1) (i+n''+2) rfl (by linarith) (by linarith) (by linarith),
          comp_K_d_eq_d E E' hn'' (i+n''+1) (i+n''+2) (by linarith) (by linarith) (i+n+1) (i+n+2) (by linarith) (by linarith),
          E.Z_d_eq i (i+1) (i+n+1) (i+n+2) (by linarith) (by linarith) (by linarith) (by linarith)]
        simp only [assoc, Iso.inv_hom_id_assoc]
      · obtain rfl | _ := (show i ≤ -n -1 by linarith).eq_or_lt
        · obtain rfl : j = -n := by linarith
          rw [E.Z_d_eq (-n-1) (-n) 0 1 (by linarith) (by linarith) (by linarith) (by linarith),
            compZToZf_eq E E' hn'' (-n) 1 (n'+2) (by linarith) (by linarith) (by linarith) (by linarith),
            (comp E E' hn'').Z_d_eq (-n-1) (-n) (n'+1) (n'+2) (by linarith) (by linarith) (by linarith) (by linarith),
            compZToZf_eq', comp_K_d_eq_d'_comp_d E E' hn'' (n'+1) (n'+2) (by linarith) (by linarith)]
          simp only [assoc, Iso.inv_hom_id_assoc]
        · obtain rfl | _ := (show i ≤ -n - 2 by linarith).eq_or_lt
          · obtain rfl : j = -n-1 := by linarith
            rw [compZToZf_eq',
              (comp E E' hn'').Z_d_eq (-n-2) (-n-1) n' (n'+1) (by linarith) (by linarith) (by linarith) (by linarith),
              comp_K_d_eq_d' E E' hn'' n' (n'+1) (by linarith) (by linarith),
              compZToZf_eq_zero_of_le E E' hn'' (-n-2) (by linarith)]
            simp only [assoc, Iso.inv_hom_id_assoc, HomologicalComplex.d_comp_d_assoc,
              zero_comp, comp_zero]
          · exact (isZero_Z_X_of_le E _ (by linarith)).eq_of_tgt _ _
    · exact (isZero_Z_X_of_ge E _ (by linarith)).eq_of_tgt _ _

lemma compZToZ_comp_ZToX₁ : compZToZ E E' hn'' ≫ E.ZToX₁ = (comp E E' hn'').ZToX₁ := by
  apply (HomologicalComplex.toSingleEquiv _ _ (-1) 0 (by simp)).injective
  ext
  dsimp [HomologicalComplex.toSingleEquiv, compZToZ]
  simp only [comp_id,
    compZToZf_eq E E' hn'' 0 (n+1) (n''+1) (by linarith) (by linarith) (by linarith) (by linarith),
    ZToX₁_f_0, HomologicalComplex.single, ComplexShape.up_Rel, HomologicalComplex.singleObjXSelf,
    eqToHom_refl, assoc, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left,
    comp_K_d_eq_d E E' hn'' (n''+1) (n''+2) (by linarith) (by linarith) (n+1) (n+2)
      (by linarith) (by linarith), Iso.inv_hom_id, comp_id]
  dsimp [comp]
  simp only [Iso.inv_hom_id_assoc]

instance : QuasiIso (compZToZ E E' hn'') := by
  rw [← quasiIso_iff_comp_right _ E.ZToX₁, compZToZ_comp_ZToX₁]
  infer_instance

def sgn₁ (m m' i : ℤ) : ℤˣ := (m * (i + m + m')).negOnePow

lemma sgn₁_rel₁ (m m' i : ℤ) : sgn₁ m m' (i+1) = m.negOnePow * sgn₁ m m' i := by
  dsimp [sgn₁]
  erw [← Int.negOnePow_add]
  congr 1
  linarith

lemma sgn₁_rel₂ (m m' k'' : ℤ) (hk'' : m + m' + k'' = 0) : sgn₁ m m' k'' = 1 := by
  obtain rfl : k'' = - m' - m := by linarith
  simp [sgn₁]

noncomputable def compZToShiftZf (i : ℤ) :
    (comp E E' hn'').Z.X i ⟶ (E'.Z⟦(m : ℤ)⟧).X i :=
  if hi : i ≤ -m
    then
      sgn₁ m (n'+1) i • ((comp E E' hn'').ZXIso i (i+n''+1) rfl (by linarith)).hom ≫
        (compKXIso' E E' (i+n''+1) (by linarith)).hom ≫
        (E'.ZXIso (i+m) (i+n''+1) (by linarith) (by linarith)).inv ≫
        (E'.Z.shiftFunctorObjXIso m i (i + m) rfl).inv
    else
      0

lemma compZToShiftZf_eq (i j k : ℤ) (hi : i ≤ -m) (hj : i + n'' +1 = j) (hk : i + m = k) :
    compZToShiftZf E E' hn'' m hm i =
    sgn₁ m (n'+1) i • ((comp E E' hn'').ZXIso i j hj (by linarith)).hom ≫
      (compKXIso' E E' j (by linarith)).hom ≫
      (E'.ZXIso k j (by linarith) (by linarith)).inv ≫
      (E'.Z.shiftFunctorObjXIso m i k hk.symm).inv := by
  subst hk
  subst hj
  dsimp [compZToShiftZf]
  rw [dif_pos hi]

noncomputable def compZToShiftZ : (comp E E' hn'').Z ⟶ E'.Z⟦(m : ℤ)⟧ where
  f := compZToShiftZf E E' hn'' m hm
  comm' i j (hij : i + 1 = j) := by
    by_cases j ≤ -m
    · subst hij
      rw [compZToShiftZf_eq E E' hn'' m hm i (i+n''+1) (i+m) (by linarith) rfl rfl,
        compZToShiftZf_eq E E' hn'' m hm (i+1) (i+n''+2) (i+1+m) (by linarith) (by linarith) rfl,
        (comp E E' hn'').Z_d_eq i (i+1) (i+n''+1) (i+n''+2) rfl (by linarith) (by linarith) (by linarith),
        comp_K_d_eq_d' E E' hn'' (i+n''+1) (i+n''+2) (by linarith) (by linarith)]
      dsimp
      rw [E'.Z_d_eq (i+m) (i+1+m) (i+n''+1) (i+n''+2) (by linarith) (by linarith) (by linarith) (by linarith)]
      simp [smul_smul, sgn₁_rel₁]
    · exact (E'.Z.isZero_of_isStrictlyLE 0 _ (by linarith)).eq_of_tgt _ _

lemma compZToShiftZ_comp_ZToZ₂ :
    compZToShiftZ E E' hn'' m hm ≫ (E'.ZToX₂ k' (by linarith))⟦(m : ℤ)⟧' ≫
      ((CochainComplex.singleFunctors C).shiftIso m k'' k' (by linarith)).hom.app X₃ =
    (comp E E' hn'').ZToX₂ k'' (by linarith) := by
  obtain rfl : k' = k'' + m := by linarith
  apply (HomologicalComplex.toSingleEquiv _ _ (k''-1) k'' (by simp)).injective
  ext
  dsimp [HomologicalComplex.toSingleEquiv, compZToShiftZ]
  rw [compZToShiftZf_eq E E' hn'' m hm k'' 0 (-n'-1) (by linarith)
    (by linarith) (by linarith), sgn₁_rel₂ m (n'+1) k'' (by linarith), one_smul]
  rw [CochainComplex.singleFunctors_shiftIso_hom_app_f _ _ _ _ _ _ rfl]
  rw [ZToX₂_f_self, ZToX₂_f_self]
  dsimp [comp, ZXIso, Z.XIso, compKXIso', HomologicalComplex.XIsoOfEq,
    HomologicalComplex.singleObjXIsoOfEq, HomologicalComplex.singleObjXSelf]
  simp only [eqToHom_trans, id_comp, assoc, eqToHom_trans_assoc, eqToHom_refl, comp_id]

def sgn₂ (a b : ℤ) : ℤˣ := (a * b).negOnePow

@[simp]
lemma sgn₂_mul_self (a b : ℤ) : sgn₂ a b * sgn₂ a b = 1 := by simp [sgn₂]

@[reassoc]
lemma compZ_comm : compZToZ E E' hn'' ≫ E.ZToX₂ k (by linarith) =
    sgn₂ m m' • compZToShiftZ E E' hn'' m (by linarith) ≫ E'.ZToX₁⟦(m : ℤ)⟧' ≫
      ((CochainComplex.singleFunctors C).shiftIso m k 0 (by linarith)).hom.app X₂ := by
  obtain rfl : k = -n-1 := by linarith
  have sgn₂_rel : sgn₂ m m' * sgn₁ m (n' + 1) (-n - 1) = 1 := by
    rw [show (n' : ℤ)+1 = m' by linarith, show -(n : ℤ)-1 = -m by linarith]
    simp [sgn₂, sgn₁]
  apply (HomologicalComplex.toSingleEquiv _ _ (-(n : ℤ)-2) (-n-1) (by simp; linarith)).injective
  ext
  dsimp [HomologicalComplex.toSingleEquiv, compZToShiftZ, compZToZ]
  simp only [compZToZf_eq' E E' hn'',
    compZToShiftZf_eq E E' hn'' m hm (-n-1) (n'+1) 0 (by linarith) (by linarith) (by linarith),
    assoc, Preadditive.zsmul_comp, smul_smul, sgn₂_rel, one_smul, ZToX₂_f_self,
    HomologicalComplex.singleObjXSelf, assoc,
    eqToHom_trans, eqToHom_refl, comp_id, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    CochainComplex.shiftFunctorObjXIso, Iso.cancel_iso_hom_left,
    ← HomologicalComplex.XIsoOfEq_inv_naturality_assoc, ZToX₁_f_0, smul_smul,
    Linear.units_smul_comp]
  rw [CochainComplex.singleFunctors_shiftIso_hom_app_f _ _ _ _ _ _ rfl]
  dsimp [HomologicalComplex.XIsoOfEq, HomologicalComplex.singleObjXIsoOfEq]
  simp only [eqToHom_trans, eqToHom_refl, comp_id]
  erw [comp_id]

@[reassoc]
lemma compZ_comm' :
    inv (DerivedCategory.Q.map (compZToZ E E' hn'')) ≫
    DerivedCategory.Q.map (compZToShiftZ E E' hn'' m (by linarith)) =
        sgn₂ m m' • DerivedCategory.Q.map (E.ZToX₂ k (by linarith)) ≫
          DerivedCategory.Q.map (((CochainComplex.singleFunctors C).shiftIso m k 0 (by linarith)).inv.app X₂) ≫
          inv (DerivedCategory.Q.map (E'.ZToX₁⟦(m : ℤ)⟧')) := by
  simp only [← cancel_epi (DerivedCategory.Q.map (compZToZ E E' hn'')), IsIso.hom_inv_id_assoc,
    ← Functor.map_comp_assoc, Preadditive.comp_zsmul, compZ_comm_assoc E E' hn'' m m' hm hm' k hk,
    Preadditive.zsmul_comp, Functor.map_units_smul, assoc, Linear.comp_units_smul,
    Linear.units_smul_comp, Iso.hom_inv_id_app, smul_smul, sgn₂_mul_self, one_smul]
  erw [comp_id, Functor.map_comp, assoc, IsIso.hom_inv_id, comp_id]

lemma compatibility :
    sgn₂ m m' • E.shiftedHom m hm •[show (m : ℤ) + m' = m'' by linarith] E'.shiftedHom m' hm' =
      (comp E E' hn'').shiftedHom m'' (by linarith) := by
  rw [ShiftedHom.γhmul_eq]
  dsimp [shiftedHom]
  simp only [assoc, Functor.map_comp, ← compZToZ_comp_ZToX₁, IsIso.inv_comp,
    ← compZToShiftZ_comp_ZToZ₂ E E' hn'' m m' m'' hm hm' hm'' (-m') (by linarith) (-m'') (by linarith),
    compZ_comm'_assoc E E' hn'' m m' hm hm' (-m) (by linarith),
    Functor.map_inv, Functor.comp_obj, assoc,
    Linear.units_smul_comp, Linear.comp_units_smul]
  congr 4
  simp only [SingleFunctors.postComp_shiftIso_inv_app' _ (DerivedCategory.singleFunctorsPostCompQIso C), assoc,
    SingleFunctors.postComp_functor, Functor.comp_obj, ← Functor.map_comp_assoc,
    SingleFunctors.inv_hom_id_hom_app_assoc, SingleFunctors.inv_hom_id_hom_app,
    Functor.map_id, id_comp]
  congr 1
  rw [← cancel_epi (DerivedCategory.Q.map ((E'.ZToX₁)⟦(m : ℤ)⟧')), IsIso.hom_inv_id_assoc]
  have eq : (DerivedCategory.Q.commShiftIso (m : ℤ)).hom.app
        ((CochainComplex.singleFunctor C 0).obj X₂) ≫
      inv ((DerivedCategory.Q.map (ZToX₁ E'))⟦(m : ℤ)⟧') =
      inv (DerivedCategory.Q.map ((ZToX₁ E')⟦(m : ℤ)⟧')) ≫
        (DerivedCategory.Q.commShiftIso (m : ℤ)).hom.app E'.Z := by
    rw [← cancel_mono ((DerivedCategory.Q.map (ZToX₁ E'))⟦(m : ℤ)⟧'), assoc, assoc,
      IsIso.inv_hom_id, comp_id, ← cancel_epi (DerivedCategory.Q.map ((ZToX₁ E')⟦(m : ℤ)⟧')),
      IsIso.hom_inv_id_assoc]
    exact (DerivedCategory.Q.commShiftIso (m : ℤ)).hom.naturality E'.ZToX₁
  rw [reassoc_of% eq, IsIso.hom_inv_id_assoc (DerivedCategory.Q.map ((ZToX₁ E')⟦(m : ℤ)⟧'))]
  clear eq
  simp only [Functor.map_comp, assoc, ← Functor.commShiftIso_hom_naturality_assoc]
  congr 1
  rw [(CochainComplex.singleFunctors C).shiftIso_add'_inv_app m m' m'' (by linarith) (-m'') (-m') 0 (by linarith) (by linarith)]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, assoc]
  congr 1
  rw [DerivedCategory.Q.commShiftIso_add' (show (m' : ℤ) + m = m'' by linarith)]
  simp only [Functor.comp_obj, Functor.CommShift.isoAdd'_hom_app, assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [Functor.map_comp, assoc, Functor.map_id, id_comp,
    NatIso.cancel_natIso_hom_left, Functor.comp_obj]
  congr 1
  erw [← NatTrans.naturality]
  rfl

-- TODO:
-- should E.extClass be E.shiftedHom, or (-1)^m E.shiftedHom [presumably this is the latter]
-- then, anyway, if the composition of newExt is defined by (-1)^{m•m'} the composition
-- of ShiftedHom (in the opposite direction), then we have a compatibility between
-- the composition of newExt and the composition on Yoneda Exts.

end composition

end IteratedExtCategory

end Abelian

end CategoryTheory
