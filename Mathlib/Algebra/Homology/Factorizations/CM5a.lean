import Mathlib.Algebra.Homology.Factorizations.CM5b
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TruncGE
import Mathlib.CategoryTheory.Abelian.YonedaExt

open CategoryTheory Category Limits Preadditive ZeroObject

namespace HomologicalComplex

variable {C ι : Type*} {c : ComplexShape ι} [Category C] [Abelian C]

noncomputable instance : NormalEpiCategory (HomologicalComplex C c) := ⟨fun p _ =>
  NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfEval _ _ (fun _ =>
      isColimit_mapCocone_of_cokernelCofork_ofπ_kernel_condition_of_epi _ _))⟩

noncomputable instance : NormalMonoCategory (HomologicalComplex C c) := ⟨fun p _ =>
  NormalMono.mk _ (cokernel.π p) (cokernel.condition _)
    (isLimitOfEval _ _ (fun _ =>
      isLimit_mapCone_of_kernelFork_ofι_cokernel_condition_of_mono _ _))⟩

noncomputable instance : Abelian (HomologicalComplex C c) where

end HomologicalComplex

namespace CochainComplex

variable {C ι : Type*} [Category C] [Preadditive C] [HasZeroObject C] [DecidableEq ι]
  {c : ComplexShape ι} (n₀ n₁ : ι) (h : c.Rel n₀ n₁) (h' : n₁ ≠ n₀) {X₀ X₁ : C} (f : X₀ ⟶ X₁)

noncomputable def double : HomologicalComplex C c where
  X i :=
    if i = n₀
      then X₀
      else if i = n₁
        then X₁
        else 0
  d i j :=
    if h : i = n₀ ∧ j = n₁
      then by
        refine' eqToHom _ ≫ f ≫ eqToHom _
        · dsimp
          rw [if_pos h.1]
        · dsimp
          rw [if_pos h.2, if_neg]
          rw [h.2]
          exact h'
      else 0
  shape i j hij := dif_neg (by
    rintro ⟨rfl, rfl⟩
    exact hij h)
  d_comp_d' i j k _ _ := by
    dsimp
    by_cases i = n₀ ∧ j = n₁
    · rw [dif_pos h]
      by_cases h'' : j = n₀ ∧ k = n₁
      · exfalso
        apply h'
        rw [← h.2, h''.1]
      · rw [dif_neg h'', comp_zero]
    · rw [dif_neg h, zero_comp]

lemma isZero_double_X (n : ι) (h₀ : n ≠ n₀) (h₁ : n ≠ n₁) :
    IsZero ((double _ _ h h' f).X n) := by
  dsimp [double]
  rw [if_neg h₀, if_neg h₁]
  exact isZero_zero C

noncomputable def doubleXIso₀ : (double _ _ h h' f).X n₀ ≅ X₀ := eqToIso (by simp [double])
noncomputable def doubleXIso₁ : (double _ _ h h' f).X n₁ ≅ X₁ := eqToIso (by
  dsimp [double]
  rw [if_neg h', if_pos rfl])

@[simp]
lemma double_d :
    (double _ _ h h' f).d n₀ n₁ = (doubleXIso₀ _ _ h h' f).hom ≫ f ≫ (doubleXIso₁ _ _ h h' f).inv := by
  simp [double, doubleXIso₀, doubleXIso₁]

lemma double_d_eq_zero₀ (i j : ι) (h₀ : i ≠ n₀) :
    (double _ _ h h' f).d i j = 0 := by
  dsimp [double]
  rw [dif_neg]
  intro h
  exact h₀ h.1

lemma double_d_eq_zero₁ (i j : ι) (h₁ : j ≠ n₁) :
    (double _ _ h h' f).d i j = 0 := by
  dsimp [double]
  rw [dif_neg]
  intro h
  exact h₁ h.2

section

variable
  (K : HomologicalComplex C c) (φ₀ : K.X n₀ ⟶ X₀) (φ₁ : K.X n₁ ⟶ X₁)
  (comm : K.d n₀ n₁ ≫ φ₁ = φ₀ ≫ f) (n : ι) (hn : c.prev n₀ = n)
  (zero : K.d n n₀ ≫ φ₀ = 0)

variable {n₀ n₁ h h' f}

noncomputable def toDouble : K ⟶ double _ _ h h' f where
  f i :=
    if h₀ : i = n₀
      then (K.XIsoOfEq h₀).hom ≫ φ₀ ≫ (doubleXIso₀ _ _ h h' f).inv ≫
          ((double _ _ h h' f).XIsoOfEq h₀).inv
      else
        if h₁ : i = n₁
          then (K.XIsoOfEq h₁).hom ≫ φ₁ ≫ (doubleXIso₁ _ _ h h' f).inv ≫
            ((double _ _ h h' f).XIsoOfEq h₁).inv
          else 0
  comm' i j hij := by
    dsimp
    by_cases h₀ : i = n₀
    · subst h₀
      rw [dif_pos rfl]
      by_cases h₁ : j = n₁
      · subst h₁
        simp [dif_neg h', comm]
      · simp [double_d_eq_zero₁ _ _ h h' f i j h₁]
        by_cases hij' : j = i
        · subst hij'
          rw [K.shape, zero_comp]
          intro hjj
          replace hjj := c.prev_eq' hjj
          rw [hn] at hjj
          subst hjj
          apply h'
          exact (c.next_eq' h).symm.trans (c.next_eq' hij)
        · rw [dif_neg hij', dif_neg h₁, comp_zero]
    · rw [dif_neg h₀]
      have := zero
      by_cases hj : j = n₀
      · subst hj
        rw [double_d_eq_zero₁ _ _ h h' f i j (fun H => h' H.symm), comp_zero]
        obtain rfl : n = i := hn.symm.trans (c.prev_eq' hij)
        simp [reassoc_of% this]
      · rw [dif_neg hj]
        by_cases hj' : j = n₁
        · subst hj'
          exfalso
          exact h₀ ((c.prev_eq' hij).symm.trans (c.prev_eq' h))
        · rw [dif_neg hj', comp_zero, double_d_eq_zero₁ _ _ h h' f i j hj', comp_zero]

@[simp]
lemma toDouble_f₀ :
    (toDouble K φ₀ φ₁ comm n hn zero).f n₀ = φ₀ ≫ (doubleXIso₀ _ _ h h' f).inv := by
  simp [toDouble]

@[simp]
lemma toDouble_f₁ :
    (toDouble K φ₀ φ₁ comm n hn zero).f n₁ = φ₁ ≫ (doubleXIso₁ _ _ h h' f).inv := by
  simp [dif_neg h', toDouble]

end

end CochainComplex

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (f : K ⟶ L)

noncomputable def mappingCocone := (mappingCone f)⟦(-1 : ℤ)⟧

namespace MappingCocone

-- not sure what are the best signs here
noncomputable def inl : Cochain K (mappingCocone f) 0 :=
  (MappingCone.inl f).rightShift (-1) 0 (zero_add _)
noncomputable def inr : Cocycle L (mappingCocone f) 1 :=
    (Cocycle.ofHom (MappingCone.inr _)).rightShift (-1) 1 (add_neg_self 1)
noncomputable def fst : (mappingCocone f) ⟶ K :=
  -((MappingCone.fst _).leftShift (-1) 0 (add_neg_self 1)).homOf
noncomputable def snd : Cochain (mappingCocone f) L (-1) :=
  (MappingCone.snd _).leftShift (-1) (-1) (zero_add _)

@[reassoc (attr := simp)]
lemma inr_fst (p q : ℤ) (hpq : p + 1 = q) : (inr f).1.v p q hpq ≫ (fst f).f q = 0 := by
    dsimp [inr, fst]
    rw [Cochain.rightShift_v _ (-1) 1 _ p q _ p (by linarith),
      Cochain.leftShift_v _ (-1) 0 _ q q _ p (by linarith)]
    simp

@[reassoc (attr := simp)]
lemma inl_snd (p q : ℤ) (hpq : p + (-1) = q) : (inl f).v p p (add_zero _) ≫ (snd f).v p q hpq = 0 := by
    dsimp [inl, snd]
    rw [Cochain.rightShift_v _ (-1) 0 _ p p _ q (by linarith),
      Cochain.leftShift_v _ (-1) (-1) _ p q _ q (by linarith)]
    simp

@[reassoc (attr := simp)]
lemma inr_snd (p q : ℤ) (hpq : p + 1 = q) : (inr f).1.v p q hpq ≫ (snd f).v q p (by linarith) = 𝟙 _ := by
    dsimp [inr, snd]
    have : ((1 : ℤ) + 1)/2 = 1 := rfl
    rw [Cochain.rightShift_v _ (-1) 1 _ p q _ p (by linarith),
      Cochain.leftShift_v _ (-1) (-1) _ q p _ p (by linarith)]
    simp [this, Int.negOnePow_succ]

@[reassoc (attr := simp)]
lemma inl_fst (p : ℤ) : (inl f).v p p (add_zero _) ≫ (fst f).f p = 𝟙 _ := by
    dsimp [inl, fst]
    have : ((1 : ℤ) + 1)/2 = 1 := rfl
    rw [Cochain.rightShift_v _ (-1) 0 _ p p _ (p-1) (by linarith),
      Cochain.leftShift_v _ (-1) 0 _ p p _ (p-1) (by linarith)]
    simp [this]
    erw [id_comp]
    simp

lemma id (p q : ℤ) (hpq : p + (-1) = q) : (fst f).f p ≫ (inl f).v p p (add_zero _) +
      (snd f).v p q hpq ≫ (inr f).1.v q p (by linarith) = 𝟙 _ := by
    dsimp [inl, inr, fst, snd]
    have : ((1 : ℤ) + 1) /2 = 1 := rfl
    rw [Cochain.rightShift_v _ (-1) 0 _ p p _ q (by linarith),
      Cochain.rightShift_v _ (-1) 1 _ q p _ q (by linarith),
      Cochain.leftShift_v _ (-1) 0 _ p p _ q (by linarith),
      Cochain.leftShift_v _ (-1) (-1) _ p q _ q (by linarith)]
    simp [this, Int.negOnePow_succ]
    rw [← comp_add]
    conv_lhs =>
      congr
      · skip
      · congr
        · rw [← assoc]
        · rw [← assoc]
    rw [← add_comp, ← MappingCone.id_X]
    simp

noncomputable def δ : L ⟶ (mappingCocone f)⟦(1 : ℤ)⟧ :=
  MappingCone.inr f ≫ (shiftEquiv (CochainComplex C ℤ) (1 : ℤ)).counitIso.inv.app _

@[simps!]
noncomputable def triangle : Pretriangulated.Triangle (CochainComplex C ℤ) :=
  Pretriangulated.Triangle.mk (fst f) f (δ f)

noncomputable def triangleIso : triangle f ≅ (MappingCone.triangle f).invRotate := by
  refine' Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
  · dsimp
    ext n
    have : ((1 : ℤ) + 1) / 2 = 1 := rfl
    dsimp [MappingCone.triangleδ]
    simp only [comp_id, neg_smul, one_smul, Cochain.rightShift_neg, Cochain.neg_v,
      neg_comp, neg_neg, id_comp, neg_inj]
    rw [Cochain.leftShift_v _ (-1) 0 _ n n _ (n-1) (by linarith),
      Cochain.rightShift_v _ 1 0 _ _ _ _ n (by linarith)]
    simp [this]
    dsimp [shiftFunctorCompIsoId]
    rw [shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f]
    simp only [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom, Iso.inv_hom_id, comp_id]
    rfl
  · dsimp
    simp only [comp_id, id_comp]
  · dsimp
    simp only [triangle, δ, shiftEquiv'_inverse, shiftEquiv'_functor, shiftEquiv'_counitIso,
      Pretriangulated.Triangle.mk_obj₁, Pretriangulated.Triangle.mk_mor₃, CategoryTheory.Functor.map_id, comp_id,
      id_comp]

end MappingCocone

end CochainComplex

namespace CategoryTheory

variable {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)

structure HomFactorization where
  I : C
  i : X ⟶ I
  p : I ⟶ Y
  fac : i ≫ p = f

variable {f}

namespace HomFactorization

@[simps]
def mk' {I : C} {i : X ⟶ I} {p : I ⟶ Y} (fac : i ≫ p = f) : HomFactorization f where
  fac := fac

attribute [reassoc (attr := simp)] fac

variable (F₁ F₂ F₃ : HomFactorization f)

@[ext]
structure Hom where
  φ : F₁.I ⟶ F₂.I
  commi : F₁.i ≫ φ = F₂.i := by aesop_cat
  commp : φ ≫ F₂.p = F₁.p := by aesop_cat

attribute [reassoc (attr := simp)] Hom.commi Hom.commp

@[simps]
def Hom.id : Hom F₁ F₁ where
  φ := 𝟙 _

variable {F₁ F₂ F₃}

@[simps]
def Hom.comp (f : Hom F₁ F₂) (g : Hom F₂ F₃) : Hom F₁ F₃ where
  φ := f.φ ≫ g.φ

@[simps]
instance : Category (HomFactorization f) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext (f g : F₁ ⟶ F₂) (h : f.φ = g.φ) : f = g :=
  Hom.ext f g h

end HomFactorization

end CategoryTheory

variable {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace CochainComplex

open HomologicalComplex HomComplex

namespace CM5aCof

variable {f}

structure IsCofFibFactorization (F : HomFactorization f) : Prop where
  hi : Mono F.i := by infer_instance
  hp : degreewiseEpiWithInjectiveKernel F.p

variable (f)

def CofFibFactorization := FullSubcategory (IsCofFibFactorization (f := f))

instance : Category (CofFibFactorization f) := by
  dsimp only [CofFibFactorization]
  infer_instance

namespace CofFibFactorization

variable {f}
variable (F : CofFibFactorization f)

instance : Mono (F.1.i) := F.2.hi

def IsIsoLE (n : ℤ) : Prop := ∀ (i : ℤ) (_ : i ≤ n), IsIso (F.1.p.f i)

class QuasiIsoLE (n : ℤ) : Prop where
  quasiIsoAt (i : ℤ) (_ : i ≤ n) : QuasiIsoAt (F.1.i) i

lemma quasiIsoAt_of_quasiIsoLE (F : CofFibFactorization f)
    (n : ℤ) [F.QuasiIsoLE n] (i : ℤ) (hi : i ≤ n) : QuasiIsoAt (F.1.i) i :=
  QuasiIsoLE.quasiIsoAt i hi

@[simps]
def mk {I : CochainComplex C ℤ} {i : K ⟶ I} {p : I ⟶ L} (fac : i ≫ p = f)
  [hi : Mono i] (hp : degreewiseEpiWithInjectiveKernel p) :
    CofFibFactorization f where
  obj := HomFactorization.mk' fac
  property := ⟨hi, hp⟩

end CofFibFactorization

lemma step₁ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (hf : ∀ (i : ℤ) (_ : i ≤ n₀), QuasiIsoAt f i) :
    ∃ (F : CofFibFactorization f) (_ : F.IsIsoLE n₀) (_ : F.QuasiIsoLE n₀),
      Mono (homologyMap F.1.i n₁) := by
  let S := ((single C (ComplexShape.up ℤ) n₁).obj (Injective.under (K.opcycles n₁)))
  let M := biprod S L
  let i₁ : K ⟶ S := ((toSingleEquiv _ _ n₀ n₁ (by subst hn₁; simp)).symm
    ⟨K.pOpcycles n₁ ≫ Injective.ι _,
      by rw [d_pOpcycles_assoc, zero_comp]⟩)
  let i : K ⟶ M := biprod.lift i₁ f
  let p : M ⟶ L := biprod.snd
  let σ : L ⟶ M := biprod.inr
  have σp : σ ≫ p = 𝟙 _ := by simp
  have hp : degreewiseEpiWithInjectiveKernel p := fun n => by
    rw [epiWithInjectiveKernel_iff]
    refine' ⟨S.X n, _, (biprod.inl : _ ⟶ M).f n, (biprod.inr : _ ⟶ M).f n,
        (biprod.fst : M ⟶ _).f n, _, _, _ , _, _⟩
    · dsimp
      by_cases n = n₁
      · rw [if_pos h]
        infer_instance
      · rw [if_neg h]
        infer_instance
    · rw [← comp_f, biprod.inl_snd, zero_f]
    · rw [← comp_f, biprod.inr_fst, zero_f]
    · rw [← comp_f, biprod.inl_fst, id_f]
    · rw [← comp_f, biprod.inr_snd, id_f]
    · rw [← id_f, ← biprod.total, add_f_apply, comp_f, comp_f]
  have fac : i ≫ p = f := by simp
  have hp' : ∀ (n : ℤ) (_ : n ≤ n₀), IsIso (p.f n) := fun n hn => by
    refine' ⟨(biprod.inr : _ ⟶ M).f n, _, _⟩
    · rw [← cancel_mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapBiprod _ _).hom]
      ext
      · apply IsZero.eq_of_tgt
        dsimp
        rw [if_neg (by linarith)]
        exact isZero_zero C
      · dsimp
        simp only [Category.assoc, biprod.lift_snd, Category.id_comp]
        rw [← comp_f, biprod.inr_snd, id_f, comp_id]
    · rw [← comp_f, biprod.inr_snd, id_f]
  have hp'' : ∀ (n : ℤ) (_ : n ≤ n₀), QuasiIsoAt p n := fun n hn => by
    obtain (hn | rfl) := hn.lt_or_eq
    · rw [quasiIsoAt_iff' _ (n-1) n (n+1) (by simp) (by simp)]
      let φ := (shortComplexFunctor' C (ComplexShape.up ℤ) (n - 1) n (n + 1)).map p
      have : IsIso φ.τ₁ := hp' _ (by linarith)
      have : IsIso φ.τ₂ := hp' _ (by linarith)
      have : IsIso φ.τ₃ := hp' _ (by linarith)
      apply ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ
    · rw [quasiIsoAt_iff_isIso_homologyMap]
      refine' ⟨homologyMap σ n, _, _⟩
      · have : cyclesMap (biprod.inl : _ ⟶ M) n = 0 := by
          have : (biprod.inl : _ ⟶ M).f n = 0 := by
            apply IsZero.eq_of_src
            dsimp
            rw [if_neg (by linarith)]
            exact Limits.isZero_zero C
          rw [← cancel_mono (M.iCycles n), zero_comp, cyclesMap_i, this, comp_zero]
        symm
        rw [← homologyMap_comp, ← homologyMap_id, ← sub_eq_zero, ← homologyMap_sub,
          ← biprod.total, add_sub_cancel, ← cancel_epi (M.homologyπ n),
          homologyπ_naturality, comp_zero, cyclesMap_comp, this, comp_zero, zero_comp]
      · rw [← homologyMap_comp, σp, homologyMap_id]
  have hi : ∀ (n : ℤ) (_ : n ≤ n₀), QuasiIsoAt i n := fun n hn => by
    have : QuasiIsoAt p n := hp'' n hn
    have : QuasiIsoAt (i ≫ p) n := by simpa only [fac] using hf n hn
    exact quasiIsoAt_of_comp_right i p n
  refine' ⟨CofFibFactorization.mk fac hp, hp', ⟨hi⟩, mono_of_cancel_zero _ _⟩
  intro A₀ x₀ (hx₀ : x₀ ≫ homologyMap i n₁ = 0)
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ := surjective_up_to_refinements_of_epi (K.homologyπ n₁) x₀
  rw [← cancel_epi π₁, comp_zero, hx₁,
    K.comp_homologyπ_eq_zero_iff_up_to_refinements x₁ n₀ (by simp [hn₁])]
  replace hx₀ := π₁ ≫= hx₀
  rw [reassoc_of% hx₁, comp_zero, homologyπ_naturality, ← assoc,
    M.comp_homologyπ_eq_zero_iff_up_to_refinements (x₁ ≫ cyclesMap i n₁) n₀ (by simp [hn₁])] at hx₀
  have : Mono (opcyclesMap i₁ n₁) := by
    let α : Injective.under (K.opcycles n₁) ⟶ S.X n₁ :=
      (singleObjXSelf C (ComplexShape.up ℤ) n₁ (Injective.under (K.opcycles n₁))).inv
    have := S.isIso_pOpcycles _ n₁ rfl rfl
    have : opcyclesMap i₁ n₁ = Injective.ι (K.opcycles n₁) ≫ α ≫ S.pOpcycles n₁ := by
      rw [← (cancel_epi (K.pOpcycles n₁)), p_opcyclesMap, ← assoc, ← assoc]
      simp [toSingleEquiv]
    rw [this]
    infer_instance
  have hx₁' : (x₁ ≫ K.iCycles n₁) ≫ K.pOpcycles n₁ = 0 := by
    obtain ⟨A₂, π₂, _, x₂, hx₂⟩ := hx₀
    replace hx₂ := hx₂ =≫ (M.iCycles n₁ ≫ M.pOpcycles n₁ ≫ opcyclesMap biprod.fst n₁)
    rw [assoc, assoc, assoc, cyclesMap_i_assoc, toCycles_i_assoc, d_pOpcycles_assoc,
      zero_comp, comp_zero, p_opcyclesMap, ← comp_f_assoc, biprod.lift_fst,
      ← p_opcyclesMap i₁ n₁] at hx₂
    rw [assoc, ← cancel_mono (opcyclesMap i₁ n₁), zero_comp, assoc, assoc,
      ← cancel_epi π₂, comp_zero, hx₂]
  rw [K.comp_pOpcycles_eq_zero_iff_up_to_refinements (x₁ ≫ K.iCycles n₁) n₀ (by simp [hn₁])] at hx₁'
  obtain ⟨A₃, π₃, _, x₃, hx₃⟩ := hx₁'
  refine' ⟨A₃, π₃, inferInstance, x₃, _⟩
  rw [← cancel_mono (K.iCycles n₁), assoc, hx₃, assoc, toCycles_i]

namespace Step₂

variable [Mono f] (n : ℤ) [Mono (homologyMap f n)]

@[simps]
noncomputable def homologyShortComplex : ShortComplex C :=
  ShortComplex.mk (homologyMap f n) (homologyMap (cokernel.π f) n)
    (by rw [← homologyMap_comp, cokernel.condition, homologyMap_zero])

lemma shortExact : (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

lemma homologyShortComplex_exact : (homologyShortComplex f n).Exact := by
  exact (shortExact f).exact₂ n

instance mono_homologyShortComplex_f : Mono (homologyShortComplex f n).f := by
  dsimp
  infer_instance

noncomputable def I := (single C (ComplexShape.up ℤ) n).obj (Injective.under (((cokernel f).truncGE n).X n))

instance (p : ℤ) : Injective ((I f n).X p) := by
  dsimp [I]
  split_ifs <;> infer_instance

noncomputable def π' : (cokernel f).truncGE n ⟶ I f n :=
  (toSingleEquiv _ _ (n-1) n (by simp)).symm ⟨Injective.ι _, by
    apply IsZero.eq_of_src
    apply isZero_truncGEX
    linarith⟩

instance : Mono ((π' f n).f n) := by
  simp [π', toSingleEquiv]
  infer_instance

lemma mono_cyclesMap_π' : Mono (cyclesMap (π' f n) n) := by
  have : Mono (cyclesMap (π' f n) n ≫ (I f n).iCycles  n) := by
    rw [cyclesMap_i]
    infer_instance
  apply mono_of_mono _ ((I f n).iCycles n)

lemma mono_homologyMap_π' : Mono (homologyMap (π' f n) n) := by
  have := mono_cyclesMap_π' f n
  have := ((cokernel f).truncGE n).isIso_homologyπ (n-1) n (by simp)
    (IsZero.eq_of_src (isZero_truncGEX _ _ _ (by linarith)) _ _)
  have := (I f n).isIso_homologyπ  (n-1) n (by simp) (by
    apply IsZero.eq_of_src
    dsimp [I]
    rw [if_neg (by linarith)]
    exact isZero_zero C)
  have : Mono ((truncGE (cokernel f) n).homologyπ n ≫ homologyMap (π' f n) n) := by
    rw [homologyπ_naturality (π' f n) n]
    infer_instance
  rw [← IsIso.inv_hom_id_assoc ((truncGE (cokernel f) n).homologyπ n) (homologyMap (π' f n) n)]
  infer_instance

noncomputable def α : L ⟶ I f n := cokernel.π f ≫ (cokernel f).truncGEπ n ≫ π' f n

@[reassoc (attr := simp)]
lemma f_α : f ≫ α f n = 0 := by simp [α]

@[reassoc (attr := simp)]
lemma f_α_f (i : ℤ) : f.f i ≫ (α f n).f i = 0 := by
  rw [← comp_f, f_α, zero_f]

@[simps]
noncomputable def homologyShortComplex' : ShortComplex C :=
  ShortComplex.mk (homologyMap f n) (homologyMap (α f n) n) (by
    rw [← homologyMap_comp, f_α, homologyMap_zero])

lemma homologyShortComplex'_exact : (homologyShortComplex' f n).Exact := by
  let φ : homologyShortComplex f n ⟶ homologyShortComplex' f n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := homologyMap ((cokernel f).truncGEπ n ≫ π' f n) n
      comm₂₃ := by
        dsimp
        rw [id_comp, ← homologyMap_comp]
        rfl }
  have : IsIso φ.τ₁ := by infer_instance
  have : IsIso φ.τ₂ := by infer_instance
  have : Mono φ.τ₃ := by
    dsimp
    rw [homologyMap_comp]
    have := mono_homologyMap_π' f n
    have := (cokernel f).isIso_homologyMap_truncGEπ n n (by rfl)
    infer_instance
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact homologyShortComplex_exact f n

instance mono_homologyShortComplex'_f : Mono (homologyShortComplex' f n).f := by
  dsimp
  infer_instance

noncomputable def L' := (mappingCone (α f n))⟦(-1 : ℤ)⟧

noncomputable def i' : Cocycle K (mappingCone (α f n)) (-1) :=
  MappingCone.liftCocycle (α f n) (Cocycle.ofHom f) 0 (neg_add_self 1) (by aesop_cat)

noncomputable def i : K ⟶ L' f n :=
  Cocycle.homOf ((i' f n).rightShift (-1) 0 (zero_add _))

noncomputable def p : L' f n ⟶ L := MappingCocone.fst _

lemma fac : i f n ≫ p f n = f := by
  ext q
  dsimp [i, p, MappingCocone.fst]
  have : ((1 : ℤ) + 1) / 2 = 1 := rfl
  rw [Cochain.rightShift_v _ (-1) 0 _ q q _ (q-1) (by linarith),
    Cochain.leftShift_v _ (-1) 0 _ q q _ (q-1) (by linarith)]
  simp [this, i']
  erw [id_comp]
  simp

instance : Mono (i f n) := mono_of_mono_fac (fac f n)

lemma isIso_p_f (q : ℤ) (hq : q ≤ n) : IsIso ((p f n).f q) := by
  refine' ⟨(MappingCocone.inl _).v q q (add_zero _), _, by simp [p]⟩
  have : (MappingCocone.snd (α f n)).v q (q-1) (by linarith) = 0 := by
    apply IsZero.eq_of_tgt
    dsimp [I]
    rw [if_neg (by linarith)]
    exact Limits.isZero_zero C
  erw [← MappingCocone.id _ q (q - 1) (by linarith), self_eq_add_right, this, zero_comp]

@[simps]
noncomputable def cofFibFactorization : CofFibFactorization f where
  obj := HomFactorization.mk' (fac f n)
  property :=
    { hi := by
        dsimp
        infer_instance
      hp := fun q => by
        dsimp
        rw [epiWithInjectiveKernel_iff]
        refine' ⟨_, _, (MappingCocone.inr _).1.v (q-1) q (by linarith),
          (MappingCocone.inl _).v q q (add_zero _), (MappingCocone.snd _).v q (q-1) (by linarith),
          by simp [p], by simp, by simp, by simp [p], _⟩
        · infer_instance
        · rw [add_comm, p, MappingCocone.id]
          rfl }

variable (hf : ∀ (i : ℤ) (_ : i ≤ n - 1), QuasiIsoAt f i)

lemma isGE_cokernel : (cokernel f).IsGE n := ⟨fun i hi => by
  apply ((shortExact f).exact₃ i (i+1) (by simp)).isZero_X₂
  · apply ((shortExact f).exact₂ i).epi_f_iff.1
    dsimp
    have := hf i (by linarith)
    infer_instance
  · apply ((shortExact f).exact₁ i (i+1) (by simp)).mono_g_iff.1
    dsimp
    by_cases i + 1 ≤ n-1
    · have := hf (i+1) h
      infer_instance
    · obtain rfl : n = i + 1 := by linarith
      infer_instance⟩

lemma quasiIso_truncGEπ : QuasiIso ((cokernel f).truncGEπ n) := by
  rw [quasiIso_iff_mem_qis, qis_truncGEπ_iff]
  exact isGE_cokernel f n hf

lemma quasiIsoLE_cofFibFactorization : (cofFibFactorization f n).QuasiIsoLE n := by
  sorry

end Step₂

section

open Step₂

lemma step₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (hf : ∀ (i : ℤ) (_ : i ≤ n₀), QuasiIsoAt f i)
    [Mono (homologyMap f n₁)] :
    ∃ (F : CofFibFactorization f) (_ : F.IsIsoLE n₁), F.QuasiIsoLE n₁ := by
  obtain : n₀ = n₁ - 1 := by linarith
  exact ⟨cofFibFactorization f n₁, isIso_p_f f n₁, quasiIsoLE_cofFibFactorization f n₁⟩

end

/-lemma step₁₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (hf : ∀ (i : ℤ) (_ : i ≤ n₀), QuasiIsoAt f i) :
    ∃ (F : CofFibFactorization f) (_ : F.IsIsoLE n₀), F.QuasiIsoLE n₁ := by
  obtain ⟨F₁, hF₁, hF₁', _⟩ := step₁ f n₀ n₁ hn₁ hf
  obtain ⟨F₂, hF₂, hF₂'⟩ := step₂ F₁.1.i n₀ n₁ hn₁ (F₁.quasiIsoAt_of_quasiIsoLE n₀)
  have fac : F₂.1.i ≫ F₂.1.p ≫ F₁.1.p = f := by
    rw [reassoc_of% F₂.1.fac, F₁.1.fac]
  refine' ⟨CofFibFactorization.mk fac
    (MorphismProperty.comp_mem _ _ _ F₂.2.hp F₁.2.hp), _,
      ⟨F₂.quasiIsoAt_of_quasiIsoLE n₁⟩⟩
  · intro i hi
    have := hF₁ i hi
    have := hF₂ i (by linarith)
    dsimp
    infer_instance

variable {f}

lemma step' (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (F : CofFibFactorization f) [F.QuasiIsoLE n₀] :
    ∃ (F' : CofFibFactorization f) (_ : F'.QuasiIsoLE n₁) (f : F' ⟶ F),
      ∀ (i : ℤ) (_ : i ≤ n₀), IsIso (f.φ.f i) := by
  obtain ⟨F₁₂, h, _⟩ := step₁₂ F.1.i n₀ n₁ hn₁ (F.quasiIsoAt_of_quasiIsoLE n₀)
  have fac : F₁₂.obj.i ≫ F₁₂.obj.p ≫ F.obj.p = f := by rw [F₁₂.1.fac_assoc, F.1.fac]
  exact ⟨CofFibFactorization.mk fac (MorphismProperty.comp_mem _ _ _ F₁₂.2.hp F.2.hp),
    ⟨F₁₂.quasiIsoAt_of_quasiIsoLE n₁⟩, { φ := F₁₂.1.p }, h⟩-/

end CM5aCof

/-lemma CM5a_cof (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n) (i : K ⟶ L') (p : L' ⟶ L)
      (_hi : Mono i) (_hi' : QuasiIso i) (_hp : degreewiseEpiWithInjectiveKernel p), i ≫ p = f :=
  sorry

lemma CM5a (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n) (i : K ⟶ L') (p : L' ⟶ L)
      (_hi : Mono i) (_hi' : QuasiIso i) (_hp : degreewiseEpiWithInjectiveKernel p), i ≫ p = f := by
  obtain ⟨L', _, i₁, p₁, _, hp₁, _, rfl⟩ := CM5b f n
  obtain ⟨L'', _, i₂, p₂, _, _, hp₂, rfl⟩ := CM5a_cof i₁ n
  refine' ⟨L'', inferInstance, i₂, p₂ ≫ p₁, inferInstance, inferInstance,
    MorphismProperty.comp_mem _ _ _ hp₂ hp₁, by simp⟩-/

end CochainComplex
