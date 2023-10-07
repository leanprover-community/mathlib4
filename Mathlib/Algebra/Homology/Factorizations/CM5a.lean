import Mathlib.Algebra.Homology.Factorizations.CM5b
import Mathlib.CategoryTheory.Abelian.YonedaExt

open CategoryTheory Category Limits Preadditive

namespace CategoryTheory

variable {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y)

structure HomFactorization where
  I : C
  i : X ⟶ I
  p : I ⟶ Y
  fac : i ≫ p = f

variable {f}

@[simps]
def HomFactorization.mk' {I : C} {i : X ⟶ I} {p : I ⟶ Y} (fac : i ≫ p = f) : HomFactorization f where
  fac := fac

attribute [reassoc (attr := simp)] HomFactorization.fac

end CategoryTheory

variable {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
  {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace CochainComplex

open HomologicalComplex

namespace CM5aCof

variable {f}

structure IsCofFibFactorization (F : HomFactorization f) : Prop where
  hi : Mono F.i := by infer_instance
  hp : degreewiseEpiWithInjectiveKernel F.p

variable (f)

def CofFibFactorization := FullSubcategory (IsCofFibFactorization (f := f))

--instance : Category (CofFibFactorization f) := by
--  dsimp only [CofFibFactorization]
--  infer_instance

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

/-lemma step₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (hf : ∀ (i : ℤ) (_ : i ≤ n₀), QuasiIsoAt f i)
    [Mono (homologyMap f n₁)] :
    ∃ (F : CofFibFactorization f) (_ : F.IsIsoLE n₁), F.QuasiIsoLE n₁ := by
  sorry

lemma step₁₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
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
    infer_instance-/

variable {f}

/-lemma step' (n₀ n₁ : ℤ) (hn₁ : n₁ = n₀ + 1)
    (F : CofFibFactorization f) [F.QuasiIsoLE n₀] :
    ∃ (F' : CofFibFactorization f) (φ : F ⟶ F'), 0 = 1 := by
  sorry-/

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
