import Mathlib.Algebra.Homology.SpectralObject.PageInfinity
import Mathlib.Algebra.Homology.SpectralObject.Images

namespace CategoryTheory

open Category ComposableArrows Limits

lemma Option.by_cases {α : Type*} (x : Option α) :
    x = none ∨ ∃ (a : α), x = some a := by
  cases x <;> tauto

namespace Abelian

variable {C ι κ : Type*} [Category C] [Abelian C] [LinearOrder ι] [OrderBot ι] [OrderTop ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  [∀ r, DecidableRel (c r).Rel]

namespace SpectralObject

noncomputable def abutment (n : ℤ) : C :=
    (X.H n).obj (mk₁ (homOfLE' ⊥ ⊤ bot_le))

noncomputable def abutmentFiltration (n : ℤ) (j : ι) : C :=
  X.image n (homOfLE' ⊥ j bot_le) (homOfLE' j ⊤ le_top) _ rfl

noncomputable def abutmentFiltrationι (n : ℤ) (j : ι) :
    X.abutmentFiltration n j ⟶ X.abutment n :=
  X.imageι _ _ _ _ _

noncomputable def πAbutmentFiltration (n : ℤ) (j : ι) :
    (X.H n).obj (mk₁ (homOfLE' ⊥ j bot_le)) ⟶ X.abutmentFiltration n j :=
  X.imageπ _ _ _ _ _

instance (n : ℤ) (j : ι) : Epi (X.πAbutmentFiltration n j) := by
  dsimp [πAbutmentFiltration]
  infer_instance

noncomputable def abutmentπ (n : ℤ) (j : ι) :
    X.abutment n ⟶ (X.H n).obj (mk₁ (homOfLE' j ⊤ le_top)) :=
  (X.H n).map (homMk₁ (homOfLE bot_le) (𝟙 _) rfl)

noncomputable def abutmentFiltrationToPageInfinity (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i j : ι) (hij : i ≤ j) :
    X.abutmentFiltration n₁ j ⟶ X.pageInfinity n₀ n₁ n₂ hn₁ hn₂ i j hij :=
  X.imageToE n₀ n₁ n₂ hn₁ hn₂ (homOfLE' ⊥ i bot_le) (homOfLE hij)
    (homOfLE' j ⊤ le_top) _ rfl _ rfl

instance (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (i j : ι) (hij : i ≤ j) :
    Epi (X.abutmentFiltrationToPageInfinity n₀ n₁ n₂ hn₁ hn₂ i j hij) := by
  dsimp [abutmentFiltrationToPageInfinity]
  infer_instance

@[reassoc (attr := simp)]
lemma abutmentFiltrationι_π (n : ℤ) (j : ι) :
    X.abutmentFiltrationι n j ≫ X.abutmentπ n j = 0 :=
  kernel.condition _

@[reassoc (attr := simp)]
lemma abutmentπ_map (n : ℤ) (j₁ j₂ : ι)
    (φ : (mk₁ (homOfLE' j₁ ⊤ le_top)) ⟶ (mk₁ (homOfLE' j₂ ⊤ le_top))) :
    X.abutmentπ n j₁ ≫ (X.H n).map φ = X.abutmentπ n j₂ :=
  ((X.H n).map_comp _ _).symm

instance (n : ℤ) (j : ι) : Mono (X.abutmentFiltrationι n j) := by
  dsimp [abutmentFiltrationι]
  infer_instance

noncomputable def abutmentFiltrationMap (n : ℤ) (j₁ j₂ : ι) (h : j₁ ≤ j₂) :
    X.abutmentFiltration n j₁ ⟶ X.abutmentFiltration n j₂ :=
  X.imageMap _ _ _ _ _ _ _ _ _ (homMk₂ (𝟙 _) (homOfLE h) (𝟙 _) rfl rfl)

@[reassoc (attr := simp)]
lemma abutmentFiltrationMap_ι (n : ℤ) (j₁ j₂ : ι) (h : j₁ ≤ j₂) :
    X.abutmentFiltrationMap n j₁ j₂ h ≫ X.abutmentFiltrationι n j₂ =
      X.abutmentFiltrationι n j₁ := by
  simpa using X.imageMap_ι n (homOfLE' ⊥ j₁ bot_le) (homOfLE' j₁ ⊤ le_top) _ rfl
    (homOfLE' ⊥ j₂ bot_le) (homOfLE' j₂ ⊤ le_top) _ rfl
    (homMk₂ (𝟙 _) (homOfLE h) (𝟙 _) rfl rfl) (𝟙 _) (by aesop_cat)

@[simps]
noncomputable def abutmentFiltrationFunctor (n : ℤ) :
    ι ⥤ MonoOver (X.abutment n) where
  obj j := MonoOver.mk' (X.abutmentFiltrationι n j)
  map {j₁ j₂} h := Over.homMk (X.abutmentFiltrationMap n j₁ j₂ (leOfHom h)) (by simp)

instance (n : ℤ) (j₁ j₂ : ι) (h : j₁ ≤ j₂) :
    Mono (X.abutmentFiltrationMap n j₁ j₂ h) :=
  mono_of_mono_fac (X.abutmentFiltrationMap_ι n j₁ j₂ h)

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (i j : ι) (hij : i ≤ j)

@[reassoc (attr := simp)]
lemma abutmentFiltrationMap_abutmentFiltrationToPageInfinity :
    X.abutmentFiltrationMap n₁ i j hij ≫
      X.abutmentFiltrationToPageInfinity n₀ n₁ n₂ hn₁ hn₂ i j hij = 0 := by
  apply X.imageMap_threeδ₂Toδ₁_imageToE
  rfl

@[simps!]
noncomputable
def abutmentFiltrationShortComplex :
    ShortComplex C :=
  ShortComplex.mk _ _
    (X.abutmentFiltrationMap_abutmentFiltrationToPageInfinity n₀ n₁ n₂ hn₁ hn₂ i j hij)

instance : Mono (X.abutmentFiltrationShortComplex n₀ n₁ n₂ hn₁ hn₂ i j hij).f := by
  dsimp
  infer_instance

instance : Epi (X.abutmentFiltrationShortComplex n₀ n₁ n₂ hn₁ hn₂ i j hij).g := by
  dsimp
  infer_instance

lemma abutmentFiltrationShortComplex_shortExact :
    (X.abutmentFiltrationShortComplex n₀ n₁ n₂ hn₁ hn₂ i j hij).ShortExact := by
  apply X.shortComplexImage_shortExact
  rfl

end

variable (data : SpectralSequenceMkData ι c r₀)
  {σ : Type*} {α : σ → Type*} [∀ n, LinearOrder (α n)]
  (s : SpectralSequence.ConvergenceStripes κ α)

namespace SpectralSequenceMkData

structure CompatibleWithConvergenceStripes where
  deg : σ → ℤ
  deg_stripe (pq : κ) : deg (s.stripe pq) = data.deg pq := by aesop
  i₂_monotone (n : σ) (i j : α n) (hij : i ≤ j) :
    data.i₂ (s.position n i) ≤ data.i₂ (s.position n j)

namespace CompatibleWithConvergenceStripes

variable {data s}
variable (hdata : data.CompatibleWithConvergenceStripes s)

@[simp]
lemma deg_position (n : σ) (i : α n) :
    data.deg (s.position n i) = hdata.deg n := by
  simp only [← s.stripe_position n i, hdata.deg_stripe]

@[nolint unusedArguments]
def mapWithBot (_ : data.CompatibleWithConvergenceStripes s) (n : σ) : WithBot (α n) → ι
  | none => ⊥
  | some i => data.i₂ (s.position n i)

@[simp]
lemma mapWithBot_none (n : σ):
    hdata.mapWithBot n none = ⊥ := rfl

@[simp]
lemma mapWithBot_bot (n : σ):
    hdata.mapWithBot n ⊥ = ⊥ := rfl

@[simp]
lemma mapWithBot_some (n : σ) (i : α n):
    hdata.mapWithBot n (some i) = data.i₂ (s.position n i) := rfl

@[simp]
lemma mapWithBot_some' (n : σ) (i : α n):
    hdata.mapWithBot n (WithBot.some i) = data.i₂ (s.position n i) := rfl

lemma mapWithBot_monotone (n : σ) : Monotone (hdata.mapWithBot n) := by
  rintro i j hij
  obtain _ | i := i
  · apply bot_le
  · obtain _ | j := j
    · change _ ≤ ⊥ at hij
      simp at hij
    · simp only [WithBot.some_le_some] at hij
      dsimp [mapWithBot]
      exact hdata.i₂_monotone n i j hij

abbrev mapWithBotFunctor (n : σ) : WithBot (α n) ⥤ ι :=
  Monotone.functor (hdata.mapWithBot_monotone n)

lemma mapWithBot_pred_le_i₂ (n : σ) (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i) :
    hdata.mapWithBot n i ≤ data.i₂ (s.position n j) := by
  obtain _|i := i
  · exact bot_le
  · apply hdata.i₂_monotone
    rw [← WithBot.coe_le_coe]
    change _ = WithBot.some i at hij
    simpa only [← hij] using s.pred'_le n j

--lemma comparable (n : σ) (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i) (pq : κ) (hpq : s.position n j = pq) :
--    (data.i₁ pq ≤ hdata.mapWithBot n i) ∨ (hdata.mapWithBot n i ≤ data.i₁ pq) := by
--  obtain _|i := i
--  · exact Or.inr bot_le
--  · subst hpq
--    exact hdata.comparable' n i j hij _ rfl

end CompatibleWithConvergenceStripes

end SpectralSequenceMkData

lemma mkDataE₂Cohomological_i₁_eq_i₂ (n : ℤ) (i j : ℤ)
    (hij : SpectralSequence.cohomologicalStripes.pred n j = WithBot.some i) (pq : ℤ × ℤ)
    (hpq : SpectralSequence.cohomologicalStripes.position n j = pq) :
    mkDataE₂Cohomological.i₁ pq =
      mkDataE₂Cohomological.i₂ (SpectralSequence.cohomologicalStripes.position n i) := by
  rw [← hpq]
  obtain rfl : j - 1 = i := by
    rw [← WithBot.coe_inj]
    exact hij
  simp

@[simps]
def mkDataE₂CohomologicalCompatibility :
    mkDataE₂Cohomological.CompatibleWithConvergenceStripes
      SpectralSequence.cohomologicalStripes where
  deg n := n
  i₂_monotone n i j hij := by simpa using hij

@[simps]
def mkDataE₂CohomologicalNatCompatibility :
    mkDataE₂CohomologicalNat.CompatibleWithConvergenceStripes
      CohomologicalSpectralSequenceNat.stripes where
  deg n := n
  i₂_monotone n i j hij := by simpa using hij

@[simps]
def homologicalStripesNat :
    SpectralSequence.ConvergenceStripes (ℕ × ℕ) (fun (n : ℕ) => Fin (n + 1)) where
  stripe pq := pq.1 + pq.2
  pred n := fun i => match i with
    | 0 => ⊥
    | ⟨j + 1, hj⟩ => WithBot.some ⟨j, by linarith⟩
  pred_lt n i := by
    obtain ⟨_ | _, _⟩ := i
    · apply WithBot.bot_lt_coe
    · simp
  position n i := ⟨i.1, n - i.1⟩
  stripe_position := by
    rintro n ⟨i, hi⟩
    exact Nat.add_sub_of_le (by linarith)
  discrete := by
    rintro n ⟨_ | i, hi⟩ ⟨j, hj⟩ h
    · simp
    · simp only [WithBot.coe_lt_coe, Fin.mk_lt_mk] at h
      simp only [Fin.mk_le_mk]
      linarith
  finite_segment n i j := by
    rw [Set.finite_def]
    refine ⟨Fintype.ofInjective (fun x => (x : Fin (n + 1))) ?_⟩
    intro x y h
    ext1
    simpa using h

@[simps]
def mkDataE₂HomologicalNatCompatibility :
    mkDataE₂HomologicalNat.CompatibleWithConvergenceStripes
      homologicalStripesNat where
  deg n := -n
  deg_stripe pq := by
    dsimp
    simp only [Nat.cast_add, neg_add_rev]
    linarith
  i₂_monotone := by
    rintro n ⟨i, hi⟩ ⟨j, hj⟩ h
    simp at h
    dsimp
    simp only [ℤt.mk_le_mk_iff]
    linarith [Nat.add_sub_of_le (show i ≤ n by linarith),
      Nat.add_sub_of_le (show j ≤ n by linarith)]

variable {data s}
variable (hdata : data.CompatibleWithConvergenceStripes s)
  [X.HasSpectralSequence data]

class ConvergesInDegree (n : σ) : Prop where
  stationnaryAt (pq : κ) (hpq : s.stripe pq = n) : X.StationaryAt data pq := by infer_instance
  isZero₁ : ∃ (i : α n), ∀ (j : α n) (_ : s.pred n i = WithBot.some j),
    IsZero ((X.H (hdata.deg n)).obj (mk₁ (homOfLE' ⊥ (data.i₂ (s.position n j)) bot_le)))
  isZero₂ : ∃ (i : α n),
    IsZero ((X.H (hdata.deg n)).obj (mk₁ (homOfLE' (data.i₂ (s.position n i)) ⊤ le_top)))
  isIso₁ (i j : α n) (hij : s.pred n j = WithBot.some i) (pq : κ) (hpq : s.position n j = pq)
      (i₁ i₂ i₂' : ι) (hi₁ : data.i₁ pq = i₁) (hi₂ : data.i₂ (s.position n i) = i₂)
      (hi₂' : data.i₂ (s.position n j) = i₂')
      (h₁₂ : i₁ < i₂) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
      (hn₁' : hdata.deg n = n₁) :
    IsIso (X.EMapFourδ₂Toδ₁' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₁ i₂ i₂' ⊤ bot_le h₁₂.le (by
        rw [← hi₂, ← hi₂']
        apply hdata.i₂_monotone
        rw [← WithBot.coe_le_coe, ← hij]
        apply s.pred_le) le_top)
  isIso₂ (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i) (pq : κ) (hpq : s.position n j = pq)
      (i₁ i₂ i₂' : ι) (hi₁ : data.i₁ pq = i₁) (hi₂ : hdata.mapWithBot n i = i₂)
      (hi₂' : data.i₂ (s.position n j) = i₂')
      (h₁₂ : i₂ < i₁) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
      (hn₁' : hdata.deg n = n₁) :
    IsIso (X.EMapFourδ₂Toδ₁' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₂ i₁ i₂' ⊤ bot_le h₁₂.le (by
        simpa only [← hi₁, ← hi₂', hpq] using (data.le₁₂ pq)) le_top)

variable (n : σ) [hX : X.ConvergesInDegree hdata n]

lemma hasPageInfinityAt_of_convergesInDegree (pq : κ)
    (hpq : s.stripe pq = n) : X.StationaryAt data pq :=
  hX.stationnaryAt pq hpq

lemma isIso₁_of_convergesInDegree
    (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i) (pq : κ) (hpq : s.position n j = pq)
      (i₁ i₂ i₂' : ι) (hi₁ : data.i₁ pq = i₁) (hi₂ : hdata.mapWithBot n i = i₂)
      (hi₂' : data.i₂ (s.position n j) = i₂')
      (h₁₂ : i₁ ≤ i₂) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
      (hn₁' : hdata.deg n = n₁) :
    IsIso (X.EMapFourδ₂Toδ₁' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₁ i₂ i₂' ⊤ bot_le h₁₂ (by
      rw [← hi₂, ← hi₂']
      obtain _|i := i
      · exact bot_le
      · apply hdata.i₂_monotone
        change _ = WithBot.some i at hij
        rw [← WithBot.coe_le_coe, ← hij]
        apply s.pred_le) le_top) := by
  obtain rfl|h₁₂ := h₁₂.eq_or_lt
  · dsimp [EMapFourδ₂Toδ₁']
    erw [EMap_id]
    infer_instance
  · obtain _|i := i
    · simp at hi₂
      exfalso
      simp only [← hi₂, not_lt_bot] at h₁₂
    · exact hX.isIso₁ i j hij pq hpq i₁ i₂ i₂' hi₁ hi₂ hi₂' h₁₂ _ _ _ _ _ hn₁'

lemma isIso₂_of_convergesInDegree
    (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i) (pq : κ) (hpq : s.position n j = pq)
      (i₁ i₂ i₂' : ι) (hi₁ : data.i₁ pq = i₁) (hi₂ : hdata.mapWithBot n i = i₂)
      (hi₂' : data.i₂ (s.position n j) = i₂')
      (h₁₂ : i₂ ≤ i₁) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
      (hn₁' : hdata.deg n = n₁) :
    IsIso (X.EMapFourδ₂Toδ₁' n₀ n₁ n₂ hn₁ hn₂ ⊥ i₂ i₁ i₂' ⊤ bot_le h₁₂ (by
      simpa only [← hi₁, ← hi₂', hpq] using (data.le₁₂ pq)) le_top) := by
  obtain rfl|h₁₂ := h₁₂.eq_or_lt
  · dsimp [EMapFourδ₂Toδ₁']
    erw [EMap_id]
    infer_instance
  · exact hX.isIso₂ i j hij pq hpq i₁ i₂ i₂' hi₁ hi₂ hi₂' h₁₂ _ _ _ _ _ hn₁'

lemma isZero₁_of_convergesInDegree :
    ∃ (i : α n),
      IsZero ((X.H (hdata.deg n)).obj (mk₁ (homOfLE' ⊥ (hdata.mapWithBot n (s.pred n i)) bot_le))) := by
  obtain ⟨i, hi⟩ := hX.isZero₁
  refine' ⟨i, _⟩
  obtain h | ⟨j, h⟩ := Option.by_cases (s.pred n i)
  · have : IsZero ((X.H (hdata.deg n)).obj (mk₁ (homOfLE' ⊥ ⊥ bot_le))) := by
      apply X.isZero_H_obj_of_isIso
      change IsIso (𝟙 _)
      infer_instance
    convert this
    rw [h]
    rfl
  · convert hi j h
    rw [h]
    rfl

lemma isZero₂_of_convergesInDegree :
    ∃ (i : α n),
      IsZero ((X.H (hdata.deg n)).obj (mk₁ (homOfLE' (data.i₂ (s.position n i)) ⊤ le_top))) :=
  hX.isZero₂

namespace ConvergesAt

section

variable (i : α n) (pq : κ) (hpq : s.position n i = pq)

noncomputable def π :
    X.abutmentFiltration (hdata.deg n) (data.i₂ (s.position n i)) ⟶ (X.spectralSequence data).pageInfinity pq :=
  X.abutmentFiltrationToPageInfinity (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp)
  (data.i₁ (s.position n i)) (data.i₂ (s.position n i))
    (data.le₁₂ (s.position n i)) ≫ Iso.inv (by
        have := X.hasPageInfinityAt_of_convergesInDegree hdata n pq (by
          rw [← hpq, s.stripe_position])
        apply X.spectralSequencePageInfinityIso
        · rw [← hpq, hdata.deg_position n i]
        · rw [hpq]
        · rw [hpq])

instance : Epi (π X hdata n i pq hpq) := epi_comp _ _

end

section

variable
  (i : WithBot (α n)) (j : α n) (hij : s.pred n j = i)
  (pq : κ) (hpq : s.position n j = pq)

@[simp]
noncomputable def composableArrows : ComposableArrows C 2 :=
  mk₂ (X.abutmentFiltrationMap (hdata.deg n) _ _ (hdata.mapWithBot_pred_le_i₂ n i j hij))
    (π X hdata n j pq hpq)

noncomputable def pageInfinityIso :
    (X.spectralSequence data).pageInfinity pq ≅
      X.pageInfinity (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp)
        (data.i₁ pq) (data.i₂ (s.position n j)) (by simpa only [hpq] using data.le₁₂ pq) := by
  haveI : X.StationaryAt data pq := X.hasPageInfinityAt_of_convergesInDegree hdata n pq (by
      rw [← hpq, s.stripe_position])
  exact X.spectralSequencePageInfinityIso data pq
    (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) _ _
    (by rw [← hdata.deg_stripe pq, ← hpq, s.stripe_position]) _ _ rfl (by rw [hpq])

namespace Iso₃

section

variable (h : data.i₁ pq ≤ hdata.mapWithBot n i)

noncomputable def hom :
    X.pageInfinity (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp)
      (data.i₁ pq) (data.i₂ (s.position n j)) (by simpa only [hpq] using data.le₁₂ pq) ⟶
    X.pageInfinity (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp)
      (hdata.mapWithBot n i) (data.i₂ (s.position n j))
        (hdata.mapWithBot_pred_le_i₂ n i j hij) :=
  X.EMapFourδ₂Toδ₁' _ _ _ _ _ _ _ _ _ _ _ h _ _

instance : IsIso (hom X hdata n i j hij pq hpq h) :=
  X.isIso₁_of_convergesInDegree hdata n i j hij pq hpq _ _ _ rfl rfl rfl _ _ _ _ _ _ rfl

noncomputable def iso := asIso (hom X hdata n i j hij pq hpq h)

@[reassoc (attr := simp)]
lemma π_pageInfinityIso_hom_iso_hom :
    π X hdata n j pq hpq ≫ (pageInfinityIso X hdata n j pq hpq).hom ≫
      (iso X hdata n i j hij pq hpq h).hom =
        X.abutmentFiltrationToPageInfinity _ _ _ _ _ _ _ _ := by
  sorry

end

section

variable (h : hdata.mapWithBot n i ≤ data.i₁ pq)

noncomputable def hom' :
    X.pageInfinity (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp)
      (hdata.mapWithBot n i) (data.i₂ (s.position n j))
        (hdata.mapWithBot_pred_le_i₂ n i j hij) ⟶
    X.pageInfinity (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp)
      (data.i₁ pq) (data.i₂ (s.position n j)) (by simpa only [hpq] using data.le₁₂ pq) :=
  X.EMapFourδ₂Toδ₁' _ _ _ _ _ _ _ _ _ _ _ h _ _

instance : IsIso (hom' X hdata n i j hij pq hpq h) :=
  X.isIso₂_of_convergesInDegree hdata n i j hij pq hpq _ _ _ rfl rfl rfl _ _ _ _ _ _ rfl

noncomputable def iso' := (asIso (hom' X hdata n i j hij pq hpq h)).symm

lemma π_pageInfinityIso_hom :
    π X hdata n j pq hpq ≫ (pageInfinityIso X hdata n j pq hpq).hom =
      X.abutmentFiltrationToPageInfinity _ _ _ _ _ _ _ _ ≫
        (iso' X hdata n i j hij pq hpq h).inv := by
  sorry

@[reassoc (attr := simp)]
lemma π_pageInfinityIso_hom_iso'_hom :
    π X hdata n j pq hpq ≫ (pageInfinityIso X hdata n j pq hpq).hom ≫
      (iso' X hdata n i j hij pq hpq h).hom =
        X.abutmentFiltrationToPageInfinity _ _ _ _ _ _ _ _ := by
  rw [← cancel_mono (iso' X hdata n i j hij pq hpq h).inv, assoc, assoc,
    Iso.hom_inv_id, comp_id, π_pageInfinityIso_hom]

end

end Iso₃

noncomputable def iso₃ :
    X.pageInfinity (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp)
      (data.i₁ pq) (data.i₂ (s.position n j)) (by simpa only [hpq] using data.le₁₂ pq) ≅
    X.pageInfinity (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp)
      (hdata.mapWithBot n i) (data.i₂ (s.position n j))
        (hdata.mapWithBot_pred_le_i₂ n i j hij) := by
  by_cases h : data.i₁ pq ≤ hdata.mapWithBot n i
  · exact Iso₃.iso X hdata n i j hij pq hpq h
  · exact Iso₃.iso' X hdata n i j hij pq hpq
      (by cases LinearOrder.le_total (data.i₁ pq) (hdata.mapWithBot n i) <;> tauto)

@[reassoc (attr := simp)]
lemma π_pageInfinityIso_hom_iso₃_hom :
    π X hdata n j pq hpq ≫ (pageInfinityIso X hdata n j pq hpq).hom ≫
      (iso₃ X hdata n i j hij pq hpq).hom =
        X.abutmentFiltrationToPageInfinity _ _ _ _ _ _ _ _ := by
  by_cases h : data.i₁ pq ≤ hdata.mapWithBot n i
  · simp [iso₃, dif_pos h]
  · simp [iso₃, dif_neg h]

noncomputable def iso : composableArrows X hdata n i j hij pq hpq ≅
    (X.abutmentFiltrationShortComplex (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1)
      (by simp) (by simp) _ _ (hdata.mapWithBot_pred_le_i₂ n i j hij)).toComposableArrows :=
  isoMk₂ (Iso.refl _) (Iso.refl _)
    (pageInfinityIso X hdata n j pq hpq ≪≫ iso₃ X hdata n i j hij pq hpq) (by simp) (by simp)

lemma composableArrows_exact :
    (composableArrows X hdata n i j hij pq hpq).Exact :=
  ComposableArrows.exact_of_iso (iso X hdata n i j hij pq hpq).symm
    (X.abutmentFiltrationShortComplex_shortExact _ _ _ _ _ _ _ _).exact.exact_toComposableArrows

end

end ConvergesAt

noncomputable def convergesAt :
    (X.spectralSequence data).StronglyConvergesToInDegree s n (X.abutment (hdata.deg n)) where
  hasPageInfinityAt pq hpq := by
    have := X.hasPageInfinityAt_of_convergesInDegree hdata n pq hpq
    infer_instance
  filtration' := hdata.mapWithBotFunctor n ⋙ X.abutmentFiltrationFunctor (hdata.deg n)
  exists_isZero' := by
    obtain ⟨i, hi⟩ := X.isZero₁_of_convergesInDegree hdata n
    exact ⟨i, X.isZero_image _ _ _ _ _ hi⟩
  exists_isIso' := by
    obtain ⟨i, hi⟩ := X.isZero₂_of_convergesInDegree hdata n
    exact ⟨i, X.isIso_imageι _ _ _ _ _ hi⟩
  π' i pq hpq := ConvergesAt.π X hdata n i pq hpq
  epi_π' i pq hpq := by infer_instance
  comp_π' i j hij pq hpq := (ConvergesAt.composableArrows_exact X hdata n i j hij pq hpq).toIsComplex.zero 0
  exact_π' i j hij pq hpq := (ConvergesAt.composableArrows_exact X hdata n i j hij pq hpq).exact 0

instance (X : SpectralObject C ℤt) [X.IsFirstQuadrant] (n : ℤ) :
    X.ConvergesInDegree mkDataE₂CohomologicalCompatibility n where
  isZero₁ := ⟨1, fun j hj => by
    apply isZero₁_of_isFirstQuadrant
    obtain rfl : j = 0 := by
      erw [Option.some.injEq] at hj
      linarith
    simp⟩
  isZero₂ := ⟨n + 1, by
    apply isZero₂_of_isFirstQuadrant
    simp⟩
  isIso₁ := by
    rintro i j hij pq hpq _ _ _ rfl rfl rfl h
    exfalso
    apply ne_of_lt h
    exact mkDataE₂Cohomological_i₁_eq_i₂ n i j hij pq hpq
  isIso₂ := by
    rintro i j hij pq hpq _ _ _ rfl rfl rfl h
    exfalso
    apply ne_of_lt h
    obtain _|i := i
    · simp at hij
    · exact (mkDataE₂Cohomological_i₁_eq_i₂ n i j hij pq hpq).symm

instance (X : SpectralObject C ℤt) [X.IsFirstQuadrant] (n : ℕ) :
    X.ConvergesInDegree mkDataE₂CohomologicalNatCompatibility n where
  isZero₁ := ⟨0, fun j hj => by
    exfalso
    dsimp at hj ⊢
    change ⊥ = _ at hj
    simp at hj⟩
  isZero₂ := ⟨Fin.last _, X.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp)⟩
  isIso₁ := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij pq hpq _ _ _ rfl rfl rfl h
    exfalso
    apply ne_of_lt h
    obtain _|j := j
    · exfalso
      change ⊥ = WithBot.some _ at hij
      simp at hij
    · dsimp at hij h hpq ⊢
      obtain rfl : j = i := by simpa using hij
      simp [← hpq]
  isIso₂ := by
    rintro i ⟨j, hj⟩ hij pq hpq _ _ _ rfl rfl rfl h
    obtain _|⟨i, hi⟩ := i
    · obtain _|j := j
      · intro n₀ n₁ n₂ hn₁ hn₂ _
        subst hpq
        dsimp
        apply X.isIso_EMapFourδ₂Toδ₁'
        · apply X.isIso_H_map_twoδ₁Toδ₀' n₁ n₂ hn₂
          · apply isZero₁_of_isFirstQuadrant
            simp
          · apply isZero₁_of_isFirstQuadrant
            simp
        · refine' ⟨0, IsZero.eq_of_src _ _ _, IsZero.eq_of_src _ _ _⟩
          · apply isZero₁_of_isFirstQuadrant
            simp
          · apply isZero₁_of_isFirstQuadrant
            simp
      · dsimp at hij
        change some _ = none at hij
        simp at hij
    · exfalso
      apply ne_of_lt h
      dsimp at hpq hij h ⊢
      obtain _|j := j
      · simp at hij
      · simp at hij
        obtain rfl : j = i := by
          change some _ = _ at hij
          simpa using hij
        rw [← hpq]
        rfl

instance (X : SpectralObject C ℤt) [X.IsThirdQuadrant] (n : ℕ) :
    X.ConvergesInDegree mkDataE₂HomologicalNatCompatibility n where
  isZero₁ := ⟨0, fun j hj => by
    exfalso
    dsimp at hj
    change ⊥ = _ at hj
    simp at hj⟩
  isZero₂ := ⟨Fin.last _, X.isZero₁_of_isThirdQuadrant _ _ _ (by simp) _⟩
  isIso₁ := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij pq hpq _ _ _ rfl rfl rfl h
    exfalso
    apply ne_of_lt h
    obtain _|j := j
    · change ⊥ = _ at hij
      simp at hij
    · obtain rfl : j = i := by simpa using hij
      rw [← hpq]
      dsimp
      congr 1
      linarith [Nat.add_sub_of_le (show j.succ ≤ n by linarith),
        Nat.add_sub_of_le (show j ≤ n by linarith)]
  isIso₂ := by
    rintro i ⟨j, hj⟩ hij pq hpq _ _ _ rfl rfl rfl h
    obtain _|⟨i, hi⟩ := i
    · dsimp at hpq h
      subst hpq
      obtain _|j := j
      · intro n₀ n₁ n₂ hn₁ hn₂ hn₁'
        apply X.isIso_EMapFourδ₂Toδ₁'
        · apply X.isIso_H_map_twoδ₁Toδ₀' n₁ n₂ hn₂
          · apply X.isZero₂_of_isThirdQuadrant
            subst hn₁'
            rfl
          · apply X.isZero₂_of_isThirdQuadrant
            subst hn₁' hn₂
            simp
        · refine' ⟨0, IsZero.eq_of_src _ _ _, IsZero.eq_of_src _ _ _⟩
          · apply X.isZero₂_of_isThirdQuadrant
            exact bot_le
          · apply X.isZero₂_of_isThirdQuadrant
            subst hn₁' hn₂
            simp
      · change some _ = _ at hij
        simp at hij
    · exfalso
      apply ne_of_lt h
      obtain _|j := j
      · change ⊥ = _ at hij
        simp at hij
      · obtain rfl : j = i := by
          change some _ = some _ at hij
          simpa using hij
        rw [← hpq]
        dsimp
        congr 1
        linarith [Nat.add_sub_of_le (show j.succ ≤ n by linarith),
          Nat.add_sub_of_le (show j ≤ n by linarith)]

end SpectralObject

end Abelian

end CategoryTheory
