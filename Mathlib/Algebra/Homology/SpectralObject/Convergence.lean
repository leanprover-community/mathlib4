import Mathlib.Algebra.Homology.SpectralObject.PageInfinity
import Mathlib.Algebra.Homology.SpectralObject.Images

namespace CategoryTheory

open Category ComposableArrows Limits

lemma Option.by_cases {α : Type*} (x : Option α) :
    x = none ∨ ∃ (a : α), x = some a := by
  cases x <;> tauto

namespace Abelian

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι] [OrderBot ι] [OrderTop ι]
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
  hi₁_bot (n : σ) (j : α n) (hj : s.pred n j = ⊥) :
    data.i₁ (s.position n j) = ⊥
  hi₁_some (n : σ) (j : α n) (i : α n) (hi : s.pred n j = WithBot.some i) :
    data.i₁ (s.position n j) = data.i₂ (s.position n i)

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

lemma mapWithBot_pred (n : σ) (j : α n) :
    hdata.mapWithBot n (s.pred n j) = data.i₁ (s.position n j) := by
  obtain h | ⟨i, h⟩ := Option.by_cases (s.pred n j)
  · rw [h, mapWithBot_none, hdata.hi₁_bot n j h]
  · rw [h, mapWithBot_some, hdata.hi₁_some n j _ h]

end CompatibleWithConvergenceStripes

end SpectralSequenceMkData

@[simps]
def mkDataE₂CohomologicalCompatibility :
    mkDataE₂Cohomological.CompatibleWithConvergenceStripes
      SpectralSequence.cohomologicalStripes where
  deg n := n
  i₂_monotone n i j hij := by simpa using hij
  hi₁_bot n j hj := by simp at hj
  hi₁_some n j i hi := by
    obtain rfl : i = j - 1 := by
      rw [← WithBot.coe_eq_coe]
      exact hi.symm
    simp

/-@[simps]
def mkDataE₂CohomologicalNatCompatibility :
    mkDataE₂CohomologicalNat.CompatibleWithConvergenceStripes
      CohomologicalSpectralSequenceNat.stripes where
  deg n := n
  i₂_monotone n i j hij := by simpa using hij
  hi₁_bot := by
    rintro n ⟨j, hj⟩ h
    dsimp at h ⊢
    sorry
  hi₁_some := by
    rintro n ⟨_|j, hj⟩ ⟨i, hi⟩ h
    · sorry -- wrong => the condition `CompatibleWithConvergenceStripes` may have to be weakened?
    · obtain rfl : j = i := by simpa using h
      rfl-/

variable {data s}
variable (hdata : data.CompatibleWithConvergenceStripes s)
  [X.HasSpectralSequence data]

class ConvergesInDegree (n : σ) : Prop where
  stationnaryAt (pq : κ) (hpq : s.stripe pq = n) : X.StationaryAt data pq := by infer_instance
  isZero₁ : ∃ (i : α n), ∀ (j : α n) (_ : s.pred n i = WithBot.some j),
    IsZero ((X.H (hdata.deg n)).obj (mk₁ (homOfLE' ⊥ (data.i₂ (s.position n j)) bot_le)))
  isZero₂ : ∃ (i : α n),
    IsZero ((X.H (hdata.deg n)).obj (mk₁ (homOfLE' (data.i₂ (s.position n i)) ⊤ le_top)))

variable (n : σ) [hX : X.ConvergesInDegree hdata n]

lemma hasPageInfinityAt_of_convergesInDegree (pq : κ)
    (hpq : s.stripe pq = n) : X.StationaryAt data pq :=
  hX.stationnaryAt pq hpq

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

variable
  (n' : ℤ) (hn' : n' = hdata.deg n)
  (i : α n) (i₂ : ι) (hi₂ : i₂ = data.i₂ (s.position n i)) (pq : κ)
  (hpq : s.position n i = pq)

noncomputable def π : X.abutmentFiltration n' i₂ ⟶ (X.spectralSequence data).pageInfinity pq :=
  X.abutmentFiltrationToPageInfinity (n' - 1) n' (n' + 1) (by simp) (by simp) (data.i₁ (s.position n i)) i₂
    (by simpa only [hi₂] using data.le₁₂ (s.position n i)) ≫ Iso.inv (by
        have := X.hasPageInfinityAt_of_convergesInDegree hdata n pq (by
          rw [← hpq, s.stripe_position])
        apply X.spectralSequencePageInfinityIso
        · rw [hn', ← hpq, hdata.deg_position n i]
        · rw [hpq]
        · rw [← hpq, hi₂])

instance : Epi (π X hdata n n' hn' i i₂ hi₂ pq hpq) := epi_comp _ _

end

section

variable (n' : ℤ) (hn' : n' = hdata.deg n)
  (i : WithBot (α n)) (j : α n) (i₂ j₂ : ι) (hi₂ : i₂ = hdata.mapWithBot n i) (hj₂ : j₂ = data.i₂ (s.position n j)) (hij : s.pred n j = i)
  (pq : κ) (hpq : s.position n j = pq)

noncomputable def composableArrows : ComposableArrows C 2 :=
  mk₂ (X.abutmentFiltrationMap n' i₂ j₂ (by
    rw [hi₂, hj₂]
    obtain _|i := i
    · apply bot_le
    · apply hdata.i₂_monotone
      rw [← WithBot.coe_le_coe]
      simpa only [hij] using s.pred_le n j)) (π X hdata n n' hn' j j₂ hj₂ pq hpq)

noncomputable def iso :
    (composableArrows X hdata n n' hn' i j i₂ j₂ hi₂ hj₂ hij pq hpq) ≅
      (X.abutmentFiltrationShortComplex (n' - 1) n' (n' + 1) (by simp) (by simp) i₂ j₂ (by
      rw [hi₂, hj₂]
      obtain _|i := i
      · apply bot_le
      · apply hdata.i₂_monotone
        rw [← WithBot.coe_le_coe]
        simpa only [hij] using s.pred_le n j)).toComposableArrows :=
  isoMk₂ (Iso.refl _) (Iso.refl _) (by
    have := X.hasPageInfinityAt_of_convergesInDegree hdata n pq (by
      rw [← hpq, s.stripe_position])
    dsimp [composableArrows]
    apply X.spectralSequencePageInfinityIso
    · rw [hn', ← hpq, hdata.deg_position n j]
    · rw [hi₂, ← hij, ← hpq, hdata.mapWithBot_pred n j]
    · rw [hj₂, ← hpq]) (by simp [composableArrows]) (by
        dsimp [composableArrows, π]
        obtain rfl : i₂ = data.i₁ (s.position n j) := by
          rw [hi₂, ← hij, hdata.mapWithBot_pred n j]
        simp)

lemma composableArrows_exact :
    (composableArrows X hdata n n' hn' i j i₂ j₂ hi₂ hj₂ hij pq hpq).Exact :=
  ComposableArrows.exact_of_iso (iso X hdata n n' hn' i j i₂ j₂ hi₂ hj₂ hij pq hpq).symm
    ((X.abutmentFiltrationShortComplex_shortExact _ _ _ _ _ _ _ _).exact.exact_toComposableArrows)

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
  π' i pq hpq := ConvergesAt.π X hdata n _ rfl i _ rfl pq hpq
  epi_π' i pq hpq := by infer_instance
  comp_π' i j hij pq hpq := (ConvergesAt.composableArrows_exact X hdata n _ rfl i j _ _ rfl rfl hij pq hpq).toIsComplex.zero 0
  exact_π' i j hij pq hpq := (ConvergesAt.composableArrows_exact X hdata n _ rfl i j _ _ rfl rfl hij pq hpq).exact 0

end SpectralObject

end Abelian

end CategoryTheory
