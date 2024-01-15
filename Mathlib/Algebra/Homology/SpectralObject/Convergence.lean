import Mathlib.Algebra.Homology.SpectralObject.PageInfinity
import Mathlib.Algebra.Homology.SpectralObject.Images

namespace CategoryTheory

open Category ComposableArrows Limits

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
  | some i => data.i₂ (s.position n i) -- or i₁ ??

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

end CompatibleWithConvergenceStripes

end SpectralSequenceMkData

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

variable {data s}
variable (hdata : data.CompatibleWithConvergenceStripes s)
  [X.HasSpectralSequence data]

class ConvergesInDegree (n : σ) : Prop where
  stationnaryAt (pq : κ) (hpq : s.stripe pq = n) : X.StationaryAt data pq := by infer_instance
  test : hdata = hdata

variable (n : σ) [hX : X.ConvergesInDegree hdata n]

lemma hasPageInfinityAt_of_convergesInDegree (pq : κ)
    (hpq : s.stripe pq = n) : X.StationaryAt data pq :=
  hX.stationnaryAt pq hpq

namespace ConvergesAt

variable (data) (s)

noncomputable def π (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i : α n) :
    X.abutmentFiltration n₁ (data.i₂ (s.position n i)) ⟶
    X.pageInfinity n₀ n₁ n₂ hn₁ hn₂ _ _ (data.le₁₂ (s.position n i)) :=
  X.abutmentFiltrationToPageInfinity n₀ n₁ n₂ hn₁ hn₂ _ _
    (data.le₁₂ (s.position n i))

end ConvergesAt

/-noncomputable def convergesAt :
    (X.spectralSequence data).StronglyConvergesToInDegree s n (X.abutment (hdata.deg n)) where
  hasPageInfinityAt pq hpq := by
    have := X.hasPageInfinityAt_of_convergesInDegree hdata n pq hpq
    infer_instance
  filtration' := hdata.mapWithBotFunctor n ⋙ X.abutmentFiltrationFunctor (hdata.deg n)
  exists_isZero' := sorry
  exists_isIso' := sorry
  π' i pq hpq := X.abutmentFiltrationToPageInfinity (hdata.deg n - 1)
    (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp) _ _
      (data.le₁₂ (s.position n i)) ≫ Iso.inv (by
        have := X.hasPageInfinityAt_of_convergesInDegree hdata n pq (by
          rw [← hpq, s.stripe_position])
        apply X.spectralSequencePageInfinityIso
        all_goals simp only [← hpq, hdata.deg_position n i])
  epi_π' i pq hpq := epi_comp _ _
  comp_π' i j hij pq hpq := by
    dsimp [MonoOver.forget]
    have pf := data.le₁₂ (s.position n j)
    have pif := X.abutmentFiltrationMap_abutmentFiltrationToPageInfinity
      (hdata.deg n - 1) (hdata.deg n) (hdata.deg n + 1) (by simp) (by simp) _ _ (data.le₁₂ (s.position n j))
    dsimp [SpectralSequenceMkData.CompatibleWithConvergenceStripes.mapWithBot]
    sorry
  exact_π' := sorry-/

end SpectralObject

end Abelian

end CategoryTheory
