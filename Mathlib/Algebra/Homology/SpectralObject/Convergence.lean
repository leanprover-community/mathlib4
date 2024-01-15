import Mathlib.Algebra.Homology.SpectralObject.PageInfinity

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
  kernel ((X.H n).map (show mk₁ (homOfLE' (⊥ : ι) ⊤ bot_le) ⟶ mk₁ (homOfLE' j ⊤ le_top) from
      homMk₁ (homOfLE bot_le) (𝟙 _) rfl))

noncomputable def abutmentFiltrationι (n : ℤ) (j : ι) :
    X.abutmentFiltration n j ⟶ X.abutment n := kernel.ι _

noncomputable def abutmentπ (n : ℤ) (j : ι) :
    X.abutment n ⟶ (X.H n).obj (mk₁ (homOfLE' j ⊤ le_top)) :=
  (X.H n).map (homMk₁ (homOfLE bot_le) (𝟙 _) rfl)

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
  kernel.lift _ (X.abutmentFiltrationι n j₁) (by
    let φ : (mk₁ (homOfLE' j₁ ⊤ le_top)) ⟶ (mk₁ (homOfLE' j₂ ⊤ le_top)) := homMk₁ (homOfLE h) (𝟙 _) rfl
    dsimp
    have h := X.abutmentFiltrationι_π n j₁ =≫ (X.H n).map φ
    convert h using 1
    · dsimp
      rw [assoc, abutmentπ_map]
      rfl
    · rw [zero_comp])

@[reassoc (attr := simp)]
lemma abutmentFiltrationMap_ι (n : ℤ) (j₁ j₂ : ι) (h : j₁ ≤ j₂) :
    X.abutmentFiltrationMap n j₁ j₂ h ≫ X.abutmentFiltrationι n j₂ =
      X.abutmentFiltrationι n j₁ :=
  kernel.lift_ι _ _ _

noncomputable def abutmentFiltrationFunctor (n : ℤ) :
    ι ⥤ MonoOver (X.abutment n) where
  obj j := MonoOver.mk' (X.abutmentFiltrationι n j)
  map {j₁ j₂} h := Over.homMk (X.abutmentFiltrationMap n j₁ j₂ (leOfHom h)) (by simp)

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

/-class ConvergesInDegree (n : σ) : Prop where
  test : hdata = hdata ∧ X = X

variable (n : σ) [hX : X.ConvergesInDegree hdata n]

noncomputable def convergesAt :
    (X.spectralSequence data).StronglyConvergesToInDegree s n (X.abutment (hdata.deg n)) where
  hasPageInfinityAt := sorry
  filtration' := hdata.mapWithBotFunctor n ⋙ X.abutmentFiltrationFunctor (hdata.deg n)
  exists_isZero' := sorry
  exists_isIso' := sorry
  π' := sorry
  epi_π' := sorry
  comp_π' := sorry
  exact_π' := sorry-/

end SpectralObject

end Abelian

end CategoryTheory
