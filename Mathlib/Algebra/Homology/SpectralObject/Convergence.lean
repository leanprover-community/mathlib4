import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
import Mathlib.Algebra.Homology.SpectralSequenceNew.LowDegreesExactSequence

namespace CategoryTheory

open ComposableArrows Limits

namespace Abelian

variable {C ι κ : Type*} [Category C] [Abelian C] [Preorder ι] [OrderBot ι] [OrderTop ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}
  [∀ r, DecidableRel (c r).Rel]


namespace SpectralObject

noncomputable def abutment (n : ℤ) : C :=
    (X.H n).obj (mk₁ (homOfLE' ⊥ ⊤ bot_le))

noncomputable def pageInfinity (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    (i j : ι) (hij : i ≤ j) : C :=
    X.E n₀ n₁ n₂ hn₁ hn₂ (homOfLE bot_le) (homOfLE hij) (homOfLE le_top)

noncomputable def abutmentFiltration (n : ℤ) (j : ι) : C :=
  kernel ((X.H n).map (show mk₁ (homOfLE' (⊥ : ι) ⊤ bot_le) ⟶ mk₁ (homOfLE' j ⊤ le_top) from
      homMk₁ (homOfLE bot_le) (𝟙 _) rfl))

variable (data : SpectralSequenceMkData ι c r₀)
  {σ : Type*} {α : σ → Type*} [∀ n, LinearOrder (α n)]
  (s : SpectralSequence.ConvergenceStripes κ α)

namespace SpectralSequenceMkData

structure CompatibleWithConvergenceStripes where
  deg : σ → ℤ
  deg_stripe (pq : κ) : deg (s.stripe pq) = data.deg pq := by aesop

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

end CompatibleWithConvergenceStripes

end SpectralSequenceMkData

@[simps]
def mkDataE₂CohomologicalCompatibility :
    mkDataE₂Cohomological.CompatibleWithConvergenceStripes
      SpectralSequence.cohomologicalStripes where
  deg n := n

@[simps]
def mkDataE₂CohomologicalNatCompatibility :
    mkDataE₂CohomologicalNat.CompatibleWithConvergenceStripes
      CohomologicalSpectralSequenceNat.stripes where
  deg n := n

end SpectralObject

end Abelian

end CategoryTheory

#lint
