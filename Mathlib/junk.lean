import Mathlib

namespace LinearMap

open Module Matrix Polynomial

variable {α R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

structure SimultaneousDiagonalization (ι : Type*) (f : α → End R M) extends Basis ι R M where
  μ : α → ι → R
  hasEigenVector_μ (a : α) (i : ι) : (f a).HasEigenvector (μ a i) (toBasis i)

abbrev Diagonalization (ι : Type*) (f : End R M) := SimultaneousDiagonalization ι fun _ : Unit ↦ f

def Diagonalization.mk {ι : Type*} {f : End R M} {b : Basis ι R M} {μ : ι → R}
    (h : ∀ i, f.HasEigenvector (μ i) (b i)) : f.Diagonalization ι :=
  { toBasis := b, μ := fun _ ↦ μ, hasEigenVector_μ := fun _ => h }

def Diagonalization.μ {ι : Type*} {f : End R M} (self : f.Diagonalization ι) :=
  SimultaneousDiagonalization.μ self ()

def Diagonalization.hasEigenVector_μ {ι : Type*} {f : End R M}
    (self : f.Diagonalization ι) (i : ι) : f.HasEigenvector (self.μ i) (self.toBasis i) :=
  SimultaneousDiagonalization.hasEigenVector_μ self () i

def SimultaneousDiagonalization.diagonalization {ι : Type*} {f : α → Module.End R M}
    (D : SimultaneousDiagonalization ι f) (a : α) : (f a).Diagonalization ι :=
  Diagonalization.mk (D.hasEigenVector_μ a)

@[ext]
theorem SimultaneousDiagonalization.ext {ι : Type*} {f : α → End R M}
    {D₁ D₂ : SimultaneousDiagonalization ι f} (h : D₁.toBasis = D₂.toBasis) : D₁ = D₂ := by
  suffices D₁.μ = D₂.μ by cases D₁; cases D₂; simp_all only
  ext a i
  suffices D₁.μ a i • D₁.toBasis i = D₂.μ a i • D₁.toBasis i by
    simpa using congr(D₁.toBasis.repr $this i)
  rw [← (D₁.hasEigenVector_μ a i).apply_eq_smul, h, ← (D₂.hasEigenVector_μ a i).apply_eq_smul]

example {ι} {f : Module.End R M} {D₁ D₂ : f.Diagonalization ι} (h : D₁.toBasis = D₂.toBasis) :
    D₁ = D₂ := by
  ext : 1
  exact h

lemma Diagonalization.toMatrix_eq_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : End R M} (D : f.Diagonalization ι) : f.toMatrix D.toBasis D.toBasis = diagonal D.μ := by
  ext i j
  simp [toMatrix_apply, (D.hasEigenVector_μ j).apply_eq_smul]
  grind [Finsupp.single_apply, diagonal_apply]

-- note: Nontrivial R golfed in #29420
lemma Diagonalization.charpoly_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial R] [Free R M]
    [Module.Finite R M] {f : End R M} (D : f.Diagonalization ι) :
    f.charpoly = ∏ i, (X - C (D.μ i)) := by
  rw [← f.charpoly_toMatrix D.toBasis, D.toMatrix_eq_diagonal, charpoly_diagonal]

def diagonalization_of_isDiag_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : End R M} (b : Basis ι R M) (h : (f.toMatrix b b).IsDiag) :
    f.Diagonalization ι := sorry

-- TODO: is it true? in what generality?
lemma nonempty_diagonalization_iff_iSup_eigenspace {ι : Type*} {f : End R M} :
    Nonempty ((ι : Type) × f.Diagonalization ι) ↔ ⨆ μ, f.eigenspace μ = ⊤ := by
  sorry

-- TODO: determine generality. Probably needs at least Module.Free?
lemma nonempty_diagonalization_iff_directSum_eigenspace {ι : Type*} {f : End R M}
    [DecidableEq f.Eigenvalues] : Nonempty ((ι : Type) × f.Diagonalization ι) ↔
    DirectSum.IsInternal fun (μ : f.Eigenvalues) => f.eigenspace μ := by
  sorry

-- probably follow-up work
proof_wanted nonempty_diagonalization_iff_minpoly_splits_and_squarefree  {ι K : Type*}
    [Field K] [Module K M] {f : End K M} : Nonempty ((ι : Type) × f.Diagonalization ι) ↔
    (minpoly K f).Splits (RingHom.id K) ∧ Squarefree (minpoly K f)

-- probably follow-up work. need determine right generality.
proof_wanted Diagonalization.isSemisimple {ι : Type*} [IsSemisimpleModule R M]
    {f : End R M} (D : f.Diagonalization ι) : f.IsSemisimple

-- TODO: Something about simultaneous diagonalization commuting
-- TODO: The above for normal endomorphisms

-- random nerdsnipe, not actually trying to add this
theorem Diagonalization.μ_unique {ι ι' : Type*} [IsDomain R] {f : End R M}
    {D₁ : f.Diagonalization ι} {D₂ : f.Diagonalization ι'} :
    ∃ e : ι ≃ ι', D₁.μ = D₂.μ ∘ e := by
  sorry

end LinearMap
