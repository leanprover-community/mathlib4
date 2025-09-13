import Mathlib

structure LinearMap.Diagonalization.{u, v} (ι : Type*) {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (f : Module.End R M) extends Module.Basis ι R M where
  μ : ι → R
  hasEigenVector_μ (i : ι) : f.HasEigenvector (μ i) (toBasis i)

@[ext]
theorem LinearMap.Diagonalization.ext {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} {D₁ D₂ : f.Diagonalization ι} (h : D₁.toBasis = D₂.toBasis) :
    D₁ = D₂ := by
  suffices D₁.μ = D₂.μ by cases D₁; cases D₂; simp_all only
  funext i
  suffices D₁.μ i • D₁.toBasis i = D₂.μ i • D₁.toBasis i by
    simpa using congr(D₁.toBasis.repr $this i)
  rw [← (D₁.hasEigenVector_μ i).apply_eq_smul, h, ← (D₂.hasEigenVector_μ i).apply_eq_smul]


lemma LinearMap.Diagonalization.toMatrix_eq_diagonal {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] {f : Module.End R M} (D : f.Diagonalization ι) :
    f.toMatrix D.toBasis D.toBasis = Matrix.diagonal D.μ := by
  ext i j
  simp [LinearMap.toMatrix_apply, (D.hasEigenVector_μ j).apply_eq_smul]
  grind [Finsupp.single_apply, Matrix.diagonal_apply]

-- note: Nontrivial R golfed in #29420
lemma LinearMap.Diagonalization.charpoly_eq {ι R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
    [Fintype ι] [DecidableEq ι] {f : Module.End R M} (D : f.Diagonalization ι) :
    f.charpoly = ∏ i, (Polynomial.X - Polynomial.C (D.μ i)) := by
  rw [← f.charpoly_toMatrix D.toBasis, D.toMatrix_eq_diagonal, Matrix.charpoly_diagonal]

def LinearMap.diagonalization_of_isDiag_toMatrix {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} (b : Module.Basis ι R M) (h : (f.toMatrix b b).IsDiag) :
    f.Diagonalization ι := sorry

-- TODO: is it true? in what generality?
lemma LinearMap.nonempty_diagonalization_iff_iSup_eigenspace {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} :
    Nonempty (f.Diagonalization ι) ↔ ⨆ μ, f.eigenspace μ = ⊤ := by
  sorry

-- TODO: determine generality. Probably needs at least Module.Free?
lemma LinearMap.nonempty_diagonalization_iff_directSum_eigenspace {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} [DecidableEq f.Eigenvalues] :
    Nonempty (f.Diagonalization ι) ↔ DirectSum.IsInternal fun (μ : f.Eigenvalues) => f.eigenspace μ := by
  sorry

-- probably follow-up work
proof_wanted LinearMap.nonempty_diagonalization_iff_minpoly_splits_and_squarefree  {ι K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    {f : Module.End K M} :
    Nonempty (f.Diagonalization ι) ↔ (minpoly K f).Splits (RingHom.id K) ∧ Squarefree (minpoly K f)

-- probably follow-up work. need determine right generality.
proof_wanted LinearMap.Diagonalization.isSemisimple {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    {f : Module.End R M} (D : f.Diagonalization ι) : f.IsSemisimple

-- random nerdsnipe, not actually trying to add this
theorem LinearMap.Diagonalization.μ_unique {ι ι' R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} {D₁ : f.Diagonalization ι} {D₂ : f.Diagonalization ι'} :
    ∃ e : ι ≃ ι', D₁.μ = D₂.μ ∘ e := by
  sorry
