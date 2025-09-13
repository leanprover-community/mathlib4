import Mathlib

namespace LinearMap

open Module Matrix Polynomial

variable {α R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/--
A diagonalization of a family of linear maps $T_i : V \to V$ is a basis of $V$
consisting of simultaneous eigenvectors of $T_i$.
-/
structure SimultaneousDiagonalization (ι : Type*) (f : α → End R M) extends Basis ι R M where
  μ : α → ι → R
  hasEigenVector_μ (a : α) (i : ι) : (f a).HasEigenvector (μ a i) (toBasis i)

/--
A diagonalization of a linear map $T : V \to V$ is a basis of $V$ consisting of eigenvectors of $T$.
-/
abbrev Diagonalization (ι : Type*) (f : End R M) := SimultaneousDiagonalization ι fun _ : Unit ↦ f

/-- The eigenvalues of the diagonalization. -/
def Diagonalization.μ {ι : Type*} {f : End R M} (self : f.Diagonalization ι) :=
  SimultaneousDiagonalization.μ self ()

theorem Diagonalization.hasEigenVector_μ {ι : Type*} {f : End R M}
    (self : f.Diagonalization ι) (i : ι) : f.HasEigenvector (self.μ i) (self.toBasis i) :=
  SimultaneousDiagonalization.hasEigenVector_μ self () i

/-- Cpnstruct `LinearMap.Diagonalization` from a basis of eigenvectors and eigenvalues. -/
def Diagonalization.mk {ι : Type*} {f : End R M} {b : Basis ι R M} {μ : ι → R}
    (hasEigenVector_μ : ∀ i, f.HasEigenvector (μ i) (b i)) : f.Diagonalization ι where
  toBasis := b
  μ := fun _ ↦ μ
  hasEigenVector_μ := fun _ => hasEigenVector_μ

/--
Alternative constructor for `LinearMap.Diagonalization` from a basis of eigenvectors and
existence of eigenvalues.
-/
noncomputable def Diagonalization.mk' {ι : Type*} {f : End R M} {b : Basis ι R M}
    (exists_hasEigenVector : ∀ i, ∃ μ, f.HasEigenvector μ (b i)) : f.Diagonalization ι where
  toBasis := b
  μ := fun _ i ↦ (exists_hasEigenVector i).choose
  hasEigenVector_μ := fun _ i => (exists_hasEigenVector i).choose_spec

/--
Alternative constructor for `LinearMap.Diagonalization` from a basis of eigenvectors and
diagonality of the matrix representation.
-/
noncomputable def diagonalization_of_isDiag_toMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : End R M} {b : Basis ι R M} (h : (f.toMatrix b b).IsDiag) :
    f.Diagonalization ι :=
  Diagonalization.mk (b := b) (μ := fun i ↦ f.toMatrix b b i i) <| by
    sorry

/-- The diagonalization of the endomorphism indexed by `a`. -/
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

lemma Diagonalization.iSup_eigenspace_eq_top {ι : Type*} {f : End R M} (D : f.Diagonalization ι) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  sorry

lemma nonempty_diagonalization_iff_iSup_eigenspace {ι : Type*} {f : End R M} [Free R M] :
    Nonempty ((ι : Type) × f.Diagonalization ι) ↔ ⨆ μ, f.eigenspace μ = ⊤ := by
  sorry

-- TODO: determine generality. Maybe needs Module.Free?
lemma nonempty_diagonalization_iff_directSum_eigenspace {ι : Type*} {f : End R M}
    [IsDomain R] [DecidableEq f.Eigenvalues] : Nonempty ((ι : Type) × f.Diagonalization ι) ↔
    DirectSum.IsInternal fun (μ : f.Eigenvalues) => f.eigenspace μ := by
  sorry

-- probably follow-up work
lemma nonempty_diagonalization_iff_minpoly_splits_and_squarefree  {ι K : Type*}
    [Field K] [Module K M] {f : End K M} : Nonempty ((ι : Type) × f.Diagonalization ι) ↔
    (minpoly K f).Splits (RingHom.id K) ∧ Squarefree (minpoly K f) := by
  sorry

-- probably follow-up work. need determine right generality.
lemma Diagonalization.isSemisimple {ι : Type*} [IsSemisimpleModule R M]
    {f : End R M} (D : f.Diagonalization ι) : f.IsSemisimple := by
  sorry

-- This is proved: https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/diagonalizable.20linear.20maps/near/539282397
theorem LinearMap.Diagonalization.μ_equiv {ι ι' R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    {f : Module.End R M} {D₁ : f.Diagonalization ι} {D₂ : f.Diagonalization ι'} :
    ∃ e : ι ≃ ι', D₁.μ = D₂.μ ∘ e := by
  sorry

-- TODO: Something about simultaneous diagonalization commuting
-- TODO: The above for normal endomorphisms

end LinearMap
