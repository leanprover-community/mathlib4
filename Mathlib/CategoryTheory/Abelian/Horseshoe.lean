import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.ProjectiveResolution

namespace CategoryTheory

open HomologicalComplex Limits

variable {C : Type*} [Category C] [Abelian C]
variable {S : ShortComplex C} (hS : S.ShortExact)
  (P : ProjectiveResolution S.X₁) (R : ProjectiveResolution S.X₃)

namespace ProjectiveResolution

namespace Horseshoe

lemma exists_ε₂ :
    ∃ (ε₂ : R.complex.X 0 ⟶ S.X₂),
      ε₂ ≫ S.g = R.π.f 0 ≫ (singleObjXSelf _ _ _).hom := by
  have := hS.epi_g
  exact ⟨Projective.factorThru (R.π.f 0 ≫ (singleObjXSelf _ _ _).hom) S.g, by simp⟩

variable (ε₂ : R.complex.X 0 ⟶ S.X₂) (hε₂ : ε₂ ≫ S.g = R.π.f 0 ≫ (singleObjXSelf _ _ _).hom)

open Classical in
noncomputable def δ : ∀ (n : ℕ), R.complex.X (n + 1) ⟶ P.complex.X n
  | 0 => Projective.factorThru (letI := hS.mono_f; hS.exact.lift (-R.complex.d 1 0 ≫ ε₂)
      (by simp [hε₂])) (P.π.f 0)
  | 1 =>
      if h : R.complex.d 2 1 ≫ δ 0 ≫ P.π.f 0 = 0
      then by
        let T := ShortComplex.mk _ _ P.complex_d_comp_π_f_zero
        have hT := T.exact_of_g_is_cokernel P.isColimitCokernelCofork
        have := hT.epi_toCycles
        exact Projective.factorThru (T.liftCycles (-R.complex.d 2 1 ≫ δ 0)
          (by simpa using h)) T.toCycles
      else 0
  | n + 2 =>
      if h : R.complex.d (n + 3) (n + 2) ≫ δ (n + 1) ≫ P.complex.d (n + 1) n = 0
      then by
        let T := (P.complex.sc' (n + 2) (n + 1) n)
        have hT := ((exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)).1
          (P.complex_exactAt_succ n)).epi_toCycles
        exact Projective.factorThru (T.liftCycles (-R.complex.d (n + 3) (n + 2) ≫
          δ (n + 1)) (by simpa using h)) T.toCycles
      else 0

@[simp]
lemma h₀ : δ hS P R ε₂ hε₂ 0 ≫ P.π.f 0 ≫ S.f + R.complex.d 1 0 ≫ ε₂ = 0 := by simp [δ]

@[simp]
lemma h₁ (n : ℕ) :
    δ hS P R ε₂ hε₂ (n + 1) ≫ P.complex.d (n + 1) n +
      R.complex.d (n + 2) (n + 1) ≫ δ hS P R ε₂ hε₂ n = 0 := by
  have := hS.mono_f
  induction n with
  | zero =>
      let T := ShortComplex.mk _ _ P.complex_d_comp_π_f_zero
      have eq := T.toCycles_i
      dsimp at eq
      rw [← eq]
      dsimp [δ]
      rw [dif_pos (by simp [← cancel_mono S.f]), Projective.factorThru_comp_assoc,
        ShortComplex.liftCycles_i, add_left_neg]
  | succ n hn =>
      dsimp [δ]
      rw [dif_pos (by simpa using R.complex.d (n + 3) (n + 2) ≫= hn)]
      let T := P.complex.sc' (n + 2) (n + 1) n
      have eq := T.toCycles_i
      dsimp [T] at eq
      rw [← eq]
      rw [Projective.factorThru_comp_assoc, ShortComplex.liftCycles_i, add_left_neg]

@[simps!]
noncomputable def Qcomplex : ChainComplex C ℕ :=
  ChainComplex.of (fun n => P.complex.X n ⊞ R.complex.X n)
    (fun n => biprod.fst ≫ P.complex.d _ _ ≫ biprod.inl +
      biprod.snd ≫ δ hS P R ε₂ hε₂ n ≫ biprod.inl + biprod.snd ≫ R.complex.d _ _ ≫ biprod.inr)
    (by aesop_cat)

@[simps]
noncomputable def shortComplex : ShortComplex (ChainComplex C ℕ) where
  X₁ := P.complex
  X₂ := Qcomplex hS P R ε₂ hε₂
  X₃ := R.complex
  f := { f := fun n => biprod.inl }
  g := { f := fun n => biprod.snd }
  zero := by aesop_cat

noncomputable def shortComplexε : shortComplex hS P R ε₂ hε₂ ⟶ S.map (ChainComplex.single₀ C) where
  τ₁ := P.π
  τ₂ := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨biprod.fst ≫ P.π.f 0 ≫ S.f + biprod.snd ≫ ε₂, by aesop_cat⟩
  τ₃ := R.π
  comm₁₂ := by
    dsimp
    ext
    dsimp
    conv_rhs => erw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    simp
  comm₂₃ := by
    dsimp
    ext
    dsimp
    erw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    simp [hε₂]

end Horseshoe

end ProjectiveResolution

end CategoryTheory
