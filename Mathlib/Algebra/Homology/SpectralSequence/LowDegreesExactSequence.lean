/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Convergence
public import Mathlib.Algebra.Homology.ConnectShortExact
public import Mathlib.Tactic.FinCases

/-!
# The low degree exact sequence of a spectral sequence

-/

@[expose] public section

namespace HomologicalComplex

open CategoryTheory Limits

variable {C ι : Type*} [Category C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K : HomologicalComplex C c)

lemma shape_from (i j : ι) (hj : ∀ (k : ι), ¬ c.Rel k j) :
    K.d i j = 0 :=
  K.shape i j (hj i)

lemma shape_to (i j : ι) (hi : ∀ (k : ι), ¬ c.Rel i k) :
    K.d i j = 0 :=
  K.shape i j (hi j)

end HomologicalComplex

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type*} [Category C] [Abelian C]

namespace CohomologicalSpectralSequenceNat

open SpectralSequence

@[simps]
def stripes : ConvergenceStripes (ℕ × ℕ) (fun (n : ℕ) => Fin (n + 1)) where
  stripe pq := pq.1 + pq.2
  pred n := fun i => match i with
    | 0 => ⊥
    | ⟨j + 1, hj⟩ => WithBot.some ⟨j, by omega⟩
  pred_lt n i := by
    obtain ⟨_ | _, _⟩ := i
    · apply WithBot.bot_lt_coe
    · simp
  position n i := ⟨n - i.1, i.1⟩
  stripe_position := by
    rintro n ⟨i, hi⟩
    exact Nat.sub_add_cancel (by omega)
  discrete := by
    rintro n ⟨_ | i, hi⟩ ⟨j, hj⟩ h
    · simp
    · simp only [WithBot.coe_lt_coe, Fin.mk_lt_mk] at h
      simp only [Fin.mk_le_mk]
      omega
  finite_segment n i j := by
    rw [Set.finite_def]
    refine ⟨Fintype.ofInjective (fun x => (x : Fin (n + 1))) ?_⟩
    intro x y h
    ext1
    simpa using h

lemma stripes.position_eq_iff (n : ℕ) (i : Fin (n + 1))
      (pq : ℕ × ℕ) (hpq : pq.1 + pq.2 = n) (hpq' : pq.2 = i) :
    stripes.position n i = pq := by
  ext
  · simp [← hpq, ← hpq']
  · exact hpq'.symm

variable {r₀ : ℤ} (E : CohomologicalSpectralSequenceNat C r₀)
  {X : ℕ → C} (hE : E.StronglyConvergesTo stripes X)

namespace LowDegreesExactSequence

def d₂ (hr : r₀ ≤ 2 := by lia) := (E.page 2).d ⟨0, 1⟩ ⟨2, 0⟩

variable {E}

instance : (hE 0).CollapsesAt 0 where
  condition := by
    intro k hk
    fin_cases k
    simp at hk

noncomputable def iso₀ [E.HasEdgeMonoAtFrom (0, 0) 2] [E.HasEdgeEpiAtFrom (0, 0) 2] :
    X 0 ≅ (E.page 2 (E.le₀_of_hasEdgeMonoAtFrom ⟨0, 0⟩ 2)).X ⟨0, 0⟩ :=
  (hE 0).isoOfCollapsesAt 0 ⟨0, 0⟩ rfl ≪≫ E.pageInfinityIso ⟨0,0⟩ 2

instance : IsIso ((hE 1).filtrationι (WithBot.some 1)) :=
  (hE _).isIso_filtrationι_of_isZero _ (by
    rintro ⟨j, hj⟩ hj'
    exfalso
    simp only [WithBot.coe_lt_coe] at hj'
    change 1 < j at hj'
    omega)

instance : IsIso ((hE 1).π 0 (1, 0) rfl) := by
  apply (hE 1).isIso_π_of_isZero
  aesop

instance : IsIso ((hE 2).π 0 (2, 0) rfl) := by
  apply (hE 2).isIso_π_of_isZero
  aesop

instance : IsIso ((hE 1).filtrationι 1) := by
  apply (hE 1).isIso_filtrationι_of_isZero
  intro j hj
  fin_cases j
  · replace hj := WithBot.coe_lt_coe.1 hj
    simp at hj
  · aesop

instance : (hE 1).CollapsesAsSESAt 0 1 :=
  (hE 1).collapsesAsSESAt_of_succ 0 1 rfl ⟨1, 0⟩ rfl inferInstance inferInstance

noncomputable def ιE₂OneZero [E.HasEdgeMonoAtFrom (1, 0) 2] [E.HasEdgeEpiAtFrom (1, 0) 2] :
    (E.page 2 (E.le₀_of_hasEdgeMonoAtFrom ⟨1, 0⟩ 2)).X ⟨1, 0⟩ ⟶ X 1 :=
  (E.pageInfinityIso ⟨1, 0⟩ 2).inv ≫ (hE 1).pageInfinityι 0 ⟨1, 0⟩ rfl inferInstance

instance [E.HasEdgeMonoAtFrom (1, 0) 2] [E.HasEdgeEpiAtFrom (1, 0) 2] : Mono (ιE₂OneZero hE) := by
  dsimp [ιE₂OneZero]
  infer_instance

noncomputable def πE₃ZeroOne [E.HasEdgeMonoAtFrom (0, 1) 3] [E.HasEdgeEpiAtFrom (0, 1) 3] :
    X 1 ⟶ (E.page 3 (E.le₀_of_hasEdgeMonoAtFrom ⟨0, 1⟩ 3)).X ⟨0, 1⟩ :=
  (hE 1).pageInfinityπ 1 ⟨0, 1⟩ rfl inferInstance ≫ (E.pageInfinityIso ⟨0, 1⟩ 3).hom

instance [E.HasEdgeMonoAtFrom (0, 1) 3] [E.HasEdgeEpiAtFrom (0, 1) 3] :
    Epi (πE₃ZeroOne hE) := by
  dsimp [πE₃ZeroOne]
  apply epi_comp

lemma ιE₂OneZero_πE₃ZeroOne
    [E.HasEdgeMonoAtFrom (1, 0) 2] [E.HasEdgeEpiAtFrom (1, 0) 2]
    [E.HasEdgeMonoAtFrom (0, 1) 3] [E.HasEdgeEpiAtFrom (0, 1) 3] :
    ιE₂OneZero hE ≫ πE₃ZeroOne hE = 0 := by
  dsimp [ιE₂OneZero, πE₃ZeroOne]
  simp only [assoc, Preadditive.IsIso.comp_left_eq_zero]
  rw [(hE 1).pageInfinityι_π_eq_zero_assoc 0 1 (by apply @zero_lt_one ℕ), zero_comp]

lemma ιE₂OneZero_πE₃ZeroOne_exact
    [E.HasEdgeMonoAtFrom (1, 0) 2] [E.HasEdgeEpiAtFrom (1, 0) 2]
    [E.HasEdgeMonoAtFrom (0, 1) 3] [E.HasEdgeEpiAtFrom (0, 1) 3] :
    (ShortComplex.mk _ _ (ιE₂OneZero_πE₃ZeroOne hE)).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (((hE 1).shortExact_of_collapses 0 1 ⟨1, 0⟩ ⟨0, 1⟩ rfl rfl).exact)
  refine ShortComplex.isoMk (E.pageInfinityIso ⟨1, 0⟩ 2) (Iso.refl _)
    (E.pageInfinityIso ⟨0, 1⟩ 3) ?_ ?_
  · simp [ιE₂OneZero]
  · simp [πE₃ZeroOne]

noncomputable def toE₂ZeroOne [E.HasEdgeMonoAtFrom (0, 1) 2] :
    X 1 ⟶ (E.page 2 (E.le₀_of_hasEdgeMonoAtFrom ⟨0, 1⟩ 2)).X ⟨0, 1⟩ :=
  (hE 1).pageInfinityπ 1 ⟨0, 1⟩ rfl inferInstance ≫ E.edgeMono ⟨0, 1⟩ 2

@[reassoc (attr := simp)]
lemma πE₃ZeroOne_edgeMonoStep
    [E.HasEdgeMonoAtFrom (0, 1) 2]
    [E.HasEdgeMonoAtFrom (0, 1) 3] [E.HasEdgeEpiAtFrom (0, 1) 3] :
    πE₃ZeroOne hE ≫ E.edgeMonoStep (0, 1) 2 3 rfl = toE₂ZeroOne hE := by
  simp [πE₃ZeroOne, toE₂ZeroOne]

noncomputable def ιE₃TwoZero
    [E.HasEdgeMonoAtFrom (2, 0) 3] [E.HasEdgeEpiAtFrom (2, 0) 3] :
    (E.page 3 (E.le₀_of_hasEdgeMonoAtFrom ⟨2, 0⟩ 3)).X ⟨2, 0⟩ ⟶ X 2 :=
  (E.pageInfinityIso ⟨2, 0⟩ 3).inv ≫ (hE 2).pageInfinityι 0 ⟨2, 0⟩ rfl inferInstance

instance [E.HasEdgeMonoAtFrom (2, 0) 3] [E.HasEdgeEpiAtFrom (2, 0) 3] : Mono (ιE₃TwoZero hE) := by
  dsimp [ιE₃TwoZero]
  infer_instance

noncomputable def fromE₂TwoZero
    [E.HasEdgeEpiAtFrom (2, 0) 2] :
    (E.page 2 (E.le₀_of_hasEdgeEpiAtFrom ⟨2, 0⟩ 2)).X ⟨2, 0⟩ ⟶ X 2 :=
  E.edgeEpi ⟨2, 0⟩ 2 ≫ (hE 2).pageInfinityι 0 ⟨2, 0⟩ rfl inferInstance

@[reassoc (attr := simp)]
lemma edgeEpiStep_ιE₃TwoZero
    [E.HasEdgeMonoAtFrom (2, 0) 3] [E.HasEdgeEpiAtFrom (2, 0) 2] :
    E.edgeEpiStep ⟨2, 0⟩ 2 3 rfl ≫ ιE₃TwoZero hE = fromE₂TwoZero hE := by
  simp [fromE₂TwoZero, ιE₃TwoZero]

@[reassoc (attr := simp)]
lemma d₂_fromE₂TwoZero [E.HasEdgeMonoAtFrom (2, 0) 3] [E.HasEdgeEpiAtFrom (2, 0) 2] :
    (E.page 2 (E.le₀_of_hasEdgeEpiAtFrom ⟨2,0⟩ 2)).d ⟨0, 1⟩ ⟨2, 0⟩ ≫ fromE₂TwoZero hE = 0 := by
  rw [← edgeEpiStep_ιE₃TwoZero, E.d_comp_edgeEpiStep_assoc _ _ _ _, zero_comp]

variable (E)

@[simp]
noncomputable def d₂Sequence
    [E.HasEdgeMonoAt (0, 1) 2] [E.HasEdgeEpiAt (2, 0) 2] :
    ComposableArrows C 3 :=
  ComposableArrows.mk₃ (E.edgeMonoStep ⟨0, 1⟩ 2 3 rfl)
    ((E.page 2 (E.le₀_of_hasEdgeMonoAt ⟨0, 1⟩ 2)).d ⟨0, 1⟩ ⟨2, 0⟩)
    (E.edgeEpiStep ⟨2, 0⟩ 2 3 rfl)

instance [E.HasEdgeMonoAt (0, 1) 2] [E.HasEdgeEpiAt (2, 0) 2] :
    Mono ((d₂Sequence E).map' 0 1) := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance [E.HasEdgeMonoAt (0, 1) 2] [E.HasEdgeEpiAt (2, 0) 2] :
    Epi ((d₂Sequence E).map' 2 3) := by
  dsimp [ComposableArrows.Precomp.map]
  infer_instance

attribute [local simp] ComposableArrows.Precomp.map ComposableArrows.Precomp.obj in
set_option backward.isDefEq.respectTransparency false in
lemma d₂Sequence_exact [E.HasEdgeMonoAt (0, 1) 2] [E.HasEdgeEpiAt (2, 0) 2] :
    (d₂Sequence E).Exact := by
  have := E.le₀_of_hasEdgeMonoAt ⟨0, 1⟩ 2
  apply ComposableArrows.exact_of_δ₀
  · apply ComposableArrows.exact₂_mk _ (by simp)
    let S := ShortComplex.mk _ _ ((E.page 2).iCycles_d ⟨0, 1⟩ ⟨2, 0⟩)
    have hS : S.Exact := by
      apply ShortComplex.exact_of_f_is_kernel
      exact (E.page 2).cyclesIsKernel ⟨0, 1⟩ ⟨2, 0⟩
        (ComplexShape.next_eq' _ (by simp))
    refine ShortComplex.exact_of_iso ?_ hS
    exact ShortComplex.isoMk ((E.page 2).isoHomologyπ _ ⟨0, 1⟩ rfl (by
        apply (E.page 2).shape_from
        rintro ⟨p, q⟩ hpq
        simp only [ComplexShape.spectralSequenceNat_rel_iff, Nat.cast_zero, Nat.cast_one] at hpq
        omega) ≪≫ (E.iso 2 3) ⟨0, 1⟩) (Iso.refl _) (Iso.refl _) (by cat_disch) (by cat_disch)
  · apply ComposableArrows.exact₂_mk _
      (by simp)
    let S := ShortComplex.mk _ _ ((E.page 2).d_pOpcycles ⟨0, 1⟩ ⟨2, 0⟩)
    have hS : S.Exact := by
      apply ShortComplex.exact_of_g_is_cokernel
      exact (E.page 2).opcyclesIsCokernel ⟨0, 1⟩ ⟨2, 0⟩
        (ComplexShape.prev_eq' _ (by simp))
    refine ShortComplex.exact_of_iso (Iso.symm ?_) hS
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (((E.iso 2 3) ⟨2, 0⟩).symm ≪≫ (E.page 2).isoHomologyι ⟨2, 0⟩ _ rfl (by
        apply (E.page 2).shape_to
        rintro ⟨p, q⟩ hpq
        simp only [ComplexShape.spectralSequenceNat_rel_iff, Nat.cast_ofNat,
          Nat.cast_zero, zero_add] at hpq
        omega)) (by aesop_cat) (by cat_disch)

end LowDegreesExactSequence

variable {E}

open LowDegreesExactSequence in
@[simp]
noncomputable def lowDegreesComposableArrows
    [E.HasEdgeMonoAtFrom (1, 0) 2] [E.HasEdgeEpiAtFrom (1, 0) 2]
    [E.HasEdgeMonoAtFrom (0, 1) 2]
    [E.HasEdgeMonoAtFrom (2, 0) 3] [E.HasEdgeEpiAtFrom (2, 0) 2] :
    ComposableArrows C 4 :=
  ComposableArrows.mk₄ (ιE₂OneZero hE) (toE₂ZeroOne hE)
    ((E.page 2 (E.le₀_of_hasEdgeMonoAtFrom ⟨0, 1⟩ 2)).d ⟨0, 1⟩ ⟨2, 0⟩) (fromE₂TwoZero hE)

instance [E.HasEdgeMonoAtFrom (1, 0) 2] [E.HasEdgeEpiAtFrom (1, 0) 2]
    [E.HasEdgeMonoAtFrom (0, 1) 2]
    [E.HasEdgeMonoAtFrom (2, 0) 3] [E.HasEdgeEpiAtFrom (2, 0) 2] :
    Mono ((lowDegreesComposableArrows hE).map' 0 1) := by
  dsimp
  infer_instance

attribute [local simp] ComposableArrows.Precomp.map ComposableArrows.Precomp.obj

set_option backward.isDefEq.respectTransparency false in
open LowDegreesExactSequence in
/-- The exact sequence `0 → E₂¹⁰ → X¹ → E₂⁰¹ → E₂²⁰ → X²` -/
lemma lowDegreesComposableArrows_exact
    [E.HasEdgeMonoAtFrom (1, 0) 2] [E.HasEdgeEpiAtFrom (1, 0) 2]
    [E.HasEdgeMonoAtFrom (0, 1) 2] [E.HasEdgeEpiAtFrom (0, 1) 3]
    [E.HasEdgeMonoAtFrom (2, 0) 3] [E.HasEdgeEpiAtFrom (2, 0) 2] :
    (lowDegreesComposableArrows hE).Exact := by
  apply ComposableArrows.exact_of_δlast
  · refine ComposableArrows.exact_of_iso ?_
      (ShortComplex.connect_exact _ _ (ιE₂OneZero_πE₃ZeroOne_exact hE)
        ((d₂Sequence_exact E).exact 0) (Iso.refl _) (toE₂ZeroOne hE) (by simp)
        (by infer_instance) (by infer_instance))
    exact ComposableArrows.isoMk₃ (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp)
  · refine ComposableArrows.exact₂_mk _ (by simp) ?_
    let φ : ShortComplex.mk _ _ ((d₂Sequence_exact E).toIsComplex.zero 1) ⟶
        ShortComplex.mk _ _ (d₂_fromE₂TwoZero hE) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := ιE₃TwoZero hE }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 ((d₂Sequence_exact E).exact 1)

end CohomologicalSpectralSequenceNat

end CategoryTheory
