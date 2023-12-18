import Mathlib.Algebra.Homology.SpectralSequenceNew.Convergence
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Tactic.FinCases

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

namespace ComplexShape

def spectralSequenceNat (u : ℤ × ℤ) : ComplexShape (ℕ × ℕ) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2
  next_eq {a b b'} := by
    rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> linarith
  prev_eq {a a' b} := by
    rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> linarith

@[simp]
lemma spectralSequenceNat_rel_iff (u : ℤ × ℤ) (a b : ℕ × ℕ) :
    (spectralSequenceNat u).Rel a b ↔ a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2 := by rfl

end ComplexShape

namespace CategoryTheory

open Category ZeroObject

variable (C : Type*) [Category C] [Abelian C]

abbrev CohomologicalSpectralSequenceNat :=
  SpectralSequence C (fun r => ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩)

abbrev E₂CohomologicalSpectralSequenceNat :=
  CohomologicalSpectralSequenceNat C 2

variable {C}

namespace CohomologicalSpectralSequenceNat

open SpectralSequence

@[simps]
def stripes : ConvergenceStripes (ℕ × ℕ) (fun (n : ℕ) => Fin (n + 1)) where
  stripe pq := pq.1 + pq.2
  pred n := fun i => match i with
    | 0 => ⊥
    | ⟨j + 1, hj⟩ => WithBot.some ⟨j, by linarith⟩
  pred_lt n i := by
    obtain ⟨_ | _, _⟩ := i
    · apply WithBot.bot_lt_coe
    · simp
  position n i := ⟨n - i.1, i.1⟩
  stripe_position := by
    rintro n ⟨i, hi⟩
    exact Nat.sub_add_cancel (by linarith)
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

lemma stripes.position_eq_iff (n : ℕ) (i : Fin (n + 1))
      (pq : ℕ × ℕ) (hpq : pq.1 + pq.2 = n) (hpq' : pq.2 = i) :
    stripes.position n i = pq := by
  ext
  · simp [← hpq, ← hpq']
  · exact hpq'.symm

variable {r₀ : ℤ} (E : CohomologicalSpectralSequenceNat C r₀) [E.HasPage 2]
  {X : ℕ → C} (hE : E.StronglyConvergesTo stripes X)

instance : E.HasPage 3 := E.hasPage_of_LE 2 3 (by linarith)

lemma hasEdgeMonoAt (pq : ℕ × ℕ) (r : ℤ) [E.HasPage r] (hr : pq.1 + 1 ≤ r) :
    E.HasEdgeMonoAt pq r where
  zero := by
    obtain ⟨p, q⟩ := pq
    rintro ⟨p', q'⟩
    apply (E.page r).shape
    simp only [ComplexShape.spectralSequenceNat_rel_iff, not_and]
    intro _ _
    linarith

lemma hasEdgeEpiAt (pq : ℕ × ℕ) (r : ℤ) [E.HasPage r] (hr : pq.2 + 2 ≤ r) :
    E.HasEdgeEpiAt pq r where
  zero := by
    obtain ⟨p, q⟩ := pq
    rintro ⟨p', q'⟩
    apply (E.page r).shape
    simp only [ComplexShape.spectralSequenceNat_rel_iff, not_and]
    intro _ _
    linarith

namespace LowDegreesExactSequence

instance (pq : ℕ × ℕ) : E.HasPageInfinityAt pq where
  nonempty_hasEdgeEpiSet := ⟨pq.2 + 2, fun r hr =>
    have := E.hasPage_of_LE 2 r (by linarith)
    ⟨this, E.hasEdgeEpiAt _ _ (by linarith)⟩⟩
  nonempty_hasEdgeMonoSet := ⟨pq.1 + 2, fun r hr =>
    have := E.hasPage_of_LE 2 r (by linarith)
    ⟨this, E.hasEdgeMonoAt _ _ (by linarith)⟩⟩

def d₂ := (E.page 2).d ⟨0, 1⟩ ⟨2, 0⟩

instance (n : ℕ) : E.HasEdgeMonoAtFrom ⟨0, n⟩ 2 :=
  HasEdgeMonoAtFrom.mk' _ _ _ (fun k => by
    apply E.hasEdgeMonoAt
    dsimp
    linarith)

instance (n : ℕ) : E.HasEdgeEpiAtFrom ⟨n, 0⟩ 2 :=
  HasEdgeEpiAtFrom.mk' _ _ _ (fun k => by
    apply E.hasEdgeEpiAt
    dsimp
    linarith)

instance (n : ℕ) : E.HasEdgeEpiAtFrom ⟨n, 1⟩ 3 :=
  HasEdgeEpiAtFrom.mk' _ _ _ (fun k => by
    apply E.hasEdgeEpiAt
    dsimp
    linarith)

instance (n : ℕ) : E.HasEdgeMonoAtFrom ⟨1, n⟩ 2 :=
  HasEdgeMonoAtFrom.mk' _ _ _ (fun k => by
    apply E.hasEdgeMonoAt
    dsimp
    linarith)

instance (n : ℕ) : E.HasEdgeMonoAtFrom ⟨2, n⟩ 3 :=
  HasEdgeMonoAtFrom.mk' _ _ _ (fun k => by
    apply E.hasEdgeMonoAt
    dsimp
    linarith)

variable {E}

instance : (hE 0).CollapsesAt 0 where
  condition := by
    intro k hk
    fin_cases k
    simp at hk

noncomputable def iso₀ : X 0 ≅ (E.page 2).X ⟨0, 0⟩ :=
  (hE 0).isoOfCollapsesAt 0 ⟨0, 0⟩ rfl ≪≫ E.pageInfinityIso ⟨0,0⟩ 2

instance : IsIso ((hE 1).filtrationι (WithBot.some 1)) :=
  (hE _).isIso_filtrationι_of_isZero _ (by
    rintro ⟨j, hj⟩ hj'
    exfalso
    simp only [WithBot.coe_lt_coe] at hj'
    change 1 < j at hj'
    linarith)

instance : IsIso ((hE 1).π 0 (1, 0) rfl) := by
  apply (hE 1).isIso_π_of_isZero
  aesop

instance : IsIso ((hE 2).π 0 (2, 0) rfl) := by
  apply (hE 2).isIso_π_of_isZero
  aesop

instance : IsIso ((hE 1).filtrationι 1) := by
  apply (hE 1).isIso_filtrationι_of_isZero
  intro j hj
  fin_cases j <;> aesop

instance : (hE 1).CollapsesAsSESAt 0 1 :=
  (hE 1).collapsesAsSESAt_of_succ 0 1 rfl ⟨1, 0⟩ rfl inferInstance inferInstance

noncomputable example : X 1 ⟶ E.pageInfinity ⟨0, 1⟩ :=
  (hE 1).pageInfinityπ 1 ⟨0, 1⟩ rfl inferInstance

noncomputable def ιE₂OneZero : (E.page 2).X ⟨1, 0⟩ ⟶ X 1 :=
  (E.pageInfinityIso ⟨1, 0⟩ 2).inv ≫ (hE 1).pageInfinityι 0 ⟨1, 0⟩ rfl inferInstance

instance : Mono (ιE₂OneZero hE) := by
  dsimp [ιE₂OneZero]
  infer_instance

noncomputable def πE₃ZeroOne : X 1 ⟶ (E.page 3).X ⟨0, 1⟩ :=
  (hE 1).pageInfinityπ 1 ⟨0, 1⟩ rfl inferInstance ≫ (E.pageInfinityIso ⟨0, 1⟩ 3).hom

instance : Epi (πE₃ZeroOne hE) := by
  dsimp [πE₃ZeroOne]
  apply epi_comp

noncomputable def toE₂OneZero :
    X 1 ⟶ (E.page 2).X ⟨0, 1⟩ :=
  (hE 1).pageInfinityπ 1 ⟨0, 1⟩ rfl inferInstance ≫ E.edgeMono ⟨0, 1⟩ 2

noncomputable def ιE₃TwoZero : (E.page 3).X ⟨2, 0⟩ ⟶ X 2 :=
  (E.pageInfinityIso ⟨2, 0⟩ 3).inv ≫ (hE 2).pageInfinityι 0 ⟨2, 0⟩ rfl inferInstance

instance : Mono (ιE₃TwoZero hE) := by
  dsimp [ιE₃TwoZero]
  infer_instance

noncomputable def fromE₂TwoZero : (E.page 2).X ⟨2, 0⟩ ⟶ X 2 :=
  E.edgeEpi ⟨2, 0⟩ 2 ≫ (hE 2).pageInfinityι 0 ⟨2, 0⟩ rfl inferInstance

@[reassoc (attr := simp)]
lemma edgeEpiStep_ιE₃TwoZero :
    E.edgeEpiStep ⟨2, 0⟩ 2 3 rfl ≫ ιE₃TwoZero hE = fromE₂TwoZero hE := by
  simp [fromE₂TwoZero, ιE₃TwoZero]

variable (E)

@[simp]
noncomputable def d₂Sequence : ComposableArrows C 3 :=
  ComposableArrows.mk₃ (E.edgeMonoStep ⟨0, 1⟩ 2 3 rfl) ((E.page 2).d ⟨0, 1⟩ ⟨2, 0⟩)
    (E.edgeEpiStep ⟨2, 0⟩ 2 3 rfl)

instance : Mono ((d₂Sequence E).map' 0 1) := by
  dsimp
  infer_instance

instance : Epi ((d₂Sequence E).map' 2 3) := by
  dsimp
  infer_instance

lemma d₂Sequence_exact : (d₂Sequence E).Exact := by
  apply ComposableArrows.exact_of_δ₀
  · apply ComposableArrows.exact₂_mk _ (by simp)
    let S := ShortComplex.mk _ _ ((E.page 2).iCycles_d ⟨0, 1⟩ ⟨2, 0⟩)
    have hS : S.Exact := by
      apply ShortComplex.exact_of_f_is_kernel
      exact (E.page 2).cyclesIsKernel ⟨0, 1⟩ ⟨2, 0⟩
        (ComplexShape.next_eq' _ (by simp; linarith))
    refine ShortComplex.exact_of_iso ?_ hS
    exact ShortComplex.isoMk ((E.page 2).isoHomologyπ _ ⟨0, 1⟩ rfl (by
        apply (E.page 2).shape_from
        rintro ⟨p, q⟩ hpq
        simp only [ComplexShape.spectralSequenceNat_rel_iff, Nat.cast_zero, Nat.cast_one] at hpq
        linarith) ≪≫ (E.iso 2 3 rfl) ⟨0, 1⟩) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  · apply ComposableArrows.exact₂_mk _ (by simp)
    let S := ShortComplex.mk _ _ ((E.page 2).d_pOpcycles ⟨0, 1⟩ ⟨2, 0⟩)
    have hS : S.Exact := by
      apply ShortComplex.exact_of_g_is_cokernel
      exact (E.page 2).opcyclesIsCokernel ⟨0, 1⟩ ⟨2, 0⟩
        (ComplexShape.prev_eq' _ (by simp; linarith))
    refine ShortComplex.exact_of_iso (Iso.symm ?_) hS
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (((E.iso 2 3 rfl) ⟨2, 0⟩).symm ≪≫ (E.page 2).isoHomologyι ⟨2, 0⟩ _ rfl (by
        apply (E.page 2).shape_to
        rintro ⟨p, q⟩ hpq
        simp only [ComplexShape.spectralSequenceNat_rel_iff, Nat.cast_ofNat,
          Nat.cast_zero, zero_add] at hpq
        linarith)) (by simp) (by simp)

end LowDegreesExactSequence

variable {E}

open LowDegreesExactSequence in
@[simp]
noncomputable def lowDegreesComposableArrows : ComposableArrows C 4 :=
  ComposableArrows.mk₄ (ιE₂OneZero hE) (toE₂OneZero hE)
    ((E.page 2).d ⟨0, 1⟩ ⟨2, 0⟩) (fromE₂TwoZero hE)

instance : Mono ((lowDegreesComposableArrows hE).map' 0 1) := by
  dsimp
  infer_instance

end CohomologicalSpectralSequenceNat

end CategoryTheory
