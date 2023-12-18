import Mathlib.Algebra.Homology.SpectralSequenceNew.Convergence
import Mathlib.Tactic.FinCases

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
  nonempty_hasEdgeMonoSet := ⟨pq.1 + 2, fun r hr => by
    have := E.hasPage_of_LE 2 r (by linarith)
    exact ⟨this, E.hasEdgeMonoAt _ _ (by linarith)⟩⟩

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

noncomputable example : X 1 ⟶ E.pageInfinity ⟨0, 1⟩ :=
  (hE 1).pageInfinityπ 1 ⟨0, 1⟩ rfl inferInstance

end LowDegreesExactSequence

end CohomologicalSpectralSequenceNat

end CategoryTheory
