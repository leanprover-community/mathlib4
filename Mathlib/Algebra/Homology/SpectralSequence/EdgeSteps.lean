/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.EdgeStep

/-!
# ...

-/

public section

namespace CategoryTheory

open Category ZeroObject

variable {C : Type*} [Category C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

/-- Given `pq`, this is the condition that the differentials to the objects `E_{r'}^{pq}`
on all pages `r' ≥ r` of a spectral sequence are zero. -/
class HasEdgeMonoAtFrom (E : SpectralSequence C c r₀) (pq : ι) (r : ℤ) : Prop where
  hasEdgeMonoAt (E pq r) (r' : ℤ) (hr' : r ≤ r' := by lia) : E.HasEdgeMonoAt pq r'

export HasEdgeMonoAtFrom (hasEdgeMonoAt)

variable (E : SpectralSequence C c r₀) (pq : ι) (r : ℤ)
  [E.HasEdgeMonoAtFrom pq r]

lemma hasEdgeMonoAtFrom_of_le (r' : ℤ) (hr' : r ≤ r' := by lia) :
    E.HasEdgeMonoAtFrom pq r' where
  hasEdgeMonoAt r'' hr' := E.hasEdgeMonoAt pq r _

instance : E.HasEdgeMonoAt pq r :=
  E.hasEdgeMonoAt pq r r

instance (k : ℕ) : E.HasEdgeMonoAtFrom pq (r + k) :=
  E.hasEdgeMonoAtFrom_of_le pq r _

/-- Auxiliary definition for `edgeMonoSteps`. -/
private noncomputable def edgeMonoSteps' (k : ℕ) :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    (E.page (r + k)).X pq ⟶ (E.page r).X pq := by
  haveI := E.le₀_of_hasEdgeMonoAt pq r
  induction k with
  | zero => exact (E.pageXIsoOfEq pq _ _ (by simp)).hom
  | succ k hk => exact E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ hk

@[simp]
private lemma edgeMonoSteps'_zero :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    E.edgeMonoSteps' pq r 0 = (E.pageXIsoOfEq pq _ _ (by simp)).hom := rfl

@[simp]
private lemma edgeMonoSteps'_succ (k : ℕ) :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    E.edgeMonoSteps' pq r (k + 1) =
      E.edgeMonoStep pq (r + k) (r + ((k + 1) : ℕ)) ≫ E.edgeMonoSteps' pq r k := rfl

private instance (k : ℕ) : Mono (E.edgeMonoSteps' pq r k) := by
  induction k with
  | zero => simp only [edgeMonoSteps'_zero]; infer_instance
  | succ => simp only [edgeMonoSteps'_succ]; infer_instance

/-- The monomorphism `E_{r'}^pq ⟶ E_r^{pq}` when `r ≤ r'` and `pq` is such
that `E.HasEdgeMonoAtFrom pq r` holds, i.e. all the differentials to the objects
`E_{r''}^pq` vanish for `r'' ≥ r`. -/
noncomputable def edgeMonoSteps (r' : ℤ) (h : r ≤ r' := by lia) :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    (E.page r').X pq ⟶ (E.page r).X pq :=
  haveI := E.le₀_of_hasEdgeMonoAt pq r
  (E.pageXIsoOfEq pq _ _ (by lia) (by lia)).inv ≫
    E.edgeMonoSteps' pq r (Int.toNat (r' - r))

private lemma edgeMonoSteps_eq (r' : ℤ) (k : ℕ) (h : r + k = r' := by lia) :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    E.edgeMonoSteps pq r r' (by lia) =
      (E.pageXIsoOfEq pq _ _ h).inv ≫ E.edgeMonoSteps' pq r k := by
  obtain rfl : k = Int.toNat (r' - r) := by lia
  rfl

instance (r' : ℤ) (h : r ≤ r') :
    Mono (E.edgeMonoSteps pq r r' h) := by
  rw [E.edgeMonoSteps_eq pq r r' (Int.toNat (r' - r))]
  infer_instance

instance (r' : ℤ) (k : ℕ) (h : r + k = r') :
    Mono (E.edgeMonoSteps pq r r') := by
  infer_instance

@[simp]
lemma edgeMonoSteps_eq_id :
    E.edgeMonoSteps pq r r (by rfl) = 𝟙 _ := by
  simp [E.edgeMonoSteps_eq pq r r 0]

@[reassoc (attr := simp)]
lemma edgeMonoStep_comp_edgeMonoSteps
    (r' r'' : ℤ) (h₁ : r ≤ r' := by lia) (h₂ : r' + 1 = r'' := by lia)
    [E.HasEdgeMonoAt pq r'] :
    E.edgeMonoStep pq r' r'' h₂ ≫ E.edgeMonoSteps pq r r' h₁ =
    E.edgeMonoSteps pq r r'' (by lia) := by
  obtain ⟨k, rfl⟩ := Int.le.dest h₁
  obtain rfl : r'' = r + ((k + 1) : ℕ) := by lia
  rw [E.edgeMonoSteps_eq pq r (r + (k + 1 : ℕ)) (k + 1), E.edgeMonoSteps_eq pq r (r + k) k]
  simp

lemma edgeMonoSteps_eq_edgeMonoStep (r' : ℤ) (h : r + 1 = r' := by lia) :
    E.edgeMonoSteps pq r r' (by lia) =
    E.edgeMonoStep pq r r' h := by
  simp [← E.edgeMonoStep_comp_edgeMonoSteps pq r r r']

@[reassoc (attr := simp)]
lemma edgeMonoSteps_comp (r' r'' : ℤ) [E.HasEdgeMonoAtFrom pq r']
    (hr' : r ≤ r' := by lia) (hr'' : r' ≤ r'' := by lia) :
    E.edgeMonoSteps pq r' r'' hr'' ≫ E.edgeMonoSteps pq r r' hr' =
      E.edgeMonoSteps pq r r'' (hr'.trans hr'') := by
  obtain ⟨k, hk⟩ := Int.le.dest hr''
  induction k generalizing r'' with
  | zero =>
    obtain rfl : r' = r'' := by simpa using hk
    simp
  | succ k hk' =>
    rw [← E.edgeMonoStep_comp_edgeMonoSteps_assoc pq r' (r' + k) r'',
      hk' _ (by lia) (by lia)]
    simp

@[reassoc (attr := simp)]
lemma edgeMonoSteps_comp_edgeMonoStep
    (r' r'' : ℤ) (h₁ : r + 1 = r' := by lia) (h₂ : r' ≤ r'' := by lia)
    [E.HasEdgeMonoAt pq r] :
    haveI := E.hasEdgeMonoAtFrom_of_le pq r r'
    E.edgeMonoSteps pq r' r'' h₂ ≫ E.edgeMonoStep pq r r' h₁ =
    E.edgeMonoSteps pq r r'' (by lia) := by
  rw [← E.edgeMonoSteps_eq_edgeMonoStep ..]
  simp

end SpectralSequence

end CategoryTheory
