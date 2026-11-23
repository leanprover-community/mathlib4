/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.EdgeSteps
public import Mathlib.Order.Int.LeastGreatest

/-!
# ...

-/

public section

namespace CategoryTheory

open Category ZeroObject

variable {C : Type*} [Category C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

/-- Given `pq`, this is the condition that the differentials to and from the
objects `E_{r'}^{pq}` are all zero for a big enough `r'`. -/
class HasPageInfinityAt (E : SpectralSequence C c r₀) (pq : ι) : Prop where
  exists_hasEdgeMonoAtFrom (E pq) : ∃ (r : ℤ), E.HasEdgeMonoAtFrom pq r
  exists_hasEdgeEpiAtFrom (E pq) : ∃ (r : ℤ), E.HasEdgeEpiAtFrom pq r

variable (E : SpectralSequence C c r₀) (pq : ι)

variable [E.HasPageInfinityAt pq]

open HasPageInfinityAt in
lemma exists_hasEdgeMonoAtFrom_and_hasEdgeEpiAtFrom :
    ∃ (n : ℤ), E.HasEdgeMonoAtFrom pq n ∧ E.HasEdgeEpiAtFrom pq n := by
  obtain ⟨r₁, _⟩ := exists_hasEdgeMonoAtFrom E pq
  obtain ⟨r₂, _⟩ := exists_hasEdgeEpiAtFrom E pq
  exact ⟨max r₁ r₂, E.hasEdgeMonoAtFrom_of_le pq r₁ _,
    E.hasEdgeEpiAtFrom_of_le pq r₂ _⟩

open Classical in
/-- Given a spectral sequence `E` and `pq` such that `E.HasPageInfinityAt pq`
holds, this is the smallest number `r` of the page such that both
`E.HasEdgeMonoAtFrom pq` and `E.HasEdgeEpiAtFrom pq` hold. -/
noncomputable def rMin : ℤ :=
  (Int.leastOfBdd r₀ (fun r ⟨_, _⟩ ↦ E.le₀_of_hasEdgeMonoAt pq r)
    (E.exists_hasEdgeMonoAtFrom_and_hasEdgeEpiAtFrom pq)).val

open Classical in
instance : E.HasEdgeMonoAtFrom pq (E.rMin pq) :=
  (Int.leastOfBdd r₀ (fun r ⟨_, _⟩ ↦ E.le₀_of_hasEdgeMonoAt pq r)
    (E.exists_hasEdgeMonoAtFrom_and_hasEdgeEpiAtFrom pq)).property.left.left

open Classical in
instance : E.HasEdgeEpiAtFrom pq (E.rMin pq) :=
  (Int.leastOfBdd r₀ (fun r ⟨_, _⟩ ↦ E.le₀_of_hasEdgeMonoAt pq r)
    (E.exists_hasEdgeMonoAtFrom_and_hasEdgeEpiAtFrom pq)).property.left.right

open Classical in
lemma rMin_le_iff (r : ℤ) :
    E.rMin pq ≤ r ↔ E.HasEdgeMonoAtFrom pq r ∧ E.HasEdgeEpiAtFrom pq r :=
  ⟨fun h ↦ ⟨E.hasEdgeMonoAtFrom_of_le pq (E.rMin pq) r,
    E.hasEdgeEpiAtFrom_of_le pq (E.rMin pq) r⟩,
  fun h ↦ (Int.leastOfBdd r₀ (fun r ⟨_, _⟩ ↦ E.le₀_of_hasEdgeMonoAt pq r)
    (E.exists_hasEdgeMonoAtFrom_and_hasEdgeEpiAtFrom pq)).property.right _ h⟩

lemma le₀_rMin : r₀ ≤ E.rMin pq :=
  E.le₀_of_hasEdgeMonoAt pq _

open Classical in
/-- If `E` is a spectral sequence and `pq` is such that
`E.HasPageInfinityAt pq` holds, this object identifies to
`E_r^{pq}` for any big enough `r` (precisely when `E.rMin pq ≤ r`).
Otherwise, we set it to be the zero object. -/
noncomputable def pageInfinity (pq : ι) : C :=
  if _ : E.HasPageInfinityAt pq then
    (E.page (E.rMin pq) (E.le₀_rMin pq)).X pq else 0

/-- Auxiliary definition for `edgeMono` and `edgeEpi`. -/
private noncomputable def pageInfinityIso' (pq : ι) [E.HasPageInfinityAt pq] :
    (E.page (E.rMin pq) (E.le₀_rMin pq)).X pq ≅ E.pageInfinity pq :=
  eqToIso (Eq.symm (dite_eq_left (by assumption)))

/-- When both `E.HasEdgeMonoAtFrom pq r` and `E.HasPageInfinityAt pq` hold,
this is the edge monomorphism `E.pageInfinity pq ⟶ (E.page r).X pq`. -/
noncomputable def edgeMono (r : ℤ) [E.HasEdgeMonoAtFrom pq r] :
    haveI := E.le₀_of_hasEdgeMonoAt pq r
    E.pageInfinity pq ⟶ (E.page r).X pq :=
  (E.pageInfinityIso' pq).inv ≫
    (E.edgeIsoSteps pq (E.rMin pq) (max (E.rMin pq) r)).hom ≫
      E.edgeMonoSteps pq r (max (E.rMin pq) r)

instance (r : ℤ) [E.HasEdgeMonoAtFrom pq r] :
    Mono (E.edgeMono pq r) := by
  dsimp [edgeMono]
  infer_instance

/-- When both `E.HasEdgeEpiAtFrom pq r` and `E.HasPageInfinityAt pq` hold,
this is the edge epimorphism `(E.page r).X pq ⟶ E.pageInfinity pq`. -/
noncomputable def edgeEpi (r : ℤ) [E.HasEdgeEpiAtFrom pq r] :
    haveI := E.le₀_of_hasEdgeEpiAt pq r
    (E.page r).X pq ⟶ E.pageInfinity pq :=
  E.edgeEpiSteps pq r _ ≫
    (E.edgeIsoSteps pq (E.rMin pq) (max (E.rMin pq) r)).inv ≫
      (E.pageInfinityIso' pq).hom

instance (r : ℤ) [E.HasEdgeEpiAtFrom pq r] :
    Epi (E.edgeEpi pq r) := by
  dsimp [edgeEpi]
  infer_instance

@[reassoc (attr := simp)]
lemma edgeMono_edgeMonoSteps (r r' : ℤ) [E.HasEdgeMonoAtFrom pq r] (hr' : r ≤ r') :
    haveI := E.hasEdgeMonoAtFrom_of_le pq r r'
    E.edgeMono pq r' ≫ E.edgeMonoSteps pq r r' hr' = E.edgeMono pq r := by
  simp [edgeMono, E.congr_edgeEpiSteps_comp_edgeMonoSteps pq
    (E.rMin pq) r (max (E.rMin pq) r) (max (E.rMin pq) r')]

@[reassoc (attr := simp)]
lemma edgeMonoSteps_edgeEpi (r r' : ℤ) [E.HasEdgeEpiAtFrom pq r] (hr' : r ≤ r') :
    haveI := E.hasEdgeEpiAtFrom_of_le pq r r'
    E.edgeEpiSteps pq r r' hr' ≫ E.edgeEpi pq r' = E.edgeEpi pq r := by
  simp [edgeEpi, E.congr_edgeEpiSteps_comp_edgeMonoSteps pq r (E.rMin pq)
    (max (E.rMin pq) r') (max (E.rMin pq) r)]

@[reassoc (attr := simp)]
lemma edgeEpi_edgeMono
    (r : ℤ) [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    E.edgeEpi pq r ≫ E.edgeMono pq r = 𝟙 _ := by
  sorry

@[reassoc (attr := simp)]
lemma edgeMono_edgeEpi
    (r : ℤ) [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    E.edgeMono pq r ≫ E.edgeEpi pq r = 𝟙 _ := by
  sorry

instance (r : ℤ) [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    IsIso (E.edgeMono pq r) := ⟨E.edgeEpi pq r, by simp⟩

instance (r : ℤ) [E.HasEdgeMonoAtFrom pq r] [E.HasEdgeEpiAtFrom pq r] :
    IsIso (E.edgeEpi pq r) := ⟨E.edgeMono pq r, by simp⟩

end SpectralSequence

end CategoryTheory
