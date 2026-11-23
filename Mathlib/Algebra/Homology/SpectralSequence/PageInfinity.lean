/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.EdgeSteps

/-!
# ...

-/

public section

-- what is the best way to do this?
lemma Int.exists_min (S : Set ℤ) (hS : S.Nonempty) (m₀ : ℤ)
    (hm₀ : ∀ (x : ℤ), x ∈ S → m₀ ≤ x) :
    ∃ (m : ℤ) (_ : m ∈ S), S ⊆ Set.Ici m := by
  let T : Set ℕ := .ofPred fun i ↦ m₀ + i ∈ S
  obtain ⟨x, hx⟩ := hS
  obtain ⟨t₀, rfl⟩ := Int.le.dest (hm₀ x hx)
  have hT : T.Nonempty := ⟨t₀, hx⟩
  let μ := (Nat.lt_wfRel.wf).min T hT
  refine ⟨m₀ + μ, (Nat.lt_wfRel.wf).min_mem T hT, fun y hy ↦ ?_⟩
  have hy' : 0 ≤ y - m₀ := by have := hm₀ y hy; lia
  obtain ⟨t, ht⟩ := Int.eq_ofNat_of_zero_le hy'
  obtain rfl : y = m₀ + t := by lia
  simpa using WellFoundedLT.min_le (s := T) hy

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

namespace HasPageInfinityAt

/-- Given a spectral sequence `E` and `pq`, this is the subset of `ℤ` consisting
of the numbers of the pages `r` such that both `E.HasEdgeMonoAtFrom pq`
and `E.HasEdgeEpiAtFrom pq` hold. -/
@[implicit_reducible]
def set : Set ℤ :=
  .ofPred (E.HasEdgeMonoAtFrom pq) ∩ .ofPred (E.HasEdgeEpiAtFrom pq)

lemma nonempty_set [E.HasPageInfinityAt pq] : (set E pq).Nonempty := by
  obtain ⟨r₁, _⟩ := exists_hasEdgeMonoAtFrom E pq
  obtain ⟨r₂, _⟩ := exists_hasEdgeEpiAtFrom E pq
  exact ⟨max r₁ r₂, E.hasEdgeMonoAtFrom_of_le pq r₁ _,
    E.hasEdgeEpiAtFrom_of_le pq r₂ _⟩

lemma le_of_mem_set (r : ℤ) (hr : r ∈ set E pq) : r₀ ≤ r :=
  have : E.HasEdgeMonoAtFrom pq r := hr.1
  E.le₀_of_hasEdgeMonoAt pq r

end HasPageInfinityAt

variable [E.HasPageInfinityAt pq]

/-- Given a spectral sequence `E` and `pq` such that `E.HasPageInfinityAt pq`
holds, this is the smallest number `r` of the page such that both
`E.HasEdgeMonoAtFrom pq` and `E.HasEdgeEpiAtFrom pq` hold. -/
noncomputable def rMin : ℤ :=
  (Int.exists_min _ (HasPageInfinityAt.nonempty_set E pq) r₀
    (HasPageInfinityAt.le_of_mem_set E pq)).choose

instance : E.HasEdgeMonoAtFrom pq (E.rMin pq) :=
  (Int.exists_min _ (HasPageInfinityAt.nonempty_set E pq) r₀
    (HasPageInfinityAt.le_of_mem_set E pq)).choose_spec.1.1

instance : E.HasEdgeEpiAtFrom pq (E.rMin pq) :=
  (Int.exists_min _ (HasPageInfinityAt.nonempty_set E pq) r₀
    (HasPageInfinityAt.le_of_mem_set E pq)).choose_spec.1.2

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

noncomputable def pageInfinityIso' (pq : ι) [E.HasPageInfinityAt pq] :
    (E.page (E.rMin pq) (E.le₀_rMin pq)).X pq ≅ E.pageInfinity pq :=
  eqToIso (Eq.symm (dite_eq_left (by assumption)))

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

end SpectralSequence

end CategoryTheory
