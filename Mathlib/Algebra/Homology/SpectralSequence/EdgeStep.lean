/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Edge maps

If there is an object `E_r^{pq}` of a page of a spectral sequence
such that the differential `E_r^{pq'} ⟶ E_r^{pq}` is zero,
then `E_{r+1}^{pq}` identifies to a subobject of `E_r^{pq}`
which we formalize through the definition of a monomophism
`E_{r+1}^{pq} ⟶ E_r^{pq}` (see `SpectralSequence.edgeMonoStep`).
Similarly, if the differential `E_r^{pq} ⟶ E_r^{pq'}` is zero,
then `E_{r+1}^{pq}` identifies to a quotient of `E_r^{pq}`,
which we formalize through the definition of an epimorphism
`E_r^{pq} ⟶ E_{r+1}^{pq}` (see `SpectralSequence.edgeEpiStep`).

These phenomena tends to occur particularly at the edge of
the first quadrant for first quadrant spectral sequences,
hence the chosen names. In this file, we are only interested
in the case of a single object on a specific page `r`.

-/

public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

variable (E E' : SpectralSequence C c r₀)

/-- This is the condition that the differential to an object `E_r^{pq}`
on a page of a spectral sequence is zero (both `r` and `pq` are fixed). -/
class HasEdgeMonoAt (pq : ι) (r : ℤ) : Prop where
  le : r₀ ≤ r := by lia
  zero (pq' : ι) : (E.page r).d pq' pq = 0

lemma le₀_of_hasEdgeMonoAt (pq : ι) (r : ℤ) [E.HasEdgeMonoAt pq r] :
    r₀ ≤ r :=
  HasEdgeMonoAt.le (E := E) (pq := pq)

@[simp]
lemma d_eq_zero_of_hasEdgeMonoAt (pq' pq : ι) (r : ℤ) [E.HasEdgeMonoAt pq r] :
    (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).d pq' pq = 0 :=
  HasEdgeMonoAt.zero _

/-- The monomorphism `E_{r'}^{pq} ⟶ E_r^{pq}` when `r + 1 = r'` and
`E_r^{pq}` is an object on a page of a spectral sequence such that
the differential to `E_r^{pq}` is zero (i.e. `E.HasEdgeMonoAt pq r` holds). -/
noncomputable def edgeMonoStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    (E.page r' (by have := E.le₀_of_hasEdgeMonoAt pq r; lia)).X pq ⟶
      (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).X pq :=
  (E.iso r r' pq hrr' (E.le₀_of_hasEdgeMonoAt pq r)).inv ≫
    ((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).isoHomologyπ _ pq rfl (by simp)).inv ≫
    (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).iCycles pq

instance (pq : ι) (r r' : ℤ) (hrr' : r + 1 = r') [E.HasEdgeMonoAt pq r] :
    Mono (E.edgeMonoStep pq r r' hrr') := by
  dsimp [edgeMonoStep]
  infer_instance

@[reassoc (attr := simp)]
lemma edgeMonoStep_comp_d (pq pq' : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    E.edgeMonoStep pq r r' hrr' ≫ (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).d pq pq' = 0 := by
  simp [edgeMonoStep]

@[reassoc (attr := simp)]
lemma iso_hom_comp_edgeMonoStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    (E.iso r r' pq hrr' (E.le₀_of_hasEdgeMonoAt pq r)).hom ≫ E.edgeMonoStep pq r r' =
    ((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).isoHomologyπ _ pq rfl (by simp)).inv ≫
      (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).iCycles pq := by
  simp [edgeMonoStep]

/-- Assuming `E.HasEdgeMonoAt pq r` holds (i.e. the differential to an object
`E_r^{pq}` of a page of a spectral sequence vanishes), this is the short complex
`E_{r'}^{pq} ⟶ E_r^{pq} ⟶ E_r^{pq'}` when `r + 1 = r'`. The left morphism
defined using `SpectralSequence.edgeMonoStep` is a monomorphism, and the short
complex is exact when `pq'` is the position of the target object of the differential
from `E_r^{pq}` on the `E_r` page. -/
@[expose, simps, implicit_reducible]
noncomputable def edgeMonoStepShortComplex (pq pq' : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hr' : r + 1 = r' := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (E.edgeMonoStep_comp_d pq pq' r r')

instance (pq pq' : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r] (hr' : r + 1 = r' := by lia) :
    Mono (E.edgeMonoStepShortComplex pq pq' r r' hr').f := by
  dsimp
  infer_instance

lemma exact_edgeMonoStepShortComplex (pq pq' : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hpq' : (c r).next pq = pq') (hr' : r + 1 = r' := by lia) :
    (E.edgeMonoStepShortComplex pq pq' r r' hr').Exact := by
  subst hpq'
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit (((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).sc pq).cyclesIsKernel) ?_
  exact (Fork.ext (((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).isoHomologyπ _ pq rfl (by simp)) ≪≫
    E.iso r r' pq hr' (E.le₀_of_hasEdgeMonoAt pq r)) (by simp; rfl))

/-- This means that the differential from an object E_r^{p,q} is zero (both r and (p,q) fixed) -/
class HasEdgeEpiAt (pq : ι) (r : ℤ) : Prop where
  le : r₀ ≤ r := by lia
  zero (pq' : ι) : (E.page r).d pq pq' = 0

lemma le₀_of_hasEdgeEpiAt (pq : ι) (r : ℤ) [E.HasEdgeEpiAt pq r] :
    r₀ ≤ r :=
  HasEdgeEpiAt.le (E := E) (pq := pq)

@[simp]
lemma d_eq_zero_of_hasEdgeEpiAt (pq pq' : ι) (r : ℤ) [E.HasEdgeEpiAt pq r] :
    (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).d pq pq' = 0 :=
  HasEdgeEpiAt.zero _

/-- The epimorphism `E_r^{pq} ⟶ E_{r'}^{pq} ` when `r + 1 = r'` and
`E_r^{pq}` is an object on a page of a spectral sequence such that
the differential from `E_r^{pq}` is zero (i.e. `E.HasEdgeEpiAt pq r` holds). -/
noncomputable def edgeEpiStep (pq : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).X pq ⟶
      (E.page r' (by have := E.le₀_of_hasEdgeEpiAt pq r; lia)).X pq :=
  (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).pOpcycles pq ≫
    ((E.page r (E.le₀_of_hasEdgeEpiAt pq r) ).isoHomologyι pq _ rfl (by simp)).inv ≫
      (E.iso r r' pq hrr' (E.le₀_of_hasEdgeEpiAt pq r)).hom

instance (pq : ι) (r r' : ℤ) (hrr' : r + 1 = r') [E.HasEdgeEpiAt pq r] :
    Epi (E.edgeEpiStep pq r r' hrr') := by
  dsimp [edgeEpiStep]
  infer_instance

@[reassoc (attr := simp)]
lemma d_comp_edgeEpiStep (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    (E.page r (E.le₀_of_hasEdgeEpiAt pq' r)).d pq pq' ≫ E.edgeEpiStep pq' r r' hrr' = 0 := by
  simp [edgeEpiStep]

@[reassoc (attr := simp)]
lemma edgeEpiStep_comp_iso_inv (pq : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    E.edgeEpiStep pq r r' hrr' ≫ (E.iso r r' pq hrr' (E.le₀_of_hasEdgeEpiAt pq r)).inv =
    (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).pOpcycles pq ≫
      ((E.page r (E.le₀_of_hasEdgeEpiAt pq r)).isoHomologyι pq _ rfl (by simp)).inv := by
  simp [edgeEpiStep]

/-- Assuming `E.HasEdgeEpiAt pq r` holds (i.e. the differential from an object
`E_r^{pq}` of a page of a spectral sequence vanishes), this is the short complex
`E_r^{pq'} ⟶ E_r^{pq} ⟶ E_{r'}^{pq}` when `r + 1 = r'`. The right morphism
defined using `SpectralSequence.edgeEpiStep` is an epimorphism, and the short
complex is exact when `pq'` is the position of the source object of the differential
to `E_r^{pq}` on the `E_r` page. -/
@[expose, simps, implicit_reducible]
noncomputable def edgeEpiStepShortComplex (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r]
    (hrr' : r + 1 = r' := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (E.d_comp_edgeEpiStep pq pq' r r' hrr')

instance (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r] (hr' : r + 1 = r' := by lia) :
    Epi (E.edgeEpiStepShortComplex pq pq' r r' hr').g := by
  dsimp
  infer_instance

lemma exact_edgeEpiStepShortComplex (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r]
    (hpq' : (c r).prev pq' = pq) (hrr' : r + 1 = r' := by lia) :
    (E.edgeEpiStepShortComplex pq pq' r r' hrr').Exact := by
  subst hpq'
  apply ShortComplex.exact_of_g_is_cokernel
  refine IsColimit.ofIsoColimit
    (((E.page r (E.le₀_of_hasEdgeEpiAt pq' r)).sc pq').opcyclesIsCokernel) (Iso.symm ?_)
  exact Cofork.ext ((E.iso r r' pq' hrr' (E.le₀_of_hasEdgeEpiAt pq' r)).symm ≪≫
    (E.page r (E.le₀_of_hasEdgeEpiAt pq' r)).isoHomologyι pq' _ rfl (by simp))

@[reassoc (attr := simp)]
lemma edgeMonoStep_edgeEpiStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r] [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    E.edgeMonoStep pq r r' hrr' ≫ E.edgeEpiStep pq r r' hrr' = 𝟙 _ := by
  simp only [edgeMonoStep, edgeEpiStep, assoc,
    ← (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).homology_π_ι_assoc pq,
    HomologicalComplex.isoHomologyι_hom_inv_id_assoc,
    HomologicalComplex.isoHomologyπ_inv_hom_id_assoc, Iso.inv_hom_id]

@[reassoc (attr := simp)]
lemma edgeEpiStep_edgeMonoStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r] [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    E.edgeEpiStep pq r r' hrr' ≫ E.edgeMonoStep pq r r' hrr' = 𝟙 _ := by
  have := E.le₀_of_hasEdgeEpiAt pq r
  simp [edgeEpiStep, edgeMonoStep,
    ← cancel_mono ((E.page r).isoHomologyπ _ pq rfl (by simp)).hom,
    ← cancel_mono ((E.page r).isoHomologyι pq _ rfl (by simp)).hom,
    ← cancel_mono ((E.page r).iCyclesIso pq _ rfl (by simp)).inv]

section

variable (r r' : ℤ) (pq pq' pq'' : ι)
  (hpq : (c r).prev pq' = pq) (hpq'' : (c r).next pq' = pq'')
  {hr : r₀ ≤ r}
  (left : ((E.page r hr).sc' pq pq' pq'').LeftHomologyData)
  (right : ((E.page r hr).sc' pq pq' pq'').RightHomologyData)

@[reassoc]
lemma π_edgeMonoStep_compatibility [E.HasEdgeMonoAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    left.π ≫ left.homologyIso.inv ≫
      ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').inv ≫
        (E.iso r r' pq' hrr').hom ≫ E.edgeMonoStep pq' r r' hrr' = left.i := by
  simp

@[reassoc (attr := simp)]
lemma edgeMonoStep_p_compatibility [E.HasEdgeMonoAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    E.edgeMonoStep pq' r r' hrr' ≫ right.p =
    (E.iso r r' pq' hrr' hr).inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').hom ≫
      right.homologyIso.hom ≫ right.ι := by
  simp [← cancel_epi (E.iso r r' pq').hom,
    ← cancel_epi ((E.page r).isoHomologyπ  _ pq' rfl (d_eq_zero_of_hasEdgeMonoAt ..)).hom]

@[reassoc]
lemma edgeEpiStep_ι_compatibility [E.HasEdgeEpiAt pq' r]
      (hrr' : r + 1 = r' := by lia) :
    E.edgeEpiStep pq' r r' hrr' ≫ (E.iso r r' pq' hrr' hr).inv ≫
      ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').hom ≫
        right.homologyIso.hom ≫ right.ι = right.p := by
  simp

@[reassoc (attr := simp)]
lemma i_edgeEpiStep_compatibility [E.HasEdgeEpiAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    left.i ≫ E.edgeEpiStep pq' r r' hrr' =
    left.π ≫ left.homologyIso.inv ≫
      ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').inv ≫
        (E.iso r r' pq' hrr' hr).hom := by
  simp [← cancel_mono (E.iso r r' pq').inv,
    ← cancel_mono ((E.page r).isoHomologyι  pq' pq'' hpq''
    (d_eq_zero_of_hasEdgeEpiAt ..)).hom]

end

section

variable {E E'}

lemma isIso_hom_add_one (f : E ⟶ E') (r : ℤ) {hr : r₀ ≤ r}
    (hf : IsIso (f.hom r hr) := by infer_instance) :
    IsIso (f.hom (r + 1)) :=
  have (pq : ι) : IsIso ((f.hom (r + 1)).f pq) :=
    IsIso.of_isIso_fac_left (Hom.comm f r (r + 1) pq).symm
  HomologicalComplex.Hom.isIso_of_components _

lemma isIso_hom_of_ge (f : E ⟶ E') (r r' : ℤ) (hrr' : r ≤ r') {hr : r₀ ≤ r}
    (hf : IsIso (f.hom r hr) := by infer_instance) :
    IsIso (f.hom r') := by
  obtain ⟨k, hk⟩ := Int.le.dest hrr'
  revert r' hrr'
  induction k with
  | zero =>
    intro r' _ hrr'
    obtain rfl : r = r' := by lia
    exact hf
  | succ k hk =>
    intro r' _ hrr'
    obtain rfl : r' = (r + k) + 1 := by omega
    exact isIso_hom_add_one f (r + k) (hk (r + k) (by lia) (by rfl))

end

end SpectralSequence

end CategoryTheory
