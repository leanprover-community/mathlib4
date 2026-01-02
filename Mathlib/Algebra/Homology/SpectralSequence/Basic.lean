/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Spectral sequences

-/

@[expose] public section

namespace ComplexShape

def spectralSequenceNat (u : ℤ × ℤ) : ComplexShape (ℕ × ℕ) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2
  next_eq {a b b'} := by
    rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> lia
  prev_eq {a a' b} := by
    rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> lia

instance (u : ℤ × ℤ) : DecidableRel (spectralSequenceNat u).Rel := fun a b => by
  dsimp [spectralSequenceNat]
  infer_instance

@[simp]
lemma spectralSequenceNat_rel_iff (u : ℤ × ℤ) (a b : ℕ × ℕ) :
    (spectralSequenceNat u).Rel a b ↔ a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2 := by rfl

def spectralSequenceFin (l : ℕ) (u : ℤ × ℤ) : ComplexShape (ℤ × Fin l) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2.1 + u.2 = b.2.1
  next_eq := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩⟨b₁', ⟨b₂', _⟩⟩ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> lia
  prev_eq := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨a₁', ⟨a₂', _⟩⟩⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> lia

end ComplexShape

namespace CategoryTheory

open Category Limits

variable (C : Type*) [Category C] [Abelian C]
  {ι : Type*} (c : ℤ → ComplexShape ι) (r₀ : ℤ)

structure SpectralSequence where
  page (r : ℤ) (hr : r₀ ≤ r := by lia) : HomologicalComplex C (c r)
  iso (r r' : ℤ) (pq : ι) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    (page r).homology pq ≅ (page r').X pq

namespace SpectralSequence

variable {C c r₀}
variable (E E' E'' : SpectralSequence C c r₀)

@[ext]
structure Hom where
  hom (r : ℤ) (hr : r₀ ≤ r := by lia) : E.page r ⟶ E'.page r
  comm (r r' : ℤ) (pq : ι) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    HomologicalComplex.homologyMap (hom r) pq ≫ (E'.iso r r' pq).hom =
      (E.iso r r' pq).hom ≫ (hom r').f pq := by aesop_cat

def pageXIsoOfEq (pq : ι) (r r' : ℤ) (h : r = r') (hr : r₀ ≤ r := by lia) :
    (E.page r).X pq ≅ (E.page r').X pq :=
  eqToIso (by subst h; rfl)

namespace Hom

attribute [reassoc] comm

@[simps]
def id : Hom E E where
  hom r hr := 𝟙 _

variable {E E' E''}

@[simps]
def comp (f : Hom E E') (g : Hom E' E'') : Hom E E'' where
  hom r hr := f.hom r ≫ g.hom r
  comm r r' hrr' pq hr := by
    dsimp
    rw [HomologicalComplex.homologyMap_comp, assoc, g.comm r r', f.comm_assoc r r']

end Hom

instance : Category (SpectralSequence C c r₀) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

variable {E E'}

lemma hom_ext {f f' : E ⟶ E'}
    (h : ∀ (r : ℤ) (hr : r₀ ≤ r), f.hom r = f'.hom r) :
    f = f' := by
  apply Hom.ext
  ext r hr : 2
  exact h r hr

variable (E)

@[simp]
lemma id_hom (r : ℕ) (hr : r₀ ≤ r := by lia) :
    Hom.hom (𝟙 E) r = 𝟙 _ := rfl

variable {E E''}

@[reassoc, simp]
lemma comp_hom (f : E ⟶ E') (g : E' ⟶ E'') (r : ℕ) (hr : r₀ ≤ r := by lia) :
    (f ≫ g).hom r = f.hom r ≫ g.hom r := rfl

variable (C c r₀)

@[simps]
def pageFunctor (r : ℤ) (hr : r₀ ≤ r := by lia) :
    SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r) where
  obj E := E.page r
  map f := f.hom r

@[simps!]
noncomputable def pageHomologyNatIso
    (r r' : ℤ) (pq : ι) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    pageFunctor C c r₀ r ⋙ HomologicalComplex.homologyFunctor _ _ pq ≅
      pageFunctor C c r₀ r' ⋙ HomologicalComplex.eval _ _ pq :=
  NatIso.ofComponents (fun E => E.iso r r' pq) (fun _ ↦ Hom.comm _ _ _ _ (by lia))

variable {C c r₀}

/-- This means that the differential to an object E_r^{p,q} is zero (both r and (p,q) fixed) -/
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
lemma edgeMonoStep_comp_d (pq pq' : ι) (r r' : ℤ)
    (hrr' : r + 1 = r' := by lia)
    [E.HasEdgeMonoAt pq r] :
    E.edgeMonoStep pq r r' hrr' ≫ (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).d pq pq' = 0 := by
  simp [edgeMonoStep]

@[reassoc (attr := simp)]
lemma iso_hom_comp_edgeMonoStep (pq : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hrr' : r + 1 = r' := by lia) :
    (E.iso r r' pq hrr' (E.le₀_of_hasEdgeMonoAt pq r)).hom ≫ E.edgeMonoStep pq r r' =
      ((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).isoHomologyπ _ pq rfl (by simp)).inv ≫
        (E.page r (E.le₀_of_hasEdgeMonoAt pq r)).iCycles pq := by
  simp [edgeMonoStep]

@[simps]
noncomputable def edgeMonoStepShortComplex (pq pq' : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hr' : r + 1 = r' := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (E.edgeMonoStep_comp_d pq pq' r r')

lemma edgeMonoStepShortComplex_exact (pq pq' : ι) (r r' : ℤ) [E.HasEdgeMonoAt pq r]
    (hpq' : (c r).next pq = pq')
    (hrr' : r + 1 = r' := by lia) :
    (E.edgeMonoStepShortComplex pq pq' r r' hrr').Exact := by
  subst hpq'
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit (((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).sc pq).cyclesIsKernel) ?_
  exact (Fork.ext (((E.page r (E.le₀_of_hasEdgeMonoAt pq r)).isoHomologyπ _ pq rfl (by simp)) ≪≫
    E.iso r r' pq hrr' (E.le₀_of_hasEdgeMonoAt pq r)) (by simp; rfl))

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

noncomputable def edgeEpiStep (pq : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) :
  (E.page r (E.le₀_of_hasEdgeEpiAt pq r)).X pq ⟶ (E.page r'
    (by have := E.le₀_of_hasEdgeEpiAt pq r; lia)).X pq :=
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

@[simps]
noncomputable def edgeEpiStepShortComplex (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r]
    (hrr' : r + 1 = r' := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (E.d_comp_edgeEpiStep pq pq' r r' hrr')

lemma edgeEpiStepShortComplex_exact (pq pq' : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq' r]
    (hpq' : (c r).prev pq' = pq) (hrr' : r + 1 = r' := by lia) :
    (E.edgeEpiStepShortComplex pq pq' r r' hrr').Exact := by
  subst hpq'
  apply ShortComplex.exact_of_g_is_cokernel
  refine IsColimit.ofIsoColimit
    (((E.page r (E.le₀_of_hasEdgeEpiAt pq' r)).sc pq').opcyclesIsCokernel) (Iso.symm ?_)
  exact Cofork.ext ((E.iso r r' pq' hrr' (E.le₀_of_hasEdgeEpiAt pq' r)).symm ≪≫
    (E.page r (E.le₀_of_hasEdgeEpiAt pq' r)).isoHomologyι pq' _ rfl (by simp))
    (by simp; rfl)

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
  simp only [edgeEpiStep, edgeMonoStep,
    ← cancel_mono ((E.page r).isoHomologyπ _ pq rfl (by simp)).hom,
    ← cancel_mono ((E.page r).isoHomologyι pq _ rfl (by simp)).hom,
    ← cancel_mono ((E.page r).iCyclesIso pq _ rfl (by simp)).inv,
    HomologicalComplex.iCyclesIso_hom_inv_id, comp_id, id_comp,
    HomologicalComplex.isoHomologyπ_hom, HomologicalComplex.isoHomologyπ_inv_hom_id,
    HomologicalComplex.isoHomologyι_hom, HomologicalComplex.isoHomologyι_inv_hom_id,
    HomologicalComplex.homology_π_ι, HomologicalComplex.iCyclesIso_inv_hom_id_assoc,
    assoc, Iso.hom_inv_id_assoc]

section

variable (r r' : ℤ) (pq pq' pq'' : ι)
  (hpq : (c r).prev pq' = pq) (hpq'' : (c r).next pq' = pq'')
  {hr : r₀ ≤ r}
  (left : ((E.page r hr).sc' pq pq' pq'').LeftHomologyData)
  (right : ((E.page r hr).sc' pq pq' pq'').RightHomologyData)

@[reassoc]
lemma leftHomologyData_π_edgeMonoStep_compatibility [E.HasEdgeMonoAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    left.π ≫ left.homologyIso.inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').inv ≫
      (E.iso r r' pq' hrr').hom ≫ E.edgeMonoStep pq' r r' hrr' = left.i := by
  simp

@[reassoc (attr := simp)]
lemma rightHomologyData_p_edgeMonoStep_compatibility [E.HasEdgeMonoAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
      E.edgeMonoStep pq' r r' hrr' ≫ right.p =
       (E.iso r r' pq' hrr' hr).inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').hom ≫
       right.homologyIso.hom ≫ right.ι := by
  rw [← cancel_epi (E.iso r r' pq').hom,
    ← cancel_epi ((E.page r).isoHomologyπ  _ pq' rfl (by apply d_eq_zero_of_hasEdgeMonoAt)).hom]
  simp [edgeMonoStep]

@[reassoc (attr := simp)]
lemma leftHomologyData_i_edgeEpiStep_compatibility [E.HasEdgeEpiAt pq' r]
    (hrr' : r + 1 = r' := by lia) :
    left.i ≫ E.edgeEpiStep pq' r r' hrr' =
      left.π ≫ left.homologyIso.inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').inv ≫
        (E.iso r r' pq' hrr' hr).hom := by
  rw [← cancel_mono (E.iso r r' pq').inv,
    ← cancel_mono ((E.page r).isoHomologyι  pq' pq'' hpq''
      (by apply d_eq_zero_of_hasEdgeEpiAt)).hom]
  simp [edgeEpiStep]

@[reassoc]
lemma rightHomologyData_ι_edgeEpiStep_compatibility [E.HasEdgeEpiAt pq' r]
      (hrr' : r + 1 = r' := by lia) :
    E.edgeEpiStep pq' r r' hrr' ≫ (E.iso r r' pq' hrr' hr).inv ≫
      ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').hom ≫
        right.homologyIso.hom ≫ right.ι = right.p := by
  simp

end


def hasEdgeMonoSet (pq : ι) : Set ℤ  :=
  fun r => r₀ ≤ r ∧ ∀ (r' : ℤ) (_ : r ≤ r'), E.HasEdgeMonoAt pq r'

def hasEdgeEpiSet (pq : ι) : Set ℤ :=
  fun r => r₀ ≤ r ∧ ∀ (r' : ℤ) (_ : r ≤ r'), E.HasEdgeEpiAt pq r'

section

lemma isIso_hom_succ (f : E ⟶ E') (r : ℤ) {hr : r₀ ≤ r}
    (hf : IsIso (f.hom r hr)) : IsIso (f.hom (r + 1)) := by
  have : ∀ (pq : ι), IsIso ((f.hom (r + 1)).f pq) := fun pq => by
    have : IsIso (HomologicalComplex.homologyMap (Hom.hom f r) pq) := by
      -- this should already be an instance
      change IsIso ((HomologicalComplex.homologyFunctor _ _ pq).map (Hom.hom f r))
      infer_instance
    exact IsIso.of_isIso_fac_left (Hom.comm f r (r + 1) pq).symm
  apply HomologicalComplex.Hom.isIso_of_components

lemma isIso_hom_of_GE (f : E ⟶ E') (r r' : ℤ) (hrr' : r ≤ r') {hr : r₀ ≤ r}
    (hf : IsIso (f.hom r hr)) : IsIso (f.hom r') := by
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
    exact isIso_hom_succ f (r + k) (hk (r + k) (by lia) (by rfl))

end

end SpectralSequence

abbrev CohomologicalSpectralSequence :=
  SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))

abbrev E₂CohomologicalSpectralSequence := CohomologicalSpectralSequence C 2

abbrev CohomologicalSpectralSequenceNat :=
  SpectralSequence C (fun r => ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩)

abbrev E₂CohomologicalSpectralSequenceNat :=
  CohomologicalSpectralSequenceNat C 2

abbrev CohomologicalSpectralSequenceFin (l : ℕ) :=
  SpectralSequence C (fun r => ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩)

abbrev E₂CohomologicalSpectralSequenceFin (l : ℕ) :=
  CohomologicalSpectralSequenceFin C 2 l

end CategoryTheory
