import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Tactic.Linarith

lemma Int.eq_add_ofNat_of_le {i j : ℤ} (hij : i ≤ j) :
    ∃ (d : ℕ), j = i + d := by
  have h : 0 ≤ j - i := by linarith
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le h
  exact ⟨d, by linarith⟩

namespace ComplexShape

def spectralSequenceNat (u : ℤ × ℤ) : ComplexShape (ℕ × ℕ) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2
  next_eq {a b b'} := by
    rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> linarith
  prev_eq {a a' b} := by
    rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> linarith

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
    ext <;> linarith
  prev_eq := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨a₁', ⟨a₂', _⟩⟩⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> linarith

end ComplexShape

namespace CategoryTheory

open Category Limits

variable (C : Type*) [Category C] [Abelian C]
  {ι : Type*} (c : ℤ → ComplexShape ι) (r₀ : ℤ)

structure SpectralSequence where
  page' (r : ℤ) (hr : r₀ ≤ r) : HomologicalComplex C (c r)
  iso' (r r' : ℤ) (hrr' : r + 1 = r') (pq : ι) (hr : r₀ ≤ r) :
    (page' r hr).homology pq ≅ (page' r' (by linarith)).X pq

namespace SpectralSequence

variable {C c r₀}
variable (E E' E'' : SpectralSequence C c r₀)

@[ext]
structure Hom where
  hom' (r : ℤ) (hr : r₀ ≤ r) : E.page' r hr ⟶ E'.page' r (by linarith)
  comm' (r r' : ℤ) (hrr' : r + 1 = r') (pq : ι) (hr : r₀ ≤ r) :
    HomologicalComplex.homologyMap (hom' r hr) pq ≫ (E'.iso' r r' hrr' pq hr).hom =
      (E.iso' r r' hrr' pq hr).hom ≫ (hom' r' (by linarith)).f pq := by aesop_cat

class HasPage (E : SpectralSequence C c r₀) (r : ℤ) : Prop where
  le : r₀ ≤ r := by linarith

lemma le_of_hasPage (r : ℤ) [h : E.HasPage r] : r₀ ≤ r := h.le

lemma hasPage_of_LE (r r' : ℤ) (le : r ≤ r') [E.HasPage r] : E.HasPage r' where
  le := by linarith [E.le_of_hasPage r]

instance : E.HasPage r₀ where

instance [E.HasPage 0] : E.HasPage 1 := E.hasPage_of_LE 0 1 (by linarith)
instance [E.HasPage 1] : E.HasPage 2 := E.hasPage_of_LE 1 2 (by linarith)
instance [E.HasPage 2] : E.HasPage 3 := E.hasPage_of_LE 2 3 (by linarith)
instance [E.HasPage 3] : E.HasPage 4 := E.hasPage_of_LE 3 4 (by linarith)
instance [E.HasPage 4] : E.HasPage 5 := E.hasPage_of_LE 4 5 (by linarith)

instance (r : ℤ) [E.HasPage r] : E.HasPage (r + 1) :=
  E.hasPage_of_LE r _ (by linarith)

instance (r r' : ℤ) [E.HasPage r] : E.HasPage (max r r') :=
    E.hasPage_of_LE r _ (le_max_left _ _)

instance (r r' : ℤ) [E.HasPage r'] : E.HasPage (max r r') :=
    E.hasPage_of_LE r' _ (le_max_right _ _)

instance (r : ℤ) [E.HasPage r] (k : ℕ) : E.HasPage (r + k) :=
  E.hasPage_of_LE r (r + k) (by linarith)

def page (r : ℤ) [E.HasPage r] :
    HomologicalComplex C (c r) :=
  E.page' r (E.le_of_hasPage r)

def iso (r r' : ℤ) (hrr' : r + 1 = r') (pq : ι) [E.HasPage r] [E.HasPage r'] :
    (E.page r).homology pq ≅ (E.page r').X pq :=
  E.iso' r r' hrr' pq (E.le_of_hasPage r)

def pageXIsoOfEq (pq : ι) (r r' : ℤ) (h : r = r') [E.HasPage r] [E.HasPage r'] :
    (E.page r).X pq ≅ (E.page r').X pq :=
  eqToIso (by subst h; rfl)

namespace Hom

attribute [reassoc] comm'

@[simps]
def id : Hom E E where
  hom' r hr := 𝟙 _

variable {E E' E''}

@[simps]
def comp (f : Hom E E') (g : Hom E' E'') : Hom E E'' where
  hom' r hr := f.hom' r hr ≫ g.hom' r hr
  comm' r r' hrr' pq hr := by
    dsimp
    rw [HomologicalComplex.homologyMap_comp, assoc, g.comm' r r', f.comm'_assoc r r']

def hom (f : Hom E E') (r : ℤ) [E.HasPage r] [E'.HasPage r] :
    E.page r ⟶ E'.page r :=
  f.hom' r (E.le_of_hasPage r)

end Hom

instance : Category (SpectralSequence C c r₀) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

variable {E E'}

lemma hom_ext {f f' : E ⟶ E'} (h : ∀ (r : ℤ) (_ : E.HasPage r) (_ : E'.HasPage r), f.hom r = f'.hom r) :
    f = f' := by
  apply Hom.ext
  ext r hr : 2
  exact h r ⟨hr⟩ ⟨hr⟩

variable (E)

@[simp]
lemma id_hom (r : ℕ) [E.HasPage r] :
    Hom.hom (𝟙 E) r = 𝟙 _ := rfl

variable {E E''}

@[reassoc, simp]
lemma comp_hom (f : E ⟶ E') (g : E' ⟶ E'') (r : ℕ) [E.HasPage r] [E'.HasPage r] [E''.HasPage r] :
    (f ≫ g).hom r = f.hom r ≫ g.hom r := rfl

@[reassoc (attr := simp)]
lemma Hom.comm (f : E ⟶ E') (r r' : ℤ) (hrr' : r + 1 = r') (pq : ι)
    [E.HasPage r] [E'.HasPage r] [E.HasPage r'] [E'.HasPage r'] :
    HomologicalComplex.homologyMap (f.hom r) pq ≫ (E'.iso r r' hrr' pq).hom =
      (E.iso r r' hrr' pq).hom ≫ (f.hom r').f pq := by
  apply f.comm'

variable (C c r₀)

@[simps]
def pageFunctor (r : ℤ) [∀ (E : SpectralSequence C c r₀), E.HasPage r] :
    SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r) where
  obj E := E.page r
  map f := f.hom r

@[simps!]
noncomputable def pageHomologyNatIso
    (r r' : ℤ) (hrr' : r + 1 = r') (pq : ι)
    [∀ (E : SpectralSequence C c r₀), E.HasPage r]
    [∀ (E : SpectralSequence C c r₀), E.HasPage r'] :
    pageFunctor C c r₀ r ⋙ HomologicalComplex.homologyFunctor _ _ pq ≅
      pageFunctor C c r₀ r' ⋙ HomologicalComplex.eval _ _ pq :=
  NatIso.ofComponents (fun E => E.iso r r' hrr' pq) (by aesop_cat)

variable {C c r₀}

/-- This means that the differential to an object E_r^{p,q} is zero (both r and (p,q) fixed) -/
class HasEdgeMonoAt (pq : ι) (r : ℤ) [E.HasPage r] : Prop where
  zero : ∀ (pq' : ι), (E.page r).d pq' pq = 0

@[simp]
lemma d_eq_zero_of_hasEdgeMonoAt (pq' pq : ι) (r : ℤ) [E.HasPage r] [E.HasEdgeMonoAt pq r] :
    (E.page r).d pq' pq = 0 := by
  apply HasEdgeMonoAt.zero

noncomputable def edgeMonoStep (pq : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r] :
  (E.page r').X pq ⟶ (E.page r).X pq :=
    (E.iso r r' hr pq).inv ≫ ((E.page r).isoHomologyπ _ pq rfl (by simp)).inv ≫
      (E.page r).iCycles pq

instance (pq : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r] :
    Mono (E.edgeMonoStep pq r r' hr) := by
  dsimp [edgeMonoStep]
  infer_instance

@[reassoc (attr := simp)]
lemma edgeMonoStep_comp_d (pq pq' : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r] :
    E.edgeMonoStep pq r r' hr ≫ (E.page r).d pq pq' = 0 := by
  simp [edgeMonoStep]

@[reassoc (attr := simp)]
lemma iso_hom_comp_edgeMonoStep (pq : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r] :
    (E.iso r r' hr pq).hom ≫ E.edgeMonoStep pq r r' hr =
      ((E.page r).isoHomologyπ _ pq rfl (by simp)).inv ≫ (E.page r).iCycles pq := by
  simp [edgeMonoStep]

@[simps]
noncomputable def edgeMonoStepShortComplex (pq pq' : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r] : ShortComplex C :=
  ShortComplex.mk _ _ (E.edgeMonoStep_comp_d pq pq' r r' hr)

lemma edgeMonoStepShortComplex_exact (pq pq' : ι) (r r' : ℤ) (hr : r + 1 = r')
    (hpq' : (c r).next pq = pq')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeMonoAt pq r] :
    (E.edgeMonoStepShortComplex pq pq' r r' hr).Exact := by
  subst hpq'
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit (((E.page r).sc pq).cyclesIsKernel) ?_
  exact (Fork.ext (((E.page r).isoHomologyπ _ pq rfl (by simp)) ≪≫ E.iso r r' hr pq)
    (by simp; rfl))

/-- This means that the differential from an object E_r^{p,q} is zero (both r and (p,q) fixed) -/
class HasEdgeEpiAt (pq : ι) (r : ℤ) [E.HasPage r] : Prop where
  zero : ∀ (pq' : ι), (E.page r).d pq pq' = 0

@[simp]
lemma d_eq_zero_of_hasEdgeEpiAt (pq pq' : ι) (r : ℤ) [E.HasPage r] [E.HasEdgeEpiAt pq r] :
    (E.page r).d pq pq' = 0 := by
  apply HasEdgeEpiAt.zero

noncomputable def edgeEpiStep (pq : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeEpiAt pq r] :
  (E.page r).X pq ⟶ (E.page r').X pq :=
    (E.page r).pOpcycles pq ≫ ((E.page r).isoHomologyι pq _ rfl (by simp)).inv ≫
      (E.iso r r' hr pq).hom

attribute [local instance] epi_comp

instance (pq : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeEpiAt pq r] :
    Epi (E.edgeEpiStep pq r r' hr) := by
  dsimp [edgeEpiStep]
  infer_instance

@[reassoc (attr := simp)]
lemma d_comp_edgeEpiStep (pq pq' : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeEpiAt pq' r] :
    (E.page r).d pq pq' ≫ E.edgeEpiStep pq' r r' hr = 0 := by
  simp [edgeEpiStep]

@[reassoc (attr := simp)]
lemma edgeEpiStep_comp_iso_inv (pq : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeEpiAt pq r] :
    E.edgeEpiStep pq r r' hr ≫ (E.iso r r' hr pq).inv =
      (E.page r).pOpcycles pq ≫ ((E.page r).isoHomologyι pq _ rfl (by simp)).inv := by
  simp [edgeEpiStep]

@[simps]
noncomputable def edgeEpiStepShortComplex (pq pq' : ι) (r r' : ℤ) (hr : r + 1 = r')
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeEpiAt pq' r] : ShortComplex C :=
  ShortComplex.mk _ _ (E.d_comp_edgeEpiStep pq pq' r r' hr)

lemma edgeEpiStepShortComplex_exact (pq pq' : ι) (r r' : ℤ) (hr : r + 1 = r')
    (hpq' : (c r).prev pq' = pq)
    [E.HasPage r] [E.HasPage r'] [E.HasEdgeEpiAt pq' r] :
    (E.edgeEpiStepShortComplex pq pq' r r' hr).Exact := by
  subst hpq'
  apply ShortComplex.exact_of_g_is_cokernel
  refine IsColimit.ofIsoColimit (((E.page r).sc pq').opcyclesIsCokernel) (Iso.symm ?_)
  exact Cofork.ext ((E.iso r r' hr pq').symm ≪≫ (E.page r).isoHomologyι pq' _ rfl (by simp))
    (by simp; rfl)

@[reassoc (attr := simp)]
lemma edgeMonoStep_edgeEpiStep (pq : ι) (r r' : ℤ) (hr : r + 1 = r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeMonoAt pq r] [E.HasEdgeEpiAt pq r] :
        E.edgeMonoStep pq r r' hr ≫ E.edgeEpiStep pq r r' hr = 𝟙 _ := by
  simp only [edgeMonoStep, edgeEpiStep, assoc, ← (E.page r).homology_π_ι_assoc pq,
    HomologicalComplex.isoHomologyι_hom_inv_id_assoc,
    HomologicalComplex.isoHomologyπ_inv_hom_id_assoc, Iso.inv_hom_id]

@[reassoc (attr := simp)]
lemma edgeEpiStep_edgeMonoStep (pq : ι) (r r' : ℤ) (hr : r + 1 = r') [E.HasPage r] [E.HasPage r']
    [E.HasEdgeMonoAt pq r] [E.HasEdgeEpiAt pq r] :
        E.edgeEpiStep pq r r' hr ≫ E.edgeMonoStep pq r r' hr = 𝟙 _ := by
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

variable (r r' : ℤ) (hr : r + 1 = r') [E.HasPage r] [E.HasPage r']
  (pq pq' pq'' : ι) (hpq : (c r).prev pq' = pq) (hpq'' : (c r).next pq' = pq'')
  (left : ((E.page r).sc' pq pq' pq'').LeftHomologyData)
  (right : ((E.page r).sc' pq pq' pq'').RightHomologyData)

@[reassoc (attr := simp)]
lemma leftHomologyData_π_edgeMonoStep_compatibility [E.HasEdgeMonoAt pq' r] :
    left.π ≫ left.homologyIso.inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').inv ≫
      (E.iso r r' hr pq').hom ≫ E.edgeMonoStep pq' r r' hr = left.i := by
  simp [edgeMonoStep]

@[reassoc (attr := simp)]
lemma rightHomologyData_p_edgeMonoStep_compatibility [E.HasEdgeMonoAt pq' r] :
      E.edgeMonoStep pq' r r' hr ≫ right.p =
       (E.iso r r' hr pq').inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').hom ≫
       right.homologyIso.hom ≫ right.ι := by
  rw [← cancel_epi (E.iso r r' hr pq').hom,
    ← cancel_epi ((E.page r).isoHomologyπ  _ pq' rfl (by apply d_eq_zero_of_hasEdgeMonoAt)).hom]
  simp [edgeMonoStep]

@[reassoc (attr := simp)]
lemma leftHomologyData_i_edgeEpiStep_compatibility [E.HasEdgeEpiAt pq' r] :
    left.i ≫ E.edgeEpiStep pq' r r' hr =
      left.π ≫ left.homologyIso.inv ≫ ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').inv ≫
        (E.iso r r' hr pq').hom := by
  rw [← cancel_mono (E.iso r r' hr pq').inv,
    ← cancel_mono ((E.page r).isoHomologyι  pq' pq'' hpq'' (by apply d_eq_zero_of_hasEdgeEpiAt)).hom]
  simp [edgeEpiStep]

@[reassoc (attr := simp)]
lemma rightHomologyData_ι_edgeEpiStep_compatibility [E.HasEdgeEpiAt pq' r] :
    E.edgeEpiStep pq' r r' hr ≫ (E.iso r r' hr pq').inv ≫
      ((E.page r).homologyIsoSc' _ _ _ hpq hpq'').hom ≫
        right.homologyIso.hom ≫ right.ι = right.p := by
  simp [edgeEpiStep]

end


def hasEdgeMonoSet (pq : ι) : Set ℤ  :=
  fun r => ∀ (r' : ℤ) (_ : r ≤ r'), ∃ (_ : E.HasPage r'), E.HasEdgeMonoAt pq r'

def hasEdgeEpiSet (pq : ι) : Set ℤ :=
  fun r => ∀ (r' : ℤ) (_ : r ≤ r'), ∃ (_ : E.HasPage r'), E.HasEdgeEpiAt pq r'

section

lemma isIso_hom_succ (f : E ⟶ E') (r : ℤ) [E.HasPage r] [E'.HasPage r]
    (hf : IsIso (f.hom r)) : IsIso (f.hom (r + 1)) := by
  have : ∀ (pq : ι), IsIso ((f.hom (r + 1)).f pq) := fun pq => by
    have : IsIso (HomologicalComplex.homologyMap (Hom.hom f r) pq) := by
      -- this should already be an instance
      change IsIso ((HomologicalComplex.homologyFunctor _ _ pq).map (Hom.hom f r))
      infer_instance
    exact IsIso.of_isIso_fac_left (Hom.comm f r _ rfl pq).symm
  apply HomologicalComplex.Hom.isIso_of_components

lemma isIso_hom_of_GE (f : E ⟶ E') (r r' : ℤ) (hrr' : r ≤ r')
    [E.HasPage r] [E'.HasPage r] [E.HasPage r'] [E'.HasPage r']
    (hf : IsIso (f.hom r)) : IsIso (f.hom r') := by
  obtain ⟨k, hk⟩ := Int.eq_add_ofNat_of_le hrr'
  revert r' hrr'
  induction' k with k hk
  · intro r' _ _ _ hr'
    obtain rfl : r = r' := by simp [hr']
    exact hf
  · intro r' hrr' _ _ hr'
    obtain rfl : r' = (r + k) + 1 := by simp only [hr', Nat.cast_succ, add_assoc]
    exact isIso_hom_succ f (r + k) (hk (r + k) (by linarith) (by rfl))

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
