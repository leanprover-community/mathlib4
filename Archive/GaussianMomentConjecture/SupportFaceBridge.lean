/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Archive.GaussianMomentConjecture.ChannelDilation
import Archive.GaussianMomentConjecture.FaceHeightFloor
import Archive.GaussianMomentConjecture.FaceReferenceChannel
import Archive.GaussianMomentConjecture.IntegralFaceSeedDescent
import Archive.GaussianMomentConjecture.NormalizedResidue
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Finite.Polynomial

set_option linter.minImports true

/-!
# Transporting a geometric face into exact-support channel coordinates

The lowest-face construction produces `F : Finset (Fin 2 →₀ ℕ)`, while the
normalized moment and dilation layers use variables indexed by
`↥P.support`.  This module supplies the finite face inside that support, the
canonical equivalence of its subtype with `↥F`, seed reindexing, the exact
balance/height dictionary, and the height obligations used by the normalized
residue argument.
-/

open MvPolynomial Finset

namespace GMC2.SupportFaceBridge

noncomputable section

/-- The geometric face, regarded as a finset of exact-support indices. -/
def supportFace
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ)) :
    Finset ↥P.support :=
  Finset.univ.filter fun s ↦ (s : Fin 2 →₀ ℕ) ∈ F

@[simp] theorem mem_supportFace
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (s : ↥P.support) :
    s ∈ supportFace P F ↔ (s : Fin 2 →₀ ℕ) ∈ F := by
  simp [supportFace]

/-- Under `F ⊆ P.support`, the geometric face subtype and its copy inside
the exact support are canonically equivalent. -/
def faceEquivSupportFace
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) : ↥F ≃ ↥(supportFace P F) where
  toFun s :=
    ⟨⟨s, hsubset s.property⟩, (mem_supportFace P F _).2 s.property⟩
  invFun t :=
    ⟨t.1, (mem_supportFace P F t.1).1 t.property⟩
  left_inv s := by
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

@[simp] theorem faceEquivSupportFace_supportValue
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (s : ↥F) :
    (faceEquivSupportFace P F hsubset s).1 =
      GMC2.FaceSeedDescent.faceToSupport hsubset s := rfl

@[simp] theorem faceEquivSupportFace_value
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (s : ↥F) :
    (((faceEquivSupportFace P F hsubset s).1 : ↥P.support) :
        Fin 2 →₀ ℕ) = (s : Fin 2 →₀ ℕ) := rfl

@[simp] theorem coefficient_faceEquivSupportFace
    {R : Type*}
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (coefficient : ↥P.support → R) (s : ↥F) :
    coefficient (faceEquivSupportFace P F hsubset s).1 =
      coefficient (GMC2.FaceSeedDescent.faceToSupport hsubset s) := rfl

@[simp] theorem exponent_faceEquivSupportFace
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (s : ↥F) :
    (fun t : ↥(supportFace P F) ↦
      ((t.1 : ↥P.support) : Fin 2 →₀ ℕ))
        (faceEquivSupportFace P F hsubset s) = s := rfl

@[simp] theorem charge_faceEquivSupportFace
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (s : ↥F) :
    (fun t : ↥(supportFace P F) ↦
      GMC2.charge ((t.1 : ↥P.support) : Fin 2 →₀ ℕ))
        (faceEquivSupportFace P F hsubset s) = GMC2.charge s := rfl

@[simp] theorem tiltedHeight_faceEquivSupportFace
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (lambda : ℚ) (s : ↥F) :
    GMC2.FrobeniusFace.tiltedHeight
        (fun t : ↥(supportFace P F) ↦
          GMC2.FaceDictionary.exponentA (t.1 : ↥P.support))
        (fun t : ↥(supportFace P F) ↦
          GMC2.FaceDictionary.exponentB (t.1 : ↥P.support))
        lambda (faceEquivSupportFace P F hsubset s) =
      GMC2.FrobeniusFace.tiltedHeight
        GMC2.FaceDictionary.exponentA GMC2.FaceDictionary.exponentB lambda s := rfl

section EquivReindex

variable {α β R : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Reindex multiplicity functions contravariantly along an equivalence. -/
def reindexChannelEquiv (e : α ≃ β) : (α → ℕ) ≃ (β → ℕ) where
  toFun r := r ∘ e.symm
  invFun s := s ∘ e
  left_inv r := by
    funext i
    simp
  right_inv s := by
    funext i
    simp

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] in
@[simp] theorem reindexChannelEquiv_apply
    (e : α ≃ β) (r : α → ℕ) (j : β) :
    reindexChannelEquiv e r j = r (e.symm j) := rfl

theorem reindexChannel_mem_piAntidiag
    (e : α ≃ β) (r : α → ℕ) (m : ℕ) :
    reindexChannelEquiv e r ∈
        Finset.piAntidiag (Finset.univ : Finset β) m ↔
      r ∈ Finset.piAntidiag (Finset.univ : Finset α) m := by
  have hsum : (∑ j : β, reindexChannelEquiv e r j) = ∑ i : α, r i := by
    simpa [reindexChannelEquiv_apply] using
      (e.sum_comp (fun j : β ↦ r (e.symm j))).symm
  rw [Finset.mem_piAntidiag, Finset.mem_piAntidiag]
  constructor
  · rintro ⟨hmass, hsupport⟩
    refine ⟨hsum.symm.trans hmass, by simp⟩
  · rintro ⟨hmass, hsupport⟩
    refine ⟨hsum.trans hmass, by simp⟩

omit [DecidableEq α] [DecidableEq β] in
theorem totalCharge_reindex
    (e : α ≃ β) (q : β → ℤ) (r : α → ℕ) :
    GMC2.ConstantTermRelations.totalCharge q (reindexChannelEquiv e r) =
      GMC2.ConstantTermRelations.totalCharge (q ∘ e) r := by
  unfold GMC2.ConstantTermRelations.totalCharge
  have hsum := e.sum_comp
    (fun j : β ↦ ((r (e.symm j) : ℕ) : ℤ) * q j)
  simpa using hsum.symm

omit [DecidableEq α] [DecidableEq β] in
theorem coefficientProduct_reindex
    [CommMonoid R] (e : α ≃ β) (coefficient : β → R) (r : α → ℕ) :
    (∏ j : β, coefficient j ^ reindexChannelEquiv e r j) =
      ∏ i : α, coefficient (e i) ^ r i := by
  have hprod := e.prod_comp
    (fun j : β ↦ coefficient j ^ r (e.symm j))
  simpa using hprod.symm

omit [DecidableEq α] [DecidableEq β] in
theorem multinomial_reindex
    (e : α ≃ β) (r : α → ℕ) :
    Nat.multinomial Finset.univ (reindexChannelEquiv e r) =
      Nat.multinomial Finset.univ r := by
  have hsum : (∑ j : β, reindexChannelEquiv e r j) = ∑ i : α, r i := by
    simpa [reindexChannelEquiv_apply] using
      (e.sum_comp (fun j : β ↦ r (e.symm j))).symm
  have hprod :
      (∏ j : β, Nat.factorial (reindexChannelEquiv e r j)) =
        ∏ i : α, Nat.factorial (r i) := by
    simpa [reindexChannelEquiv_apply] using
      (e.prod_comp (fun j : β ↦ Nat.factorial (r (e.symm j)))).symm
  change
    Nat.factorial (∑ j : β, reindexChannelEquiv e r j) /
        (∏ j : β, Nat.factorial (reindexChannelEquiv e r j)) =
      Nat.factorial (∑ i : α, r i) / ∏ i : α, Nat.factorial (r i)
  rw [hsum, hprod]

/-- Integral constant-term evaluation is invariant under a finite
reindexing equivalence. -/
theorem aeval_constantTermRelationInt_equiv
    [CommRing R] [Algebra ℤ R]
    (e : α ≃ β) (q : β → ℤ) (coefficient : β → R) (m : ℕ) :
    MvPolynomial.aeval (coefficient ∘ e)
        (GMC2.IntegralRelations.constantTermRelationInt (q ∘ e) m) =
      MvPolynomial.aeval coefficient
        (GMC2.IntegralRelations.constantTermRelationInt q m) := by
  rw [GMC2.IntegralRelations.aeval_constantTermRelationInt,
    GMC2.IntegralRelations.aeval_constantTermRelationInt]
  apply Finset.sum_equiv (reindexChannelEquiv e)
  · intro r
    exact (reindexChannel_mem_piAntidiag e r m).symm
  · intro r hr
    rw [totalCharge_reindex]
    by_cases hcharge :
        GMC2.ConstantTermRelations.totalCharge (q ∘ e) r = 0
    · simp only [if_pos hcharge, Function.comp_apply]
      rw [multinomial_reindex, coefficientProduct_reindex]
    · simp only [if_neg hcharge]

end EquivReindex

/-- Direct seed bridge from the lifted support polynomial to the canonical
constant-term polynomial on `↥(supportFace P F)`. -/
theorem aeval_liftedFaceSeedInt_eq_supportFace
    {R : Type*} [CommRing R] [Algebra ℤ R]
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (m0 : ℕ)
    (coefficient : ↥P.support → R) :
    MvPolynomial.aeval coefficient
        (GMC2.IntegralFaceSeedDescent.liftedFaceSeedInt P F hsubset m0) =
      MvPolynomial.aeval (fun t : ↥(supportFace P F) ↦ coefficient t.1)
        (GMC2.IntegralRelations.constantTermRelationInt
          (fun t : ↥(supportFace P F) ↦
            GMC2.charge ((t.1 : ↥P.support) : Fin 2 →₀ ℕ)) m0) := by
  rw [GMC2.IntegralFaceSeedDescent.aeval_liftedFaceSeedInt]
  simpa only [Function.comp_def, Function.comp_apply, coefficient_faceEquivSupportFace,
    charge_faceEquivSupportFace, GMC2.FaceSeedDescent.faceToSupport] using
    (aeval_constantTermRelationInt_equiv
      (faceEquivSupportFace P F hsubset)
      (fun t : ↥(supportFace P F) ↦
        GMC2.charge ((t.1 : ↥P.support) : Fin 2 →₀ ℕ))
      (fun t : ↥(supportFace P F) ↦ coefficient t.1) m0)

section ExactSupportDictionary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Exact bidegree balance is the same as vanishing of total integral charge. -/
theorem isBalanced_iff_totalCharge_zero
    (exponent : ι → Fin 2 →₀ ℕ) (r : ι → ℕ) :
    GMC2.NormalizedMoment.IsBalanced exponent r ↔
      GMC2.ConstantTermRelations.totalCharge
        (fun i ↦ GMC2.charge (exponent i)) r = 0 := by
  have hcharge :
      GMC2.ConstantTermRelations.totalCharge
          (fun i ↦ GMC2.charge (exponent i)) r =
        ((GMC2.MomentRelations.channelExponent exponent r) 0 : ℤ) -
          ((GMC2.MomentRelations.channelExponent exponent r) 1 : ℤ) := by
    unfold GMC2.ConstantTermRelations.totalCharge
    calc
      (∑ i, (r i : ℤ) * GMC2.charge (exponent i)) =
          ∑ i, ((r i : ℤ) * ((exponent i) 0 : ℤ) -
            (r i : ℤ) * ((exponent i) 1 : ℤ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [GMC2.charge]
        ring
      _ = (∑ i, (r i : ℤ) * ((exponent i) 0 : ℤ)) -
          ∑ i, (r i : ℤ) * ((exponent i) 1 : ℤ) := by
        rw [Finset.sum_sub_distrib]
      _ = ((GMC2.MomentRelations.channelExponent exponent r) 0 : ℤ) -
          ((GMC2.MomentRelations.channelExponent exponent r) 1 : ℤ) := by
        simp [GMC2.MomentRelations.channelExponent]
  rw [hcharge, sub_eq_zero]
  exact_mod_cast Iff.rfl

/-- Membership in the full antidiagonal records the natural channel mass. -/
theorem channelMass_eq_of_mem_piAntidiag
    (r : ι → ℕ) (m : ℕ)
    (hr : r ∈ Finset.piAntidiag (Finset.univ : Finset ι) m) :
    GMC2.FaceHeightFloor.channelMass Finset.univ r = m := by
  simpa [GMC2.FaceHeightFloor.channelMass] using
    (Finset.mem_piAntidiag.mp hr).1

end ExactSupportDictionary

section FaceConstantTerm

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

/-- Extending a face channel by zero does not change its total charge. -/
theorem totalCharge_extendByZero
    (exponent : ι → Fin 2 →₀ ℕ) (face : Finset ι) (s : ↥face → ℕ) :
    GMC2.ConstantTermRelations.totalCharge
        (fun i ↦ GMC2.charge (exponent i))
        (GMC2.ChannelDilation.extendByZero face s) =
      GMC2.ConstantTermRelations.totalCharge
        (fun i : ↥face ↦ GMC2.charge (exponent i)) s := by
  unfold GMC2.ConstantTermRelations.totalCharge
  simpa using
    (GMC2.ChannelDilation.sum_extendByZero face s
      (fun i n ↦ (n : ℤ) * GMC2.charge (exponent i)) (by simp))

/-- Balance after extension by zero is exactly vanishing of the face charge
sum used by the integral constant-term polynomial. -/
theorem isBalanced_extendByZero_iff_totalCharge_zero
    (exponent : ι → Fin 2 →₀ ℕ) (face : Finset ι) (s : ↥face → ℕ) :
    GMC2.NormalizedMoment.IsBalanced exponent
        (GMC2.ChannelDilation.extendByZero face s) ↔
      GMC2.ConstantTermRelations.totalCharge
        (fun i : ↥face ↦ GMC2.charge (exponent i)) s = 0 := by
  rw [isBalanced_iff_totalCharge_zero, totalCharge_extendByZero]

/-- The full multinomial coefficient of an extension-by-zero channel is the
face multinomial coefficient. -/
theorem multinomial_extendByZero
    (face : Finset ι) (s : ↥face → ℕ) :
    Nat.multinomial Finset.univ
        (GMC2.ChannelDilation.extendByZero face s) =
      Nat.multinomial Finset.univ s := by
  have hsum :
      (∑ i : ι, GMC2.ChannelDilation.extendByZero face s i) =
        ∑ i : ↥face, s i := by
    simpa using
      (GMC2.ChannelDilation.sum_extendByZero face s
        (fun _ n ↦ n) (by simp))
  have hprod :
      (∏ i : ι, Nat.factorial
          (GMC2.ChannelDilation.extendByZero face s i)) =
        ∏ i : ↥face, Nat.factorial (s i) := by
    simpa using
      (GMC2.ChannelDilation.prod_extendByZero face s
        (fun _ n ↦ Nat.factorial n) (by simp))
  change
    Nat.factorial
          (∑ i : ι, GMC2.ChannelDilation.extendByZero face s i) /
        (∏ i : ι, Nat.factorial
          (GMC2.ChannelDilation.extendByZero face s i)) =
      Nat.factorial (∑ i : ↥face, s i) /
        ∏ i : ↥face, Nat.factorial (s i)
  rw [hsum, hprod]

/-- Evaluating the face constant-term polynomial is literally the normalized
residue layer's `faceConstantTerm`, with no coefficient or index translation
left implicit. -/
theorem aeval_constantTermRelationInt_eq_faceConstantTerm
    [CommRing R] [Algebra ℤ R]
    (exponent : ι → Fin 2 →₀ ℕ) (coefficient : ι → R)
    (face : Finset ι) (m0 : ℕ) :
    MvPolynomial.aeval (fun i : ↥face ↦ coefficient i)
        (GMC2.IntegralRelations.constantTermRelationInt
          (fun i : ↥face ↦ GMC2.charge (exponent i)) m0) =
      GMC2.NormalizedResidue.faceConstantTerm
        exponent coefficient face m0 := by
  rw [GMC2.IntegralRelations.aeval_constantTermRelationInt]
  rw [GMC2.NormalizedResidue.faceConstantTerm,
    GMC2.NormalizedResidue.balancedFaceChannels, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  have hbalanced :=
    isBalanced_extendByZero_iff_totalCharge_zero exponent face s
  by_cases hcharge :
      GMC2.ConstantTermRelations.totalCharge
        (fun i : ↥face ↦ GMC2.charge (exponent i)) s = 0
  · have hb := hbalanced.mpr hcharge
    simp only [if_pos hcharge, if_pos hb]
    rw [multinomial_extendByZero]
    rfl
  · have hb : ¬ GMC2.NormalizedMoment.IsBalanced exponent
        (GMC2.ChannelDilation.extendByZero face s) :=
      fun h ↦ hcharge (hbalanced.mp h)
    simp only [if_neg hcharge, if_neg hb]

end FaceConstantTerm

/-- Exact finite-field seed input: the lifted geometric face seed evaluates
to the precise `faceConstantTerm` consumed by normalized residue assembly. -/
theorem aeval_liftedFaceSeedInt_eq_faceConstantTerm
    {R : Type*} [CommRing R] [Algebra ℤ R]
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (hsubset : F ⊆ P.support) (m0 : ℕ)
    (coefficient : ↥P.support → R) :
    MvPolynomial.aeval coefficient
        (GMC2.IntegralFaceSeedDescent.liftedFaceSeedInt P F hsubset m0) =
      GMC2.NormalizedResidue.faceConstantTerm
        (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ))
        coefficient (supportFace P F) m0 := by
  rw [aeval_liftedFaceSeedInt_eq_supportFace]
  exact aeval_constantTermRelationInt_eq_faceConstantTerm
    (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ))
    coefficient (supportFace P F) m0

/-- Balance of an exact-support Wick channel gives rational total charge
zero in the face-height dictionary. -/
theorem support_totalChargeQ_eq_zero_of_isBalanced
    (P : MvPolynomial (Fin 2) ℂ) (r : ↥P.support → ℕ)
    (hbalanced : GMC2.NormalizedMoment.IsBalanced
      (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r) :
    GMC2.FrobeniusFace.totalChargeQ
        (fun s : ↥P.support ↦ GMC2.FaceDictionary.exponentA s)
        (fun s : ↥P.support ↦ GMC2.FaceDictionary.exponentB s)
        Finset.univ r = 0 := by
  rw [GMC2.FaceReferenceChannel.face_totalChargeQ_eq_cast_totalCharge]
  rw [(isBalanced_iff_totalCharge_zero
    (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r).1 hbalanced]
  simp

/-- The geometric lower-face inequality transported to exact-support
indices. -/
theorem support_tiltedHeight_lower
    (P : MvPolynomial (Fin 2) ℂ) (lambda delta : ℚ)
    (hlower : ∀ s ∈ P.support,
      delta ≤ GMC2.radialExponentQ s - lambda * GMC2.chargeQ s) :
    ∀ i ∈ (Finset.univ : Finset ↥P.support),
      delta ≤ GMC2.FrobeniusFace.tiltedHeight
        (fun s : ↥P.support ↦ GMC2.FaceDictionary.exponentA s)
        (fun s : ↥P.support ↦ GMC2.FaceDictionary.exponentB s)
        lambda i := by
  intro i hi
  simpa [GMC2.FrobeniusFace.tiltedHeight, GMC2.FrobeniusFace.charge,
      GMC2.FaceDictionary.exponentA, GMC2.FaceDictionary.exponentB,
      GMC2.radialExponentQ, GMC2.chargeQ, GMC2.charge] using hlower i i.property

/-- The exact equality locus of the supporting line is precisely
`supportFace P F`. -/
theorem mem_supportFace_iff_tiltedHeight_eq
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (lambda delta : ℚ)
    (hface : ∀ s, s ∈ F ↔ s ∈ P.support ∧
      GMC2.radialExponentQ s - lambda * GMC2.chargeQ s = delta)
    (i : ↥P.support) :
    i ∈ supportFace P F ↔
      GMC2.FrobeniusFace.tiltedHeight
        (fun s : ↥P.support ↦ GMC2.FaceDictionary.exponentA s)
        (fun s : ↥P.support ↦ GMC2.FaceDictionary.exponentB s)
        lambda i = delta := by
  rw [mem_supportFace]
  constructor
  · intro hi
    simpa [GMC2.FrobeniusFace.tiltedHeight, GMC2.FrobeniusFace.charge,
      GMC2.FaceDictionary.exponentA, GMC2.FaceDictionary.exponentB,
      GMC2.radialExponentQ, GMC2.chargeQ, GMC2.charge] using (hface i).1 hi |>.2
  · intro hi
    apply (hface i).2
    refine ⟨i.property, ?_⟩
    simpa [GMC2.FrobeniusFace.tiltedHeight, GMC2.FrobeniusFace.charge,
      GMC2.FaceDictionary.exponentA, GMC2.FaceDictionary.exponentB,
      GMC2.radialExponentQ, GMC2.chargeQ, GMC2.charge] using hi

section DilationSemantics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Dilation scales the accumulated exact bidegree. -/
theorem channelExponent_dilate
    (p : ℕ) (face : Finset ι) (s : ↥face → ℕ)
    (exponent : ι → Fin 2 →₀ ℕ) :
    GMC2.MomentRelations.channelExponent exponent
        (GMC2.ChannelDilation.dilate p face s) =
      p • GMC2.MomentRelations.channelExponent
        (fun i : ↥face ↦ exponent i) s := by
  simpa only [GMC2.MomentRelations.channelExponent] using
    GMC2.ChannelDilation.accumulatedBidegree_dilate p face s exponent

/-- Semantic height scaling under dilation. -/
theorem channelHeight_dilate
    (p : ℕ) (face : Finset ι) (s : ↥face → ℕ)
    (exponent : ι → Fin 2 →₀ ℕ) :
    GMC2.NormalizedMoment.channelHeight exponent
        (GMC2.ChannelDilation.dilate p face s) =
      p * GMC2.NormalizedMoment.channelHeight
        (fun i : ↥face ↦ exponent i) s := by
  unfold GMC2.NormalizedMoment.channelHeight
  rw [channelExponent_dilate]
  simp

/-- For positive dilation, exact balance is preserved and reflected. -/
theorem isBalanced_dilate_iff
    {p : ℕ} (hp : 0 < p) (face : Finset ι) (s : ↥face → ℕ)
    (exponent : ι → Fin 2 →₀ ℕ) :
    GMC2.NormalizedMoment.IsBalanced exponent
        (GMC2.ChannelDilation.dilate p face s) ↔
      GMC2.NormalizedMoment.IsBalanced
        (fun i : ↥face ↦ exponent i) s := by
  unfold GMC2.NormalizedMoment.IsBalanced
  rw [channelExponent_dilate]
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro h
    simp [h]

end DilationSemantics

/-- The compact geometric interface consumed by normalized residue assembly.
It packages the scaled floor on all balanced channels, exact base height on
face-supported channels, and the unit gap for channels meeting the complement
of the face. -/
structure ReferenceHeightObligations
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (m0 A0 : ℕ) : Prop where
  scaledFullFloor : ∀ p : ℕ, ∀ r : ↥P.support → ℕ,
    r ∈ Finset.piAntidiag (Finset.univ : Finset ↥P.support) (p * m0) →
    GMC2.NormalizedMoment.IsBalanced
      (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r →
    p * A0 ≤ GMC2.NormalizedMoment.channelHeight
      (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r
  faceBaseHeight : ∀ r : ↥P.support → ℕ,
    r ∈ Finset.piAntidiag (Finset.univ : Finset ↥P.support) m0 →
    GMC2.NormalizedMoment.IsBalanced
      (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r →
    (∀ i, r i ≠ 0 → i ∈ supportFace P F) →
    GMC2.NormalizedMoment.channelHeight
      (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r = A0
  offFaceGap : ∀ r : ↥P.support → ℕ,
    r ∈ Finset.piAntidiag (Finset.univ : Finset ↥P.support) m0 →
    GMC2.NormalizedMoment.IsBalanced
      (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r →
    (∃ i, r i ≠ 0 ∧ i ∉ supportFace P F) →
    A0 + 1 ≤ GMC2.NormalizedMoment.channelHeight
      (fun s : ↥P.support ↦ (s : Fin 2 →₀ ℕ)) r

/-- The three height obligations needed by normalized residue assembly:
the global scaled floor, equality for base channels supported on the face,
and the strict integral gap for base channels using an off-face point. -/
theorem normalized_height_obligations_of_face_reference
    (P : MvPolynomial (Fin 2) ℂ) (F : Finset (Fin 2 →₀ ℕ))
    (lambda delta : ℚ) (m0 A0 : ℕ) (r0 : ↥F → ℕ)
    (hlower : ∀ s ∈ P.support,
      delta ≤ GMC2.radialExponentQ s - lambda * GMC2.chargeQ s)
    (hface : ∀ s, s ∈ F ↔ s ∈ P.support ∧
      GMC2.radialExponentQ s - lambda * GMC2.chargeQ s = delta)
    (hrefBalanced : GMC2.FrobeniusFace.totalChargeQ
      (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
      (fun s : ↥F ↦ GMC2.FaceDictionary.exponentB s)
      Finset.univ r0 = 0)
    (hrefMass : GMC2.FaceHeightFloor.channelMass Finset.univ r0 = m0)
    (hrefHeight : GMC2.FrobeniusFace.radialHeightQ
      (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
      Finset.univ r0 = (A0 : ℚ)) :
    ReferenceHeightObligations P F m0 A0 := by
  let exponentP : ↥P.support → Fin 2 →₀ ℕ := fun s ↦ s
  let aP : ↥P.support → ℤ := fun s ↦ GMC2.FaceDictionary.exponentA s
  let bP : ↥P.support → ℤ := fun s ↦ GMC2.FaceDictionary.exponentB s
  have hrefSupport : ∀ i ∈ (Finset.univ : Finset ↥F), r0 i ≠ 0 →
      GMC2.FrobeniusFace.tiltedHeight
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
        (fun s : ↥F ↦ GMC2.FaceDictionary.exponentB s)
        lambda i = delta := by
    intro i hi hri
    have hiFace := (hface i).1 i.property
    simpa [GMC2.FrobeniusFace.tiltedHeight, GMC2.FrobeniusFace.charge,
      GMC2.FaceDictionary.exponentA, GMC2.FaceDictionary.exponentB,
      GMC2.radialExponentQ, GMC2.chargeQ, GMC2.charge] using hiFace.2
  have hrefFloor := GMC2.FaceHeightFloor.balanced_radialHeight_eq_floor_of_mass
    (fun s : ↥F ↦ GMC2.FaceDictionary.exponentA s)
    (fun s : ↥F ↦ GMC2.FaceDictionary.exponentB s)
    lambda delta Finset.univ r0 m0 hrefSupport hrefBalanced hrefMass
  have hrefQ : (A0 : ℚ) = (m0 : ℚ) * delta := by
    rw [← hrefHeight]
    exact hrefFloor
  have hlowerP : ∀ i ∈ (Finset.univ : Finset ↥P.support),
      delta ≤ GMC2.FrobeniusFace.tiltedHeight aP bP lambda i := by
    simpa only [aP, bP] using support_tiltedHeight_lower P lambda delta hlower
  have hradial : ∀ r : ↥P.support → ℕ,
      GMC2.FrobeniusFace.radialHeightQ aP Finset.univ r =
        (GMC2.NormalizedMoment.channelHeight exponentP r : ℚ) := by
    intro r
    simpa only [aP, exponentP] using
      GMC2.FaceReferenceChannel.face_radialHeightQ_eq_cast_channelHeight P.support r
  have hbalancedQ : ∀ r : ↥P.support → ℕ,
      GMC2.NormalizedMoment.IsBalanced exponentP r →
      GMC2.FrobeniusFace.totalChargeQ aP bP Finset.univ r = 0 := by
    intro r hr
    simpa only [aP, bP, exponentP] using
      support_totalChargeQ_eq_zero_of_isBalanced P r hr
  refine ⟨?_, ?_, ?_⟩
  · intro p r hr hbal
    have hmass := channelMass_eq_of_mem_piAntidiag r (p * m0) hr
    have hfloor := GMC2.FaceHeightFloor.balanced_radialHeight_floor_of_mass
      aP bP lambda delta Finset.univ r (p * m0) hlowerP
      (hbalancedQ r hbal) hmass
    rw [hradial r] at hfloor
    have hcast : ((p * A0 : ℕ) : ℚ) ≤
        (GMC2.NormalizedMoment.channelHeight exponentP r : ℚ) := by
      calc
        ((p * A0 : ℕ) : ℚ) = (p : ℚ) * (A0 : ℚ) := by norm_num
        _ = (p : ℚ) * ((m0 : ℚ) * delta) := by rw [hrefQ]
        _ = ((p * m0 : ℕ) : ℚ) * delta := by
          push_cast
          ring
        _ ≤ (GMC2.NormalizedMoment.channelHeight exponentP r : ℚ) := hfloor
    exact_mod_cast hcast
  · intro r hr hbal hsupported
    have hmass := channelMass_eq_of_mem_piAntidiag r m0 hr
    have hsuppHeight : ∀ i ∈ (Finset.univ : Finset ↥P.support), r i ≠ 0 →
        GMC2.FrobeniusFace.tiltedHeight aP bP lambda i = delta := by
      intro i hi hri
      have hiFace := hsupported i hri
      simpa only [aP, bP] using
        (mem_supportFace_iff_tiltedHeight_eq P F lambda delta hface i).1 hiFace
    have heq := GMC2.FaceHeightFloor.balanced_radialHeight_eq_floor_of_mass
      aP bP lambda delta Finset.univ r m0 hsuppHeight
      (hbalancedQ r hbal) hmass
    rw [hradial r] at heq
    have hcast :
        (GMC2.NormalizedMoment.channelHeight exponentP r : ℚ) = (A0 : ℚ) := by
      rw [heq, hrefQ]
    exact_mod_cast hcast
  · intro r hr hbal hoff
    obtain ⟨j, hrj, hjFace⟩ := hoff
    have hmass := channelMass_eq_of_mem_piAntidiag r m0 hr
    have hjNe : GMC2.FrobeniusFace.tiltedHeight aP bP lambda j ≠ delta := by
      intro hjEq
      apply hjFace
      exact (mem_supportFace_iff_tiltedHeight_eq P F lambda delta hface j).2
        (by simpa only [aP, bP] using hjEq)
    have hjStrict : delta < GMC2.FrobeniusFace.tiltedHeight aP bP lambda j :=
      lt_of_le_of_ne (hlowerP j (Finset.mem_univ j)) (Ne.symm hjNe)
    have hoffStrict := GMC2.FrobeniusFace.balanced_height_strict_of_off_face
      aP bP lambda delta Finset.univ r hlowerP (hbalancedQ r hbal)
      j (Finset.mem_univ j) (Nat.pos_of_ne_zero hrj) hjStrict
    have hstrictQ : (A0 : ℚ) <
        (GMC2.NormalizedMoment.channelHeight exponentP r : ℚ) := by
      calc
        (A0 : ℚ) = (m0 : ℚ) * delta := hrefQ
        _ = delta * GMC2.FrobeniusFace.massQ Finset.univ r := by
          rw [GMC2.FaceHeightFloor.massQ_eq_natCast_channelMass, hmass]
          ring
        _ < GMC2.FrobeniusFace.radialHeightQ aP Finset.univ r := hoffStrict
        _ = (GMC2.NormalizedMoment.channelHeight exponentP r : ℚ) := hradial r
    have hstrictNat : A0 < GMC2.NormalizedMoment.channelHeight exponentP r := by
      exact_mod_cast hstrictQ
    have : A0 + 1 ≤ GMC2.NormalizedMoment.channelHeight exponentP r := by
      omega
    simpa only [exponentP] using this

end

end GMC2.SupportFaceBridge

