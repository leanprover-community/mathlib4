/-
Copyright (c) 2024 Nir Paz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nir Paz
-/
import Mathlib.SetTheory.Cardinal.Cofinality


/-!
# Club and stationary sets
This file sets up the basic theory of clubs (closed and unbounded sets) and stationary sets.

## Main definitions
* `IsClosed`: A set of ordinals is closed in `o` if all of its elements are
  less than `o` and it contains all of its accumulation points below `o`.
* `IsClub`: A set of ordinals is a club in `o` if it is closed in `o` and unbounded in `o`.

## Main results
* `isClub_sInter`: The intersection of fewer than `o.cof` clubs in `o` is a club in `o`.
-/

noncomputable section

open Classical Cardinal Set Order

universe u

namespace Ordinal

/-- A set of ordinals is unbounded in an ordinal if it
  is a subset of it and it is an unbounded set in it. -/
def IsUnbounded (S : Set Ordinal) (o : Ordinal) : Prop :=
  S ⊆ (Iio o) ∧ (∀ p < o, ∃ s ∈ S, p < s)

/-- A positive ordinal is an accumulation point of a set of ordinals if there
  are elements in the set arbitrarily close to the ordinal from below. -/
def IsAcc (o : Ordinal) (S : Set Ordinal) : Prop :=
  0 < o ∧ (∀ p < o, ∃ s ∈ S, s < o ∧ p < s)

/-- A set of ordinals is closed in an ordinals if it is a subset of it
  and it contains all of its accumulation points below the ordinal. -/
def IsClosed (S : Set Ordinal) (o : Ordinal) : Prop :=
  S ⊆ (Iio o) ∧ (∀ p < o, IsAcc p S → p ∈ S)

/-- A set of ordinals is a club in an ordinal if it is closed and unbounded in it. -/
def IsClub (S : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosed S o ∧ IsUnbounded S o

theorem isAcc_of_subset {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAcc S) :
    o.IsAcc T := ⟨ho.1, fun p plto ↦ (ho.2 p plto).casesOn fun s hs ↦ ⟨s, h hs.1, hs.2⟩⟩

theorem isLimit_of_isUnbounded {o : Ordinal} {U} (h : IsUnbounded U o)
    (ho : o ≠ 0) : IsLimit o := by
  refine' isLimit_of_not_succ_of_ne_zero (fun ⟨x, hx⟩ ↦ _) ho
  rcases h.2 x (hx ▸ lt_succ x) with ⟨p, hp⟩
  exact (hx ▸ succ_le_iff.mpr hp.2).not_lt (h.1 hp.1)

theorem inter_suffix_of_isUnbounded {o : Ordinal} {U} (hU : IsUnbounded U o) {p : Ordinal}
    (hp : p < o) : (U ∩ (Ioo p o)).Nonempty :=
  (hU.2 p hp).casesOn (fun x ⟨xmemU, pltx⟩ ↦ ⟨x, xmemU, ⟨pltx, hU.1 xmemU⟩⟩)


section ClubIntersection

variable {o : Ordinal.{u}} {S : Set (Set Ordinal)}

theorem isClosed_sInter_of_isClosed (hS : S.Nonempty) (h : ∀ C ∈ S, IsClosed C o) :
    IsClosed (⋂₀ S) o :=
  ⟨fun s hs ↦ by
    rcases hS with ⟨C, CmemS⟩
    exact (h C CmemS).1 ((sInter_subset_of_mem CmemS) hs),
  fun p plto pAcc ↦ by
    rw [mem_sInter]
    intro C CmemS
    exact (h C CmemS).2 p plto (isAcc_of_subset (sInter_subset_of_mem CmemS) pAcc)⟩

/-- Given less than `o.cof` unbounded sets in `o` and some `q < o`, there is a `q < p < o`
  such that `Ioo q p` contains an element of every unbounded set. -/
theorem exists_above_of_lt_cof {p : Ordinal} (hp : p < o) (hSemp : Nonempty S)
    (hSunb : ∀ U ∈ S, IsUnbounded U o) (hScard : #S < Cardinal.lift.{u + 1, u} o.cof) :
    ∃ q, q < o ∧ p < q ∧ (∀ U ∈ S, (U ∩ Ioo p q).Nonempty) := by
  rw [lift_cof] at hScard
  have oLim : IsLimit o := hSemp.casesOn fun ⟨T, hT⟩ ↦ isLimit_of_isUnbounded
    (hSunb T hT) (pos_of_gt hp).ne.symm
  let f : ↑S → Ordinal := fun U ↦ lift.{u + 1, u} (sInf (U ∩ (Ioo p o)))
  have infMem : ∀ U : S, sInf (↑U ∩ Ioo p o) ∈ ↑U ∩ Ioo p o := fun U ↦
    csInf_mem (inter_suffix_of_isUnbounded (hSunb U.1 U.2) hp : (↑U ∩ Ioo p o).Nonempty)
  have flto : ∀ U : S, f U < lift.{u + 1, u} o := fun U ↦ by
    simp_all only [mem_inter_iff, mem_Ioo, lift_lt, f]
  set q := (Ordinal.sup.{u + 1, u} f) + 1 with qdef
  have qlto : q < lift.{u + 1, u} o :=
    ((lift_isLimit.{u + 1, u} o).mpr oLim).2 (sup.{u + 1, u} f) (sup_lt_ord hScard flto)
  rcases lift_down qlto.le with ⟨q', hq'⟩
  use q'
  have fltq : ∀ U, f U < q := fun U ↦
    lt_of_le_of_lt (le_sup.{u + 1, u} f U) (qdef ▸ lt_add_one (sup f))
  constructor <;> try constructor
  · exact lift_lt.mp (hq' ▸ qlto)
  · rcases hSemp with ⟨U, hU⟩
    have pltf : lift.{u + 1, u} p < f ⟨U, hU⟩ :=
      lift_lt.mpr (mem_of_mem_inter_right (infMem ⟨U, hU⟩)).1
    have := lt_of_lt_of_le pltf (fltq ⟨U, hU⟩).le
    rwa [← hq', lift_lt] at this
  intro U hU
  specialize infMem ⟨U, hU⟩
  specialize fltq ⟨U, hU⟩
  have : f ⟨U, hU⟩ ∈ Ioo (lift.{u + 1, u} p) q := ⟨lift_lt.mpr infMem.2.1, fltq⟩
  rw [← hq'] at fltq
  rcases lift_down fltq.le with ⟨fUdown, fUlift⟩
  use fUdown
  constructor
  · simp_all only [lift_inj, mem_inter_iff, f]
  · constructor
    exact lift_lt.mp <| fUlift ▸ (this.1)
    exact lift_lt.mp <| hq' ▸ (fUlift ▸ this).2

/-- Given a limit ordinal `o` and a property on pairs of ordinals `P`, such that
  for any `p < o` there is a `q < o` above `p` so that `P p q`, we can construct
  an increasing `ω`-sequence below `o` that satisfies `P` between every 2 consecutive elements.
  Additionaly, the sequence can begin arbitrarily high in `o`. That is, above any `r < o`. -/
theorem exists_omega_seq_succ_prop (oLim : IsLimit o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p < o, ∃ q < o, (p < q ∧ P p q)) {r} (rlto : r < o) : ∃ f : Π p < ω, (Iio o),
    (∀ i : Ordinal.{u}, (hi : i < ω) → P (f i hi) (f (i + 1) (omega_isLimit.2 i hi)))
    ∧ (∀ i : Ordinal.{u}, (hi : i < ω) → f i hi < f (i + 1) (omega_isLimit.2 i hi))
    ∧ r < f 0 omega_pos := by
  let H₂ : (p : Ordinal) → p < ω → (Iio o) → (Iio o) := fun p _ fp ↦ by
    let C := choose (hP fp fp.2)
    have hC := (choose_spec (hP fp fp.2)).1
    exact ⟨C, hC⟩
  let H₃ : (w : Ordinal) → w < ω → w.IsLimit → ((o' : Ordinal) → o' < w → (Iio o)) → (Iio o) :=
    fun w _ _ _ ↦ ⟨0, oLim.pos⟩
  let f : Π p < ω, Iio o := @boundedLimitRec' (α := Iio o) ω omega_isLimit
    ⟨r + 1, oLim.succ_lt rlto⟩ H₂ H₃
  use f
  constructor <;> try constructor
  intro n hn
  · simp [f]
    generalize_proofs _ pf
    exact (choose_spec pf).2.2
  · intro i hi
    simp [f, H₂]
    generalize_proofs _ _ _ pf
    exact (choose_spec pf).casesOn fun _ x ↦ x.casesOn fun x _ ↦ x
  simp [f]

/-- If between every 2 consecutive elements of an increasing `δ`-sequence
  there is an element of `C`, and `δ` is a limit ordinal,
  then the supremum of the sequence is an accumulation point of `C`. -/
theorem isAcc_bsup_of_between {δ : Ordinal} (C : Set Ordinal) (δLim : δ.IsLimit)
    (s : Π o < δ, Ordinal) (sInc : ∀ o, (h : o < δ) → s o h < s (o + 1) (δLim.succ_lt h))
    (h : ∀ o, (h : o < δ) → (C ∩ Ioo (s o h) (s (o + 1) (δLim.succ_lt h))).Nonempty) :
    IsAcc (bsup δ s) C := by
  use (by
    apply (lt_bsup s).mpr
    exact ⟨0 + 1, δLim.nat_lt (0 + 1), pos_of_gt (sInc 0 δLim.pos)⟩)
  intro p pltsup
  rw [lt_bsup] at pltsup
  rcases pltsup with ⟨i, hi, plt⟩
  rcases h i hi with ⟨q, qmemC, qmemIoo⟩
  use q; use qmemC
  exact ⟨lt_of_lt_of_le qmemIoo.2 (le_bsup _ _ _), plt.trans qmemIoo.1⟩

/-- The intersection of less than `o.cof` clubs in `o` is a club in `o`. -/
theorem isClub_sInter (hCof : ℵ₀ < o.cof) (hS : ∀ C ∈ S, IsClub C o) (hSemp : S.Nonempty)
    (Scard : #S < Cardinal.lift.{u + 1, u} o.cof) : IsClub (⋂₀ S) o := by
  refine' ⟨isClosed_sInter_of_isClosed hSemp (fun C CmemS ↦ (hS C CmemS).1), _⟩
  refine' ⟨fun x xmem ↦ hSemp.casesOn fun C CmemS ↦ (hS C CmemS).1.1 (xmem C CmemS), _⟩
  intro q qlto
  have oLim : IsLimit o := aleph0_le_cof.mp hCof.le
  have nonemptyS : Nonempty S := Nonempty.to_subtype hSemp
  let P : Ordinal → Ordinal → Prop := fun p q ↦ ∀ C ∈ S, (C ∩ Ioo p q).Nonempty
  have auxP : ∀ p < o, ∃ q < o, p < q ∧ P p q := fun p plto ↦
    exists_above_of_lt_cof plto nonemptyS (fun U hU ↦ (hS U hU).2) Scard
  rcases exists_omega_seq_succ_prop oLim auxP qlto with ⟨f, hf⟩
  let g := fun p pltω ↦ (f p pltω).1
  have gInc : ∀ o h, g o h < g (o + 1) (omega_isLimit.succ_lt h) := fun o h ↦ hf.2.1 o h
  have bsuplt : bsup ω g < o := (bsup_lt_ord hCof) (fun i hi ↦ (f i hi).2)
  use bsup ω g
  constructor
  · apply mem_sInter.mpr
    intro C CmemS
    have := isAcc_bsup_of_between C omega_isLimit g gInc (fun i hi ↦ (hf.1 i hi) C CmemS)
    exact (hS C CmemS).1.2 ((bsup ω g)) bsuplt this
  exact (lt_bsup g).mpr ⟨0, omega_pos, hf.2.2⟩

end ClubIntersection
