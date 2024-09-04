/-
Copyright (c) 2024 Nir Paz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nir Paz
-/
--import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Cardinal.Cofinality

/-!
# Club and stationary sets

This file sets up the basic theory of clubs (closed and unbounded sets) and stationary sets.

## Main definitions

* `Ordinal.IsClosed`: A set of ordinals `S` is closed in `o` if `S ⊆ Iio o`
  and `S` contains every `x < o` such that `x.IsAcc S`.
* `Ordinal.IsClub`: A set of ordinals `S` is a club in `o` if
  it is closed in `o` and unbounded in `o`.

## Main results

* `isClub_sInter`: The intersection of fewer than `o.cof` clubs in `o` is a club in `o`.
-/

noncomputable section

open Classical Cardinal Set Order

universe u v

namespace Ordinal

/-- A positive ordinal is an accumulation point of a set of ordinals if there
are elements in the set arbitrarily close to the ordinal from below. -/
def IsAcc (o : Ordinal) (S : Set Ordinal) : Prop :=
  o ≠ 0 ∧ ∀ p < o, ∃ s ∈ S, p < s ∧ s < o

/-- A set of ordinals is closed in an ordinal if it contains all of
its accumulation points below the ordinal. -/
def IsClosed (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ p < o, IsAcc p S → p ∈ S

/-- A set of ordinals is a club in an ordinal if it is closed and unbounded in it. -/
def IsClub (S : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosed S o ∧ IsAcc o S

theorem IsAcc.subset {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAcc S) :
    o.IsAcc T := ⟨ho.1, fun p plto ↦ (ho.2 p plto).casesOn fun s hs ↦ ⟨s, h hs.1, hs.2⟩⟩

theorem IsAcc.isLimit {o : Ordinal} {U : Set Ordinal} (h : o.IsAcc U) : IsLimit o := by
  refine' isLimit_of_not_succ_of_ne_zero (fun ⟨x, hx⟩ ↦ _) h.1
  rcases h.2 x (lt_of_lt_of_le (lt_succ x) hx.symm.le) with ⟨p, hp⟩
  exact (hx.symm ▸ (succ_le_iff.mpr hp.2.1)).not_lt hp.2.2

theorem IsAcc.inter_Ioo_nonempty {o : Ordinal} {U : Set Ordinal} (hU : o.IsAcc U)
    {p : Ordinal} (hp : p < o) : (U ∩ Ioo p o).Nonempty := by
  rcases hU.2 p hp with ⟨q, hq⟩
  exact ⟨q, hq.1, hq.2.1, hq.2.2⟩

section ClubIntersection

variable {o : Ordinal.{u}} {S : Set (Set Ordinal)}
variable {ι : Type u} {f : ι → Set Ordinal}

theorem IsClosed.sInter (h : ∀ C ∈ S, IsClosed C o) : IsClosed (⋂₀ S) o :=
  fun p plto pAcc C CmemS ↦ (h C CmemS) p plto (pAcc.subset (sInter_subset_of_mem CmemS))

theorem IsClosed.iInter (h : ∀ i, IsClosed (f i) o) : IsClosed (⋂ i, f i) o := by
  have := IsClosed.sInter (fun C (⟨i, fieqC⟩ : C ∈ range f) ↦ fieqC ▸ (h i))
  change IsClosed (⋂₀ (range f)) o at this
  rwa [sInter_range] at this

/-- Given less than `o.cof` unbounded sets in `o` and some `q < o`, there is a `q < p < o`
  such that `Ioo q p` contains an element of every unbounded set. -/
theorem exists_above_of_lt_cof {p : Ordinal} (h : p < o) (hSemp : Nonempty S)
    (hSacc : ∀ U ∈ S, o.IsAcc U) (hScard : #S < Cardinal.lift.{u + 1, u} o.cof) :
    ∃ q < o, p < q ∧ ∀ U ∈ S, (U ∩ Ioo p q).Nonempty := by
  rw [lift_cof] at hScard
  have oLim : IsLimit o := hSemp.casesOn fun ⟨T, hT⟩ ↦ (hSacc T hT).isLimit
  let f : ↑S → Ordinal := fun U ↦ lift.{u + 1, u} (sInf (U ∩ (Ioo p o)))
  have infMem : ∀ U : S, sInf (↑U ∩ Ioo p o) ∈ ↑U ∩ Ioo p o := fun U ↦
    csInf_mem ((hSacc U.1 U.2).inter_Ioo_nonempty h : (↑U ∩ Ioo p o).Nonempty)
  have flto : ∀ U : S, f U < lift.{u + 1, u} o := fun U ↦ by
    simp_all only [mem_inter_iff, mem_Ioo, lift_lt, f]
  set q := (Ordinal.sup.{u + 1, u} f) + 1 with qdef
  have qlto : q < lift.{u + 1, u} o :=
    ((lift_isLimit.{u + 1, u} o).mpr oLim).2 (sup.{u + 1, u} f) (sup_lt_ord hScard flto)
  rcases lift_down qlto.le with ⟨q', hq'⟩
  use q', lift_lt.mp (hq' ▸ qlto)
  have fltq : ∀ U, f U < q := fun U ↦
    lt_of_le_of_lt (le_sup.{u + 1, u} f U) (qdef ▸ lt_add_one (sup f))
  constructor <;> try constructor
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
    exact lift_lt.mp (hq'.symm ▸ (fUlift ▸ this).2)

theorem strictMono_of_succ_lt_omega (f : Iio ω → Iio o)
    (hf : ∀ i, f i < f ⟨i + 1, omega_isLimit.succ_lt i.2⟩) (i j) (h : i < j) : f i < f j := by
  have mono := strictMono_nat_of_lt_succ fun n ↦ hf ⟨n, nat_lt_omega n⟩
  have := @mono (relIso_nat_omega.symm i) (relIso_nat_omega.symm j)
    ((OrderIso.lt_iff_lt relIso_nat_omega.symm).mpr h)
  simp at this
  rw [(rfl : i = ⟨i.1, i.2⟩)] at this
  change f ⟨↑(relIso_nat_omega.symm ⟨i.1, i.2⟩), _⟩ <
    f ⟨↑(relIso_nat_omega.symm ⟨j.1, j.2⟩), _⟩ at this
  simp_rw [relIso_nat_omega.symm_eq] at this
  exact this

/--
Given a limit ordinal `o` and a property on pairs of ordinals `P`, such that
for any `p < o` there is a `q < o` above `p` so that `P p q`, we can construct
an increasing `ω`-sequence below `o` that satisfies `P` between every 2 consecutive elements.
Additionaly, the sequence can begin arbitrarily high in `o`. That is, above any `r < o`.
-/
theorem exists_omega_seq_succ_prop (opos : 0 < o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p : Iio o, ∃ q, (p < q ∧ P p q)) (r : Iio o) : ∃ f : (Iio ω) → Iio o,
    (∀ i, P (f i) (f ⟨i + 1, omega_isLimit.2 i i.2⟩)) ∧ (∀ i j, (i < j) → f i < f j)
    ∧ r < f ⟨0, omega_pos⟩ := by
  have oLim : o.IsLimit := ⟨opos.ne.symm, fun a alto ↦ (hP ⟨a, alto⟩).casesOn fun r hr ↦
    lt_of_le_of_lt (succ_le_of_lt hr.1) r.2⟩
  let H₂ : (p : Iio ω) → (Iio o) → (Iio o) := λ _ fp ↦ choose (hP fp)
  let H₃ : (w : Iio ω) → IsLimit w → ((o' : Iio ω) → o' < w → (Iio o)) → (Iio o) :=
    fun w _ _ ↦ ⟨0, oLim.pos⟩
  let f : Iio ω → Iio o := @boundedLimitRec' (α := Iio o) ω omega_isLimit
    ⟨r + 1, oLim.succ_lt r.2⟩ H₂ H₃
  use f
  constructor <;> try constructor
  · intro n
    simp [f, H₂]
    generalize_proofs _ pf
    exact (choose_spec pf).2
  · have aux : ∀ i, f i < f ⟨i + 1, omega_isLimit.2 i i.2⟩ := fun i ↦ by
      simp [f, H₂]
      generalize_proofs _ pf
      exact (choose_spec pf).casesOn fun h _ ↦ h
    exact strictMono_of_succ_lt_omega f aux
  simp [f]
  exact lt_succ r.1

theorem exists_omega_seq_succ_prop_pos (onelto : 1 < o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p : Iio o, 0 < p.1 → ∃ q : Iio o, (p < q ∧ P p q)) (r : Iio o) :
    ∃ f : (Iio ω : Set Ordinal.{0}) → (Iio o), (∀ i, P (f i) (f ⟨i + 1, omega_isLimit.2 i i.2⟩))
    ∧ (∀ i j, (i < j) → f i < f j) ∧ r < f ⟨0, omega_pos⟩ := by
  let P' : Ordinal → Ordinal → Prop := fun p q ↦ p = 0 ∨ P p q
  have hP' : ∀ p : Iio o, ∃ q : Iio o, (p < q ∧ P' p q) := fun p ↦ by
    by_cases h : p.1 = 0
    · use ⟨1, onelto⟩
      use (by change p.1 < 1; exact h ▸ zero_lt_one)
      exact Or.inl h
    convert hP p (Ordinal.pos_iff_ne_zero.mpr h) using 1
    simp_all only [false_or, P']
  rcases exists_omega_seq_succ_prop (zero_lt_one.trans onelto) hP' r with ⟨f, hf⟩
  use f
  refine' ⟨fun i ↦ _, hf.2⟩
  have := hf.1 i
  have rltf0 := hf.2.2
  by_cases hi' : i.1 = 0
  · refine this.resolve_left ?_
    convert (pos_of_gt' rltf0 : (0 : Ordinal) < _).ne.symm
  · refine this.resolve_left ?_
    have aux' : (0 : Ordinal) < _ := pos_of_gt' (hf.2.1 ⟨0, omega_pos⟩ i
      (Ordinal.pos_iff_ne_zero.mpr hi'))
    exact aux'.ne.symm

/-- If between every 2 consecutive elements of a weakly increasing `δ`-sequence
  there is an element of `C`, and `δ` is a limit ordinal,
  then the supremum of the sequence is an accumulation point of `C`. -/
theorem isAcc_bsup_of_between {δ : Ordinal.{u}} (C : Set Ordinal) (δLim : δ.IsLimit)
    (s : Iio δ → Ordinal.{u}) (sInc : ∀ o, s o < s ⟨o + 1, δLim.succ_lt o.2⟩)
    (h : ∀ o, (C ∩ (Ioo (s o) (s ⟨o + 1, δLim.succ_lt o.2⟩))).Nonempty) :
    IsAcc (iSup s) C := by
  let g : Π o < δ, Ordinal := fun i hi ↦ s ⟨i, hi⟩
  rw [iSup_eq_bsup δLim.pos.ne s]
  use (by
    apply Ordinal.pos_iff_ne_zero.mp; apply (lt_bsup g).mpr
    exact ⟨0 + 1, δLim.nat_lt (0 + 1), pos_of_gt' (sInc ⟨0, δLim.pos⟩)⟩)
  intro p pltsup
  rw [lt_bsup] at pltsup
  rcases pltsup with ⟨i, hi, plt⟩
  rcases h ⟨i, hi⟩ with ⟨q, qmemC, qmemIoo⟩
  use q; use qmemC
  exact ⟨plt.trans qmemIoo.1, lt_of_lt_of_le qmemIoo.2 (le_bsup _ _ _)⟩

/--
The intersection of less than `o.cof` clubs in `o` is a club in `o`.
-/
theorem IsClub.sInter (hCof : ℵ₀ < o.cof) (hS : ∀ C ∈ S, IsClub C o) (hSemp : S.Nonempty)
    (Scard : #S < Cardinal.lift.{u + 1, u} o.cof) : IsClub (⋂₀ S) o := by
  refine' ⟨IsClosed.sInter (fun C CmemS ↦ (hS C CmemS).1), _⟩
  use (aleph0_le_cof.mp hCof.le).pos.ne.symm
  intro q qlto
  have oLim : IsLimit o := aleph0_le_cof.mp hCof.le
  have nonemptyS : Nonempty S := Nonempty.to_subtype hSemp
  let P : Ordinal → Ordinal → Prop := fun p q ↦ ∀ C ∈ S, (C ∩ Ioo p q).Nonempty
  have auxP : ∀ p : Iio o, ∃ q, p < q ∧ P p q := fun p ↦ by
    rcases exists_above_of_lt_cof p.2 nonemptyS (fun U hU ↦ (hS U hU).2) Scard with ⟨q, hq⟩
    use ⟨q, hq.1⟩, hq.2.1, hq.2.2
  rcases exists_omega_seq_succ_prop oLim.pos auxP ⟨q, qlto⟩ with ⟨f, hf⟩
  let g : Π p < ω, Ordinal := fun p pltω ↦ (f ⟨p, pltω⟩).1
  have gInc : ∀ o h, g o h < g (o + 1) (omega_isLimit.succ_lt h) := fun o h ↦
    hf.2.1 ⟨o, h⟩ ⟨o + 1, omega_isLimit.succ_lt h⟩ (lt_succ o)
  have bsuplt : bsup ω g < o := (bsup_lt_ord hCof) (fun i hi ↦ (f ⟨i, hi⟩).2)
  use bsup ω g
  constructor
  · apply mem_sInter.mpr
    intro C CmemS
    have := isAcc_bsup_of_between C omega_isLimit (fun x ↦ (f x).1)
      (fun o ↦ gInc o.1 o.2) (fun i ↦ (hf.1 i) C CmemS)
    rw [iSup_eq_bsup omega_ne_zero.symm] at this
    exact (hS C CmemS).1 ((bsup ω g)) bsuplt this
  exact ⟨(lt_bsup g).mpr ⟨0, omega_pos, hf.2.2⟩, bsuplt⟩

theorem isClub_iInter [Nonempty ι] (hCof : ℵ₀ < o.cof) (hf : ∀ i, IsClub (f i) o)
    (ιCard : #ι < o.cof) : IsClub (⋂ i, f i) o := by
  let f' : ULift.{u + 1, u} ι → Set Ordinal.{u} := fun ⟨i⟩ ↦ f i
  have rangelt : #(range f') < Cardinal.lift.{u + 1, u} o.cof :=
    lt_of_le_of_lt (@mk_range_le _ _ f') ((mk_uLift _) ▸ (Cardinal.lift_lt.mpr ιCard))
  have clubRange : ∀ C ∈ (range f'), IsClub C o := fun C ⟨⟨i⟩, hi⟩ ↦ hi ▸ hf i
  have intClub := IsClub.sInter hCof clubRange (range_nonempty f') rangelt
  rw [sInter_range] at intClub
  convert intClub
  have : range f = range f' :=
    Set.ext fun x ↦ ⟨fun ⟨i, hi⟩ ↦ ⟨⟨i⟩, hi⟩, fun ⟨⟨i⟩, hi⟩ ↦ ⟨i, hi⟩⟩
  unfold iInter iInf; rw [this]

end ClubIntersection
