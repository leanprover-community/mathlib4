/-
Copyright (c) 2024 Nir Paz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nir Paz
-/
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.Topology

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

open Classical Cardinal Set Order Filter

universe u v

namespace Ordinal

instance {o : Ordinal.{u}} : Small.{max u v} (Iio o) := small_lift (Iio o)

/-- A set of ordinals is a club below an ordinal if it is closed and unbounded in it. -/
def IsClub (C : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosedBelow C o ∧ IsAcc o C

theorem isClub_iff {C : Set Ordinal} {o : Ordinal} : IsClub C o
    ↔ ((∀ p < o, IsAcc p C → p ∈ C) ∧ (o ≠ 0 ∧ ∀ p < o, (C ∩ Ioo p o).Nonempty)) :=
  and_congr isClosedBelow_iff isAcc_iff

section ClubIntersection

variable {o : Ordinal.{u}} {S : Set (Set Ordinal)}
variable {ι : Type u} {f : ι → Set Ordinal}

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
  set q := (iSup f) + 1 with qdef
  have qlto : q < lift.{u + 1, u} o :=
    ((lift_isLimit.{u + 1, u} o).mpr oLim).2 (iSup f) (iSup_lt_ord hScard flto)
  rcases mem_range_lift_of_le qlto.le with ⟨q', hq'⟩
  use q', lift_lt.mp (hq' ▸ qlto)
  have fltq : ∀ U, f U < q := fun U ↦ by
    convert lt_of_le_of_lt (le_ciSup (by apply bddAbove_of_small) U) (qdef ▸ lt_add_one (iSup f))
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
  rcases mem_range_lift_of_le fltq.le with ⟨fUdown, fUlift⟩
  use fUdown
  constructor
  · simp_all only [lift_inj, mem_inter_iff, f]
  · exact ⟨lift_lt.mp <| fUlift ▸ (this.1), lift_lt.mp (hq'.symm ▸ (fUlift ▸ this).2)⟩

/--
Given a limit ordinal `o` and a property on pairs of ordinals `P`, such that
for any `p < o` there is a `q < o` above `p` so that `P p q`, we can construct
an increasing `ω`-sequence below `o` that satisfies `P` between every 2 consecutive elements.
Additionaly, the sequence can begin arbitrarily high in `o`. That is, above any `r < o`.
-/
theorem exists_omega_seq_succ_prop (opos : 0 < o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p : Iio o, ∃ q, (p < q ∧ P p q)) (r : Iio o) : ∃ f : (Iio ω) → Iio o,
    (∀ i, P (f i) (f ⟨i + 1, isLimit_omega0.2 i i.2⟩)) ∧ (∀ i j, (i < j) → f i < f j)
    ∧ r < f ⟨0, omega0_pos⟩ := by
  have oLim : o.IsLimit := ⟨opos.ne.symm, fun a alto ↦ (hP ⟨a, alto⟩).casesOn fun r hr ↦
    lt_of_le_of_lt (succ_le_of_lt hr.1) r.2⟩
  let H₂ : (p : Iio ω) → (Iio o) → (Iio o) := fun _ fp ↦ choose (hP fp)
  let H₃ : (w : Iio ω) → IsLimit w → ((o' : Iio ω) → o' < w → (Iio o)) → (Iio o) :=
    fun w _ _ ↦ ⟨0, oLim.pos⟩
  let f : Iio ω → Iio o := fun x ↦ @boundedLimitRecOn ω isLimit_omega0 (fun _ ↦ Iio o) x
    ⟨r + 1, oLim.succ_lt r.2⟩ H₂ H₃
  use f
  constructor <;> try constructor
  · intro n
    simp [f, H₂]
    generalize_proofs _ pf
    exact (choose_spec pf).2
  · have aux : ∀ i, f i < f ⟨i + 1, isLimit_omega0.2 i i.2⟩ := fun i ↦ by
      simp [f, H₂]
      generalize_proofs _ pf
      exact (choose_spec pf).casesOn fun h _ ↦ h
    exact fun _ _ ↦ strictMono_of_succ_lt_omega f aux
  simp [f]
  exact lt_succ r.1

theorem exists_omega_seq_succ_prop_pos (onelto : 1 < o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p : Iio o, 0 < p.1 → ∃ q : Iio o, (p < q ∧ P p q)) (r : Iio o) :
    ∃ f : (Iio ω : Set Ordinal.{0}) → (Iio o), (∀ i, P (f i) (f ⟨i + 1, isLimit_omega0.2 i i.2⟩))
    ∧ (∀ i j, (i < j) → f i < f j) ∧ r < f ⟨0, omega0_pos⟩ := by
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
  refine ⟨fun i ↦ ?_, hf.2⟩
  have := hf.1 i
  have rltf0 := hf.2.2
  by_cases hi' : i.1 = 0
  · refine this.resolve_left ?_
    convert (LT.lt.bot_lt rltf0 : (0 : Ordinal) < _).ne.symm
  · refine this.resolve_left ?_
    have aux' : (0 : Ordinal) < _ := LT.lt.bot_lt (hf.2.1 ⟨0, omega0_pos⟩ i
      (Ordinal.pos_iff_ne_zero.mpr hi'))
    exact aux'.ne.symm

/-- If between every 2 consecutive elements of a weakly increasing `δ`-sequence
  there is an element of `C`, and `δ` is a limit ordinal,
  then the supremum of the sequence is an accumulation point of `C`. -/
theorem isAcc_iSup_of_between {δ : Ordinal.{u}} (C : Set Ordinal) (δLim : δ.IsLimit)
    (s : Iio δ → Ordinal.{max u v}) (sInc : ∀ o, s o < s (succ o))
    (h : ∀ o, (C ∩ (Icc (s o) (s (succ o)))).Nonempty) :
    IsAcc (iSup s) C := by
  rw [isAcc_iff]
  constructor
  · rw [← Ordinal.pos_iff_ne_zero, Ordinal.lt_iSup_iff]
    use ⟨1, δLim.one_lt⟩
    refine lt_of_le_of_lt (Ordinal.zero_le (s ⟨0, δLim.pos⟩)) ?_
    convert sInc ⟨0, δLim.pos⟩
    exact coe_succ_Iio δLim.isSuccPrelimit ▸ succ_zero.symm
  intro p hp
  rw [Ordinal.lt_iSup_iff] at hp
  obtain ⟨r, hr⟩ := hp
  obtain ⟨q, hq⟩ := h r
  use q
  refine ⟨hq.1, ⟨hr.trans_le hq.2.1, ?_⟩⟩
  rw [Ordinal.lt_iSup_iff]
  exact ⟨succ (succ r), hq.2.2.trans_lt (sInc (succ r))⟩

/--
The intersection of less than `o.cof` clubs in `o` is a club in `o`.
-/
theorem IsClub.sInter (hCof : ℵ₀ < o.cof) (hS : ∀ C ∈ S, IsClub C o) (hSemp : S.Nonempty)
    (Scard : #S < Cardinal.lift.{u + 1, u} o.cof) : IsClub (⋂₀ S) o := by
  refine ⟨IsClosedBelow.sInter (fun C CmemS ↦ (hS C CmemS).1), isAcc_iff.mpr ?_⟩
  have nonemptyS : Nonempty S := hSemp.to_subtype
  have oLim : IsLimit o := aleph0_le_cof.mp hCof.le
  use oLim.pos.ne.symm
  intro p plto
  let P : Ordinal → Ordinal → Prop := fun p q ↦ ∀ C ∈ S, (C ∩ Ioo p q).Nonempty
  have auxP : ∀ p : Iio o, ∃ q, p < q ∧ P p q := fun p ↦ by
    rcases exists_above_of_lt_cof p.2 nonemptyS (fun U hU ↦ (hS U hU).2) Scard with ⟨q, hq⟩
    use ⟨q, hq.1⟩, hq.2.1, hq.2.2
  rcases exists_omega_seq_succ_prop.{u, u} oLim.pos auxP ⟨p, plto⟩ with ⟨f, hf⟩
  let sup := iSup (fun n ↦ (f n).1)
  use sup
  have suplt : sup < o := by
    apply iSup_lt_ord_lift'
    · rw [mk_Iio_ordinal, card_omega0, lift_aleph0, lift_aleph0]
      exact aleph0_lt_lift.mpr hCof
    intro n
    exact (f n).2
  constructor
  · intro s hs
    apply (hS s hs).1.forall_lt sup suplt
    apply isAcc_iSup_of_between
    · exact isLimit_omega0
    · intro n
      rw [@Subtype.coe_lt_coe]
      convert hf.2.1 n (succ n) ?_
      · apply Subtype.coe_lt_coe.mp
        rw [coe_succ_of_mem]
        · exact lt_succ n.1
        exact isLimit_omega0.succ_lt n.2
    · intro n
      apply (hf.1 n s hs).mono
      convert inter_subset_inter_right _ Ioo_subset_Icc_self
      rw [coe_succ_Iio isLimit_omega0.isSuccPrelimit, succ_eq_add_one]
  · constructor
    · rw [Ordinal.lt_iSup_iff]
      exact ⟨⟨0, omega0_pos⟩, hf.2.2⟩
    · exact suplt

theorem IsClub.iInter_lift {ι : Type v} {f : ι → Set Ordinal.{u}} [Nonempty ι] (hCof : ℵ₀ < o.cof)
    (hf : ∀ i, IsClub (f i) o) (ιCard : Cardinal.lift.{u} #ι < Cardinal.lift.{v} o.cof) :
    IsClub (⋂ i, f i) o := by
  refine IsClub.sInter (S := range f) hCof (fun y ⟨x, hx⟩ ↦ hx ▸ hf x) (range_nonempty f) ?_
  have := mk_range_le_lift (f := f)
  rw [← Cardinal.lift_lt.{_, max v (u + 1)}]
  have aux : Cardinal.lift.{max v (u + 1), u + 1} #↑(range f) =
      Cardinal.lift.{max v, u + 1} #↑(range f) := by
    convert (@lift_umax_eq.{u + 1, u + 1, v} #(range f) #(range f)).mpr rfl
    exact Cardinal.lift_umax.symm
  rw [aux]
  apply this.trans_lt
  convert lift_strictMono.{max u v, max (u + 1) v} ιCard
  · rw [Cardinal.lift_lift, Cardinal.lift_umax.{v, u + 1}]
  · rw [Cardinal.lift_lift, Cardinal.lift_lift]

theorem IsClub.iInter [Nonempty ι] (hCof : ℵ₀ < o.cof) (hf : ∀ i, IsClub (f i) o)
    (ιCard : #ι < o.cof) : IsClub (⋂ i, f i) o :=
  IsClub.iInter_lift hCof hf (Cardinal.lift_lt.mpr ιCard)

end ClubIntersection
end Ordinal
