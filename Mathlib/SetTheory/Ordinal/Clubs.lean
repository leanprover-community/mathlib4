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
theorem exists_above_of_lt_cof (p : Iio o) (hSemp : Nonempty S) --change!
    (hSunb : ∀ U ∈ S, IsUnbounded U o) (hScard : #S < Cardinal.lift.{u + 1, u} o.cof) :
    ∃ q : Iio o, p < q ∧ (∀ U ∈ S, (U ∩ Ioo p q).Nonempty) := by
  rw [lift_cof] at hScard
  have oLim : IsLimit o := hSemp.casesOn fun ⟨T, hT⟩ ↦ isLimit_of_isUnbounded
    (hSunb T hT) (pos_of_gt p.2).ne.symm
  let f : ↑S → Ordinal := fun U ↦ lift.{u + 1, u} (sInf (U ∩ (Ioo p o)))
  have infMem : ∀ U : S, sInf (↑U ∩ Ioo p.1 o) ∈ ↑U ∩ Ioo p.1 o := fun U ↦
    csInf_mem (inter_suffix_of_isUnbounded (hSunb U.1 U.2) p.2 : (↑U ∩ Ioo p.1 o).Nonempty)
  have flto : ∀ U : S, f U < lift.{u + 1, u} o := fun U ↦ by
    simp_all only [mem_inter_iff, mem_Ioo, lift_lt, f]
  set q := (Ordinal.sup.{u + 1, u} f) + 1 with qdef
  have qlto : q < lift.{u + 1, u} o :=
    ((lift_isLimit.{u + 1, u} o).mpr oLim).2 (sup.{u + 1, u} f) (sup_lt_ord hScard flto)
  rcases lift_down qlto.le with ⟨q', hq'⟩
  use ⟨q', lift_lt.mp (hq' ▸ qlto)⟩
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

-- TODO: improve
theorem monotone_of_succ_lt_omega (f : Iio ω → Iio o)
    (hf : ∀ i, f i < f ⟨i + 1, omega_isLimit.2 i i.2⟩) : -- ask about linter
    ∀ i j, i < j → f i < f j := fun i j iltj ↦ by
  have : ∀ n, ∀ k, (kltj : k < n) → f k < f n := Ordinal.boundedLimitRec omega_isLimit
      (C := fun n ↦ ∀ k : Iio ω, (kltj : k < n) → f k < f n)
    (by
      intro k hk
      cases (Ordinal.zero_le k).not_lt hk)
    (by
      intro j ih k hk
      change k.1 < j.1 + 1 at hk -- succOrder
      have := (lt_succ_iff.mp (hk : k.1 < j.1 + 1)).lt_or_eq
      cases this with
      | inl h =>
          exact (ih k h).trans (hf j)
      | inr h =>
          have := trivial
          simp_rw [← h]
          exact hf k)
    (by
      intro o h _ _
      cases (omega_le_of_isLimit h).not_lt o.2)
  exact this j i iltj

/--
Given a limit ordinal `o` and a property on pairs of ordinals `P`, such that
for any `p < o` there is a `q < o` above `p` so that `P p q`, we can construct
an increasing `ω`-sequence below `o` that satisfies `P` between every 2 consecutive elements.
Additionaly, the sequence can begin arbitrarily high in `o`. That is, above any `r < o`.
-/
theorem exists_omega_seq_succ_prop (opos : 0 < o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p : Iio o, ∃ q : Iio o, (p < q ∧ P p q)) (r : Iio o) : ∃ f : (Iio ω : Set Ordinal.{0}) → Iio o,
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
    exact monotone_of_succ_lt_omega f aux
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
  · exact this.resolve_left (by convert ((pos_of_gt rltf0).ne.symm))
  · have aux := (pos_of_gt (hf.2.1 ⟨0, omega_pos⟩ i (Ordinal.pos_iff_ne_zero.mpr hi'))).ne
    exact this.resolve_left (by convert aux.symm)

/-- If between every 2 consecutive elements of an increasing `δ`-sequence
  there is an element of `C`, and `δ` is a limit ordinal,
  then the supremum of the sequence is an accumulation point of `C`. -/
theorem isAcc_bsup_of_between {δ : Ordinal} (C : Set Ordinal) (δLim : δ.IsLimit)
    (s : Iio δ → Ordinal) (sInc : ∀ o, s o < s ⟨o.1 + 1, δLim.succ_lt o.2⟩)
    (h : ∀ o, (C ∩ Ioo (s o) (s ⟨o + 1, δLim.succ_lt o.2⟩)).Nonempty) : IsAcc (sup s) C := by
  use lt_sup.mpr ⟨⟨0 + 1, δLim.nat_lt (0 + 1)⟩, pos_of_gt (sInc ⟨0, δLim.pos⟩)⟩
  intro p pltsup
  rw [lt_sup] at pltsup
  rcases pltsup with ⟨i, plt⟩
  rcases h i with ⟨q, qmemC, qmemIoo⟩
  use q; use qmemC
  exact ⟨lt_of_lt_of_le qmemIoo.2 (le_sup _ _), plt.trans qmemIoo.1⟩
#check Ordinal.bsup
/--
The intersection of less than `o.cof` clubs in `o` is a club in `o`.
-/
theorem isClub_sInter (hCof : ℵ₀ < o.cof) (hS : ∀ C ∈ S, IsClub C o) (hSemp : S.Nonempty)
    (Scard : #S < Cardinal.lift.{u + 1, u} o.cof) : IsClub (⋂₀ S) o := by
  refine' ⟨isClosed_sInter_of_isClosed hSemp (fun C CmemS ↦ (hS C CmemS).1), _⟩
  refine' ⟨fun x xmem ↦ hSemp.casesOn fun C CmemS ↦ (hS C CmemS).1.1 (xmem C CmemS), _⟩
  intro q qlto
  have oLim : IsLimit o := aleph0_le_cof.mp hCof.le
  have nonemptyS : Nonempty S := Nonempty.to_subtype hSemp
  let P : Ordinal → Ordinal → Prop := fun p q ↦ ∀ C ∈ S, (C ∩ Ioo p q).Nonempty
  have auxP : ∀ p : Iio o, ∃ q : Iio o, p < q ∧ P p q := fun p ↦
    exists_above_of_lt_cof p nonemptyS (fun U h ↦ (hS U h).2) Scard
  rcases exists_omega_seq_succ_prop oLim.pos auxP ⟨q, qlto⟩ with ⟨f, hf⟩
  let g := fun p ↦ lift.{1, u} (f p).1 -- have to lift to use `sup`
  have := hf.2.1
  have gInc : ∀ o, g o < g ⟨o + 1, omega_isLimit.succ_lt o.2⟩ := fun o ↦
    lift_lt.mpr (hf.2.1 o ⟨o + 1, omega_isLimit.succ_lt o.2⟩ (lt_succ o.1))

  have suplt : sup g < lift o := by
    sorry
    --apply sup_lt_ord hCof
    --(sup_lt_ord hCof) sorry
  sorry
  /-
  use sup g
  constructor
  · apply mem_sInter.mpr
    intro C CmemS
    have := isAcc_bsup_of_between C omega_isLimit g gInc (fun i hi ↦ (hf.1 i hi) C CmemS)
    exact (hS C CmemS).1.2 ((bsup ω g)) suplt this
  exact (lt_bsup g).mpr ⟨0, omega_pos, hf.2.2⟩-/

end ClubIntersection
