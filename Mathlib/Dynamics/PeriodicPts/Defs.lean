/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.Cycle
import Mathlib.Data.PNat.Notation
import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Periodic points

A point `x : α` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.

## Main definitions

* `IsPeriodicPt f n x` : `x` is a periodic point of `f` of period `n`, i.e. `f^[n] x = x`.
  We do not require `n > 0` in the definition.
* `ptsOfPeriod f n` : the set `{x | IsPeriodicPt f n x}`. Note that `n` is not required to
  be the minimal period of `x`.
* `periodicPts f` : the set of all periodic points of `f`.
* `minimalPeriod f x` : the minimal period of a point `x` under an endomorphism `f` or zero
  if `x` is not a periodic point of `f`.
* `orbit f x`: the cycle `[x, f x, f (f x), ...]` for a periodic point.
* `MulAction.period g x` : the minimal period of a point `x` under the multiplicative action of `g`;
  an equivalent `AddAction.period g x` is defined for additive actions.

## Main statements

We provide “dot syntax”-style operations on terms of the form `h : IsPeriodicPt f n x` including
arithmetic operations on `n` and `h.map (hg : SemiconjBy g f f')`. We also prove that `f`
is bijective on each set `ptsOfPeriod f n` and on `periodicPts f`. Finally, we prove that `x`
is a periodic point of `f` of period `n` if and only if `minimalPeriod f x | n`.

## References

* https://en.wikipedia.org/wiki/Periodic_point

-/

assert_not_exists MonoidWithZero


open Set

namespace Function

open Function (Commute)

variable {α : Type*} {β : Type*} {f fa : α → α} {fb : β → β} {x y : α} {m n : ℕ}

/-- A point `x` is a periodic point of `f : α → α` of period `n` if `f^[n] x = x`.
Note that we do not require `0 < n` in this definition. Many theorems about periodic points
need this assumption. -/
def IsPeriodicPt (f : α → α) (n : ℕ) (x : α) :=
  IsFixedPt f^[n] x

/-- A fixed point of `f` is a periodic point of `f` of any prescribed period. -/
theorem IsFixedPt.isPeriodicPt (hf : IsFixedPt f x) (n : ℕ) : IsPeriodicPt f n x :=
  hf.iterate n

/-- For the identity map, all points are periodic. -/
theorem is_periodic_id (n : ℕ) (x : α) : IsPeriodicPt id n x :=
  (isFixedPt_id x).isPeriodicPt n

/-- Any point is a periodic point of period `0`. -/
theorem isPeriodicPt_zero (f : α → α) (x : α) : IsPeriodicPt f 0 x :=
  isFixedPt_id x

namespace IsPeriodicPt

@[nontriviality]
theorem of_subsingleton [Subsingleton α] (f : α → α) (n : ℕ) (x : α) : IsPeriodicPt f n x :=
  IsFixedPt.of_subsingleton _ _

instance [DecidableEq α] {f : α → α} {n : ℕ} {x : α} : Decidable (IsPeriodicPt f n x) :=
  IsFixedPt.decidable

protected theorem isFixedPt (hf : IsPeriodicPt f n x) : IsFixedPt f^[n] x :=
  hf

protected theorem map (hx : IsPeriodicPt fa n x) {g : α → β} (hg : Semiconj g fa fb) :
    IsPeriodicPt fb n (g x) :=
  IsFixedPt.map hx (hg.iterate_right n)

theorem apply_iterate (hx : IsPeriodicPt f n x) (m : ℕ) : IsPeriodicPt f n (f^[m] x) :=
  hx.map <| Commute.iterate_self f m

protected theorem apply (hx : IsPeriodicPt f n x) : IsPeriodicPt f n (f x) :=
  hx.apply_iterate 1

protected theorem add (hn : IsPeriodicPt f n x) (hm : IsPeriodicPt f m x) :
    IsPeriodicPt f (n + m) x := by
  rw [IsPeriodicPt, iterate_add]
  exact hn.comp hm

theorem left_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f m x) :
    IsPeriodicPt f n x := by
  rw [IsPeriodicPt, iterate_add] at hn
  exact hn.left_of_comp hm

theorem right_of_add (hn : IsPeriodicPt f (n + m) x) (hm : IsPeriodicPt f n x) :
    IsPeriodicPt f m x := by
  rw [add_comm] at hn
  exact hn.left_of_add hm

protected theorem sub (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m - n) x := by
  rcases le_total n m with h | h
  · refine left_of_add ?_ hn
    rwa [tsub_add_cancel_of_le h]
  · rw [tsub_eq_zero_iff_le.mpr h]
    apply isPeriodicPt_zero

protected theorem mul_const (hm : IsPeriodicPt f m x) (n : ℕ) : IsPeriodicPt f (m * n) x := by
  simp only [IsPeriodicPt, iterate_mul, hm.isFixedPt.iterate n]

protected theorem const_mul (hm : IsPeriodicPt f m x) (n : ℕ) : IsPeriodicPt f (n * m) x := by
  simp only [mul_comm n, hm.mul_const n]

theorem trans_dvd (hm : IsPeriodicPt f m x) {n : ℕ} (hn : m ∣ n) : IsPeriodicPt f n x :=
  let ⟨k, hk⟩ := hn
  hk.symm ▸ hm.mul_const k

protected theorem iterate (hf : IsPeriodicPt f n x) (m : ℕ) : IsPeriodicPt f^[m] n x := by
  rw [IsPeriodicPt, ← iterate_mul, mul_comm, iterate_mul]
  exact hf.isFixedPt.iterate m

theorem comp {g : α → α} (hco : Commute f g) (hf : IsPeriodicPt f n x) (hg : IsPeriodicPt g n x) :
    IsPeriodicPt (f ∘ g) n x := by
  rw [IsPeriodicPt, hco.comp_iterate]
  exact IsFixedPt.comp hf hg

theorem comp_lcm {g : α → α} (hco : Commute f g) (hf : IsPeriodicPt f m x)
    (hg : IsPeriodicPt g n x) : IsPeriodicPt (f ∘ g) (Nat.lcm m n) x :=
  (hf.trans_dvd <| Nat.dvd_lcm_left _ _).comp hco (hg.trans_dvd <| Nat.dvd_lcm_right _ _)

theorem left_of_comp {g : α → α} (hco : Commute f g) (hfg : IsPeriodicPt (f ∘ g) n x)
    (hg : IsPeriodicPt g n x) : IsPeriodicPt f n x := by
  rw [IsPeriodicPt, hco.comp_iterate] at hfg
  exact hfg.left_of_comp hg

theorem iterate_mod_apply (h : IsPeriodicPt f n x) (m : ℕ) : f^[m % n] x = f^[m] x := by
  conv_rhs => rw [← Nat.mod_add_div m n, iterate_add_apply, (h.mul_const _).eq]

protected theorem mod (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m % n) x :=
  (hn.iterate_mod_apply m).trans hm

protected theorem gcd (hm : IsPeriodicPt f m x) (hn : IsPeriodicPt f n x) :
    IsPeriodicPt f (m.gcd n) x := by
  revert hm hn
  refine Nat.gcd.induction m n (fun n _ hn => ?_) fun m n _ ih hm hn => ?_
  · rwa [Nat.gcd_zero_left]
  · rw [Nat.gcd_rec]
    exact ih (hn.mod hm) hm

/-- If `f` sends two periodic points `x` and `y` of the same positive period to the same point,
then `x = y`. For a similar statement about points of different periods see `eq_of_apply_eq`. -/
theorem eq_of_apply_eq_same (hx : IsPeriodicPt f n x) (hy : IsPeriodicPt f n y) (hn : 0 < n)
    (h : f x = f y) : x = y := by
  rw [← hx.eq, ← hy.eq, ← iterate_pred_comp_of_pos f hn, comp_apply, comp_apply, h]

/-- If `f` sends two periodic points `x` and `y` of positive periods to the same point,
then `x = y`. -/
theorem eq_of_apply_eq (hx : IsPeriodicPt f m x) (hy : IsPeriodicPt f n y) (hm : 0 < m) (hn : 0 < n)
    (h : f x = f y) : x = y :=
  (hx.mul_const n).eq_of_apply_eq_same (hy.const_mul m) (Nat.mul_pos hm hn) h

end IsPeriodicPt

/-- The set of periodic points of a given (possibly non-minimal) period. -/
def ptsOfPeriod (f : α → α) (n : ℕ) : Set α :=
  { x : α | IsPeriodicPt f n x }

@[simp]
theorem mem_ptsOfPeriod : x ∈ ptsOfPeriod f n ↔ IsPeriodicPt f n x :=
  Iff.rfl

theorem Semiconj.mapsTo_ptsOfPeriod {g : α → β} (h : Semiconj g fa fb) (n : ℕ) :
    MapsTo g (ptsOfPeriod fa n) (ptsOfPeriod fb n) :=
  (h.iterate_right n).mapsTo_fixedPoints

theorem bijOn_ptsOfPeriod (f : α → α) {n : ℕ} (hn : 0 < n) :
    BijOn f (ptsOfPeriod f n) (ptsOfPeriod f n) :=
  ⟨(Commute.refl f).mapsTo_ptsOfPeriod n, fun _ hx _ hy hxy => hx.eq_of_apply_eq_same hy hn hxy,
    fun x hx =>
    ⟨f^[n.pred] x, hx.apply_iterate _, by
      rw [← comp_apply (f := f), comp_iterate_pred_of_pos f hn, hx.eq]⟩⟩

/-- The set of periodic points of a map `f : α → α`. -/
def periodicPts (f : α → α) : Set α :=
  { x : α | ∃ n > 0, IsPeriodicPt f n x }

theorem mk_mem_periodicPts (hn : 0 < n) (hx : IsPeriodicPt f n x) : x ∈ periodicPts f :=
  ⟨n, hn, hx⟩

theorem mem_periodicPts : x ∈ periodicPts f ↔ ∃ n > 0, IsPeriodicPt f n x :=
  Iff.rfl

theorem periodicPts_subset_range : periodicPts f ⊆ range f := by
  intro x h
  rw [mem_periodicPts] at h
  rcases h with ⟨n, _, h⟩
  use f^[n - 1] x
  nth_rw 1 [← iterate_one f]
  rw [← iterate_add_apply, Nat.add_sub_cancel' (by cutsat)]
  exact h

@[deprecated (since := "2025-04-27")]
alias periodicPts_subset_image := periodicPts_subset_range

theorem isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate (hx : x ∈ periodicPts f)
    (hm : IsPeriodicPt f m (f^[n] x)) : IsPeriodicPt f m x := by
  rcases hx with ⟨r, hr, hr'⟩
  suffices n ≤ (n / r + 1) * r by
    unfold IsPeriodicPt IsFixedPt
    convert (hm.apply_iterate ((n / r + 1) * r - n)).eq <;>
      rw [← iterate_add_apply, Nat.sub_add_cancel this, iterate_mul, (hr'.iterate _).eq]
  rw [Nat.add_mul, one_mul]
  exact (Nat.lt_div_mul_add hr).le

variable (f)

theorem bUnion_ptsOfPeriod : ⋃ n > 0, ptsOfPeriod f n = periodicPts f :=
  Set.ext fun x => by simp [mem_periodicPts]

theorem iUnion_pnat_ptsOfPeriod : ⋃ n : ℕ+, ptsOfPeriod f n = periodicPts f :=
  iSup_subtype.trans <| bUnion_ptsOfPeriod f

@[deprecated (since := "2025-04-27")]
alias iUnion_pNat_ptsOfPeriod := iUnion_pnat_ptsOfPeriod

variable {f}

theorem Semiconj.mapsTo_periodicPts {g : α → β} (h : Semiconj g fa fb) :
    MapsTo g (periodicPts fa) (periodicPts fb) := fun _ ⟨n, hn, hx⟩ => ⟨n, hn, hx.map h⟩

noncomputable section

open scoped Classical in
/-- Minimal period of a point `x` under an endomorphism `f`. If `x` is not a periodic point of `f`,
then `minimalPeriod f x = 0`. -/
def minimalPeriod (f : α → α) (x : α) :=
  if h : x ∈ periodicPts f then Nat.find h else 0

theorem isPeriodicPt_minimalPeriod (f : α → α) (x : α) : IsPeriodicPt f (minimalPeriod f x) x := by
  classical
  delta minimalPeriod
  split_ifs with hx
  · exact (Nat.find_spec hx).2
  · exact isPeriodicPt_zero f x

@[simp]
theorem iterate_minimalPeriod : f^[minimalPeriod f x] x = x :=
  isPeriodicPt_minimalPeriod f x

@[simp]
theorem iterate_add_minimalPeriod_eq : f^[n + minimalPeriod f x] x = f^[n] x := by
  rw [iterate_add_apply]
  congr
  exact isPeriodicPt_minimalPeriod f x

@[simp]
theorem iterate_mod_minimalPeriod_eq : f^[n % minimalPeriod f x] x = f^[n] x :=
  (isPeriodicPt_minimalPeriod f x).iterate_mod_apply n

theorem minimalPeriod_pos_of_mem_periodicPts (hx : x ∈ periodicPts f) : 0 < minimalPeriod f x := by
  classical
  simp only [minimalPeriod, dif_pos hx, (Nat.find_spec hx).1.lt]

theorem minimalPeriod_eq_zero_of_notMem_periodicPts (hx : x ∉ periodicPts f) :
    minimalPeriod f x = 0 := by simp only [minimalPeriod, dif_neg hx]

@[deprecated (since := "2025-05-24")]
alias minimalPeriod_eq_zero_of_nmem_periodicPts := minimalPeriod_eq_zero_of_notMem_periodicPts

theorem IsPeriodicPt.minimalPeriod_pos (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    0 < minimalPeriod f x :=
  minimalPeriod_pos_of_mem_periodicPts <| mk_mem_periodicPts hn hx

theorem minimalPeriod_pos_iff_mem_periodicPts : 0 < minimalPeriod f x ↔ x ∈ periodicPts f :=
  ⟨not_imp_not.1 fun h => by simp only [minimalPeriod, dif_neg h, lt_irrefl 0, not_false_iff],
    minimalPeriod_pos_of_mem_periodicPts⟩

theorem minimalPeriod_eq_zero_iff_notMem_periodicPts :
    minimalPeriod f x = 0 ↔ x ∉ periodicPts f := by
  rw [← minimalPeriod_pos_iff_mem_periodicPts, not_lt, nonpos_iff_eq_zero]

@[deprecated (since := "2025-05-24")]
alias minimalPeriod_eq_zero_iff_nmem_periodicPts := minimalPeriod_eq_zero_iff_notMem_periodicPts

theorem IsPeriodicPt.minimalPeriod_le (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    minimalPeriod f x ≤ n := by
  classical
  rw [minimalPeriod, dif_pos (mk_mem_periodicPts hn hx)]
  exact Nat.find_min' (mk_mem_periodicPts hn hx) ⟨hn, hx⟩

theorem minimalPeriod_apply_iterate (hx : x ∈ periodicPts f) (n : ℕ) :
    minimalPeriod f (f^[n] x) = minimalPeriod f x := by
  apply
    (IsPeriodicPt.minimalPeriod_le (minimalPeriod_pos_of_mem_periodicPts hx) _).antisymm
      ((isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate hx
            (isPeriodicPt_minimalPeriod f _)).minimalPeriod_le
        (minimalPeriod_pos_of_mem_periodicPts _))
  · exact (isPeriodicPt_minimalPeriod f x).apply_iterate n
  · rcases hx with ⟨m, hm, hx⟩
    exact ⟨m, hm, hx.apply_iterate n⟩

theorem minimalPeriod_apply (hx : x ∈ periodicPts f) : minimalPeriod f (f x) = minimalPeriod f x :=
  minimalPeriod_apply_iterate hx 1

theorem le_of_lt_minimalPeriod_of_iterate_eq {m n : ℕ} (hm : m < minimalPeriod f x)
    (hmn : f^[m] x = f^[n] x) : m ≤ n := by
  by_contra! hmn'
  rw [← Nat.add_sub_of_le hmn'.le, add_comm, iterate_add_apply] at hmn
  exact
    ((IsPeriodicPt.minimalPeriod_le (tsub_pos_of_lt hmn')
              (isPeriodicPt_of_mem_periodicPts_of_isPeriodicPt_iterate
                (minimalPeriod_pos_iff_mem_periodicPts.1 ((zero_le m).trans_lt hm)) hmn)).trans
          (Nat.sub_le m n)).not_gt
      hm

theorem iterate_injOn_Iio_minimalPeriod : (Iio <| minimalPeriod f x).InjOn (f^[·] x) :=
  fun _m hm _n hn hmn ↦ (le_of_lt_minimalPeriod_of_iterate_eq hm hmn).antisymm
    (le_of_lt_minimalPeriod_of_iterate_eq hn hmn.symm)

theorem iterate_eq_iterate_iff_of_lt_minimalPeriod {m n : ℕ} (hm : m < minimalPeriod f x)
    (hn : n < minimalPeriod f x) : f^[m] x = f^[n] x ↔ m = n :=
  iterate_injOn_Iio_minimalPeriod.eq_iff hm hn

@[simp] theorem minimalPeriod_id : minimalPeriod id x = 1 :=
  ((is_periodic_id _ _).minimalPeriod_le Nat.one_pos).antisymm
    (Nat.succ_le_of_lt ((is_periodic_id _ _).minimalPeriod_pos Nat.one_pos))

@[simp]
theorem minimalPeriod_eq_one_iff_isFixedPt : minimalPeriod f x = 1 ↔ IsFixedPt f x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← iterate_one f]
    refine Function.IsPeriodicPt.isFixedPt ?_
    rw [← h]
    exact isPeriodicPt_minimalPeriod f x
  · exact
      ((h.isPeriodicPt 1).minimalPeriod_le Nat.one_pos).antisymm
        (Nat.succ_le_of_lt ((h.isPeriodicPt 1).minimalPeriod_pos Nat.one_pos))

@[nontriviality]
theorem minimalPeriod_eq_one_of_subsingleton [Subsingleton α] : minimalPeriod f x = 1 := by
  simp [nontriviality]

theorem IsPeriodicPt.eq_zero_of_lt_minimalPeriod (hx : IsPeriodicPt f n x)
    (hn : n < minimalPeriod f x) : n = 0 :=
  Eq.symm <|
    (eq_or_lt_of_le <| n.zero_le).resolve_right fun hn0 => not_lt.2 (hx.minimalPeriod_le hn0) hn

theorem not_isPeriodicPt_of_pos_of_lt_minimalPeriod :
    ∀ {n : ℕ} (_ : n ≠ 0) (_ : n < minimalPeriod f x), ¬IsPeriodicPt f n x
  | 0, n0, _ => (n0 rfl).elim
  | _ + 1, _, hn => fun hp => Nat.succ_ne_zero _ (hp.eq_zero_of_lt_minimalPeriod hn)

theorem IsPeriodicPt.minimalPeriod_dvd (hx : IsPeriodicPt f n x) : minimalPeriod f x ∣ n :=
  (eq_or_lt_of_le <| n.zero_le).elim (fun hn0 => hn0 ▸ Nat.dvd_zero _) fun hn0 =>
    Nat.dvd_iff_mod_eq_zero.2 <|
      (hx.mod <| isPeriodicPt_minimalPeriod f x).eq_zero_of_lt_minimalPeriod <|
        Nat.mod_lt _ <| hx.minimalPeriod_pos hn0

theorem isPeriodicPt_iff_minimalPeriod_dvd : IsPeriodicPt f n x ↔ minimalPeriod f x ∣ n :=
  ⟨IsPeriodicPt.minimalPeriod_dvd, fun h => (isPeriodicPt_minimalPeriod f x).trans_dvd h⟩

open Nat

theorem minimalPeriod_eq_minimalPeriod_iff {g : β → β} {y : β} :
    minimalPeriod f x = minimalPeriod g y ↔ ∀ n, IsPeriodicPt f n x ↔ IsPeriodicPt g n y := by
  simp_rw [isPeriodicPt_iff_minimalPeriod_dvd, dvd_right_iff_eq]

theorem Commute.minimalPeriod_of_comp_dvd_lcm {g : α → α} (h : Commute f g) :
    minimalPeriod (f ∘ g) x ∣ Nat.lcm (minimalPeriod f x) (minimalPeriod g x) := by
  rw [← isPeriodicPt_iff_minimalPeriod_dvd]
  exact (isPeriodicPt_minimalPeriod f x).comp_lcm h (isPeriodicPt_minimalPeriod g x)

private theorem minimalPeriod_iterate_eq_div_gcd_aux (h : 0 < gcd (minimalPeriod f x) n) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n := by
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt, IsFixedPt, ← iterate_mul, ← Nat.mul_div_assoc _ (gcd_dvd_left _ _),
      mul_comm, Nat.mul_div_assoc _ (gcd_dvd_right _ _), mul_comm, iterate_mul]
    exact (isPeriodicPt_minimalPeriod f x).iterate _
  · apply Coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd h)
    apply Nat.dvd_of_mul_dvd_mul_right h
    rw [Nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc, Nat.div_mul_cancel (gcd_dvd_right _ _),
      mul_comm]
    apply IsPeriodicPt.minimalPeriod_dvd
    rw [IsPeriodicPt, IsFixedPt, iterate_mul]
    exact isPeriodicPt_minimalPeriod _ _

theorem minimalPeriod_iterate_eq_div_gcd (h : n ≠ 0) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n :=
  minimalPeriod_iterate_eq_div_gcd_aux <| gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h)

theorem minimalPeriod_iterate_eq_div_gcd' (h : x ∈ periodicPts f) :
    minimalPeriod f^[n] x = minimalPeriod f x / Nat.gcd (minimalPeriod f x) n :=
  minimalPeriod_iterate_eq_div_gcd_aux <|
    gcd_pos_of_pos_left n (minimalPeriod_pos_iff_mem_periodicPts.mpr h)

/-- The orbit of a periodic point `x` of `f` is the cycle `[x, f x, f (f x), ...]`. Its length is
the minimal period of `x`.

If `x` is not a periodic point, then this is the empty (aka nil) cycle. -/
def periodicOrbit (f : α → α) (x : α) : Cycle α :=
  (List.range (minimalPeriod f x)).map fun n => f^[n] x

/-- The definition of a periodic orbit, in terms of `List.map`. -/
theorem periodicOrbit_def (f : α → α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x)).map fun n => f^[n] x :=
  rfl

/-- The definition of a periodic orbit, in terms of `Cycle.map`. -/
theorem periodicOrbit_eq_cycle_map (f : α → α) (x : α) :
    periodicOrbit f x = (List.range (minimalPeriod f x) : Cycle ℕ).map fun n => f^[n] x :=
  rfl

@[simp]
theorem periodicOrbit_length : (periodicOrbit f x).length = minimalPeriod f x := by
  rw [periodicOrbit, Cycle.length_coe, List.length_map, List.length_range]

@[simp]
theorem periodicOrbit_eq_nil_iff_not_periodic_pt :
    periodicOrbit f x = Cycle.nil ↔ x ∉ periodicPts f := by
  simp only [periodicOrbit.eq_1, Cycle.coe_eq_nil, List.map_eq_nil_iff, List.range_eq_nil]
  exact minimalPeriod_eq_zero_iff_notMem_periodicPts

theorem periodicOrbit_eq_nil_of_not_periodic_pt (h : x ∉ periodicPts f) :
    periodicOrbit f x = Cycle.nil :=
  periodicOrbit_eq_nil_iff_not_periodic_pt.2 h

@[simp]
theorem mem_periodicOrbit_iff (hx : x ∈ periodicPts f) :
    y ∈ periodicOrbit f x ↔ ∃ n, f^[n] x = y := by
  simp only [periodicOrbit, Cycle.mem_coe_iff, List.mem_map, List.mem_range]
  use fun ⟨a, _, ha'⟩ => ⟨a, ha'⟩
  rintro ⟨n, rfl⟩
  use n % minimalPeriod f x, mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx)
  rw [iterate_mod_minimalPeriod_eq]

theorem iterate_mem_periodicOrbit (hx : x ∈ periodicPts f) (n : ℕ) :
    f^[n] x ∈ periodicOrbit f x := by
  simp [hx]

@[simp]
theorem exists_iterate_apply_eq_of_mem_periodicPts (hx : x ∈ periodicPts f) : ∃ n, f^[n] x = x := by
  simpa only [← mem_periodicOrbit_iff hx] using iterate_mem_periodicOrbit hx 0

theorem self_mem_periodicOrbit (hx : x ∈ periodicPts f) : x ∈ periodicOrbit f x := by
  simp [hx]

theorem nodup_periodicOrbit : (periodicOrbit f x).Nodup := by
  rw [periodicOrbit, Cycle.nodup_coe_iff, List.nodup_map_iff_inj_on List.nodup_range]
  intro m hm n hn hmn
  rw [List.mem_range] at hm hn
  rwa [iterate_eq_iterate_iff_of_lt_minimalPeriod hm hn] at hmn

theorem periodicOrbit_apply_iterate_eq (hx : x ∈ periodicPts f) (n : ℕ) :
    periodicOrbit f (f^[n] x) = periodicOrbit f x :=
  Eq.symm <| Cycle.coe_eq_coe.2 <| .intro n <|
    List.ext_get (by simp [minimalPeriod_apply_iterate hx]) fun m _ _ ↦ by
      simp [List.getElem_rotate, iterate_add_apply]

theorem periodicOrbit_apply_eq (hx : x ∈ periodicPts f) :
    periodicOrbit f (f x) = periodicOrbit f x :=
  periodicOrbit_apply_iterate_eq hx 1

theorem periodicOrbit_chain (r : α → α → Prop) {f : α → α} {x : α} :
    (periodicOrbit f x).Chain r ↔ ∀ n < minimalPeriod f x, r (f^[n] x) (f^[n+1] x) := by
  by_cases hx : x ∈ periodicPts f
  · have hx' := minimalPeriod_pos_of_mem_periodicPts hx
    have hM := Nat.sub_add_cancel (succ_le_iff.2 hx')
    rw [periodicOrbit, ← Cycle.map_coe, Cycle.chain_map, ← hM, Cycle.chain_range_succ]
    refine ⟨?_, fun H => ⟨?_, fun m hm => H _ (hm.trans (Nat.lt_succ_self _))⟩⟩
    · rintro ⟨hr, H⟩ n hn
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hn) with hM' | hM'
      · rwa [hM', hM, iterate_minimalPeriod]
      · exact H _ hM'
    · rw [iterate_zero_apply]
      nth_rw 3 [← @iterate_minimalPeriod α f x]
      nth_rw 2 [← hM]
      exact H _ (Nat.lt_succ_self _)
  · rw [periodicOrbit_eq_nil_of_not_periodic_pt hx, minimalPeriod_eq_zero_of_notMem_periodicPts hx]
    simp

theorem periodicOrbit_chain' (r : α → α → Prop) {f : α → α} {x : α} (hx : x ∈ periodicPts f) :
    (periodicOrbit f x).Chain r ↔ ∀ n, r (f^[n] x) (f^[n+1] x) := by
  rw [periodicOrbit_chain r]
  refine ⟨fun H n => ?_, fun H n _ => H n⟩
  rw [iterate_succ_apply, ← iterate_mod_minimalPeriod_eq, ← iterate_mod_minimalPeriod_eq (n := n),
    ← iterate_succ_apply, minimalPeriod_apply hx]
  exact H _ (mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx))

end -- noncomputable

end Function

namespace Function

variable {α β : Type*} {f : α → α} {g : β → β} {x : α × β} {a : α} {b : β} {m n : ℕ}

@[simp]
theorem isFixedPt_prodMap (x : α × β) :
    IsFixedPt (Prod.map f g) x ↔ IsFixedPt f x.1 ∧ IsFixedPt g x.2 :=
  Prod.ext_iff

@[deprecated (since := "2025-04-18")]
alias isFixedPt_prod_map := isFixedPt_prodMap

theorem IsFixedPt.prodMap (ha : IsFixedPt f a) (hb : IsFixedPt g b) :
    IsFixedPt (Prod.map f g) (a, b) :=
  (isFixedPt_prodMap _).mpr ⟨ha, hb⟩

@[simp]
theorem isPeriodicPt_prodMap (x : α × β) :
    IsPeriodicPt (Prod.map f g) n x ↔ IsPeriodicPt f n x.1 ∧ IsPeriodicPt g n x.2 := by
  simp [IsPeriodicPt]

@[deprecated (since := "2025-04-18")]
alias isPeriodicPt_prod_map := isPeriodicPt_prodMap

theorem IsPeriodicPt.prodMap (ha : IsPeriodicPt f n a) (hb : IsPeriodicPt g n b) :
    IsPeriodicPt (Prod.map f g) n (a, b) :=
  (isPeriodicPt_prodMap _).mpr ⟨ha, hb⟩

end Function

namespace MulAction

open Function

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

/--
The period of a multiplicative action of `g` on `a` is the smallest positive `n` such that
`g ^ n • a = a`, or `0` if such an `n` does not exist.
-/
@[to_additive /-- The period of an additive action of `g` on `a` is the smallest positive `n`
such that `(n • g) +ᵥ a = a`, or `0` if such an `n` does not exist. -/]
noncomputable def period (m : M) (a : α) : ℕ := minimalPeriod (fun x => m • x) a

/-- `MulAction.period m a` is definitionally equal to `Function.minimalPeriod (m • ·) a`. -/
@[to_additive /-- `AddAction.period m a` is definitionally equal to
`Function.minimalPeriod (m +ᵥ ·) a` -/]
theorem period_eq_minimalPeriod {m : M} {a : α} :
    MulAction.period m a = minimalPeriod (fun x => m • x) a := rfl

/-- `m ^ (period m a)` fixes `a`. -/
@[to_additive (attr := simp) /-- `(period m a) • m` fixes `a`. -/]
theorem pow_period_smul (m : M) (a : α) : m ^ (period m a) • a = a := by
  rw [period_eq_minimalPeriod, ← smul_iterate_apply, iterate_minimalPeriod]

@[to_additive]
lemma isPeriodicPt_smul_iff {m : M} {a : α} {n : ℕ} :
    IsPeriodicPt (m • ·) n a ↔ m ^ n • a = a := by
  rw [← smul_iterate_apply, IsPeriodicPt, IsFixedPt]

/-! ### Multiples of `MulAction.period`

It is easy to convince oneself that if `g ^ n • a = a` (resp. `(n • g) +ᵥ a = a`),
then `n` must be a multiple of `period g a`.

This also holds for negative powers/multiples.
-/

@[to_additive]
theorem pow_smul_eq_iff_period_dvd {n : ℕ} {m : M} {a : α} :
    m ^ n • a = a ↔ period m a ∣ n := by
  rw [period_eq_minimalPeriod, ← isPeriodicPt_iff_minimalPeriod_dvd, isPeriodicPt_smul_iff]

@[to_additive]
theorem zpow_smul_eq_iff_period_dvd {j : ℤ} {g : G} {a : α} :
    g ^ j • a = a ↔ (period g a : ℤ) ∣ j := by
  match j with
  | (n : ℕ) => rw [zpow_natCast, Int.natCast_dvd_natCast, pow_smul_eq_iff_period_dvd]
  | -(n + 1 : ℕ) =>
    rw [zpow_neg, zpow_natCast, inv_smul_eq_iff, eq_comm, Int.dvd_neg, Int.natCast_dvd_natCast,
      pow_smul_eq_iff_period_dvd]

@[to_additive (attr := simp)]
theorem pow_mod_period_smul (n : ℕ) {m : M} {a : α} :
    m ^ (n % period m a) • a = m ^ n • a := by
  conv_rhs => rw [← Nat.mod_add_div n (period m a), pow_add, mul_smul,
    pow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]
theorem zpow_mod_period_smul (j : ℤ) {g : G} {a : α} :
    g ^ (j % (period g a : ℤ)) • a = g ^ j • a := by
  conv_rhs => rw [← Int.emod_add_mul_ediv j (period g a), zpow_add, mul_smul,
    zpow_smul_eq_iff_period_dvd.mpr (dvd_mul_right _ _)]

@[to_additive (attr := simp)]
theorem pow_add_period_smul (n : ℕ) (m : M) (a : α) :
    m ^ (n + period m a) • a = m ^ n • a := by
  rw [← pow_mod_period_smul, Nat.add_mod_right, pow_mod_period_smul]

@[to_additive (attr := simp)]
theorem pow_period_add_smul (n : ℕ) (m : M) (a : α) :
    m ^ (period m a + n) • a = m ^ n • a := by
  rw [← pow_mod_period_smul, Nat.add_mod_left, pow_mod_period_smul]

@[to_additive (attr := simp)]
theorem zpow_add_period_smul (i : ℤ) (g : G) (a : α) :
    g ^ (i + period g a) • a = g ^ i • a := by
  rw [← zpow_mod_period_smul, Int.add_emod_right, zpow_mod_period_smul]

@[to_additive (attr := simp)]
theorem zpow_period_add_smul (i : ℤ) (g : G) (a : α) :
    g ^ (period g a + i) • a = g ^ i • a := by
  rw [← zpow_mod_period_smul, Int.add_emod_left, zpow_mod_period_smul]

variable {a : G} {b : α}

@[to_additive]
theorem pow_smul_eq_iff_minimalPeriod_dvd {n : ℕ} :
    a ^ n • b = b ↔ minimalPeriod (a • ·) b ∣ n := by
  rw [← period_eq_minimalPeriod, pow_smul_eq_iff_period_dvd]

@[to_additive]
theorem zpow_smul_eq_iff_minimalPeriod_dvd {n : ℤ} :
    a ^ n • b = b ↔ (minimalPeriod (a • ·) b : ℤ) ∣ n := by
  rw [← period_eq_minimalPeriod, zpow_smul_eq_iff_period_dvd]

variable (a b)

@[to_additive (attr := simp)]
theorem pow_smul_mod_minimalPeriod (n : ℕ) :
    a ^ (n % minimalPeriod (a • ·) b) • b = a ^ n • b := by
  rw [← period_eq_minimalPeriod, pow_mod_period_smul]

@[to_additive (attr := simp)]
theorem zpow_smul_mod_minimalPeriod (n : ℤ) :
    a ^ (n % (minimalPeriod (a • ·) b : ℤ)) • b = a ^ n • b := by
  rw [← period_eq_minimalPeriod, zpow_mod_period_smul]

end MulAction
