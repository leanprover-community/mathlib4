/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Equivalence of real-valued absolute values

Two absolute values `v₁, v₂ : AbsoluteValue R ℝ` are *equivalent* if there exists a
positive real number `c` such that `v₁ x ^ c = v₂ x` for all `x : R`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace AbsoluteValue

section OrderedSemiring

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S]
  (v w : AbsoluteValue R S)

/-- Two absolute values `v` and `w` are *equivalent* if `v x ≤ v y` precisely when
`w x ≤ w y`.

Note that for real absolute values this condition is equivalent to the existence of a positive
real number `c` such that `v x ^ c = w x` for all `x`. See
`AbsoluteValue.isEquiv_iff_exists_rpow_eq`. -/
def IsEquiv : Prop := ∀ x y, v x ≤ v y ↔ w x ≤ w y

theorem IsEquiv.refl : v.IsEquiv v := fun _ _ ↦ .rfl

variable {v w}

theorem IsEquiv.rfl : v.IsEquiv v := fun _ _ ↦ .rfl

theorem IsEquiv.symm (h : v.IsEquiv w) : w.IsEquiv v := fun _ _ ↦ (h _ _).symm

theorem IsEquiv.trans {u : AbsoluteValue R S} (h₁ : v.IsEquiv w)
    (h₂ : w.IsEquiv u) : v.IsEquiv u := fun _ _ ↦ (h₁ _ _).trans (h₂ _ _)

instance : Setoid (AbsoluteValue R S) where
  r := IsEquiv
  iseqv := {
    refl := .refl
    symm := .symm
    trans := .trans
  }

theorem IsEquiv.le_iff_le (h : v.IsEquiv w) {x y : R} : v x ≤ v y ↔ w x ≤ w y := h ..

theorem IsEquiv.lt_iff_lt (h : v.IsEquiv w) {x y : R} : v x < v y ↔ w x < w y :=
  lt_iff_lt_of_le_iff_le' (h y x) (h x y)

theorem IsEquiv.eq_iff_eq (h : v.IsEquiv w) {x y : R} : v x = v y ↔ w x = w y := by
  simp [le_antisymm_iff, h x y, h y x]

variable [IsDomain S] [Nontrivial R]

theorem IsEquiv.lt_one_iff (h : v.IsEquiv w) {x : R} :
    v x < 1 ↔ w x < 1 := by
  simpa only [map_one] using h.lt_iff_lt (y := 1)

theorem IsEquiv.one_lt_iff (h : v.IsEquiv w) {x : R} :
    1 < v x ↔ 1 < w x := by
  simpa only [map_one] using h.lt_iff_lt (x := 1)

theorem IsEquiv.le_one_iff (h : v.IsEquiv w) {x : R} :
    v x ≤ 1 ↔ w x ≤ 1 := by
  simpa only [map_one] using h x 1

theorem IsEquiv.one_le_iff (h : v.IsEquiv w) {x : R} :
    1 ≤ v x ↔ 1 ≤ w x := by
  simpa only [map_one] using h 1 x

theorem IsEquiv.eq_one_iff (h : v.IsEquiv w) {x : R} : v x = 1 ↔ w x = 1 := by
  simpa only [map_one] using h.eq_iff_eq (x := x) (y := 1)

theorem IsEquiv.isNontrivial_congr {w : AbsoluteValue R S} (h : v.IsEquiv w) :
    v.IsNontrivial ↔ w.IsNontrivial :=
  not_iff_not.1 <| by aesop (add simp [not_isNontrivial_iff, h.eq_one_iff])

alias ⟨IsEquiv.isNontrivial, _⟩ := IsEquiv.isNontrivial_congr

end OrderedSemiring

section LinearOrderedSemifield

variable {R S : Type*} [Field R] [Semifield S] [LinearOrder S] {v w : AbsoluteValue R S}

/-- An absolute value is equivalent to the trivial iff it is trivial itself. -/
@[simp]
lemma isEquiv_trivial_iff_eq_trivial [DecidablePred fun x : R ↦ x = 0] [NoZeroDivisors R]
    [IsStrictOrderedRing S] {f : AbsoluteValue R S} :
    f.IsEquiv .trivial ↔ f = .trivial :=
  ⟨fun h ↦ by aesop (add simp [h.eq_one_iff, AbsoluteValue.trivial]), fun h ↦ h ▸ .rfl⟩

variable [IsStrictOrderedRing S]

theorem isEquiv_iff_lt_one_iff :
    v.IsEquiv w ↔ ∀ x, v x < 1 ↔ w x < 1 := by
  refine ⟨fun h _ ↦ h.lt_one_iff, fun h x y ↦ ?_⟩
  rcases eq_or_ne (v x) 0 with (_ | hy₀)
  · simp_all
  rw [le_iff_le_iff_lt_iff_lt, ← one_mul (v x), ← mul_inv_lt_iff₀ (by simp_all), ← one_mul (w x),
    ← mul_inv_lt_iff₀ (by simp_all), ← map_inv₀, ← map_mul, ← map_inv₀, ← map_mul]
  exact h _

variable [Archimedean S] [ExistsAddOfLE S]

theorem isEquiv_of_lt_one_imp (hv : v.IsNontrivial) (h : ∀ x, v x < 1 → w x < 1) : v.IsEquiv w := by
  refine isEquiv_iff_lt_one_iff.2 fun a ↦ ?_
  rcases eq_or_ne a 0 with (rfl | ha₀)
  · simp
  refine ⟨h a, fun hw ↦ ?_⟩
  let ⟨x₀, hx₀⟩ := hv.exists_abv_lt_one
  have hpow (n : ℕ) (hv : 1 ≤ v a) : w x₀ < w a ^ n := by
    rw [← one_mul (_ ^ _), ← mul_inv_lt_iff₀ (pow_pos (by simp_all) _),
      ← map_pow, ← map_inv₀, ← map_mul]
    apply h
    rw [map_mul, map_inv₀, map_pow, mul_inv_lt_iff₀ (pow_pos (by simp [ha₀]) _), one_mul]
    exact lt_of_lt_of_le hx₀.2 <| one_le_pow₀ hv
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (w.pos hx₀.1) hw
  exact not_le.1 <| mt (hpow n) <| not_lt.2 hn.le

/--
If `v` and `w` are inequivalent absolute values and `v` is non-trivial, then we can find an `a : R`
such that `v a < 1` while `1 ≤ w a`.
-/
theorem exists_lt_one_one_le_of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNontrivial)
    (h : ¬v.IsEquiv w) : ∃ a : R, v a < 1 ∧ 1 ≤ w a := by
  contrapose! h
  exact isEquiv_of_lt_one_imp hv h

/--
If `v` and `w` are two non-trivial and inequivalent absolute values then we can find an `a : R`
such that `1 < v a` while `w a < 1`.
-/
theorem exists_one_lt_lt_one_of_not_isEquiv {v w : AbsoluteValue R S} (hv : v.IsNontrivial)
    (hw : w.IsNontrivial) (h : ¬v.IsEquiv w) :
    ∃ a : R, 1 < v a ∧ w a < 1 := by
  let ⟨a, hva, hwa⟩ := exists_lt_one_one_le_of_not_isEquiv hv h
  let ⟨b, hwb, hvb⟩ := exists_lt_one_one_le_of_not_isEquiv hw (mt .symm h)
  exact ⟨b / a, by simp [w.pos_iff.1 (lt_of_lt_of_le zero_lt_one hwa), one_lt_div, div_lt_one,
    lt_of_le_of_lt' hvb hva, lt_of_le_of_lt' hwa hwb]⟩

end LinearOrderedSemifield

section LinearOrderedField

open Filter
open scoped Topology

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}
  [TopologicalSpace S] [IsStrictOrderedRing S] [Archimedean S] [OrderTopology S]
  {ι : Type*} [Finite ι] {v : ι → AbsoluteValue R S} {w : AbsoluteValue R S}
  {a b : R} {i : ι}

/--
Suppose that
- `v i` and `w` are absolute values on a field `R`.
- `v i` is inequivalent to `v j` for all `j ≠ i` via the divergent point `a : R`.
- `v i` is inequivalent to `w` via the divergent point `b : R`.
- `w a = 1`.

Then there is a common divergent point `k` causing both `v i` and `w` to be inequivalent to
each `v j` for `j ≠ i`.
-/
private theorem exists_one_lt_lt_one_pi_of_eq_one (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1)
    (haw : w a = 1) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : R, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  classical
  let c : ℕ → R := fun n ↦ a ^ n * b
  have hcᵢ : Tendsto (fun n ↦ (v i) (c n)) atTop atTop := by
    simpa [c] using Tendsto.atTop_mul_const (by linarith) (tendsto_pow_atTop_atTop_of_one_lt ha)
  have hcⱼ (j : ι) (hj : j ≠ i) : Tendsto (fun n ↦ (v j) (c n)) atTop (𝓝 0) := by
    simpa [c] using (tendsto_pow_atTop_nhds_zero_of_lt_one ((v j).nonneg _) (haj j hj)).mul_const _
  simp_rw +instances [OrderTopology.topology_eq_generate_intervals,
    TopologicalSpace.tendsto_nhds_generateFrom_iff, mem_atTop_sets, Set.mem_preimage] at hcⱼ
  choose r₁ hr₁ using tendsto_atTop_atTop.1 hcᵢ 2
  choose rₙ hrₙ using fun j hj ↦ hcⱼ j hj (.Iio 1) (by simpa using ⟨1, .inr rfl⟩) (by simp)
  have := Fintype.ofFinite ι
  let r := Finset.univ.sup fun j ↦ if h : j = i then r₁ else rₙ j h
  refine ⟨c r, lt_of_lt_of_le (by linarith) (hr₁ r ?_), fun j hj ↦ ?_, by simpa [c, haw]⟩
  · exact Finset.le_sup_dite_pos (p := fun j ↦ j = i) (f := fun _ _ ↦ r₁) (Finset.mem_univ _) rfl
  · simpa using hrₙ j hj _ <| Finset.le_sup_dite_neg (fun j ↦ j = i) (Finset.mem_univ j) _

/--
Suppose that
- `v i` and `w` are absolute values on a field `R`.
- `v i` is inequivalent to `v j` for all `j ≠ i` via the divergent point `a : R`.
- `v i` is inequivalent to `w` via the divergent point `b : R`.
- `1 < w a`.

Then there is a common divergent point `k : R` causing both `v i` and `w` to be inequivalent to
each `v j` for `j ≠ i`.
-/
private theorem exists_one_lt_lt_one_pi_of_one_lt (ha : 1 < v i a) (haj : ∀ j ≠ i, v j a < 1)
    (haw : 1 < w a) (hb : 1 < v i b) (hbw : w b < 1) :
    ∃ k : R, 1 < v i k ∧ (∀ j ≠ i, v j k < 1) ∧ w k < 1 := by
  classical
  let c : ℕ → R := fun n ↦ 1 / (1 + a⁻¹ ^ n) * b
  have hcᵢ : Tendsto (fun n ↦ v i (c n)) atTop (𝓝 (v i b)) := by
    have : v i a⁻¹ < 1 := map_inv₀ (v i) a ▸ inv_lt_one_of_one_lt₀ ha
    simpa [c] using (tendsto_div_one_add_pow_nhds_one this).mul_const (v i b)
  have hcⱼ (j : ι) (hj : j ≠ i) : atTop.Tendsto (fun n ↦ v j (c n)) (𝓝 0) := by
    have : 1 < v j a⁻¹ := map_inv₀ (v j) _ ▸
      (one_lt_inv₀ <| (v j).pos fun h ↦ by linarith [map_zero (v _) ▸ h ▸ ha]).2 (haj j hj)
    simpa [c] using (tendsto_div_one_add_pow_nhds_zero this).mul_const _
  have hcₙ : atTop.Tendsto (fun n ↦ w (c n)) (𝓝 (w b)) := by
    have : w a⁻¹ < 1 := map_inv₀ w _ ▸ inv_lt_one_of_one_lt₀ haw
    simpa [c] using (tendsto_div_one_add_pow_nhds_one this).mul_const (w b)
  simp_rw +instances [OrderTopology.topology_eq_generate_intervals,
    TopologicalSpace.tendsto_nhds_generateFrom_iff, mem_atTop_sets, Set.mem_preimage] at hcⱼ
  choose r₁ hr₁ using Filter.eventually_atTop.1 <| Filter.Tendsto.eventually_const_lt hb hcᵢ
  choose rₙ hrₙ using fun j hj ↦ hcⱼ j hj (.Iio 1) (by simpa using ⟨1, .inr rfl⟩) (by simp)
  choose rN hrN using Filter.eventually_atTop.1 <| Filter.Tendsto.eventually_lt_const hbw hcₙ
  have := Fintype.ofFinite ι
  let r := max (Finset.univ.sup fun j ↦ if h : j = i then r₁ else rₙ j h) rN
  refine ⟨c r, hr₁ r ?_, fun j hj ↦ ?_, ?_⟩
  · exact le_max_iff.2 <| .inl <|
      Finset.le_sup_dite_pos (p := fun j ↦ j = i) (f := fun _ _ ↦ r₁) (Finset.mem_univ _) rfl
  · exact hrₙ j hj _ <| le_max_iff.2 <| .inl <|
      Finset.le_sup_dite_neg (fun j ↦ j = i) (Finset.mem_univ j) _
  · exact hrN _ <| le_max_iff.2 (.inr le_rfl)

open Fintype Subtype in
/--
If `v : ι → AbsoluteValue R S` is a finite collection of non-trivial and pairwise inequivalent
absolute values, then for any `i` there is some `a : R` such that `1 < v i a` and
`v j a < 1` for all `j ≠ i`.
-/
theorem exists_one_lt_lt_one_pi_of_not_isEquiv (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) :
    ∀ i, ∃ (a : R), 1 < v i a ∧ ∀ j ≠ i, v j a < 1 := by
  classical
  have := Fintype.ofFinite ι
  let P (ι : Type _) [Fintype ι] : Prop :=
    ∀ v : ι → AbsoluteValue R S, (∀ i, (v i).IsNontrivial) →
      (Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) → ∀ i, ∃ (a : R), 1 < v i a ∧ ∀ j ≠ i, v j a < 1
  -- Use strong induction on the index.
  revert hv h; refine induction_subsingleton_or_nontrivial (P := P) ι (fun ι _ _ v h hv i ↦ ?_)
    (fun ι _ _ ih v h hv i ↦ ?_) v
  · -- If `ι` is trivial this follows immediately from `(v i).IsNontrivial`.
    let ⟨a, ha⟩ := (h i).exists_abv_gt_one
    exact ⟨a, ha, fun j hij ↦ absurd (Subsingleton.elim i j) hij.symm⟩
  · rcases eq_or_ne (card ι) 2 with (hc | hc)
    · -- If `ι` has two elements this is `exists_one_lt_lt_one_of_not_isEquiv`.
      let ⟨j, hj⟩ := (Nat.card_eq_two_iff' i).1 <| card_eq_nat_card ▸ hc
      let ⟨a, ha⟩ := (v i).exists_one_lt_lt_one_of_not_isEquiv (h i) (h j) (hv hj.1.symm)
      exact ⟨a, ha.1, fun _ h ↦ hj.2 _ h ▸ ha.2⟩
    have hlt : 2 < card ι := Nat.lt_of_le_of_ne (one_lt_card_iff_nontrivial.2 ‹_›) hc.symm
    -- Otherwise, choose another distinguished index `j ≠ i`.
    let ⟨j, hj⟩ := exists_ne i
    -- Apply induction first on the subcollection `v i` for `i ≠ j` to get `a : K`
    let ⟨a, ha⟩ := ih {k : ι // k ≠ j} (card_subtype_lt fun a ↦ a rfl) (restrict _ v)
      (fun i ↦ h _) (hv.comp_of_injective val_injective) ⟨i, hj.symm⟩
    -- Then apply induction next to the subcollection `{v i, v j}` to get `b : K`.
    let ⟨b, hb⟩ := ih {k : ι // k = i ∨ k = j} (by linarith [card_subtype_eq_or_eq_of_ne hj.symm])
      (restrict _ v) (fun _ ↦ h _) (hv.comp_of_injective val_injective) ⟨i, .inl rfl⟩
    rcases eq_or_ne (v j a) 1 with (ha₁ | ha₁)
    · -- If `v j a = 1` then take a large enough value from the sequence `a ^ n * b`.
      let ⟨c, hc⟩ := exists_one_lt_lt_one_pi_of_eq_one ha.1 ha.2 ha₁ hb.1 (hb.2 ⟨j, .inr rfl⟩
        (by grind))
      refine ⟨c, hc.1, fun k hk ↦ ?_⟩
      rcases eq_or_ne k j with (rfl | h); try exact hc.2.2; exact hc.2.1 ⟨k, h⟩ (by grind)
    rcases ha₁.lt_or_gt with (ha_lt | ha_gt)
    · -- If `v j a < 1` then `a` works as the divergent point.
      refine ⟨a, ha.1, fun k hk ↦ ?_⟩
      rcases eq_or_ne k j with (rfl | h); try exact ha_lt; exact ha.2 ⟨k, h⟩ (by grind)
    · -- If `1 < v j a` then take a large enough value from the sequence `b / (1 + a ^ (-n))`.
      let ⟨c, hc⟩ := exists_one_lt_lt_one_pi_of_one_lt ha.1 ha.2 ha_gt hb.1 (hb.2 ⟨j, .inr rfl⟩
        (by grind))
      refine ⟨c, hc.1, fun k hk ↦ ?_⟩
      rcases eq_or_ne k j with (rfl | h); try exact hc.2.2; exact hc.2.1 ⟨k, h⟩ (by grind)

end LinearOrderedField

section Real

open Real Topology

variable {F : Type*} [Field F] {v w : AbsoluteValue F ℝ}

theorem IsEquiv.log_div_log_pos (h : v.IsEquiv w) {a : F} (ha₀ : a ≠ 0) (ha₁ : w a ≠ 1) :
    0 < (w a).log / (v a).log := by
  rcases ha₁.lt_or_gt with hwa | hwa
  · simpa using div_pos (neg_pos_of_neg <| log_neg (w.pos ha₀) (hwa))
      (neg_pos_of_neg <| log_neg (v.pos ha₀) (h.lt_one_iff.2 hwa))
  · exact div_pos (log_pos <| hwa) (log_pos (h.one_lt_iff.2 hwa))

/--
If $v$ and $w$ are two real absolute values on a field $F$, equivalent in the sense that
$v(x) \leq v(y)$ if and only if $w(x) \leq w(y)$, then $\frac{\log (v(a))}{\log (w(a))}$ is
constant for all $0 \neq a\in F$ with $v(a) \neq 1$.
-/
theorem IsEquiv.log_div_log_eq_log_div_log (h : v.IsEquiv w)
    {a : F} (ha₀ : a ≠ 0) (ha₁ : v a ≠ 1) {b : F} (hb₀ : b ≠ 0) (hb₁ : v b ≠ 1) :
    (v b).log / (w b).log = (v a).log / (w a).log := by
  by_contra! h_ne
  wlog! ha : 1 < v a generalizing a b
  · apply this (inv_ne_zero ha₀) (by simpa) hb₀ hb₁ (by simpa)
    simpa using one_lt_inv_iff₀.2 ⟨v.pos ha₀, ha₁.lt_of_le ha⟩
  wlog! hb : 1 < v b generalizing a b
  · apply this ha₀ ha₁ (inv_ne_zero hb₀) (by simpa) (by simpa) ha
    simpa using one_lt_inv_iff₀.2 ⟨v.pos hb₀, hb₁.lt_of_le hb⟩
  wlog! h_lt : (v b).log / (w b).log < (v a).log / (w a).log generalizing a b
  · exact this hb₀ hb₁ ha₀ ha₁ h_ne.symm hb ha <| lt_of_le_of_ne h_lt h_ne.symm
  have hwa := h.one_lt_iff.1 ha
  have hwb := h.one_lt_iff.1 hb
  rw [div_lt_div_iff₀ (log_pos hwb) (log_pos hwa), mul_comm (v a).log,
    ← div_lt_div_iff₀ (log_pos ha) (log_pos hwa)] at h_lt
  let ⟨q, ⟨hq₁, hq₂⟩⟩ := exists_rat_btwn h_lt
  rw [← Rat.num_div_den q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hq₁ hq₂
  rw [div_lt_div_iff₀ (log_pos ha) (by simp [q.den_pos]), mul_comm, ← log_pow, ← log_zpow,
    log_lt_log_iff (pow_pos (by linarith) _) (zpow_pos (by linarith) _),
    ← div_lt_one (zpow_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at hq₁
  rw [div_lt_div_iff₀ (by simp [q.den_pos]) (log_pos hwa), mul_comm (w _).log,
    ← log_pow, ← log_zpow, log_lt_log_iff (zpow_pos (by linarith) _) (pow_pos (by linarith) _),
    ← one_lt_div (zpow_pos (by linarith) _), ← map_pow, ← map_zpow₀, ← map_div₀] at hq₂
  exact not_lt_of_gt (h.lt_one_iff.1 hq₁) hq₂

/--
If `v` and `w` are two real absolute values on a field `F`, then `v` and `w` are equivalent if
and only if there exists a positive real constant `c` such that for all `x : R`, `(f x)^c = g x`.
-/
theorem isEquiv_iff_exists_rpow_eq {v w : AbsoluteValue F ℝ} :
    v.IsEquiv w ↔ ∃ c : ℝ, 0 < c ∧ (v · ^ c) = w := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht, h⟩ ↦ isEquiv_iff_lt_one_iff.2
    fun x ↦ h ▸ (rpow_lt_one_iff' (v.nonneg x) ht).symm⟩
  by_cases hw : w.IsNontrivial
  · let ⟨a, ha₀, ha₁⟩ := hw
    refine ⟨(w a).log / (v a).log, h.log_div_log_pos ha₀ ha₁, funext fun b ↦ ?_⟩
    rcases eq_or_ne b 0 with rfl | hb₀; · simp [zero_rpow (by linarith [h.log_div_log_pos ha₀ ha₁])]
    rcases eq_or_ne (w b) 1 with hb₁ | hb₁; · simp [hb₁, h.eq_one_iff.2 hb₁]
    rw [← h.symm.log_div_log_eq_log_div_log ha₀ ha₁ hb₀ hb₁, div_eq_inv_mul, rpow_mul (v.nonneg _),
      rpow_inv_log (v.pos hb₀) (h.eq_one_iff.not.2 hb₁), exp_one_rpow, exp_log (w.pos hb₀)]
  · exact ⟨1, zero_lt_one,
      funext fun x ↦ by
        rcases eq_or_ne x 0 with rfl | h₀ <;>
        aesop (add simp [h.isNontrivial_congr])⟩

theorem IsEquiv.equivWithAbs_image_mem_nhds_zero (h : v.IsEquiv w) {U : Set (WithAbs v)}
    (hU : U ∈ 𝓝 0) : WithAbs.congr v w (.refl F) '' U ∈ 𝓝 0 := by
  rw [Metric.mem_nhds_iff] at hU ⊢
  obtain ⟨ε, hε, hU⟩ := hU
  obtain ⟨c, hc, hvw⟩ := isEquiv_iff_exists_rpow_eq.1 h
  refine ⟨ε ^ c, rpow_pos_of_pos hε _, fun x hx ↦ ?_⟩
  rw [← RingEquiv.apply_symm_apply (WithAbs.congr v w (.refl F)) x]
  refine Set.mem_image_of_mem _ (hU ?_)
  rw [Metric.mem_ball, dist_zero_right, WithAbs.norm_eq_apply_ofAbs, ← funext_iff.1 hvw,
    rpow_lt_rpow_iff (v.nonneg _) hε.le hc] at hx
  simpa [WithAbs.norm_eq_apply_ofAbs]

open Topology IsTopologicalAddGroup in
theorem IsEquiv.isEmbedding_equivWithAbs (h : v.IsEquiv w) :
    IsEmbedding (WithAbs.congr v w (.refl F)) := by
  refine IsInducing.isEmbedding <| isInducing_iff_nhds_zero.2 <| Filter.ext fun U ↦
    ⟨fun hU ↦ ?_, fun hU ↦ ?_⟩
  · exact ⟨WithAbs.congr v w (.refl F)'' U, h.equivWithAbs_image_mem_nhds_zero hU,
      by
        #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
        (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
        goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
        the new canonicalizer; a minimization would help. The original proof was:
        `grind [RingEquiv.image_eq_preimage_symm, Set.preimage_preimage]` -/
        rw [RingEquiv.image_eq_preimage_symm, Set.preimage_preimage]; simp⟩
  · rw [← RingEquiv.coe_toEquiv, ← Filter.map_equiv_symm] at hU
    obtain ⟨s, hs, hss⟩ := Filter.mem_map_iff_exists_image.1 hU
    rw [← RingEquiv.coe_toEquiv_symm, WithAbs.congr_symm] at hss
    exact Filter.mem_of_superset (h.symm.equivWithAbs_image_mem_nhds_zero hs) hss

theorem isEquiv_iff_isHomeomorph (v w : AbsoluteValue F ℝ) :
    v.IsEquiv w ↔ IsHomeomorph (WithAbs.congr v w (.refl F)) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  refine ⟨fun h ↦ ⟨h.isEmbedding_equivWithAbs, RingEquiv.surjective _⟩, fun ⟨hi, _⟩ ↦ ?_⟩
  refine isEquiv_iff_lt_one_iff.2 fun x ↦ ?_
  conv_lhs => rw [← WithAbs.ofAbs_toAbs v x]
  conv_rhs => rw [← WithAbs.ofAbs_toAbs w x]
  rw [← WithAbs.norm_eq_apply_ofAbs, ← WithAbs.norm_eq_apply_ofAbs,
    ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  exact ⟨fun h ↦ by simpa [Function.comp_def] using (hi.continuous.tendsto 0).comp h, fun h ↦ by
    simpa [Function.comp_def] using (hi.continuous_iff (f := (WithAbs.congr v w (.refl F)).symm)).2
      continuous_id |>.tendsto 0 |>.comp h ⟩

end Real

end AbsoluteValue
