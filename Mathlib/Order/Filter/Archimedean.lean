/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic.GCongr

#align_import order.filter.archimedean from "leanprover-community/mathlib"@"8631e2d5ea77f6c13054d9151d82b83069680cb1"

/-!
# `Filter.atTop` filter and archimedean (semi)rings/fields

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `Nat.cast ∘ f : α → R` tends to `Filter.atTop` along a filter `l` if and only if so
does `f`. We also prove that `Nat.cast : ℕ → R` tends to `Filter.atTop` along `Filter.atTop`, as
well as version of these two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/


variable {α R : Type*}

open Filter Set Function

@[simp]
theorem Nat.comap_cast_atTop [StrictOrderedSemiring R] [Archimedean R] :
    comap ((↑) : ℕ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Nat.cast_le) exists_nat_ge
#align nat.comap_coe_at_top Nat.comap_cast_atTop

theorem tendsto_natCast_atTop_iff [StrictOrderedSemiring R] [Archimedean R] {f : α → ℕ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop :=
  tendsto_atTop_embedding (fun _ _ => Nat.cast_le) exists_nat_ge
#align tendsto_coe_nat_at_top_iff tendsto_natCast_atTop_iff

@[deprecated (since := "2024-04-17")]
alias tendsto_nat_cast_atTop_iff := tendsto_natCast_atTop_iff

theorem tendsto_natCast_atTop_atTop [OrderedSemiring R] [Archimedean R] :
    Tendsto ((↑) : ℕ → R) atTop atTop :=
  Nat.mono_cast.tendsto_atTop_atTop exists_nat_ge
#align tendsto_coe_nat_at_top_at_top tendsto_natCast_atTop_atTop

@[deprecated (since := "2024-04-17")]
alias tendsto_nat_cast_atTop_atTop := tendsto_natCast_atTop_atTop

theorem Filter.Eventually.natCast_atTop [OrderedSemiring R] [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x:R) in atTop, p x) : ∀ᶠ (n:ℕ) in atTop, p n :=
  tendsto_natCast_atTop_atTop.eventually h

@[deprecated (since := "2024-04-17")]
alias Filter.Eventually.nat_cast_atTop := Filter.Eventually.natCast_atTop

@[simp] theorem Int.comap_cast_atTop [StrictOrderedRing R] [Archimedean R] :
    comap ((↑) : ℤ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, mod_cast hn⟩
#align int.comap_coe_at_top Int.comap_cast_atTop

@[simp]
theorem Int.comap_cast_atBot [StrictOrderedRing R] [Archimedean R] :
    comap ((↑) : ℤ → R) atBot = atBot :=
  comap_embedding_atBot (fun _ _ => Int.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le] using hn⟩
#align int.comap_coe_at_bot Int.comap_cast_atBot

theorem tendsto_intCast_atTop_iff [StrictOrderedRing R] [Archimedean R] {f : α → ℤ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop := by
  rw [← @Int.comap_cast_atTop R, tendsto_comap_iff]; rfl
#align tendsto_coe_int_at_top_iff tendsto_intCast_atTop_iff

@[deprecated (since := "2024-04-17")]
alias tendsto_int_cast_atTop_iff := tendsto_intCast_atTop_iff

theorem tendsto_intCast_atBot_iff [StrictOrderedRing R] [Archimedean R] {f : α → ℤ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atBot ↔ Tendsto f l atBot := by
  rw [← @Int.comap_cast_atBot R, tendsto_comap_iff]; rfl
#align tendsto_coe_int_at_bot_iff tendsto_intCast_atBot_iff

@[deprecated (since := "2024-04-17")]
alias tendsto_int_cast_atBot_iff := tendsto_intCast_atBot_iff

theorem tendsto_intCast_atTop_atTop [StrictOrderedRing R] [Archimedean R] :
    Tendsto ((↑) : ℤ → R) atTop atTop :=
  tendsto_intCast_atTop_iff.2 tendsto_id
#align tendsto_coe_int_at_top_at_top tendsto_intCast_atTop_atTop

@[deprecated (since := "2024-04-17")]
alias tendsto_int_cast_atTop_atTop := tendsto_intCast_atTop_atTop

theorem Filter.Eventually.intCast_atTop [StrictOrderedRing R] [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x:R) in atTop, p x) : ∀ᶠ (n:ℤ) in atTop, p n := by
  rw [← Int.comap_cast_atTop (R := R)]; exact h.comap _

@[deprecated (since := "2024-04-17")]
alias Filter.Eventually.int_cast_atTop := Filter.Eventually.intCast_atTop

theorem Filter.Eventually.intCast_atBot [StrictOrderedRing R] [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x:R) in atBot, p x) : ∀ᶠ (n:ℤ) in atBot, p n := by
  rw [← Int.comap_cast_atBot (R := R)]; exact h.comap _

@[deprecated (since := "2024-04-17")]
alias Filter.Eventually.int_cast_atBot := Filter.Eventually.intCast_atBot

@[simp]
theorem Rat.comap_cast_atTop [LinearOrderedField R] [Archimedean R] :
    comap ((↑) : ℚ → R) atTop = atTop :=
  comap_embedding_atTop (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge r; ⟨n, by simpa⟩
#align rat.comap_coe_at_top Rat.comap_cast_atTop

@[simp] theorem Rat.comap_cast_atBot [LinearOrderedField R] [Archimedean R] :
    comap ((↑) : ℚ → R) atBot = atBot :=
  comap_embedding_atBot (fun _ _ => Rat.cast_le) fun r =>
    let ⟨n, hn⟩ := exists_nat_ge (-r)
    ⟨-n, by simpa [neg_le]⟩
#align rat.comap_coe_at_bot Rat.comap_cast_atBot

theorem tendsto_ratCast_atTop_iff [LinearOrderedField R] [Archimedean R] {f : α → ℚ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atTop ↔ Tendsto f l atTop := by
  rw [← @Rat.comap_cast_atTop R, tendsto_comap_iff]; rfl
#align tendsto_coe_rat_at_top_iff tendsto_ratCast_atTop_iff

@[deprecated (since := "2024-04-17")]
alias tendsto_rat_cast_atTop_iff := tendsto_ratCast_atTop_iff

theorem tendsto_ratCast_atBot_iff [LinearOrderedField R] [Archimedean R] {f : α → ℚ}
    {l : Filter α} : Tendsto (fun n => (f n : R)) l atBot ↔ Tendsto f l atBot := by
  rw [← @Rat.comap_cast_atBot R, tendsto_comap_iff]; rfl
#align tendsto_coe_rat_at_bot_iff tendsto_ratCast_atBot_iff

@[deprecated (since := "2024-04-17")]
alias tendsto_rat_cast_atBot_iff := tendsto_ratCast_atBot_iff

theorem Filter.Eventually.ratCast_atTop [LinearOrderedField R] [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x:R) in atTop, p x) : ∀ᶠ (n:ℚ) in atTop, p n := by
  rw [← Rat.comap_cast_atTop (R := R)]; exact h.comap _

@[deprecated (since := "2024-04-17")]
alias Filter.Eventually.rat_cast_atTop := Filter.Eventually.ratCast_atTop

theorem Filter.Eventually.ratCast_atBot [LinearOrderedField R] [Archimedean R] {p : R → Prop}
    (h : ∀ᶠ (x:R) in atBot, p x) : ∀ᶠ (n:ℚ) in atBot, p n := by
  rw [← Rat.comap_cast_atBot (R := R)]; exact h.comap _

@[deprecated (since := "2024-04-17")]
alias Filter.Eventually.rat_cast_atBot := Filter.Eventually.ratCast_atBot

-- Porting note (#10756): new lemma
theorem atTop_hasAntitoneBasis_of_archimedean [OrderedSemiring R] [Archimedean R] :
    (atTop : Filter R).HasAntitoneBasis fun n : ℕ => Ici n :=
  hasAntitoneBasis_atTop.comp_mono Nat.mono_cast tendsto_natCast_atTop_atTop

theorem atTop_hasCountableBasis_of_archimedean [StrictOrderedSemiring R] [Archimedean R] :
    (atTop : Filter R).HasCountableBasis (fun _ : ℕ => True) fun n => Ici n :=
  ⟨atTop_hasAntitoneBasis_of_archimedean.1, to_countable _⟩
#align at_top_countable_basis_of_archimedean atTop_hasCountableBasis_of_archimedean

-- Porting note (#11215): TODO: generalize to a `StrictOrderedRing`
theorem atBot_hasCountableBasis_of_archimedean [LinearOrderedRing R] [Archimedean R] :
    (atBot : Filter R).HasCountableBasis (fun _ : ℤ => True) fun m => Iic m :=
  { countable := to_countable _
    toHasBasis :=
      atBot_basis.to_hasBasis
        (fun x _ => let ⟨m, hm⟩ := exists_int_lt x; ⟨m, trivial, Iic_subset_Iic.2 hm.le⟩)
        fun m _ => ⟨m, trivial, Subset.rfl⟩ }
#align at_bot_countable_basis_of_archimedean atBot_hasCountableBasis_of_archimedean

instance (priority := 100) atTop_isCountablyGenerated_of_archimedean [StrictOrderedSemiring R]
    [Archimedean R] : (atTop : Filter R).IsCountablyGenerated :=
  atTop_hasCountableBasis_of_archimedean.isCountablyGenerated
#align at_top_countably_generated_of_archimedean atTop_isCountablyGenerated_of_archimedean

instance (priority := 100) atBot_isCountablyGenerated_of_archimedean [LinearOrderedRing R]
    [Archimedean R] : (atBot : Filter R).IsCountablyGenerated :=
  atBot_hasCountableBasis_of_archimedean.isCountablyGenerated
#align at_bot_countably_generated_of_archimedean atBot_isCountablyGenerated_of_archimedean

namespace Filter

variable {l : Filter α} {f : α → R} {r : R}

section LinearOrderedSemiring

variable [LinearOrderedSemiring R] [Archimedean R]

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the left) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `Filter.Tendsto.const_mul_atTop`). -/
theorem Tendsto.const_mul_atTop' (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr
  rw [nsmul_eq_mul'] at hn
  filter_upwards [tendsto_atTop.1 hf (n * max b 0)] with x hx
  calc
    b ≤ 1 * max b 0 := by
    { rw [one_mul]
      exact le_max_left _ _ }
    _ ≤ r * n * max b 0 := by gcongr
    _ = r * (n * max b 0) := by rw [mul_assoc]
    _ ≤ r * f x := by gcongr
#align filter.tendsto.const_mul_at_top' Filter.Tendsto.const_mul_atTop'

/-- If a function tends to infinity along a filter, then this function multiplied by a positive
constant (on the right) also tends to infinity. The archimedean assumption is convenient to get a
statement that works on `ℕ`, `ℤ` and `ℝ`, although not necessary (a version in ordered fields is
given in `Filter.Tendsto.atTop_mul_const`). -/
theorem Tendsto.atTop_mul_const' (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop := by
  refine tendsto_atTop.2 fun b => ?_
  obtain ⟨n : ℕ, hn : 1 ≤ n • r⟩ := Archimedean.arch 1 hr
  have hn' : 1 ≤ (n : R) * r := by rwa [nsmul_eq_mul] at hn
  filter_upwards [tendsto_atTop.1 hf (max b 0 * n)] with x hx
  calc
    b ≤ max b 0 * 1 := by
    { rw [mul_one]
      exact le_max_left _ _ }
    _ ≤ max b 0 * (n * r) := by gcongr
    _ = max b 0 * n * r := by rw [mul_assoc]
    _ ≤ f x * r := by gcongr
#align filter.tendsto.at_top_mul_const' Filter.Tendsto.atTop_mul_const'

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing R] [Archimedean R]

/-- See also `Filter.Tendsto.atTop_mul_neg_const` for a version of this lemma for
`LinearOrderedField`s which does not require the `Archimedean` assumption. -/
theorem Tendsto.atTop_mul_neg_const' (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot := by
  simpa only [tendsto_neg_atTop_iff, mul_neg] using hf.atTop_mul_const' (neg_pos.mpr hr)
#align filter.tendsto.at_top_mul_neg_const' Filter.Tendsto.atTop_mul_neg_const'

/-- See also `Filter.Tendsto.atBot_mul_const` for a version of this lemma for
`LinearOrderedField`s which does not require the `Archimedean` assumption. -/
theorem Tendsto.atBot_mul_const' (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot := by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul] at hf ⊢
  exact hf.atTop_mul_const' hr
#align filter.tendsto.at_bot_mul_const' Filter.Tendsto.atBot_mul_const'

/-- See also `Filter.Tendsto.atBot_mul_neg_const` for a version of this lemma for
`LinearOrderedField`s which does not require the `Archimedean` assumption. -/
theorem Tendsto.atBot_mul_neg_const' (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop := by
  simpa only [mul_neg, tendsto_neg_atBot_iff] using hf.atBot_mul_const' (neg_pos.2 hr)
#align filter.tendsto.at_bot_mul_neg_const' Filter.Tendsto.atBot_mul_neg_const'

end LinearOrderedRing

section LinearOrderedCancelAddCommMonoid

variable [LinearOrderedCancelAddCommMonoid R] [Archimedean R]

theorem Tendsto.atTop_nsmul_const {f : α → ℕ} (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atTop := by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : ℕ, hn : s ≤ n • r⟩ := Archimedean.arch s hr
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (nsmul_le_nsmul_left hr.le ha)
#align filter.tendsto.at_top_nsmul_const Filter.Tendsto.atTop_nsmul_const

end LinearOrderedCancelAddCommMonoid

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup R] [Archimedean R]

theorem Tendsto.atTop_nsmul_neg_const {f : α → ℕ} (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atBot := by simpa using hf.atTop_nsmul_const (neg_pos.2 hr)
#align filter.tendsto.at_top_nsmul_neg_const Filter.Tendsto.atTop_nsmul_neg_const

theorem Tendsto.atTop_zsmul_const {f : α → ℤ} (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atTop := by
  refine tendsto_atTop.mpr fun s => ?_
  obtain ⟨n : ℕ, hn : s ≤ n • r⟩ := Archimedean.arch s hr
  replace hn : s ≤ (n : ℤ) • r := by simpa
  exact (tendsto_atTop.mp hf n).mono fun a ha => hn.trans (zsmul_le_zsmul hr.le ha)
#align filter.tendsto.at_top_zsmul_const Filter.Tendsto.atTop_zsmul_const

theorem Tendsto.atTop_zsmul_neg_const {f : α → ℤ} (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x • r) l atBot := by simpa using hf.atTop_zsmul_const (neg_pos.2 hr)
#align filter.tendsto.at_top_zsmul_neg_const Filter.Tendsto.atTop_zsmul_neg_const

theorem Tendsto.atBot_zsmul_const {f : α → ℤ} (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x • r) l atBot := by
  simp only [← tendsto_neg_atTop_iff, ← neg_zsmul] at hf ⊢
  exact hf.atTop_zsmul_const hr
#align filter.tendsto.at_bot_zsmul_const Filter.Tendsto.atBot_zsmul_const

theorem Tendsto.atBot_zsmul_neg_const {f : α → ℤ} (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x • r) l atTop := by simpa using hf.atBot_zsmul_const (neg_pos.2 hr)
#align filter.tendsto.at_bot_zsmul_neg_const Filter.Tendsto.atBot_zsmul_neg_const

end LinearOrderedAddCommGroup

end Filter
