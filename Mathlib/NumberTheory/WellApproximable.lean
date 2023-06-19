/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module number_theory.well_approximable
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Dynamics.Ergodic.AddCircle
import Mathbin.MeasureTheory.Covering.LiminfLimsup

/-!
# Well-approximable numbers and Gallagher's ergodic theorem

Gallagher's ergodic theorem is a result in metric number theory. It thus belongs to that branch of
mathematics concerning arithmetic properties of real numbers which hold almost eveywhere with
respect to the Lebesgue measure.

Gallagher's theorem concerns the approximation of real numbers by rational numbers. The input is a
sequence of distances `δ₁, δ₂, ...`, and the theorem concerns the set of real numbers `x` for which
there is an infinity of solutions to:
$$
  |x - m/n| < δₙ,
$$
where the rational number `m/n` is in lowest terms. The result is that for any `δ`, this set is
either almost all `x` or almost no `x`.

This result was proved by Gallagher in 1959
[P. Gallagher, *Approximation by reduced fractions*](Gallagher1961). It is formalised here as
`add_circle.add_well_approximable_ae_empty_or_univ` except with `x` belonging to the circle `ℝ ⧸ ℤ`
since this turns out to be more natural.

Given a particular `δ`, the Duffin-Schaeffer conjecture (now a theorem) gives a criterion for
deciding which of the two cases in the conclusion of Gallagher's theorem actually occurs. It was
proved by Koukoulopoulos and Maynard in 2019
[D. Koukoulopoulos, J. Maynard, *On the Duffin-Schaeffer conjecture*](KoukoulopoulosMaynard2020).
We do *not* include a formalisation of the Koukoulopoulos-Maynard result here.

## Main definitions and results:

 * `approx_order_of`: in a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approx_order_of A n δ`
   is the set of elements within a distance `δ` of a point of order `n`.
 * `well_approximable`: in a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`,
   `well_approximable A δ` is the limsup as `n → ∞` of the sets `approx_order_of A n δₙ`. Thus, it
   is the set of points that lie in infinitely many of the sets `approx_order_of A n δₙ`.
 * `add_circle.add_well_approximable_ae_empty_or_univ`: *Gallagher's ergodic theorem* says that for
   for the (additive) circle `𝕊`, for any sequence of distances `δ`, the set
   `add_well_approximable 𝕊 δ` is almost empty or almost full.

## TODO:

The hypothesis `hδ` in `add_circle.add_well_approximable_ae_empty_or_univ` can be dropped.
An elementary (non-measure-theoretic) argument shows that if `¬ hδ` holds then
`add_well_approximable 𝕊 δ = univ` (provided `δ` is non-negative).
-/


open Set Filter Function Metric MeasureTheory

open scoped MeasureTheory Topology Pointwise

/-- In a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approx_order_of A n δ` is the set of
elements within a distance `δ` of a point of order `n`. -/
@[to_additive approxAddOrderOf
      "In a seminormed additive group `A`, given `n : ℕ` and `δ : ℝ`,\n`approx_add_order_of A n δ` is the set of elements within a distance `δ` of a point of order `n`."]
def approxOrderOf (A : Type _) [SeminormedGroup A] (n : ℕ) (δ : ℝ) : Set A :=
  thickening δ {y | orderOf y = n}
#align approx_order_of approxOrderOf
#align approx_add_order_of approxAddOrderOf

@[to_additive mem_approx_add_orderOf_iff]
theorem mem_approxOrderOf_iff {A : Type _} [SeminormedGroup A] {n : ℕ} {δ : ℝ} {a : A} :
    a ∈ approxOrderOf A n δ ↔ ∃ b : A, orderOf b = n ∧ a ∈ ball b δ := by
  simp only [approxOrderOf, thickening_eq_bUnion_ball, mem_Union₂, mem_set_of_eq, exists_prop]
#align mem_approx_order_of_iff mem_approxOrderOf_iff
#align mem_approx_add_order_of_iff mem_approx_add_orderOf_iff

/-- In a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`, `well_approximable A δ`
is the limsup as `n → ∞` of the sets `approx_order_of A n δₙ`. Thus, it is the set of points that
lie in infinitely many of the sets `approx_order_of A n δₙ`. -/
@[to_additive addWellApproximable
      "In a seminormed additive group `A`, given a sequence of\ndistances `δ₁, δ₂, ...`, `add_well_approximable A δ` is the limsup as `n → ∞` of the sets\n`approx_add_order_of A n δₙ`. Thus, it is the set of points that lie in infinitely many of the sets\n`approx_add_order_of A n δₙ`."]
def wellApproximable (A : Type _) [SeminormedGroup A] (δ : ℕ → ℝ) : Set A :=
  blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n
#align well_approximable wellApproximable
#align add_well_approximable addWellApproximable

@[to_additive mem_add_wellApproximable_iff]
theorem mem_wellApproximable_iff {A : Type _} [SeminormedGroup A] {δ : ℕ → ℝ} {a : A} :
    a ∈ wellApproximable A δ ↔
      a ∈ blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n :=
  Iff.rfl
#align mem_well_approximable_iff mem_wellApproximable_iff
#align mem_add_well_approximable_iff mem_add_wellApproximable_iff

namespace approxOrderOf

variable {A : Type _} [SeminormedCommGroup A] {a : A} {m n : ℕ} (δ : ℝ)

@[to_additive]
theorem image_pow_subset_of_coprime (hm : 0 < m) (hmn : n.coprime m) :
    (fun y => y ^ m) '' approxOrderOf A n δ ⊆ approxOrderOf A n (m * δ) :=
  by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hab⟩ := mem_approx_order_of_iff.mp ha
  replace hb : b ^ m ∈ {u : A | orderOf u = n}; · rw [← hb] at hmn ⊢; exact orderOf_pow_coprime hmn
  apply ball_subset_thickening hb ((m : ℝ) • δ)
  convert pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul, Algebra.id.smul_eq_mul]
#align approx_order_of.image_pow_subset_of_coprime approxOrderOf.image_pow_subset_of_coprime
#align approx_add_order_of.image_nsmul_subset_of_coprime approxAddOrderOf.image_nsmul_subset_of_coprime

@[to_additive]
theorem image_pow_subset (n : ℕ) (hm : 0 < m) :
    (fun y => y ^ m) '' approxOrderOf A (n * m) δ ⊆ approxOrderOf A n (m * δ) :=
  by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb : orderOf b = n * m, hab : a ∈ ball b δ⟩ := mem_approx_order_of_iff.mp ha
  replace hb : b ^ m ∈ {y : A | orderOf y = n}
  · rw [mem_set_of_eq, orderOf_pow' b hm.ne', hb, Nat.gcd_mul_left_left, n.mul_div_cancel hm]
  apply ball_subset_thickening hb (m * δ)
  convert pow_mem_ball hm hab
  simp only [nsmul_eq_mul]
#align approx_order_of.image_pow_subset approxOrderOf.image_pow_subset
#align approx_add_order_of.image_nsmul_subset approxAddOrderOf.image_nsmul_subset

@[to_additive]
theorem smul_subset_of_coprime (han : (orderOf a).coprime n) :
    a • approxOrderOf A n δ ⊆ approxOrderOf A (orderOf a * n) δ :=
  by
  simp_rw [approxOrderOf, thickening_eq_bUnion_ball, ← image_smul, image_Union₂, image_smul,
    smul_ball'', smul_eq_mul, mem_set_of_eq]
  refine' Union₂_subset_iff.mpr fun b hb c hc => _
  simp only [mem_Union, exists_prop]
  refine' ⟨a * b, _, hc⟩
  rw [← hb] at han ⊢
  exact (Commute.all a b).orderOf_mul_eq_mul_orderOf_of_coprime han
#align approx_order_of.smul_subset_of_coprime approxOrderOf.smul_subset_of_coprime
#align approx_add_order_of.vadd_subset_of_coprime approxAddOrderOf.vadd_subset_of_coprime

@[to_additive vadd_eq_of_mul_dvd]
theorem smul_eq_of_mul_dvd (hn : 0 < n) (han : orderOf a ^ 2 ∣ n) :
    a • approxOrderOf A n δ = approxOrderOf A n δ :=
  by
  simp_rw [approxOrderOf, thickening_eq_bUnion_ball, ← image_smul, image_Union₂, image_smul,
    smul_ball'', smul_eq_mul, mem_set_of_eq]
  replace han : ∀ {b : A}, orderOf b = n → orderOf (a * b) = n
  · intro b hb
    rw [← hb] at han hn 
    rw [sq] at han 
    rwa [(Commute.all a b).orderOf_mul_eq_right_of_forall_prime_mul_dvd (order_of_pos_iff.mp hn)
        fun p hp hp' => dvd_trans (mul_dvd_mul_right hp' <| orderOf a) han]
  let f : {b : A | orderOf b = n} → {b : A | orderOf b = n} := fun b => ⟨a * b, han b.property⟩
  have hf : surjective f := by
    rintro ⟨b, hb⟩
    refine' ⟨⟨a⁻¹ * b, _⟩, _⟩
    · rw [mem_set_of_eq, ← orderOf_inv, mul_inv_rev, inv_inv, mul_comm]
      apply han
      simpa
    · simp only [Subtype.mk_eq_mk, Subtype.coe_mk, mul_inv_cancel_left]
  simpa only [f, mem_set_of_eq, Subtype.coe_mk, Union_coe_set] using
    hf.Union_comp fun b => ball (b : A) δ
#align approx_order_of.smul_eq_of_mul_dvd approxOrderOf.smul_eq_of_mul_dvd
#align approx_add_order_of.vadd_eq_of_mul_dvd approxAddOrderOf.vadd_eq_of_mul_dvd

end approxOrderOf

namespace UnitAddCircle

theorem mem_approxAddOrderOf_iff {δ : ℝ} {x : UnitAddCircle} {n : ℕ} (hn : 0 < n) :
    x ∈ approxAddOrderOf UnitAddCircle n δ ↔ ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ :=
  by
  haveI := Real.fact_zero_lt_one
  simp only [mem_approx_add_orderOf_iff, mem_set_of_eq, ball, exists_prop, dist_eq_norm,
    AddCircle.addOrderOf_eq_pos_iff hn, mul_one]
  constructor
  · rintro ⟨y, ⟨m, hm₁, hm₂, rfl⟩, hx⟩; exact ⟨m, hm₁, hm₂, hx⟩
  · rintro ⟨m, hm₁, hm₂, hx⟩; exact ⟨↑((m : ℝ) / n), ⟨m, hm₁, hm₂, rfl⟩, hx⟩
#align unit_add_circle.mem_approx_add_order_of_iff UnitAddCircle.mem_approxAddOrderOf_iff

theorem mem_addWellApproximable_iff (δ : ℕ → ℝ) (x : UnitAddCircle) :
    x ∈ addWellApproximable UnitAddCircle δ ↔
      {n : ℕ | ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ n}.Infinite :=
  by
  simp only [mem_add_wellApproximable_iff, ← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq,
    mem_set_of_eq]
  refine' iff_of_eq (congr_arg Set.Infinite <| ext fun n => ⟨fun hn => _, fun hn => _⟩)
  · exact (mem_approx_add_orderOf_iff hn.1).mp hn.2
  · have h : 0 < n := by obtain ⟨m, hm₁, hm₂, hm₃⟩ := hn; exact pos_of_gt hm₁
    exact ⟨h, (mem_approx_add_orderOf_iff h).mpr hn⟩
#align unit_add_circle.mem_add_well_approximable_iff UnitAddCircle.mem_addWellApproximable_iff

end UnitAddCircle

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

local notation a "∤" b => ¬a ∣ b

local notation a "∣∣" b => a ∣ b ∧ (a * a)∤b

local notation "𝕊" => AddCircle T

/-- *Gallagher's ergodic theorem* on Diophantine approximation. -/
theorem addWellApproximable_ae_empty_or_univ (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    (∀ᵐ x, ¬addWellApproximable 𝕊 δ x) ∨ ∀ᵐ x, addWellApproximable 𝕊 δ x :=
  by
  /- Sketch of proof:
  
    Let `E := add_well_approximable 𝕊 δ`. For each prime `p : ℕ`, we can partition `E` into three
    pieces `E = (A p) ∪ (B p) ∪ (C p)` where:
      `A p = blimsup (approx_add_order_of 𝕊 n (δ n)) at_top (λ n, 0 < n ∧ (p ∤ n))`
      `B p = blimsup (approx_add_order_of 𝕊 n (δ n)) at_top (λ n, 0 < n ∧ (p ∣∣ n))`
      `C p = blimsup (approx_add_order_of 𝕊 n (δ n)) at_top (λ n, 0 < n ∧ (p*p ∣ n))`.
    (In other words, `A p` is the set of points `x` for which there exist infinitely-many `n` such
    that `x` is within a distance `δ n` of a point of order `n` and `p ∤ n`. Similarly for `B`, `C`.)
  
    These sets have the following key properties:
      1. `A p` is almost invariant under the ergodic map `y ↦ p • y`
      2. `B p` is almost invariant under the ergodic map `y ↦ p • y + 1/p`
      3. `C p` is invariant under the map `y ↦ y + 1/p`
    To prove 1 and 2 we need the key result `blimsup_thickening_mul_ae_eq` but 3 is elementary.
  
    It follows from `add_circle.ergodic_nsmul_add` and `ergodic.ae_empty_or_univ_of_image_ae_le` that
    if either `A p` or `B p` is not almost empty for any `p`, then it is almost full and thus so is
    `E`. We may therefore assume that both `A p` and `B p` are almost empty for all `p`. We thus have
    `E` is almost equal to `C p` for every prime. Combining this with 3 we find that `E` is almost
    invariant under the map `y ↦ y + 1/p` for every prime `p`. The required result then follows from
    `add_circle.ae_empty_or_univ_of_forall_vadd_ae_eq_self`. -/
  letI : SemilatticeSup Nat.Primes := Nat.Subtype.semilatticeSup _
  set μ : Measure 𝕊 := volume
  set u : Nat.Primes → 𝕊 := fun p => ↑((↑(1 : ℕ) : ℝ) / p * T)
  have hu₀ : ∀ p : Nat.Primes, addOrderOf (u p) = (p : ℕ) := by rintro ⟨p, hp⟩;
    exact add_order_of_div_of_gcd_eq_one hp.pos (gcd_one_left p)
  have hu : tendsto (addOrderOf ∘ u) at_top at_top :=
    by
    rw [(funext hu₀ : addOrderOf ∘ u = coe)]
    have h_mono : Monotone (coe : Nat.Primes → ℕ) := fun p q hpq => hpq
    refine' h_mono.tendsto_at_top_at_top fun n => _
    obtain ⟨p, hp, hp'⟩ := n.exists_infinite_primes
    exact ⟨⟨p, hp'⟩, hp⟩
  set E := addWellApproximable 𝕊 δ
  set X : ℕ → Set 𝕊 := fun n => approxAddOrderOf 𝕊 n (δ n)
  set A : ℕ → Set 𝕊 := fun p => blimsup X at_top fun n => 0 < n ∧ p∤n
  set B : ℕ → Set 𝕊 := fun p => blimsup X at_top fun n => 0 < n ∧ p∣∣n
  set C : ℕ → Set 𝕊 := fun p => blimsup X at_top fun n => 0 < n ∧ p ^ 2 ∣ n
  have hA₀ : ∀ p, MeasurableSet (A p) := fun p =>
    MeasurableSet.measurableSet_blimsup fun n hn => is_open_thickening.measurable_set
  have hB₀ : ∀ p, MeasurableSet (B p) := fun p =>
    MeasurableSet.measurableSet_blimsup fun n hn => is_open_thickening.measurable_set
  have hE₀ : null_measurable_set E μ :=
    by
    refine'
      (MeasurableSet.measurableSet_blimsup fun n hn => IsOpen.measurableSet _).NullMeasurableSet
    exact is_open_thickening
  have hE₁ : ∀ p, E = A p ∪ B p ∪ C p := by
    intro p
    simp only [E, addWellApproximable, ← blimsup_or_eq_sup, ← and_or_left, ← sup_eq_union, sq]
    congr
    refine' funext fun n => propext <| iff_self_and.mpr fun hn => _
    -- `tauto` can finish from here but unfortunately it's very slow.
    simp only [(em (p ∣ n)).symm, (em (p * p ∣ n)).symm, or_and_left, or_true_iff, true_and_iff,
      or_assoc']
  have hE₂ : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∧ B p =ᵐ[μ] (∅ : Set 𝕊) → E =ᵐ[μ] C p :=
    by
    rintro p ⟨hA, hB⟩
    rw [hE₁ p]
    exact union_ae_eq_right_of_ae_eq_empty ((union_ae_eq_right_of_ae_eq_empty hA).trans hB)
  have hA : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∨ A p =ᵐ[μ] univ :=
    by
    rintro ⟨p, hp⟩
    let f : 𝕊 → 𝕊 := fun y => (p : ℕ) • y
    suffices
      f '' A p ⊆ blimsup (fun n => approxAddOrderOf 𝕊 n (p * δ n)) at_top fun n => 0 < n ∧ p∤n
      by
      apply (ergodic_nsmul hp.one_lt).ae_empty_or_univ_of_image_ae_le (hA₀ p)
      apply (HasSubset.Subset.eventuallyLE this).congr eventually_eq.rfl
      exact
        blimsup_thickening_mul_ae_eq μ (fun n => 0 < n ∧ p∤n) (fun n => {y | addOrderOf y = n})
          (nat.cast_pos.mpr hp.pos) _ hδ
    refine' (sSupHom.setImage f).apply_blimsup_le.trans (mono_blimsup fun n hn => _)
    replace hn := nat.coprime_comm.mp (hp.coprime_iff_not_dvd.2 hn.2)
    exact approxAddOrderOf.image_nsmul_subset_of_coprime (δ n) hp.pos hn
  have hB : ∀ p : Nat.Primes, B p =ᵐ[μ] (∅ : Set 𝕊) ∨ B p =ᵐ[μ] univ :=
    by
    rintro ⟨p, hp⟩
    let x := u ⟨p, hp⟩
    let f : 𝕊 → 𝕊 := fun y => p • y + x
    suffices
      f '' B p ⊆ blimsup (fun n => approxAddOrderOf 𝕊 n (p * δ n)) at_top fun n => 0 < n ∧ p∣∣n
      by
      apply (ergodic_nsmul_add x hp.one_lt).ae_empty_or_univ_of_image_ae_le (hB₀ p)
      apply (HasSubset.Subset.eventuallyLE this).congr eventually_eq.rfl
      exact
        blimsup_thickening_mul_ae_eq μ (fun n => 0 < n ∧ p∣∣n) (fun n => {y | addOrderOf y = n})
          (nat.cast_pos.mpr hp.pos) _ hδ
    refine' (sSupHom.setImage f).apply_blimsup_le.trans (mono_blimsup _)
    rintro n ⟨hn, h_div, h_ndiv⟩
    have h_cop : (addOrderOf x).coprime (n / p) :=
      by
      obtain ⟨q, rfl⟩ := h_div
      rw [hu₀, Subtype.coe_mk, hp.coprime_iff_not_dvd, q.mul_div_cancel_left hp.pos]
      exact fun contra => h_ndiv (mul_dvd_mul_left p contra)
    replace h_div : n / p * p = n := Nat.div_mul_cancel h_div
    have hf : f = (fun y => x + y) ∘ fun y => p • y := by ext; simp [add_comm x]
    simp_rw [comp_app]
    rw [le_eq_subset, sSupHom.setImage_to_fun, hf, image_comp]
    have := @monotone_image 𝕊 𝕊 fun y => x + y
    specialize this (approxAddOrderOf.image_nsmul_subset (δ n) (n / p) hp.pos)
    simp only [h_div] at this ⊢
    refine' this.trans _
    convert approxAddOrderOf.vadd_subset_of_coprime (p * δ n) h_cop
    simp only [hu₀, Subtype.coe_mk, h_div, mul_comm p]
  change (∀ᵐ x, x ∉ E) ∨ E ∈ volume.ae
  rw [← eventually_eq_empty, ← eventually_eq_univ]
  have hC : ∀ p : Nat.Primes, u p +ᵥ C p = C p :=
    by
    intro p
    let e := (AddAction.toPerm (u p) : Equiv.Perm 𝕊).toOrderIsoSet
    change e (C p) = C p
    rw [e.apply_blimsup, ← hu₀ p]
    exact
      blimsup_congr
        (eventually_of_forall fun n hn => approxAddOrderOf.vadd_eq_of_mul_dvd (δ n) hn.1 hn.2)
  by_cases h : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∧ B p =ᵐ[μ] (∅ : Set 𝕊)
  · replace h : ∀ p : Nat.Primes, (u p +ᵥ E : Set _) =ᵐ[μ] E
    · intro p
      replace hE₂ : E =ᵐ[μ] C p := hE₂ p (h p)
      have h_qmp : MeasureTheory.Measure.QuasiMeasurePreserving ((· +ᵥ ·) (-u p)) μ μ :=
        (measure_preserving_vadd _ μ).QuasiMeasurePreserving
      refine' (h_qmp.vadd_ae_eq_of_ae_eq (u p) hE₂).trans (ae_eq_trans _ hE₂.symm)
      rw [hC]
    exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hE₀ h hu
  · right
    simp only [not_forall, not_and_or] at h 
    obtain ⟨p, hp⟩ := h
    rw [hE₁ p]
    cases hp
    · cases hA p; · contradiction
      simp only [h, union_ae_eq_univ_of_ae_eq_univ_left]
    · cases hB p; · contradiction
      simp only [h, union_ae_eq_univ_of_ae_eq_univ_left, union_ae_eq_univ_of_ae_eq_univ_right]
#align add_circle.add_well_approximable_ae_empty_or_univ AddCircle.addWellApproximable_ae_empty_or_univ

end AddCircle

