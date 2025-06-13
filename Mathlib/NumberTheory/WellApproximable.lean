/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.MeasureTheory.Covering.LiminfLimsup

/-!
# Well-approximable numbers and Gallagher's ergodic theorem

Gallagher's ergodic theorem is a result in metric number theory. It thus belongs to that branch of
mathematics concerning arithmetic properties of real numbers which hold almost everywhere with
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
[P. Gallagher, *Approximation by reduced fractions*][Gallagher1961]. It is formalised here as
`AddCircle.addWellApproximable_ae_empty_or_univ` except with `x` belonging to the circle `ℝ ⧸ ℤ`
since this turns out to be more natural.

Given a particular `δ`, the Duffin-Schaeffer conjecture (now a theorem) gives a criterion for
deciding which of the two cases in the conclusion of Gallagher's theorem actually occurs. It was
proved by Koukoulopoulos and Maynard in 2019
[D. Koukoulopoulos, J. Maynard, *On the Duffin-Schaeffer conjecture*][KoukoulopoulosMaynard2020].
We do *not* include a formalisation of the Koukoulopoulos-Maynard result here.

## Main definitions and results:

* `approxOrderOf`: in a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approxOrderOf A n δ`
  is the set of elements within a distance `δ` of a point of order `n`.
* `wellApproximable`: in a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`,
  `wellApproximable A δ` is the limsup as `n → ∞` of the sets `approxOrderOf A n δₙ`. Thus, it
  is the set of points that lie in infinitely many of the sets `approxOrderOf A n δₙ`.
* `AddCircle.addWellApproximable_ae_empty_or_univ`: *Gallagher's ergodic theorem* says that for
  the (additive) circle `𝕊`, for any sequence of distances `δ`, the set
  `addWellApproximable 𝕊 δ` is almost empty or almost full.
* `NormedAddCommGroup.exists_norm_nsmul_le`: a general version of Dirichlet's approximation theorem
* `AddCircle.exists_norm_nsmul_le`: Dirichlet's approximation theorem

## TODO

The hypothesis `hδ` in `AddCircle.addWellApproximable_ae_empty_or_univ` can be dropped.
An elementary (non-measure-theoretic) argument shows that if `¬ hδ` holds then
`addWellApproximable 𝕊 δ = univ` (provided `δ` is non-negative).

Use `AddCircle.exists_norm_nsmul_le` to prove:
`addWellApproximable 𝕊 (fun n ↦ 1 / n^2) = { ξ | ¬ IsOfFinAddOrder ξ }`
(which is equivalent to `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`).
-/


open Set Filter Function Metric MeasureTheory

open scoped MeasureTheory Topology Pointwise

/-- In a seminormed group `A`, given `n : ℕ` and `δ : ℝ`, `approxOrderOf A n δ` is the set of
elements within a distance `δ` of a point of order `n`. -/
@[to_additive "In a seminormed additive group `A`, given `n : ℕ` and `δ : ℝ`,
`approxAddOrderOf A n δ` is the set of elements within a distance `δ` of a point of order `n`."]
def approxOrderOf (A : Type*) [SeminormedGroup A] (n : ℕ) (δ : ℝ) : Set A :=
  thickening δ {y | orderOf y = n}

@[to_additive mem_approx_add_orderOf_iff]
theorem mem_approxOrderOf_iff {A : Type*} [SeminormedGroup A] {n : ℕ} {δ : ℝ} {a : A} :
    a ∈ approxOrderOf A n δ ↔ ∃ b : A, orderOf b = n ∧ a ∈ ball b δ := by
  simp only [approxOrderOf, thickening_eq_biUnion_ball, mem_iUnion₂, mem_setOf_eq, exists_prop]

/-- In a seminormed group `A`, given a sequence of distances `δ₁, δ₂, ...`, `wellApproximable A δ`
is the limsup as `n → ∞` of the sets `approxOrderOf A n δₙ`. Thus, it is the set of points that
lie in infinitely many of the sets `approxOrderOf A n δₙ`. -/
@[to_additive addWellApproximable "In a seminormed additive group `A`, given a sequence of
distances `δ₁, δ₂, ...`, `addWellApproximable A δ` is the limsup as `n → ∞` of the sets
`approxAddOrderOf A n δₙ`. Thus, it is the set of points that lie in infinitely many of the sets
`approxAddOrderOf A n δₙ`."]
def wellApproximable (A : Type*) [SeminormedGroup A] (δ : ℕ → ℝ) : Set A :=
  blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n

@[to_additive mem_add_wellApproximable_iff]
theorem mem_wellApproximable_iff {A : Type*} [SeminormedGroup A] {δ : ℕ → ℝ} {a : A} :
    a ∈ wellApproximable A δ ↔
      a ∈ blimsup (fun n => approxOrderOf A n (δ n)) atTop fun n => 0 < n :=
  Iff.rfl

namespace approxOrderOf

variable {A : Type*} [SeminormedCommGroup A] {a : A} {m n : ℕ} (δ : ℝ)

@[to_additive]
theorem image_pow_subset_of_coprime (hm : 0 < m) (hmn : n.Coprime m) :
    (fun (y : A) => y ^ m) '' approxOrderOf A n δ ⊆ approxOrderOf A n (m * δ) := by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hab⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m ∈ {u : A | orderOf u = n} := by
    rw [← hb] at hmn ⊢; exact hmn.orderOf_pow
  apply ball_subset_thickening hb ((m : ℝ) • δ)
  convert pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul, Algebra.id.smul_eq_mul]

@[to_additive]
theorem image_pow_subset (n : ℕ) (hm : 0 < m) :
    (fun (y : A) => y ^ m) '' approxOrderOf A (n * m) δ ⊆ approxOrderOf A n (m * δ) := by
  rintro - ⟨a, ha, rfl⟩
  obtain ⟨b, hb : orderOf b = n * m, hab : a ∈ ball b δ⟩ := mem_approxOrderOf_iff.mp ha
  replace hb : b ^ m ∈ {y : A | orderOf y = n} := by
    rw [mem_setOf_eq, orderOf_pow' b hm.ne', hb, Nat.gcd_mul_left_left, n.mul_div_cancel hm]
  apply ball_subset_thickening hb (m * δ)
  convert pow_mem_ball hm hab using 1
  simp only [nsmul_eq_mul]

@[to_additive]
theorem smul_subset_of_coprime (han : (orderOf a).Coprime n) :
    a • approxOrderOf A n δ ⊆ approxOrderOf A (orderOf a * n) δ := by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_setOf_eq]
  refine iUnion₂_subset_iff.mpr fun b hb c hc => ?_
  simp only [mem_iUnion, exists_prop]
  refine ⟨a * b, ?_, hc⟩
  rw [← hb] at han ⊢
  exact (Commute.all a b).orderOf_mul_eq_mul_orderOf_of_coprime han

@[to_additive vadd_eq_of_mul_dvd]
theorem smul_eq_of_mul_dvd (hn : 0 < n) (han : orderOf a ^ 2 ∣ n) :
    a • approxOrderOf A n δ = approxOrderOf A n δ := by
  simp_rw [approxOrderOf, thickening_eq_biUnion_ball, ← image_smul, image_iUnion₂, image_smul,
    smul_ball'', smul_eq_mul, mem_setOf_eq]
  replace han : ∀ {b : A}, orderOf b = n → orderOf (a * b) = n := by
    intro b hb
    rw [← hb] at han hn
    rw [sq] at han
    rwa [(Commute.all a b).orderOf_mul_eq_right_of_forall_prime_mul_dvd (orderOf_pos_iff.mp hn)
      fun p _ hp' => dvd_trans (mul_dvd_mul_right hp' <| orderOf a) han]
  let f : {b : A | orderOf b = n} → {b : A | orderOf b = n} := fun b => ⟨a * b, han b.property⟩
  have hf : Surjective f := by
    rintro ⟨b, hb⟩
    refine ⟨⟨a⁻¹ * b, ?_⟩, ?_⟩
    · rw [mem_setOf_eq, ← orderOf_inv, mul_inv_rev, inv_inv, mul_comm]
      apply han
      simpa
    · simp only [f, Subtype.mk_eq_mk, Subtype.coe_mk, mul_inv_cancel_left]
  simpa only [mem_setOf_eq, Subtype.coe_mk, iUnion_coe_set] using
    hf.iUnion_comp fun b => ball (b : A) δ

end approxOrderOf

namespace UnitAddCircle

theorem mem_approxAddOrderOf_iff {δ : ℝ} {x : UnitAddCircle} {n : ℕ} (hn : 0 < n) :
    x ∈ approxAddOrderOf UnitAddCircle n δ ↔ ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ := by
  simp only [mem_approx_add_orderOf_iff, mem_setOf_eq, ball, exists_prop, dist_eq_norm,
    AddCircle.addOrderOf_eq_pos_iff hn, mul_one]
  constructor
  · rintro ⟨y, ⟨m, hm₁, hm₂, rfl⟩, hx⟩; exact ⟨m, hm₁, hm₂, hx⟩
  · rintro ⟨m, hm₁, hm₂, hx⟩; exact ⟨↑((m : ℝ) / n), ⟨m, hm₁, hm₂, rfl⟩, hx⟩

theorem mem_addWellApproximable_iff (δ : ℕ → ℝ) (x : UnitAddCircle) :
    x ∈ addWellApproximable UnitAddCircle δ ↔
      {n : ℕ | ∃ m < n, gcd m n = 1 ∧ ‖x - ↑((m : ℝ) / n)‖ < δ n}.Infinite := by
  simp only [mem_add_wellApproximable_iff, ← Nat.cofinite_eq_atTop, cofinite.blimsup_set_eq,
    mem_setOf_eq]
  refine iff_of_eq (congr_arg Set.Infinite <| ext fun n => ⟨fun hn => ?_, fun hn => ?_⟩)
  · exact (mem_approxAddOrderOf_iff hn.1).mp hn.2
  · have h : 0 < n := by obtain ⟨m, hm₁, _, _⟩ := hn; exact pos_of_gt hm₁
    exact ⟨h, (mem_approxAddOrderOf_iff h).mpr hn⟩

end UnitAddCircle

namespace AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

local notation a "∤" b => ¬a ∣ b

local notation a "∣∣" b => a ∣ b ∧ (a * a)∤b

local notation "𝕊" => AddCircle T

/-- **Gallagher's ergodic theorem** on Diophantine approximation. -/
theorem addWellApproximable_ae_empty_or_univ (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    (∀ᵐ x, ¬addWellApproximable 𝕊 δ x) ∨ ∀ᵐ x, addWellApproximable 𝕊 δ x := by
  /- Sketch of proof:

    Let `E := addWellApproximable 𝕊 δ`. For each prime `p : ℕ`, we can partition `E` into three
    pieces `E = (A p) ∪ (B p) ∪ (C p)` where:
      `A p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p ∤ n))`
      `B p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p ∣∣ n))`
      `C p = blimsup (approxAddOrderOf 𝕊 n (δ n)) atTop (fun n => 0 < n ∧ (p*p ∣ n))`.
    In other words, `A p` is the set of points `x` for which there exist infinitely-many `n` such
    that `x` is within a distance `δ n` of a point of order `n` and `p ∤ n`. Similarly for `B`, `C`.

    These sets have the following key properties:
      1. `A p` is almost invariant under the ergodic map `y ↦ p • y`
      2. `B p` is almost invariant under the ergodic map `y ↦ p • y + 1/p`
      3. `C p` is invariant under the map `y ↦ y + 1/p`
    To prove 1 and 2 we need the key result `blimsup_thickening_mul_ae_eq` but 3 is elementary.

    It follows from `AddCircle.ergodic_nsmul_add` and `Ergodic.ae_empty_or_univ_of_image_ae_le` that
    if either `A p` or `B p` is not almost empty for any `p`, then it is almost full and thus so is
    `E`. We may therefore assume that `A p` and `B p` are almost empty for all `p`. We thus have
    `E` is almost equal to `C p` for every prime. Combining this with 3 we find that `E` is almost
    invariant under the map `y ↦ y + 1/p` for every prime `p`. The required result then follows from
    `AddCircle.ae_empty_or_univ_of_forall_vadd_ae_eq_self`. -/
  letI : SemilatticeSup Nat.Primes := Nat.Subtype.semilatticeSup _
  set μ : Measure 𝕊 := volume
  set u : Nat.Primes → 𝕊 := fun p => ↑((↑(1 : ℕ) : ℝ) / ((p : ℕ) : ℝ) * T)
  have hu₀ : ∀ p : Nat.Primes, addOrderOf (u p) = (p : ℕ) := by
    rintro ⟨p, hp⟩; exact addOrderOf_div_of_gcd_eq_one hp.pos (gcd_one_left p)
  have hu : Tendsto (addOrderOf ∘ u) atTop atTop := by
    rw [(funext hu₀ : addOrderOf ∘ u = (↑))]
    have h_mono : Monotone ((↑) : Nat.Primes → ℕ) := fun p q hpq => hpq
    refine h_mono.tendsto_atTop_atTop fun n => ?_
    obtain ⟨p, hp, hp'⟩ := n.exists_infinite_primes
    exact ⟨⟨p, hp'⟩, hp⟩
  set E := addWellApproximable 𝕊 δ
  set X : ℕ → Set 𝕊 := fun n => approxAddOrderOf 𝕊 n (δ n)
  set A : ℕ → Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p∤n
  set B : ℕ → Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p∣∣n
  set C : ℕ → Set 𝕊 := fun p => blimsup X atTop fun n => 0 < n ∧ p ^ 2 ∣ n
  have hA₀ : ∀ p, MeasurableSet (A p) := fun p =>
    MeasurableSet.measurableSet_blimsup fun n _ => isOpen_thickening.measurableSet
  have hB₀ : ∀ p, MeasurableSet (B p) := fun p =>
    MeasurableSet.measurableSet_blimsup fun n _ => isOpen_thickening.measurableSet
  have hE₀ : NullMeasurableSet E μ := by
    refine (MeasurableSet.measurableSet_blimsup fun n hn =>
      IsOpen.measurableSet ?_).nullMeasurableSet
    exact isOpen_thickening
  have hE₁ : ∀ p, E = A p ∪ B p ∪ C p := by
    intro p
    simp only [E, A, B, C, addWellApproximable, ← blimsup_or_eq_sup, ← and_or_left, ← sup_eq_union,
      sq]
    congr
    ext n
    tauto
  have hE₂ : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∧ B p =ᵐ[μ] (∅ : Set 𝕊) → E =ᵐ[μ] C p := by
    rintro p ⟨hA, hB⟩
    rw [hE₁ p]
    exact union_ae_eq_right_of_ae_eq_empty ((union_ae_eq_right_of_ae_eq_empty hA).trans hB)
  have hA : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∨ A p =ᵐ[μ] univ := by
    rintro ⟨p, hp⟩
    let f : 𝕊 → 𝕊 := fun y => (p : ℕ) • y
    suffices
      f '' A p ⊆ blimsup (fun n => approxAddOrderOf 𝕊 n (p * δ n)) atTop fun n => 0 < n ∧ p∤n by
      apply (ergodic_nsmul hp.one_lt).ae_empty_or_univ_of_image_ae_le (hA₀ p).nullMeasurableSet
      apply (HasSubset.Subset.eventuallyLE this).congr EventuallyEq.rfl
      exact blimsup_thickening_mul_ae_eq μ (fun n => 0 < n ∧ p∤n) (fun n => {y | addOrderOf y = n})
        (Nat.cast_pos.mpr hp.pos) _ hδ
    refine (sSupHom.setImage f).apply_blimsup_le.trans (mono_blimsup fun n hn => ?_)
    replace hn := Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.2 hn.2)
    exact approxAddOrderOf.image_nsmul_subset_of_coprime (δ n) hp.pos hn
  have hB : ∀ p : Nat.Primes, B p =ᵐ[μ] (∅ : Set 𝕊) ∨ B p =ᵐ[μ] univ := by
    rintro ⟨p, hp⟩
    let x := u ⟨p, hp⟩
    let f : 𝕊 → 𝕊 := fun y => p • y + x
    suffices
      f '' B p ⊆ blimsup (fun n => approxAddOrderOf 𝕊 n (p * δ n)) atTop fun n => 0 < n ∧ p∣∣n by
      apply (ergodic_nsmul_add x hp.one_lt).ae_empty_or_univ_of_image_ae_le
        (hB₀ p).nullMeasurableSet
      apply (HasSubset.Subset.eventuallyLE this).congr EventuallyEq.rfl
      exact blimsup_thickening_mul_ae_eq μ (fun n => 0 < n ∧ p∣∣n) (fun n => {y | addOrderOf y = n})
        (Nat.cast_pos.mpr hp.pos) _ hδ
    refine (sSupHom.setImage f).apply_blimsup_le.trans (mono_blimsup ?_)
    rintro n ⟨hn, h_div, h_ndiv⟩
    have h_cop : (addOrderOf x).Coprime (n / p) := by
      obtain ⟨q, rfl⟩ := h_div
      rw [hu₀, Subtype.coe_mk, hp.coprime_iff_not_dvd, q.mul_div_cancel_left hp.pos]
      exact fun contra => h_ndiv (mul_dvd_mul_left p contra)
    replace h_div : n / p * p = n := Nat.div_mul_cancel h_div
    have hf : f = (fun y => x + y) ∘ fun y => p • y := by
      ext; simp [f, add_comm x]
    simp_rw [Function.comp_apply, le_eq_subset]
    rw [sSupHom.setImage_toFun, hf, image_comp]
    have := @monotone_image 𝕊 𝕊 fun y => x + y
    specialize this (approxAddOrderOf.image_nsmul_subset (δ n) (n / p) hp.pos)
    simp only [h_div] at this ⊢
    refine this.trans ?_
    convert approxAddOrderOf.vadd_subset_of_coprime (p * δ n) h_cop
    rw [hu₀, Subtype.coe_mk, mul_comm p, h_div]
  change (∀ᵐ x, x ∉ E) ∨ E ∈ ae volume
  rw [← eventuallyEq_empty, ← eventuallyEq_univ]
  have hC : ∀ p : Nat.Primes, u p +ᵥ C p = C p := by
    intro p
    let e := (AddAction.toPerm (u p) : Equiv.Perm 𝕊).toOrderIsoSet
    change e (C p) = C p
    rw [OrderIso.apply_blimsup e, ← hu₀ p]
    exact blimsup_congr (Eventually.of_forall fun n hn =>
      approxAddOrderOf.vadd_eq_of_mul_dvd (δ n) hn.1 hn.2)
  by_cases h : ∀ p : Nat.Primes, A p =ᵐ[μ] (∅ : Set 𝕊) ∧ B p =ᵐ[μ] (∅ : Set 𝕊)
  · replace h : ∀ p : Nat.Primes, (u p +ᵥ E : Set _) =ᵐ[μ] E := by
      intro p
      replace hE₂ : E =ᵐ[μ] C p := hE₂ p (h p)
      have h_qmp : Measure.QuasiMeasurePreserving (-u p +ᵥ ·) μ μ :=
        (measurePreserving_vadd _ μ).quasiMeasurePreserving
      refine (h_qmp.vadd_ae_eq_of_ae_eq (u p) hE₂).trans (ae_eq_trans ?_ hE₂.symm)
      rw [hC]
    exact ae_empty_or_univ_of_forall_vadd_ae_eq_self hE₀ h hu
  · right
    simp only [not_forall, not_and_or] at h
    obtain ⟨p, hp⟩ := h
    rw [hE₁ p]
    cases hp
    · rcases hA p with _ | h; · contradiction
      simp only [μ, h, union_ae_eq_univ_of_ae_eq_univ_left]
    · rcases hB p with _ | h; · contradiction
      simp only [μ, h, union_ae_eq_univ_of_ae_eq_univ_left,
        union_ae_eq_univ_of_ae_eq_univ_right]

/-- A general version of **Dirichlet's approximation theorem**.

See also `AddCircle.exists_norm_nsmul_le`. -/
lemma _root_.NormedAddCommGroup.exists_norm_nsmul_le {A : Type*}
    [NormedAddCommGroup A] [CompactSpace A] [PreconnectedSpace A]
    [MeasurableSpace A] [BorelSpace A] {μ : Measure A} [μ.IsAddHaarMeasure]
    (ξ : A) {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : μ univ ≤ (n + 1) • μ (closedBall (0 : A) (δ/2))) :
    ∃ j ∈ Icc 1 n, ‖j • ξ‖ ≤ δ := by
  have : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  let B : Icc 0 n → Set A := fun j ↦ closedBall ((j : ℕ) • ξ) (δ/2)
  have hB : ∀ j, IsClosed (B j) := fun j ↦ isClosed_closedBall
  suffices ¬ Pairwise (Disjoint on B) by
    obtain ⟨i, j, hij, x, hx⟩ := exists_lt_mem_inter_of_not_pairwise_disjoint this
    refine ⟨j - i, ⟨le_tsub_of_add_le_left hij, ?_⟩, ?_⟩
    · simpa only [tsub_le_iff_right] using j.property.2.trans le_self_add
    · rw [sub_nsmul _ (Subtype.coe_le_coe.mpr hij.le), ← sub_eq_add_neg, ← dist_eq_norm]
      exact (dist_triangle ((j : ℕ) • ξ) x ((i : ℕ) • ξ)).trans (by
        linarith [mem_closedBall.mp hx.1, mem_closedBall'.mp hx.2])
  by_contra h
  apply hn.ne'
  have h' : ⋃ j, B j = univ := by
    rw [← (isClosed_iUnion_of_finite hB).measure_eq_univ_iff_eq (μ := μ)]
    refine le_antisymm (μ.mono (subset_univ _)) ?_
    simp_rw [measure_iUnion h (fun _ ↦ measurableSet_closedBall), tsum_fintype,
      B, μ.addHaar_closedBall_center, Finset.sum_const, Finset.card_univ, Fintype.card_Icc,
      Nat.card_Icc, tsub_zero]
    exact hδ
  replace hδ : 0 ≤ δ/2 := by
    by_contra contra
    suffices μ (closedBall 0 (δ/2)) = 0 by
      apply isOpen_univ.measure_ne_zero μ univ_nonempty <| le_zero_iff.mp <| le_trans hδ _
      simp [this]
    rw [not_le, ← closedBall_eq_empty (x := (0 : A))] at contra
    simp [contra]
  have h'' : ∀ j, (B j).Nonempty := by intro j; rwa [nonempty_closedBall]
  simpa using subsingleton_of_disjoint_isClosed_iUnion_eq_univ h'' h hB h'

/-- **Dirichlet's approximation theorem**

See also `Real.exists_rat_abs_sub_le_and_den_le`. -/
lemma exists_norm_nsmul_le (ξ : 𝕊) {n : ℕ} (hn : 0 < n) :
    ∃ j ∈ Icc 1 n, ‖j • ξ‖ ≤ T / ↑(n + 1) := by
  apply NormedAddCommGroup.exists_norm_nsmul_le (μ := volume) ξ hn
  rw [AddCircle.measure_univ, volume_closedBall, ← ENNReal.ofReal_nsmul,
    mul_div_cancel₀ _ two_ne_zero, min_eq_right (div_le_self hT.out.le <| by simp), nsmul_eq_mul,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr n.succ_ne_zero)]

end AddCircle
