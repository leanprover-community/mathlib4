/-
Copyright (c) 2026 Boris Bilich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Bilich, Alexei Piskunov, Jonathan Shneyer
-/
module

public import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.Ideal.BigOperators


/-!
# The class group of a Unique Factorization Domain is trivial
This file proves that the ideal class group of a Unique Factorization Domain is trivial.

## Main result
- `UniqueFactorizationMonoid.instSubsingletonClassGroup` : the class group of a UFD is trivial.

## References

- [stacks-project]: The Stacks project, [tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
-/

@[expose] public section

open scoped nonZeroDivisors Pointwise BigOperators

open IsLocalization IsFractionRing FractionalIdeal

section CommRing

variable (R : Type*) [CommRing R]

private lemma exists_bezout_coeffs_of_isUnit_fractionalIdeal_of_span {n : ℕ} {c : Fin n → R}
    {J : Ideal R}
    [IsDomain R]
    (hJspan : J = Ideal.span (Set.range c))
    (hJunit : IsUnit (J : FractionalIdeal R⁰ (FractionRing R))) :
    ∃ (K : FractionalIdeal R⁰ (FractionRing R)),
      (J : FractionalIdeal R⁰ (FractionRing R)) * K = 1 ∧
        ∃ ℓ : Fin n → FractionRing R,
          (∀ i, ℓ i ∈ K) ∧
            (Finset.univ : Finset (Fin n)).sum
                (fun i => algebraMap R (FractionRing R) (c i) * ℓ i) = 1 := by
  set K : FractionalIdeal R⁰ (FractionRing R) :=
    (J : FractionalIdeal R⁰ (FractionRing R))⁻¹
  have hJK : (J : FractionalIdeal R⁰ (FractionRing R)) * K = 1 := by
    simpa [K] using
      (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing R)
            (I := (J : FractionalIdeal R⁰ (FractionRing R)))).2
        hJunit
  refine ⟨K, hJK, ?_⟩
  -- Induct on the proof that `1 ∈ J * K` in the `R`-submodule `FractionRing R`.
  let C : FractionRing R → Prop :=
    fun r =>
      ∃ ℓ : Fin n → FractionRing R,
        (∀ i, ℓ i ∈ K) ∧
          (Finset.univ : Finset (Fin n)).sum
              (fun i => algebraMap R (FractionRing R) (c i) * ℓ i) = r
  have hr : (1 : FractionRing R) ∈ (J : FractionalIdeal R⁰ (FractionRing R)) * K := by
    simpa [hJK] using
      (FractionalIdeal.one_mem_one (S := (R⁰)) (P := FractionRing R))
  have hC1 : C 1 := by
    refine
      FractionalIdeal.mul_induction_on (I := (J : FractionalIdeal R⁰ (FractionRing R))) (J := K)
        (r := (1 : FractionRing R)) hr ?_ ?_
    · intro i hi j hj
      rcases (FractionalIdeal.mem_coeIdeal (S := (R⁰)) (P := FractionRing R) (I := J) (x := i)).1
          hi with
        ⟨y, hyJ, rfl⟩
      have hyspan : y ∈ Ideal.span (Set.range c) := by simpa [hJspan] using hyJ
      have hyspan' : y ∈ Submodule.span R (Set.range c) := by
        -- Avoid simp loops between `Ideal.span` and `Submodule.span`.
        simpa using hyspan
      rcases (Submodule.mem_span_range_iff_exists_fun (R := R) (v := c) (x := y)).1 hyspan' with
        ⟨a, ha⟩
      refine ⟨fun k => a k • j, ?_, ?_⟩
      · intro k
        exact (K : Submodule R (FractionRing R)).smul_mem (a k) hj
      · have hy :
            (Finset.univ : Finset (Fin n)).sum (fun k => a k * c k) = y := by
          simpa using ha
        have hy_map :
            (Finset.univ : Finset (Fin n)).sum
                (fun k => algebraMap R (FractionRing R) (a k * c k)) =
              algebraMap R (FractionRing R) y := by
          simpa [map_sum] using congrArg (algebraMap R (FractionRing R)) hy
        have hterm :
            ∀ k : Fin n,
              algebraMap R (FractionRing R) (c k) * (a k • j) =
                algebraMap R (FractionRing R) (a k * c k) * j := by
          intro k
          -- Use that `a • j = algebraMap a * j`, and commute scalars past `c k`.
          simp [Algebra.smul_def, mul_left_comm, mul_comm]
        calc
          (Finset.univ : Finset (Fin n)).sum
              (fun k => algebraMap R (FractionRing R) (c k) * (a k • j)) =
              (Finset.univ : Finset (Fin n)).sum
                (fun k => algebraMap R (FractionRing R) (a k * c k) * j) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                exact hterm k
          _ =
              ((Finset.univ : Finset (Fin n)).sum
                  (fun k => algebraMap R (FractionRing R) (a k * c k))) * j := by
                simpa using
                  (Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
                        (f := fun k => algebraMap R (FractionRing R) (a k * c k)) (a := j)).symm
          _ = algebraMap R (FractionRing R) y * j := by
                exact congrArg (fun t => t * j) hy_map
    · intro x y hx hy
      rcases hx with ⟨ℓx, hℓx, hxsum⟩
      rcases hy with ⟨ℓy, hℓy, hysum⟩
      refine ⟨fun k => ℓx k + ℓy k, ?_, ?_⟩
      · intro k
        exact (K : Submodule R (FractionRing R)).add_mem (hℓx k) (hℓy k)
      · -- Distribute multiplication over addition, then use the two induction hypotheses.
        simp [mul_add, Finset.sum_add_distrib, hxsum, hysum]
  rcases hC1 with ⟨ℓ, hℓ, hsum⟩
  exact ⟨ℓ, hℓ, by simpa using hsum⟩

private lemma dvd_relations_of_bezout_and_clearDenoms {n : ℕ} {c : Fin n → R} {J : Ideal R}
    (hJspan : J = Ideal.span (Set.range c))
    {K : FractionalIdeal R⁰ (FractionRing R)}
    (hJK : (J : FractionalIdeal R⁰ (FractionRing R)) * K = 1)
    {ℓ : Fin n → FractionRing R} (hℓK : ∀ i, ℓ i ∈ K)
    {x : R} {b : Fin n → R}
    (hb :
      ∀ i,
        algebraMap R (FractionRing R) (b i) =
          algebraMap R (FractionRing R) x * ℓ i) :
    ∀ i j : Fin n, x ∣ c i * b j := by
  intro i j
  have hcJ : c i ∈ J := by
    have : c i ∈ Ideal.span (Set.range c) :=
      Ideal.subset_span (by exact ⟨i, rfl⟩)
    simpa [hJspan] using this
  have hci :
      algebraMap R (FractionRing R) (c i) ∈
        (J : FractionalIdeal R⁰ (FractionRing R)) :=
    FractionalIdeal.mem_coeIdeal_of_mem (S := (R⁰)) (P := FractionRing R) hcJ
  have hij :
      algebraMap R (FractionRing R) (c i) * ℓ j ∈
        (J : FractionalIdeal R⁰ (FractionRing R)) * K :=
    FractionalIdeal.mul_mem_mul hci (hℓK j)
  have hij1 :
      algebraMap R (FractionRing R) (c i) * ℓ j ∈ (1 : FractionalIdeal R⁰ (FractionRing R)) := by
    simpa [hJK] using hij
  rcases (FractionalIdeal.mem_one_iff (S := (R⁰)) (P := FractionRing R)).1 hij1 with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hmap :
      algebraMap R (FractionRing R) (x * r) =
        algebraMap R (FractionRing R) (c i * b j) := by
    calc
      algebraMap R (FractionRing R) (x * r)
          = algebraMap R (FractionRing R) x * algebraMap R (FractionRing R) r := by
              simp [map_mul]
      _ = algebraMap R (FractionRing R) x *
            (algebraMap R (FractionRing R) (c i) * ℓ j) := by
              simp [hr]
      _ = algebraMap R (FractionRing R) (c i) *
            (algebraMap R (FractionRing R) x * ℓ j) := by
              simp [mul_left_comm, mul_comm]
      _ = algebraMap R (FractionRing R) (c i) * algebraMap R (FractionRing R) (b j) := by
              simp [hb j]
      _ = algebraMap R (FractionRing R) (c i * b j) := by
              simp [map_mul]
  have hxrr : x * r = c i * b j := hinj (by simpa [map_mul] using hmap)
  exact hxrr.symm

section Domain
variable [IsDomain R]

private lemma exists_clearDenoms_fin {n : ℕ} (ℓ : Fin n → FractionRing R) :
    ∃ (x : R) (_hx0 : x ≠ 0) (b : Fin n → R),
      ∀ i,
        algebraMap R (FractionRing R) (b i) =
          algebraMap R (FractionRing R) x * ℓ i := by
  -- Use the `commonDenom/integerMultiple` API for clearing denominators in a localization.
  let x₀ : R⁰ := IsLocalization.commonDenom (M := (R⁰)) (s := (Finset.univ : Finset (Fin n)))
    (S := FractionRing R) ℓ
  let x : R := (x₀ : R)
  let b : Fin n → R :=
    fun i =>
      IsLocalization.integerMultiple (M := (R⁰)) (s := (Finset.univ : Finset (Fin n)))
          (S := FractionRing R) ℓ ⟨i, by simp⟩
  refine ⟨x, ?_, b, ?_⟩
  · simp [x]
  · intro i
    have hbi :
        algebraMap R (FractionRing R) (b i) =
          IsLocalization.commonDenom (M := (R⁰)) (s := (Finset.univ : Finset (Fin n)))
              (S := FractionRing R) ℓ •
            ℓ i := by
      exact map_integerMultiple R⁰ Finset.univ ℓ ⟨i, of_eq_true (Finset.mem_univ._simp_1 i)⟩
    -- Rewrite the scalar multiplication as multiplication by `algebraMap x`.
    calc
      algebraMap R (FractionRing R) (b i) =
          IsLocalization.commonDenom (M := (R⁰)) (s := (Finset.univ : Finset (Fin n)))
              (S := FractionRing R) ℓ •
            ℓ i := hbi
      _ = algebraMap R (FractionRing R) x * ℓ i := by
          -- `•` here is the scalar action of `R⁰`; rewrite it to the `R`-action and then to
          -- multiplication by `algebraMap`.
          simp [x₀, x, Submonoid.smul_def, Algebra.smul_def]


private lemma mem_mul_span_of_bezout_and_clearDenoms {n : ℕ} {c : Fin n → R} {J : Ideal R}
    (hJspan : J = Ideal.span (Set.range c))
    {ℓ : Fin n → FractionRing R}
    (hsum :
      (Finset.univ : Finset (Fin n)).sum
          (fun i => algebraMap R (FractionRing R) (c i) * ℓ i) = 1)
    {x : R} {b : Fin n → R}
    (hb :
      ∀ i,
        algebraMap R (FractionRing R) (b i) =
          algebraMap R (FractionRing R) x * ℓ i) :
    x ∈ J * Ideal.span (Set.range b) := by
  let B : Ideal R := Ideal.span (Set.range b)
  have hinj : Function.Injective (algebraMap R (FractionRing R)) :=
    IsFractionRing.injective R (FractionRing R)
  have hx_eq_sum : x = (Finset.univ : Finset (Fin n)).sum (fun i => c i * b i) := by
    -- Work in the fraction field, then pull back by injectivity.
    apply hinj
    let ax : FractionRing R := algebraMap R (FractionRing R) x
    have hmul_ax :
        ((Finset.univ : Finset (Fin n)).sum
            (fun i => algebraMap R (FractionRing R) (c i) * ℓ i)) *
          ax =
        ax := by
      have := congrArg (fun t => t * ax) hsum
      simpa [ax] using this
    have hsum_ax :
        (Finset.univ : Finset (Fin n)).sum
            (fun i => (algebraMap R (FractionRing R) (c i) * ℓ i) * ax) =
          ax := by
      -- Move the right multiplication by `ax` inside the sum.
      have hsum_mul :=
        Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i => algebraMap R (FractionRing R) (c i) * ℓ i) (a := ax)
      -- `hsum_mul : (∑ f) * ax = ∑ (f * ax)`
      calc
        (Finset.univ : Finset (Fin n)).sum
            (fun i => (algebraMap R (FractionRing R) (c i) * ℓ i) * ax) =
            ((Finset.univ : Finset (Fin n)).sum
                (fun i => algebraMap R (FractionRing R) (c i) * ℓ i)) * ax := by
              simpa using hsum_mul.symm
        _ = ax := hmul_ax
    have hterm :
        ∀ i : Fin n,
          (algebraMap R (FractionRing R) (c i) * ℓ i) * ax =
            algebraMap R (FractionRing R) (c i * b i) := by
      intro i
      -- Rewrite using `hb i : algebraMap (b i) = ax * ℓ i`, and commutativity.
      calc
        (algebraMap R (FractionRing R) (c i) * ℓ i) * ax =
            algebraMap R (FractionRing R) (c i) * (ax * ℓ i) := by
              simp [mul_left_comm, mul_comm]
        _ = algebraMap R (FractionRing R) (c i) * algebraMap R (FractionRing R) (b i) := by
              simpa [ax]
                using congrArg (fun t => algebraMap R (FractionRing R) (c i) * t) (hb i).symm
        _ = algebraMap R (FractionRing R) (c i * b i) := by
              simp [map_mul]
    have : (Finset.univ : Finset (Fin n)).sum
          (fun i => algebraMap R (FractionRing R) (c i * b i)) = ax := by
      calc
        (Finset.univ : Finset (Fin n)).sum
            (fun i => algebraMap R (FractionRing R) (c i * b i)) =
            (Finset.univ : Finset (Fin n)).sum
              (fun i => (algebraMap R (FractionRing R) (c i) * ℓ i) * ax) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                simpa using (hterm i).symm
        _ = ax := hsum_ax
    -- Rewrite `algebraMap` of the sum on the right.
    simpa [ax, map_sum] using this.symm
  -- Prove the sum is in the product ideal, then rewrite using `hx_eq_sum`.
  have hsum_mem :
      (Finset.univ : Finset (Fin n)).sum (fun i => c i * b i) ∈ J * B := by
    refine Ideal.sum_mem (I := J * B) ?_
    intro i hi
    have hcJ : c i ∈ J := by
      have : c i ∈ Ideal.span (Set.range c) :=
        Ideal.subset_span (by exact ⟨i, rfl⟩)
      simpa [hJspan] using this
    have hbB : b i ∈ B := by
      exact Ideal.subset_span (by exact ⟨i, rfl⟩)
    -- `c i * b i` is a product of an element of `J` with an element of `B`.
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using Ideal.mul_mem_mul hcJ hbB
  have hxmem : x ∈ J * B := by
    simpa [hx_eq_sum] using hsum_mem
  simpa [B] using hxmem

private lemma exists_relations_of_isUnit_fractionalIdeal_of_span
    {n : ℕ} {c : Fin n → R} {J : Ideal R}
    (hJspan : J = Ideal.span (Set.range c))
    (hJunit : IsUnit (J : FractionalIdeal R⁰ (FractionRing R))) :
    ∃ (x : R) (_hx0 : x ≠ 0) (b : Fin n → R),
      (∀ i j : Fin n, x ∣ c i * b j) ∧
      x ∈ J * Ideal.span (Set.range b) := by
  rcases
      exists_bezout_coeffs_of_isUnit_fractionalIdeal_of_span (R := R) (c := c) (J := J) hJspan
        hJunit with
    ⟨K, hJK, ℓ, hℓK, hsum₁⟩
  rcases exists_clearDenoms_fin (R := R) (n := n) ℓ with ⟨x, hx0, b, hb⟩
  refine ⟨x, hx0, b, ?_, ?_⟩
  · exact
      dvd_relations_of_bezout_and_clearDenoms (R := R) (c := c) (J := J) hJspan (K := K) hJK hℓK
        hb
  · exact
      mem_mul_span_of_bezout_and_clearDenoms (R := R) (c := c) (J := J) (ℓ := ℓ) hJspan
        hsum₁ hb

/-- A family `c : Fin n → R` has “unit gcd” if every common divisor is a unit. -/
private def CommonDivisorsAreUnits {n : ℕ} (c : Fin n → R) : Prop :=
  ∀ d : R, (∀ i : Fin n, d ∣ c i) → IsUnit d

private lemma ideal_eq_top_of_relations {n : ℕ} {J : Ideal R}
    {x : R} (hx0 : x ≠ 0) {b : Fin n → R} (hxmem : x ∈ J * Ideal.span (Set.range b))
    (hb : ∀ j : Fin n, x ∣ b j) :
    J = ⊤ := by
  let B : Ideal R := Ideal.span (Set.range b)
  have hxmem' : x ∈ J * B := by simpa [B] using hxmem
  -- `B ≤ (x)` since all generators are divisible by `x`.
  have hB_le : B ≤ Ideal.span ({x} : Set R) := by
    refine (Ideal.span_le).2 ?_
    rintro z ⟨j, rfl⟩
    rcases hb j with ⟨t, ht⟩
    refine (Ideal.mem_span_singleton').2 ?_
    refine ⟨t, ?_⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using ht.symm
  -- `J * B = (x)`: inclusion `≤` from monotonicity, and inclusion `≥` from `hxmem`.
  have hJB_le : J * B ≤ Ideal.span ({x} : Set R) := by
    calc
      J * B ≤ (⊤ : Ideal R) * B := Ideal.mul_mono_left (le_top : J ≤ (⊤ : Ideal R))
      _ = B := by simp
      _ ≤ Ideal.span ({x} : Set R) := hB_le
  have hspan_le : Ideal.span ({x} : Set R) ≤ J * B :=
    (Ideal.span_singleton_le_iff_mem (I := J * B) (x := x)).2 hxmem'
  have hJB : J * B = Ideal.span ({x} : Set R) := le_antisymm hJB_le hspan_le
  -- From `J * B = (x)` and `B ≤ (x)`, deduce `J * (x) = (x)`.
  have hJx : J * Ideal.span ({x} : Set R) = Ideal.span ({x} : Set R) := by
    apply le_antisymm
    · -- `J * (x) ≤ (x)` since `J ≤ ⊤`.
      have : J * Ideal.span ({x} : Set R) ≤ (⊤ : Ideal R) * Ideal.span ({x} : Set R) :=
        Ideal.mul_mono_left (le_top : J ≤ (⊤ : Ideal R))
      simpa using this
    · -- `(x) = J * B ≤ J * (x)`.
      have : J * B ≤ J * Ideal.span ({x} : Set R) := Ideal.mul_mono_right hB_le
      simpa [hJB] using this
  -- Cancel the nonzero principal ideal `(x)` on the right.
  have hxcomm : Ideal.span ({x} : Set R) * J = Ideal.span ({x} : Set R) := by
    simpa [mul_comm] using hJx
  have : Ideal.span ({x} : Set R) * J = Ideal.span ({x} : Set R) * ⊤ := by
    calc
      Ideal.span ({x} : Set R) * J = Ideal.span ({x} : Set R) := hxcomm
      _ = Ideal.span ({x} : Set R) * ⊤ := (Ideal.mul_top _).symm
  exact (Ideal.span_singleton_mul_right_inj (R := R) hx0).1 this


section UFD

variable [UniqueFactorizationMonoid R]

private lemma exists_gcd_normalization_of_isUnit_fractionalIdeal (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) :
    ∃ (y : R) (n : ℕ) (_hn : 0 < n) (c : Fin n → R) (J : Ideal R),
      I = Ideal.span ({y} : Set R) * J ∧
      J = Ideal.span (Set.range c) ∧
      IsUnit (J : FractionalIdeal R⁰ (FractionRing R)) ∧
      CommonDivisorsAreUnits (R := R) c := by
  -- Choose a `NormalizedGCDMonoid` structure (available noncomputably for any UFM).
  letI : NormalizedGCDMonoid R :=
    Classical.choice (by infer_instance : Nonempty (NormalizedGCDMonoid R))
  -- Finite generation of `I` and a distinguished nonzero element of `I`.
  have hfg : (I : Submodule R R).FG :=
    (Ideal.fg_of_isUnit (IsFractionRing.injective R (FractionRing R)) I hI)
  rcases Submodule.exists_mem_ne_zero_of_ne_bot
    (fun a ↦ (IsUnit.ne_zero hI) (congrArg coeIdeal a)) with ⟨f, hfI, hf0⟩
  -- Choose a finite generating family for `I`, and add `f` as an extra generator to ensure
  -- nonemptiness and a nonzero element among the generators.
  obtain ⟨n₀, a₀, ha₀⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family (N := (I : Submodule R R))).1 hfg
  let n : ℕ := n₀ + 1
  have hn : 0 < n := Nat.succ_pos n₀
  let a : Fin n → R := fun i => Fin.cases f a₀ i
  have ha : Ideal.span (Set.range a) = I := by
    -- First show the corresponding statement for submodule spans.
    have ha_sub : Submodule.span R (Set.range a) = (I : Submodule R R) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro x ⟨i, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hfI
        · have hj : a₀ j ∈ Submodule.span R (Set.range a₀) := Submodule.subset_span ⟨j, rfl⟩
          have : a₀ j ∈ (I : Submodule R R) := ha₀ ▸ hj
          simpa [a] using this
      · have hrange : Set.range a₀ ⊆ Set.range a := by
          intro x hx
          rcases hx with ⟨j, rfl⟩
          refine ⟨Fin.succ j, ?_⟩
          simp [a]
        have hspan : Submodule.span R (Set.range a₀) ≤ Submodule.span R (Set.range a) :=
          Submodule.span_mono hrange
        -- Rewrite the left-hand side of the goal using `ha₀ : span (range a₀) = I`.
        -- This avoids `simp` rewriting `Submodule.span` into `Ideal.span`.
        -- Goal: `I ≤ span (range a)`.
        -- After `rw [← ha₀]`, this becomes `span (range a₀) ≤ span (range a)`.
        exact (show (I : Submodule R R) ≤ Submodule.span R (Set.range a) by
          rw [← ha₀]
          exact hspan)
    -- Convert the submodule equality to an ideal
    -- equality (without triggering simp loops on `span`).
    ext x
    change x ∈ Submodule.span R (Set.range a) ↔ x ∈ (I : Submodule R R)
    rw [ha_sub]
  -- Extract a gcd from the generating family: `a i = y * c i` and `gcd c = 1`.
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := by
    refine ⟨0, by simp⟩
  obtain ⟨c, hac, hgcd⟩ := Finset.extract_gcd (s := (Finset.univ : Finset (Fin n))) a huniv
  let y : R := (Finset.univ : Finset (Fin n)).gcd a
  have ha_mul : ∀ i : Fin n, a i = y * c i := by
    intro i
    have := hac i (by simp)
    simpa [y] using this
  have hy0 : y ≠ 0 := by
    refine (Finset.gcd_ne_zero_iff (s := (Finset.univ : Finset (Fin n))) (f := a)).2 ?_
    refine ⟨0, by simp, ?_⟩
    simpa [a] using hf0
  -- Define `J` as the ideal generated by the normalized family.
  let J : Ideal R := Ideal.span (Set.range c)
  have hrange : Set.range a = ({y} : Set R) * Set.range c := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      refine Set.mem_mul.mpr ?_
      refine ⟨y, by simp, c i, ⟨i, rfl⟩, ?_⟩
      simp [ha_mul i]
    · intro hr
      rcases Set.mem_mul.mp hr with ⟨u, hu, v, hv, rfl⟩
      rcases (by simpa using hu) with rfl
      rcases hv with ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      simp [ha_mul i]
  have hIJ : I = Ideal.span ({y} : Set R) * J := by
    calc
      I = Ideal.span (Set.range a) := ha.symm
      _ = Ideal.span (({y} : Set R) * Set.range c) := by simp [hrange]
      _ = Ideal.span ({y} : Set R) * Ideal.span (Set.range c) := by
        simpa using
          (Ideal.span_mul_span' (R := R) (S := ({y} : Set R)) (T := Set.range c)).symm
      _ = Ideal.span ({y} : Set R) * J := by simp [J]
  have hJunit : IsUnit (J : FractionalIdeal R⁰ (FractionRing R)) := by
    have hprod :
        IsUnit
          (((Ideal.span ({y} : Set R) : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) *
            (J : FractionalIdeal R⁰ (FractionRing R))) := by
      -- Transport `hI` along `hIJ`, and rewrite the ideal product as
      -- a product of fractional ideals.
      simpa [hIJ, FractionalIdeal.coeIdeal_mul] using hI
    exact isUnit_of_mul_isUnit_right hprod
  have hc : CommonDivisorsAreUnits (R := R) c := by
    intro d hd
    have hd' : ∀ i ∈ (Finset.univ : Finset (Fin n)), d ∣ c i := by
      intro i _
      exact hd i
    have : d ∣ (Finset.univ : Finset (Fin n)).gcd c := Finset.dvd_gcd hd'
    have : d ∣ (1 : R) := by simpa [hgcd] using this
    exact isUnit_of_dvd_one this
  refine ⟨y, n, hn, c, J, ?_, rfl, hJunit, hc⟩
  exact hIJ

private lemma dvd_of_dvd_mul_of_commonDivisorsAreUnits {n : ℕ} {c : Fin n → R}
    (hc : CommonDivisorsAreUnits (R := R) c) {x b : R} (hx0 : x ≠ 0)
    (h : ∀ i : Fin n, x ∣ c i * b) : x ∣ b := by
  -- We prove the stronger statement by induction on the prime factorization of `x`.
  let P : R → Prop :=
    fun x' => x' ≠ 0 → ∀ b' : R, (∀ i : Fin n, x' ∣ c i * b') → x' ∣ b'
  have hP : P x := by
    -- Induction on `x` using `UniqueFactorizationMonoid.induction_on_prime`.
    refine UniqueFactorizationMonoid.induction_on_prime (α := R) x ?_ ?_ ?_
    · intro hx'
      exact (hx' rfl).elim
    · intro x' hx' hx'0 b' _
      -- A unit divides everything.
      exact hx'.dvd
    · intro a p ha0 hp ih hp0 b' hb'
      -- Show `p ∣ b'` by choosing an index where `p ∤ c i`.
      have hex : ∃ i : Fin n, ¬ p ∣ c i := by
        by_contra hcontra
        have hall : ∀ i : Fin n, p ∣ c i := by
          intro i
          by_contra hi
          exact hcontra ⟨i, hi⟩
        have : IsUnit p := hc p hall
        exact hp.not_unit this
      rcases hex with ⟨i0, hi0⟩
      have hpCb : p ∣ c i0 * b' := by
        exact dvd_trans (dvd_mul_right p a) (hb' i0)
      have hpb : p ∣ b' := (hp.dvd_or_dvd hpCb).resolve_left hi0
      rcases hpb with ⟨b₁, rfl⟩
      -- Reduce to the induction hypothesis for `a` after cancelling `p`.
      have ha : a ∣ b₁ := by
        refine ih ha0 b₁ ?_
        intro i
        -- From `p * a ∣ c i * (p * b₁)` we cancel `p` (since `p ≠ 0`).
        have hpa : p * a ∣ p * (c i * b₁) := by
          -- reassociate/commute the right-hand side.
          simpa [mul_assoc, mul_left_comm, mul_comm] using hb' i
        exact (mul_dvd_mul_iff_left hp.ne_zero).1 hpa
      -- Conclude `p * a ∣ p * b₁`.
      exact mul_dvd_mul_left p ha
  exact hP hx0 b h


/-- In a UFD, an integral ideal that is invertible as a fractional ideal is principal. -/
private theorem ideal_isPrincipal_of_isUnit_fractionalIdeal (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) :
    I.IsPrincipal := by
  obtain ⟨y, n, hn, c, J, hIJ, hJspan, hJunit, hc⟩ :=
    exists_gcd_normalization_of_isUnit_fractionalIdeal (R := R) (I := I) hI
  obtain ⟨x, hx0, b, hdiv, hxmem⟩ :=
    exists_relations_of_isUnit_fractionalIdeal_of_span (R := R) (c := c) (J := J) hJspan hJunit
  have hb : ∀ j : Fin n, x ∣ b j := by
    intro j
    refine dvd_of_dvd_mul_of_commonDivisorsAreUnits (R := R) (c := c) hc (x := x) (b := b j) hx0
      ?_
    intro i
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdiv i j
  have hJtop : J = ⊤ :=
    ideal_eq_top_of_relations (R := R) (J := J) (x := x) hx0 (b := b) hxmem hb
  refine ⟨y, ?_⟩
  simpa [hJtop] using hIJ


/-- In a UFD, every invertible fractional ideal is principal. -/
theorem UniqueFactorizationMonoid.fractionalIdeal_isPrincipal_of_isUnit
  (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    (I : Submodule R (FractionRing R)).IsPrincipal := by
  let J : Ideal R := (I : FractionalIdeal R⁰ (FractionRing R)).num
  have hJunit : IsUnit (J : FractionalIdeal R⁰ (FractionRing R)) := by
    have hIunit : IsUnit (I : FractionalIdeal R⁰ (FractionRing R)) := ⟨I, rfl⟩
    -- `J = spanSingleton den * I`, and both factors are units.
    have hden0 :
        algebraMap R (FractionRing R)
            (((I : FractionalIdeal R⁰ (FractionRing R)).den : R⁰) : R) ≠ 0 := by
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (SetLike.coe_mem ((I : FractionalIdeal R⁰ (FractionRing R)).den))
    let u : (FractionRing R)ˣ :=
      Units.mk0
        (algebraMap R (FractionRing R)
          (((I : FractionalIdeal R⁰ (FractionRing R)).den : R⁰) : R))
        hden0
    have hdenUnit :
        IsUnit
          (FractionalIdeal.spanSingleton (R⁰)
            (algebraMap R (FractionRing R)
              (((I : FractionalIdeal R⁰ (FractionRing R)).den : R⁰) : R))) := by
      refine ⟨toPrincipalIdeal R (FractionRing R) u, ?_⟩
      simp [u]
    have hmul :
        FractionalIdeal.spanSingleton (R⁰)
            (algebraMap R (FractionRing R)
              (((I : FractionalIdeal R⁰ (FractionRing R)).den : R⁰) : R)) *
          (I : FractionalIdeal R⁰ (FractionRing R)) = J := by
      simpa [J] using
        (FractionalIdeal.den_mul_self_eq_num' (S := (R⁰)) (P := FractionRing R)
          (I := (I : FractionalIdeal R⁰ (FractionRing R))))
    -- Transport `IsUnit` along the equality.
    simpa [hmul] using hdenUnit.mul hIunit
  have hJprin : J.IsPrincipal :=
    ideal_isPrincipal_of_isUnit_fractionalIdeal (R := R) J hJunit
  -- If the numerator ideal is principal, the fractional ideal is principal.
  simpa [J] using
    FractionalIdeal.isPrincipal_of_num_isPrincipal (R := R)
      (I := (I : FractionalIdeal R⁰ (FractionRing R))) hJprin

/-- In a UFD, every class in the ideal class group is `1`. -/
theorem UniqueFactorizationMonoid.classGroup_eq_one (x : ClassGroup R) : x = 1 := by
  refine ClassGroup.induction (R := R) (K := FractionRing R) (P := fun y => y = 1) ?_ x
  intro I
  -- `mk I = 1` iff `I` is principal as a submodule.
  refine (ClassGroup.mk_eq_one_iff (R := R) (K := FractionRing R) (I := I)).2 ?_
  exact fractionalIdeal_isPrincipal_of_isUnit (R := R) I

/-- The ideal class group of a UFD is trivial. -/
instance UniqueFactorizationMonoid.instSubsingletonClassGroup : Subsingleton (ClassGroup R) := by
  refine ⟨fun x y => ?_⟩
  calc
    x = 1 := classGroup_eq_one (R := R) x
    _ = y := (classGroup_eq_one (R := R) y).symm

end UFD

end Domain
end CommRing
