/-
Copyright (c) 2026 Boris Bilich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Bilich, Alexei Piskunov, Jonathan Shneyer
-/
module

public import Mathlib.RingTheory.ClassGroup
import Mathlib.Algebra.GCDMonoid.Finset


/-!
# The class group of a Unique Factorization Domain is trivial
This file proves that the ideal class group of a Normalized GCD Domain is trivial.
The main application is to Unique Factorization Domains,
which are known to be Normalized GCD Domains.

## Main result
- `NormalizedGCDMonoid.instSubsingletonClassGroup` : the class group of a
  Normalized GCD Domain is trivial.
- `UniqueFactorizationMonoid.instSubsingletonClassGroup` : the class group of a UFD is trivial.

## References

- [stacks-project]: The Stacks project, [tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
-/

open scoped nonZeroDivisors Pointwise BigOperators

open IsLocalization IsFractionRing

section CommRing

variable (R : Type*) [CommRing R]

section Domain
variable [IsDomain R]

/-- Bridge lemma: if `J` is a unit after coercion to fractional ideals, then `J` admits an
integral inverse up to a principal ideal. -/
lemma Ideal.exists_mul_eq_span_singleton_of_isUnit_coe (J : Ideal R)
    (hJ : IsUnit (J : FractionalIdeal R⁰ (FractionRing R))) :
    ∃ (K : Ideal R) (x : R), x ≠ 0 ∧ J * K = Ideal.span ({x} : Set R) := by
  classical
  set Iinv : FractionalIdeal R⁰ (FractionRing R) :=
    (J : FractionalIdeal R⁰ (FractionRing R))⁻¹
  have hJinv :
      (J : FractionalIdeal R⁰ (FractionRing R)) * Iinv = 1 := by
    simpa [Iinv] using
      (FractionalIdeal.mul_inv_cancel_iff_isUnit (K := FractionRing R)
            (I := (J : FractionalIdeal R⁰ (FractionRing R)))).2
        hJ
  obtain ⟨a, K, ha0, hIinv⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (I := Iinv)
  have ha0' : algebraMap R (FractionRing R) a ≠ 0 := by
    exact
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_iff_ne_zero.2 ha0)
  have hJK_frac :
      (J : FractionalIdeal R⁰ (FractionRing R)) * (K : FractionalIdeal R⁰ (FractionRing R)) =
        FractionalIdeal.spanSingleton (R⁰) (algebraMap R (FractionRing R) a) := by
    set z : FractionRing R := algebraMap R (FractionRing R) a
    have hJinv' :
        (J : FractionalIdeal R⁰ (FractionRing R)) *
            (FractionalIdeal.spanSingleton (R⁰) z⁻¹ *
              (K : FractionalIdeal R⁰ (FractionRing R))) =
          1 := by
      simpa [Iinv, hIinv, z] using hJinv
    have hmul :=
      congrArg (fun t => FractionalIdeal.spanSingleton (R⁰) z * t) hJinv'
    have h' :
        ((FractionalIdeal.spanSingleton (R⁰) z) * (FractionalIdeal.spanSingleton (R⁰) z⁻¹)) *
            ((J : FractionalIdeal R⁰ (FractionRing R)) *
              (K : FractionalIdeal R⁰ (FractionRing R))) =
          FractionalIdeal.spanSingleton (R⁰) z := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    have hzz :
        (FractionalIdeal.spanSingleton (R⁰) z) * (FractionalIdeal.spanSingleton (R⁰) z⁻¹) = 1 := by
      simp [FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ ha0']
    simpa [hzz, z, mul_assoc] using h'
  refine ⟨K, a, ha0, ?_⟩
  -- Descend to integral ideals via `coeIdeal` injectivity.
  refine (FractionalIdeal.coeIdeal_inj (K := FractionRing R)).1 ?_
  simpa [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] using hJK_frac

lemma Ideal.isPrincipal_of_exists_mul_eq_span_singleton [NormalizedGCDMonoid R]
    {J K : Ideal R} {x : R} (hx0 : x ≠ 0)
    (hJK : J * K = Ideal.span ({x} : Set R)) :
    J.IsPrincipal := by
  classical
  have hxmemJK : x ∈ J * K := by
    simpa [hJK] using (Ideal.subset_span (by simp : x ∈ ({x} : Set R)))
  -- Shrink `K` to a finitely generated subideal `K'` witnessing `x ∈ J * K'`.
  have hxmemJK_sub :
      (x : R) ∈ (J : Submodule R R) * (K : Submodule R R) := by
    simpa using hxmemJK
  obtain ⟨T, T', hTJ, hT'K, hxTT'⟩ :=
    Submodule.mem_span_mul_finite_of_mem_mul (P := (J : Submodule R R)) (Q := (K : Submodule R R))
      hxmemJK_sub
  let K' : Ideal R := Ideal.span (T' : Set R)
  have hK'leK : K' ≤ K := by
    refine Ideal.span_le.2 ?_
    intro z hz
    exact hT'K hz
  have hxmemJK' : x ∈ J * K' := by
    have hmulset : ((T : Set R) * (T' : Set R)) ⊆ ((J : Set R) * (K' : Set R)) := by
      rintro z ⟨a, haT, b, hbT', rfl⟩
      refine ⟨a, hTJ haT, b, ?_, rfl⟩
      exact Ideal.subset_span hbT'
    have hxspan' :
        (x : R) ∈ Submodule.span R ((J : Set R) * (K' : Set R)) :=
      (Submodule.span_mono hmulset) hxTT'
    have :
        (x : R) ∈ (J : Submodule R R) * (K' : Submodule R R) := by
      simpa [Submodule.mul_eq_span_mul_set] using hxspan'
    simpa using this
  -- Let `g` be the gcd of the chosen generators of `K'`; then `K' ≤ (g)`.
  let g : R := T'.gcd id
  have hK'le_g : K' ≤ Ideal.span ({g} : Set R) := by
    refine Ideal.span_le.2 ?_
    intro z hz
    have hgdvd : g ∣ z := by
      simpa [g] using (Finset.gcd_dvd (s := T') (f := id) hz)
    rcases hgdvd with ⟨t, ht⟩
    refine (Ideal.mem_span_singleton').2 ⟨t, ?_⟩
    simpa [mul_comm] using ht.symm
  -- Upgrade to `x ∈ J * (g)`, hence `(x) ≤ J * (g)`.
  have hxmemJg : x ∈ J * Ideal.span ({g} : Set R) := by
    have : J * K' ≤ J * Ideal.span ({g} : Set R) := Ideal.mul_mono_right hK'le_g
    exact this hxmemJK'
  have hspanx_le : Ideal.span ({x} : Set R) ≤ J * Ideal.span ({g} : Set R) :=
    (Ideal.span_singleton_le_iff_mem (I := J * Ideal.span ({g} : Set R)) (x := x)).2 hxmemJg
  -- Show `J * (g) ≤ (x)` by proving `x ∣ b * g` for all `b ∈ J`.
  have hxdvd_bg : ∀ b ∈ J, x ∣ b * g := by
    intro b hbJ
    have hxdvd_bc : ∀ c ∈ T', x ∣ b * c := by
      intro c hc
      have hcK' : c ∈ K' := Ideal.subset_span hc
      have hbc_mem : b * c ∈ J * K' := Ideal.mul_mem_mul hbJ hcK'
      have hbc_mem' : b * c ∈ Ideal.span ({x} : Set R) := by
        have hle : J * K' ≤ J * K := Ideal.mul_mono_right hK'leK
        have : b * c ∈ J * K := hle hbc_mem
        simpa [hJK] using this
      rcases (Ideal.mem_span_singleton').1 hbc_mem' with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simpa [mul_comm, mul_left_comm, mul_assoc] using ht.symm
    have hxgcd : x ∣ T'.gcd (fun c => b * c) := by
      refine Finset.dvd_gcd ?_
      intro c hc
      exact hxdvd_bc c hc
    have hxnorm : x ∣ normalize b * g := by
      have hgcd_mul :
          T'.gcd (fun c => b * c) = normalize b * T'.gcd (id : R → R) := by
        simpa using (Finset.gcd_mul_left (s := T') (f := (id : R → R)) (a := b))
      have : x ∣ normalize b * T'.gcd (id : R → R) := by
        simpa [hgcd_mul] using hxgcd
      simpa [g] using this
    rcases associated_normalize b with ⟨u, hu⟩
    have hxmul : x ∣ (normalize b * g) * (↑u⁻¹ : R) := dvd_mul_of_dvd_left hxnorm _
    have : (normalize b * g) * (↑u⁻¹ : R) = b * g := by
      -- rewrite `normalize b` as `b * u` and cancel `u` on the right
      calc
        (normalize b * g) * (↑u⁻¹ : R) = ((b * (u : R)) * g) * (↑u⁻¹ : R) := by
          simp [hu, mul_assoc]
        _ = b * g * ((u : R) * (↑u⁻¹ : R)) := by
          ac_rfl
        _ = b * g := by simp
    simpa [this] using hxmul
  have hJg_le : J * Ideal.span ({g} : Set R) ≤ Ideal.span ({x} : Set R) := by
    refine Ideal.mul_le.2 ?_
    intro b hbJ z hz
    rcases (Ideal.mem_span_singleton').1 hz with ⟨t, rfl⟩
    rcases hxdvd_bg b hbJ with ⟨s, hs⟩
    refine (Ideal.mem_span_singleton').2 ?_
    refine ⟨t * s, ?_⟩
    -- `t * (b * g) = x * (t * s)`, so the product lies in `(x)`.
    calc
      (t * s) * x = t * (s * x) := by simp [mul_assoc]
      _ = t * (x * s) := by simp [mul_left_comm, mul_comm]
      _ = t * (b * g) := by simpa using congrArg (fun r => t * r) hs.symm
      _ = b * (t * g) := by simp [mul_left_comm]
  have hJg : J * Ideal.span ({g} : Set R) = Ideal.span ({x} : Set R) :=
    le_antisymm hJg_le hspanx_le
  -- From `(x) = J * (g)`, extract `y` with `x = y * g` and cancel `(g)` to show `J` is principal.
  have hxmem_g : x ∈ Ideal.span ({g} : Set R) := by
    have hle : J * Ideal.span ({g} : Set R) ≤ (⊤ : Ideal R) * Ideal.span ({g} : Set R) :=
      Ideal.mul_mono_left (le_top : J ≤ (⊤ : Ideal R))
    have : x ∈ (⊤ : Ideal R) * Ideal.span ({g} : Set R) := hle hxmemJg
    simpa using this
  rcases (Ideal.mem_span_singleton').1 hxmem_g with ⟨y, hy⟩
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hx0
    simpa [hg0] using hy.symm
  have hspanx : Ideal.span ({x} : Set R) = Ideal.span ({y} : Set R) * Ideal.span ({g} : Set R) := by
    -- Rewrite `(x)` as `(y*g) = (y)*(g)`.
    calc
      Ideal.span ({x} : Set R) = Ideal.span ({y * g} : Set R) := by simp [hy]
      _ = Ideal.span ({y} : Set R) * Ideal.span ({g} : Set R) := by
        simpa using (Ideal.span_singleton_mul_span_singleton (R := R) y g).symm
  have hcancel :
      (Ideal.span ({g} : Set R)) * J = (Ideal.span ({g} : Set R)) * Ideal.span ({y} : Set R) := by
    -- Commute to put `(g)` on the left, then use `(x) = J*(g) = (y)*(g)`.
    calc
      (Ideal.span ({g} : Set R)) * J = J * Ideal.span ({g} : Set R) := by simp [Ideal.mul_comm]
      _ = Ideal.span ({x} : Set R) := hJg
      _ = Ideal.span ({y} : Set R) * Ideal.span ({g} : Set R) := hspanx
      _ = (Ideal.span ({g} : Set R)) * Ideal.span ({y} : Set R) := by simp [Ideal.mul_comm]
  have hJ : J = Ideal.span ({y} : Set R) :=
    (Ideal.span_singleton_mul_right_inj (R := R) hg0).1 hcancel
  refine ⟨y, ?_⟩
  simp [hJ]

/-- In a normalized GCD domain, an integral ideal that is invertible as a fractional ideal
is principal. -/
theorem ideal_isPrincipal_of_isUnit_fractionalIdeal [NormalizedGCDMonoid R] (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) :
    I.IsPrincipal := by
  obtain ⟨K, x, hx0, hIK⟩ := Ideal.exists_mul_eq_span_singleton_of_isUnit_coe (R := R) I hI
  exact Ideal.isPrincipal_of_exists_mul_eq_span_singleton (R := R) (J := I) (K := K) hx0 hIK

@[expose] public section

section NormalizedGCDMonoid
variable [NormalizedGCDMonoid R]

/-- In a normalized GCD domain, every invertible fractional ideal is principal. -/
theorem NormalizedGCDMonoid.fractionalIdeal_isPrincipal_of_isUnit
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

/-- In a normalized GCD Domain, every class in the ideal class group is `1`. -/
theorem NormalizedGCDMonoid.classGroup_eq_one (x : ClassGroup R) : x = 1 := by
  refine ClassGroup.induction (R := R) (K := FractionRing R) (P := fun y => y = 1) ?_ x
  intro I
  -- `mk I = 1` iff `I` is principal as a submodule.
  refine (ClassGroup.mk_eq_one_iff (R := R) (K := FractionRing R) (I := I)).2 ?_
  exact fractionalIdeal_isPrincipal_of_isUnit (R := R) I

/-- The ideal class group of a normalized GCD Domain is trivial. -/
instance NormalizedGCDMonoid.instSubsingletonClassGroup : Subsingleton (ClassGroup R) := by
  refine ⟨fun x y => ?_⟩
  calc
    x = 1 := classGroup_eq_one (R := R) x
    _ = y := (classGroup_eq_one (R := R) y).symm

end NormalizedGCDMonoid
section UFD

variable [UniqueFactorizationMonoid R]

/-- The ideal class group of a UFD is trivial. -/
noncomputable instance UniqueFactorizationMonoid.instSubsingletonClassGroup :
    Subsingleton (ClassGroup R) :=
  letI : NormalizedGCDMonoid R :=
    Classical.choice (inferInstance : Nonempty (NormalizedGCDMonoid R))
  NormalizedGCDMonoid.instSubsingletonClassGroup R

end UFD
end

end Domain
end CommRing
