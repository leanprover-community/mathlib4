module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.DepRewrite

@[expose] public section

variable {R : Type*} [CommRing R] (n : ℕ) (I : Ideal R)

/--
For `I` an ideal of `R`, the group morphism from the roots of unity of `R`
of order `n` to `(R ⧸ I)ˣ`.
-/
def rootsOfUnity.mapQuot : (rootsOfUnity n R) →* (R ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).restrict _

@[simp]
theorem rootsOfUnity._coe_mapQuot (x : rootsOfUnity n R) :
    (rootsOfUnity.mapQuot n I x).val = Ideal.Quotient.mk I x.val := rfl

variable {n I} (h : Function.Bijective (rootsOfUnity.mapQuot n I))

open Classical in
@[simps]
noncomputable def teichmuller : MulChar (R ⧸ I) R where
  toFun := fun x ↦ if hx : IsUnit x then ((MulEquiv.ofBijective _ h).symm hx.unit).val else 0
  map_one' := by simp
  map_mul' x y := by
    by_cases h : IsUnit (x * y)
    · obtain ⟨hx, hy⟩ := IsUnit.mul_iff.mp h
      rw [dif_pos h, dif_pos hx, dif_pos hy, IsUnit.unit_mul hx hy, map_mul, Subgroup.coe_mul,
        Units.val_mul]
    · obtain hx | hy := not_and_or.mp <| IsUnit.mul_iff.not.mp h
      · rw [dif_neg h, dif_neg hx, zero_mul]
      · rw [dif_neg h, dif_neg hy, mul_zero]
  map_nonunit' _ h := by simp [h]

theorem teichmuller_eq_one (hI : I = ⊤) :
    teichmuller h = 1 := by
  rw [MulChar.eq_one_iff]
  intro x
  rw [← Ideal.Quotient.subsingleton_iff] at hI
  simp [teichmuller_apply, isUnit_iff_eq_one, Units.eq_one x]

theorem teichmuller_apply_nonunit {x : (R ⧸ I)} (hx : ¬ IsUnit x) :
    teichmuller h x = 0 := by
  rw [teichmuller_apply, dif_neg hx]

theorem teichmuller_zero (hI : I ≠ ⊤) :
    teichmuller h 0 = 0 := by
  have : Nontrivial (R ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hI
  rw [teichmuller_apply_nonunit _ not_isUnit_zero]

theorem teichmuller_apply_unit (x : (R ⧸ I)ˣ) :
    teichmuller h x = ((MulEquiv.ofBijective _ h).symm x).val := by simp

theorem teichmuller_eq_one_iff (x : (R ⧸ I)ˣ) :
    teichmuller h x = 1 ↔ x = 1 := by simp

theorem teichmuller_apply_pow_eq_one (x : (R ⧸ I)ˣ) :
    teichmuller h (x ^ n) = 1 := by
  rw [map_pow, teichmuller_apply, dif_pos x.isUnit, ← Units.val_pow_eq_pow_val,
    (mem_rootsOfUnity _ _).mp, Units.val_one]
  exact SetLike.coe_mem _

theorem exists_nat_teichmuller_eq_pow [IsDomain R] [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (x : (R ⧸ I)ˣ) :
    ∃ a : ℕ, a < n ∧ teichmuller h x = ζ ^ a := by
  have := teichmuller_apply_pow_eq_one h x
  rw [map_pow] at this
  obtain ⟨a, ha, ha'⟩ := hζ.eq_pow_of_pow_eq_one this
  refine ⟨a, ha, ha'.symm⟩

theorem map_teichmuller_eq_pow [IsDomain R] [NeZero n] {σ : R →+* R} {m : ℕ} {ζ : R}
    (hm : m ≠ 0) (hζ : IsPrimitiveRoot ζ n) (hσ : σ ζ = ζ ^ m) (x : R ⧸ I) :
    σ (teichmuller h x) = (teichmuller h x) ^ m  := by
  by_cases hx : IsUnit x
  · lift x to (R ⧸ I)ˣ using hx
    obtain ⟨a, -, ha⟩ := exists_nat_teichmuller_eq_pow h hζ x
    rw [ha, map_pow, hσ, pow_right_comm]
  · rw [teichmuller_apply_nonunit h hx, map_zero, zero_pow hm]

theorem teichmuller_pow_eq_one :
    teichmuller h ^ n = 1 := by
  refine MulChar.eq_one_iff.mpr fun _ ↦ ?_
  rw [MulChar.pow_apply_coe, ← map_pow, teichmuller_apply_pow_eq_one]

theorem IsPrimitiveRoot.exists_teichmuller_eq [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    ∃ x : (R ⧸ I)ˣ, teichmuller h x = ζ := by
  have : (hζ.isUnit (NeZero.ne _)).unit ∈ rootsOfUnity n R := by
    rw! [mem_rootsOfUnity, ← IsUnit.unit_pow, hζ.pow_eq_one, IsUnit.unit_one]
    rfl
  refine ⟨rootsOfUnity.mapQuot n I ⟨(hζ.isUnit (NeZero.ne n)).unit, this⟩, ?_⟩
  rw [teichmuller_apply, dif_pos (Units.isUnit _), IsUnit.unit_of_val_units,
    ← MulEquiv.ofBijective_apply _ h, MulEquiv.symm_apply_apply, IsUnit.unit_spec]

theorem orderOf_teichmuller [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    orderOf (teichmuller h) = n := by
  refine (orderOf_eq_iff (NeZero.pos _)).mpr ⟨teichmuller_pow_eq_one h, fun m hm₁ hm₂ ↦ ?_⟩
  rw [MulChar.ne_one_iff]
  obtain ⟨x, hx⟩ := hζ.exists_teichmuller_eq h
  refine ⟨x, ?_⟩
  rw [MulChar.pow_apply_coe, hx, ne_eq, ← orderOf_dvd_iff_pow_eq_one, ← hζ.eq_orderOf]
  exact Nat.not_dvd_of_pos_of_lt hm₂ hm₁

theorem teichmuller_pow_ne_one [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) {a : ℤ}
    (ha : ¬ ↑n ∣ a) :
    teichmuller h ^ a ≠ 1 := by
  rwa [ne_eq, ← orderOf_dvd_iff_zpow_eq_one, orderOf_teichmuller h hζ]

theorem teichmuller_mk_eq_of_unit (x : (R ⧸ I)ˣ) :
    Ideal.Quotient.mk I (teichmuller h x) = x := by
  set y := (MulEquiv.ofBijective _ h).symm x
  have : x = MulEquiv.ofBijective _ h y := by rw [← MulEquiv.symm_apply_eq]
  rw [teichmuller_apply_unit, this, MulEquiv.symm_apply_apply, MulEquiv.ofBijective_apply,
    rootsOfUnity._coe_mapQuot]

attribute [local instance] Ideal.Quotient.field in
theorem teichmuller_mk_zpow_eq_of_unit [I.IsMaximal] (a : ℤ) (x : (R ⧸ I)ˣ) :
    Ideal.Quotient.mk I ((teichmuller h ^ a) x) = (x ^ a : (R ⧸ I)ˣ) := by
  rw [MulChar.zpow_apply_coe (teichmuller h), teichmuller_mk_eq_of_unit]

attribute [local instance] Ideal.Quotient.field in
theorem teichmuller_mk_eq [I.IsMaximal] (x : R ⧸ I) :
    Ideal.Quotient.mk I (teichmuller h x) = x := by
  by_cases hI : I = ⊤
  · have := Ideal.Quotient.subsingleton_iff.mpr hI
    rw [teichmuller_eq_one _ hI, MulChar.one_apply (isUnit_of_subsingleton x),
      Subsingleton.eq_one x, map_one]
  by_cases hx : x = 0
  · rw [hx, teichmuller_zero _ hI, map_zero]
  lift x to (R ⧸ I)ˣ using Ne.isUnit hx
  exact teichmuller_mk_eq_of_unit h x

theorem orderOf_teichmuller_comp_mk [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    orderOf ((teichmuller h).ringHomComp (Ideal.Quotient.mk I)) = n := by
  refine (orderOf_eq_iff (NeZero.pos _)).mpr ⟨?_, fun m hm₁ hm₂ ↦ ?_⟩
  · rw [MulChar.ringHomComp_pow, teichmuller_pow_eq_one h, MulChar.ringHomComp_one]
  · rw [MulChar.ringHomComp_pow, MulChar.ne_one_iff]
    obtain ⟨x, hx⟩ := hζ.exists_teichmuller_eq h
    rw [teichmuller_apply_unit] at hx
    refine ⟨x, ?_⟩
    rw [MulChar.ringHomComp_apply, MulChar.pow_apply_coe, map_pow, teichmuller_mk_eq_of_unit]
    set y := (MulEquiv.ofBijective _ h).symm x with y_def
    have : x = MulEquiv.ofBijective _ h y := by rw [← MulEquiv.symm_apply_eq]
    rw [this, ne_eq, ← Units.val_pow_eq_pow_val, Units.val_eq_one,
      ← map_eq_one_iff (MulEquiv.ofBijective _ h).symm (MulEquiv.injective _), ← map_pow,
      MulEquiv.symm_apply_apply, y_def, Subtype.ext_iff, Units.ext_iff, rootsOfUnity.coe_pow, hx,
      OneMemClass.coe_one, Units.val_one, ← orderOf_dvd_iff_pow_eq_one, ← hζ.eq_orderOf]
    exact Nat.not_dvd_of_pos_of_lt hm₂ hm₁
