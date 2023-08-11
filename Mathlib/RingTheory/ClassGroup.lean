/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.GroupTheory.QuotientGroup
import Mathlib.RingTheory.DedekindDomain.Ideal

#align_import ring_theory.class_group from "leanprover-community/mathlib"@"565eb991e264d0db702722b4bde52ee5173c9950"

/-!
# The ideal class group

This file defines the ideal class group `ClassGroup R` of fractional ideals of `R`
inside its field of fractions.

## Main definitions
 - `toPrincipalIdeal` sends an invertible `x : K` to an invertible fractional ideal
 - `ClassGroup` is the quotient of invertible fractional ideals modulo `toPrincipalIdeal.range`
 - `ClassGroup.mk0` sends a nonzero integral ideal in a Dedekind domain to its class

## Main results
 - `ClassGroup.mk0_eq_mk0_iff` shows the equivalence with the "classical" definition,
   where `I ~ J` iff `x I = y J` for `x y ≠ (0 : R)`

## Implementation details

The definition of `ClassGroup R` involves `FractionRing R`. However, the API should be completely
identical no matter the choice of field of fractions for `R`.
-/


variable {R K L : Type*} [CommRing R]

variable [Field K] [Field L] [DecidableEq L]

variable [Algebra R K] [IsFractionRing R K]

variable [Algebra K L] [FiniteDimensional K L]

variable [Algebra R L] [IsScalarTower R K L]

open scoped nonZeroDivisors

open IsLocalization IsFractionRing FractionalIdeal Units

section

variable (R K)

/-- `toPrincipalIdeal R K x` sends `x ≠ 0 : K` to the fractional `R`-ideal generated by `x` -/
irreducible_def toPrincipalIdeal : Kˣ →* (FractionalIdeal R⁰ K)ˣ :=
  { toFun := fun x =>
      ⟨spanSingleton _ x, spanSingleton _ x⁻¹, by
        simp only [spanSingleton_one, Units.mul_inv', spanSingleton_mul_spanSingleton], by
        simp only [spanSingleton_one, Units.inv_mul', spanSingleton_mul_spanSingleton]⟩
    map_mul' := fun x y =>
      ext (by simp only [Units.val_mk, Units.val_mul, spanSingleton_mul_spanSingleton])
    map_one' := ext (by simp only [spanSingleton_one, Units.val_mk, Units.val_one]) }
#align to_principal_ideal toPrincipalIdeal

variable {R K}

@[simp]
theorem coe_toPrincipalIdeal (x : Kˣ) :
    (toPrincipalIdeal R K x : FractionalIdeal R⁰ K) = spanSingleton _ (x : K) := by
  simp only [toPrincipalIdeal]; rfl
#align coe_to_principal_ideal coe_toPrincipalIdeal

@[simp]
theorem toPrincipalIdeal_eq_iff {I : (FractionalIdeal R⁰ K)ˣ} {x : Kˣ} :
    toPrincipalIdeal R K x = I ↔ spanSingleton R⁰ (x : K) = I := by
  simp only [toPrincipalIdeal]; exact Units.ext_iff
#align to_principal_ideal_eq_iff toPrincipalIdeal_eq_iff

theorem mem_principal_ideals_iff {I : (FractionalIdeal R⁰ K)ˣ} :
    I ∈ (toPrincipalIdeal R K).range ↔ ∃ x : K, spanSingleton R⁰ x = I := by
  simp only [MonoidHom.mem_range, toPrincipalIdeal_eq_iff]
  constructor <;> rintro ⟨x, hx⟩
  · exact ⟨x, hx⟩
  · refine ⟨Units.mk0 x ?_, hx⟩
    rintro rfl
    simp [I.ne_zero.symm] at hx
#align mem_principal_ideals_iff mem_principal_ideals_iff

instance PrincipalIdeals.normal : (toPrincipalIdeal R K).range.Normal :=
  Subgroup.normal_of_comm _
#align principal_ideals.normal PrincipalIdeals.normal

end

variable (R)

variable [IsDomain R]

/-- The ideal class group of `R` is the group of invertible fractional ideals
modulo the principal ideals. -/
def ClassGroup :=
  (FractionalIdeal R⁰ (FractionRing R))ˣ ⧸ (toPrincipalIdeal R (FractionRing R)).range
#align class_group ClassGroup

noncomputable instance : CommGroup (ClassGroup R) :=
  QuotientGroup.Quotient.commGroup (toPrincipalIdeal R (FractionRing R)).range

noncomputable instance : Inhabited (ClassGroup R) := ⟨1⟩

variable {R}

/-- Send a nonzero fractional ideal to the corresponding class in the class group. -/
noncomputable def ClassGroup.mk : (FractionalIdeal R⁰ K)ˣ →* ClassGroup R :=
  (QuotientGroup.mk' (toPrincipalIdeal R (FractionRing R)).range).comp
    (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)))
#align class_group.mk ClassGroup.mk

-- Can't be `@[simp]` because it can't figure out the quotient relation.
theorem ClassGroup.Quot_mk_eq_mk (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    Quot.mk _ I = ClassGroup.mk I := by
  rw [ClassGroup.mk, canonicalEquiv_self, RingEquiv.coe_monoidHom_refl, Units.map_id,
      MonoidHom.comp_apply, MonoidHom.id_apply, QuotientGroup.mk'_apply]
  rfl

theorem ClassGroup.mk_eq_mk {I J : (FractionalIdeal R⁰ <| FractionRing R)ˣ} :
    ClassGroup.mk I = ClassGroup.mk J ↔
      ∃ x : (FractionRing R)ˣ, I * toPrincipalIdeal R (FractionRing R) x = J := by
  erw [QuotientGroup.mk'_eq_mk', canonicalEquiv_self, Units.map_id, Set.exists_range_iff]
  rfl
#align class_group.mk_eq_mk ClassGroup.mk_eq_mk

theorem ClassGroup.mk_eq_mk_of_coe_ideal {I J : (FractionalIdeal R⁰ <| FractionRing R)ˣ}
    {I' J' : Ideal R} (hI : (I : FractionalIdeal R⁰ <| FractionRing R) = I')
    (hJ : (J : FractionalIdeal R⁰ <| FractionRing R) = J') :
    ClassGroup.mk I = ClassGroup.mk J ↔
      ∃ x y : R, x ≠ 0 ∧ y ≠ 0 ∧ Ideal.span {x} * I' = Ideal.span {y} * J' := by
  rw [ClassGroup.mk_eq_mk]
  constructor
  · rintro ⟨x, rfl⟩
    rw [Units.val_mul, hI, coe_toPrincipalIdeal, mul_comm,
      spanSingleton_mul_coeIdeal_eq_coeIdeal] at hJ
    exact ⟨_, _, sec_fst_ne_zero (R := R) le_rfl x.ne_zero,
      sec_snd_ne_zero (R := R) le_rfl (x : FractionRing R), hJ⟩
  · rintro ⟨x, y, hx, hy, h⟩
    constructor
    rw [mul_comm, ← Units.eq_iff, Units.val_mul, coe_toPrincipalIdeal]
    convert
      (mk'_mul_coeIdeal_eq_coeIdeal (FractionRing R) <| mem_nonZeroDivisors_of_ne_zero hy).2 h
    apply (Ne.isUnit _).unit_spec
    rwa [Ne, mk'_eq_zero_iff_eq_zero]
#align class_group.mk_eq_mk_of_coe_ideal ClassGroup.mk_eq_mk_of_coe_ideal

theorem ClassGroup.mk_eq_one_of_coe_ideal {I : (FractionalIdeal R⁰ <| FractionRing R)ˣ}
    {I' : Ideal R} (hI : (I : FractionalIdeal R⁰ <| FractionRing R) = I') :
    ClassGroup.mk I = 1 ↔ ∃ x : R, x ≠ 0 ∧ I' = Ideal.span {x} := by
  rw [← map_one (ClassGroup.mk (R := R) (K := FractionRing R)),
    ClassGroup.mk_eq_mk_of_coe_ideal hI (?_ : _ = ↑(⊤ : Ideal R))]
  any_goals rfl
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    rw [Ideal.mul_top] at h
    rcases Ideal.mem_span_singleton_mul.mp ((Ideal.span_singleton_le_iff_mem _).mp h.ge) with
      ⟨i, _hi, rfl⟩
    rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_right_inj hx] at h
    exact ⟨i, right_ne_zero_of_mul hy, h⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨1, x, one_ne_zero, hx, by rw [Ideal.span_singleton_one, Ideal.top_mul, Ideal.mul_top]⟩
#align class_group.mk_eq_one_of_coe_ideal ClassGroup.mk_eq_one_of_coe_ideal

variable (K)

/-- Induction principle for the class group: to show something holds for all `x : ClassGroup R`,
we can choose a fraction field `K` and show it holds for the equivalence class of each
`I : FractionalIdeal R⁰ K`. -/
@[elab_as_elim]
theorem ClassGroup.induction {P : ClassGroup R → Prop}
    (h : ∀ I : (FractionalIdeal R⁰ K)ˣ, P (ClassGroup.mk I)) (x : ClassGroup R) : P x :=
  QuotientGroup.induction_on x fun I => by
    have : I = (Units.mapEquiv (canonicalEquiv R⁰ K (FractionRing R)).toMulEquiv)
      (Units.mapEquiv (canonicalEquiv R⁰ (FractionRing R) K).toMulEquiv I) := by
      simp [← Units.eq_iff]
    rw [congr_arg (QuotientGroup.mk (s := (toPrincipalIdeal R (FractionRing R)).range)) this]
    exact h _
#align class_group.induction ClassGroup.induction

/-- The definition of the class group does not depend on the choice of field of fractions. -/
noncomputable def ClassGroup.equiv :
    ClassGroup R ≃* (FractionalIdeal R⁰ K)ˣ ⧸ (toPrincipalIdeal R K).range := by
  haveI : Subgroup.map
    (Units.mapEquiv (canonicalEquiv R⁰ (FractionRing R) K).toMulEquiv).toMonoidHom
    (toPrincipalIdeal R (FractionRing R)).range = (toPrincipalIdeal R K).range := by
    ext I
    simp only [Subgroup.mem_map, mem_principal_ideals_iff]
    constructor
    · rintro ⟨I, ⟨x, hx⟩, rfl⟩
      refine ⟨FractionRing.algEquiv R K x, ?_⟩
      simp only [RingEquiv.toMulEquiv_eq_coe, MulEquiv.coe_toMonoidHom, coe_mapEquiv, ← hx,
        RingEquiv.coe_toMulEquiv, canonicalEquiv_spanSingleton]
      rfl
    · rintro ⟨x, hx⟩
      refine ⟨Units.mapEquiv (canonicalEquiv R⁰ K (FractionRing R)).toMulEquiv I,
        ⟨(FractionRing.algEquiv R K).symm x, ?_⟩, Units.ext ?_⟩
      · simp only [RingEquiv.toMulEquiv_eq_coe, coe_mapEquiv, ← hx, RingEquiv.coe_toMulEquiv,
          canonicalEquiv_spanSingleton]
        rfl
      · simp only [RingEquiv.toMulEquiv_eq_coe, MulEquiv.coe_toMonoidHom, coe_mapEquiv,
          RingEquiv.coe_toMulEquiv, canonicalEquiv_canonicalEquiv, canonicalEquiv_self,
          RingEquiv.refl_apply]
  exact @QuotientGroup.congr (FractionalIdeal R⁰ (FractionRing R))ˣ _ (FractionalIdeal R⁰ K)ˣ _
    (toPrincipalIdeal R (FractionRing R)).range (toPrincipalIdeal R K).range _ _
    (Units.mapEquiv (FractionalIdeal.canonicalEquiv R⁰ (FractionRing R) K).toMulEquiv) this
#align class_group.equiv ClassGroup.equiv

@[simp]
theorem ClassGroup.equiv_mk (K' : Type*) [Field K'] [Algebra R K'] [IsFractionRing R K']
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.equiv K' (ClassGroup.mk I) =
      QuotientGroup.mk' _ (Units.mapEquiv (↑(FractionalIdeal.canonicalEquiv R⁰ K K')) I) := by
  rw [ClassGroup.equiv, ClassGroup.mk, MonoidHom.comp_apply, QuotientGroup.congr_mk']
  congr
  rw [← Units.eq_iff, Units.coe_mapEquiv, Units.coe_mapEquiv, Units.coe_map]
  exact FractionalIdeal.canonicalEquiv_canonicalEquiv _ _ _ _ _
#align class_group.equiv_mk ClassGroup.equiv_mk

@[simp]
theorem ClassGroup.mk_canonicalEquiv (K' : Type*) [Field K'] [Algebra R K'] [IsFractionRing R K']
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mk (Units.map (↑(canonicalEquiv R⁰ K K')) I : (FractionalIdeal R⁰ K')ˣ) =
      ClassGroup.mk I := by
  rw [ClassGroup.mk, MonoidHom.comp_apply, ← MonoidHom.comp_apply (Units.map _), ← Units.map_comp, ←
      RingEquiv.coe_monoidHom_trans, FractionalIdeal.canonicalEquiv_trans_canonicalEquiv]
  rfl
#align class_group.mk_canonical_equiv ClassGroup.mk_canonicalEquiv

/-- Send a nonzero integral ideal to an invertible fractional ideal. -/
noncomputable def FractionalIdeal.mk0 [IsDedekindDomain R] : (Ideal R)⁰ →* (FractionalIdeal R⁰ K)ˣ
    where
  toFun I := Units.mk0 I (coeIdeal_ne_zero.mpr <| mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  map_one' := by simp
  map_mul' x y := by simp
#align fractional_ideal.mk0 FractionalIdeal.mk0

@[simp]
theorem FractionalIdeal.coe_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    (FractionalIdeal.mk0 K I : FractionalIdeal R⁰ K) = I := rfl
#align fractional_ideal.coe_mk0 FractionalIdeal.coe_mk0

theorem FractionalIdeal.canonicalEquiv_mk0 [IsDedekindDomain R] (K' : Type*) [Field K']
    [Algebra R K'] [IsFractionRing R K'] (I : (Ideal R)⁰) :
    FractionalIdeal.canonicalEquiv R⁰ K K' (FractionalIdeal.mk0 K I) = FractionalIdeal.mk0 K' I :=
  by simp only [FractionalIdeal.coe_mk0, FractionalIdeal.canonicalEquiv_coeIdeal]
#align fractional_ideal.canonical_equiv_mk0 FractionalIdeal.canonicalEquiv_mk0

@[simp]
theorem FractionalIdeal.map_canonicalEquiv_mk0 [IsDedekindDomain R] (K' : Type*) [Field K']
    [Algebra R K'] [IsFractionRing R K'] (I : (Ideal R)⁰) :
    Units.map (↑(FractionalIdeal.canonicalEquiv R⁰ K K')) (FractionalIdeal.mk0 K I) =
      FractionalIdeal.mk0 K' I :=
  Units.ext (FractionalIdeal.canonicalEquiv_mk0 K K' I)
#align fractional_ideal.map_canonical_equiv_mk0 FractionalIdeal.map_canonicalEquiv_mk0

/-- Send a nonzero ideal to the corresponding class in the class group. -/
noncomputable def ClassGroup.mk0 [IsDedekindDomain R] : (Ideal R)⁰ →* ClassGroup R :=
  ClassGroup.mk.comp (FractionalIdeal.mk0 (FractionRing R))
#align class_group.mk0 ClassGroup.mk0

@[simp]
theorem ClassGroup.mk_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    ClassGroup.mk (FractionalIdeal.mk0 K I) = ClassGroup.mk0 I := by
  rw [ClassGroup.mk0, MonoidHom.comp_apply, ← ClassGroup.mk_canonicalEquiv K (FractionRing R),
    FractionalIdeal.map_canonicalEquiv_mk0]
#align class_group.mk_mk0 ClassGroup.mk_mk0

@[simp]
theorem ClassGroup.equiv_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    ClassGroup.equiv K (ClassGroup.mk0 I) =
      QuotientGroup.mk' (toPrincipalIdeal R K).range (FractionalIdeal.mk0 K I) := by
  rw [ClassGroup.mk0, MonoidHom.comp_apply, ClassGroup.equiv_mk]
  congr 1
  simp [← Units.eq_iff]
#align class_group.equiv_mk0 ClassGroup.equiv_mk0

theorem ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring [IsDedekindDomain R] {I J : (Ideal R)⁰} :
    ClassGroup.mk0 I =
      ClassGroup.mk0 J ↔ ∃ (x : _) (_ : x ≠ (0 : K)), spanSingleton R⁰ x * I = J := by
  refine (ClassGroup.equiv K).injective.eq_iff.symm.trans ?_
  simp only [ClassGroup.equiv_mk0, QuotientGroup.mk'_eq_mk', mem_principal_ideals_iff,
    Units.ext_iff, Units.val_mul, FractionalIdeal.coe_mk0, exists_prop]
  constructor
  · rintro ⟨X, ⟨x, hX⟩, hx⟩
    refine ⟨x, ?_, ?_⟩
    · rintro rfl; simp [X.ne_zero.symm] at hX
    simpa only [hX, mul_comm] using hx
  · rintro ⟨x, hx, eq_J⟩
    refine ⟨Units.mk0 _ (spanSingleton_ne_zero_iff.mpr hx), ⟨x, rfl⟩, ?_⟩
    simpa only [mul_comm] using eq_J
#align class_group.mk0_eq_mk0_iff_exists_fraction_ring ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring

variable {K}

theorem ClassGroup.mk0_eq_mk0_iff [IsDedekindDomain R] {I J : (Ideal R)⁰} :
    ClassGroup.mk0 I = ClassGroup.mk0 J ↔
      ∃ (x y : R) (_hx : x ≠ 0) (_hy : y ≠ 0), Ideal.span {x} * (I : Ideal R) =
      Ideal.span {y} * J := by
  refine (ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring (FractionRing R)).trans ⟨?_, ?_⟩
  · rintro ⟨z, hz, h⟩
    obtain ⟨x, ⟨y, hy⟩, rfl⟩ := IsLocalization.mk'_surjective R⁰ z
    refine ⟨x, y, ?_, mem_nonZeroDivisors_iff_ne_zero.mp hy, ?_⟩
    · rintro hx; apply hz
      rw [hx, IsFractionRing.mk'_eq_div, _root_.map_zero, zero_div]
    · exact (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal _ hy).mp h
  · rintro ⟨x, y, hx, hy, h⟩
    have hy' : y ∈ R⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hy
    refine ⟨IsLocalization.mk' _ x ⟨y, hy'⟩, ?_, ?_⟩
    · contrapose! hx
      rwa [mk'_eq_iff_eq_mul, MulZeroClass.zero_mul, ← (algebraMap R (FractionRing R)).map_zero,
        (IsFractionRing.injective R (FractionRing R)).eq_iff] at hx
    · exact (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal _ hy').mpr h
#align class_group.mk0_eq_mk0_iff ClassGroup.mk0_eq_mk0_iff

/-- Maps a nonzero fractional ideal to an integral representative in the class group. -/
noncomputable def ClassGroup.integralRep
    (I : FractionalIdeal R⁰ (FractionRing R)) :
    Ideal R :=
  let a := I.2.choose
  { carrier := {x | (algebraMap R _ a)⁻¹ * algebraMap R _ x ∈ I.1}
    add_mem' := by
      simp only [Set.mem_setOf_eq, RingHom.map_add, mul_add]
      exact fun ha hb => Submodule.add_mem _ ha hb
    zero_mem' := by
      simp only [Set.mem_setOf_eq, RingHom.map_zero, mul_zero]
      exact Submodule.zero_mem _
    smul_mem' := by
      intro c _ hb
      simp only [smul_eq_mul, Set.mem_setOf_eq, RingHom.map_mul,
        mul_left_comm ((algebraMap R (FractionRing R)) a)⁻¹]
      rw [← Algebra.smul_def c]
      exact Submodule.smul_mem _ c hb }

theorem ClassGroup.integralRep_mem_nonZeroDivisors
    {I} (hI : I ≠ 0) :
    ClassGroup.integralRep I ∈ (Ideal R)⁰ := by
  let a := I.2.choose
  have a_ne_zero' := I.2.choose_spec.1
  have a_ne_zero := mem_nonZeroDivisors_iff_ne_zero.mp a_ne_zero'
  have fa_ne_zero : (algebraMap R (FractionRing R)) a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a_ne_zero'
  rw [mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot, Submodule.ne_bot_iff]
  obtain ⟨x, x_ne, x_mem⟩ := exists_ne_zero_mem_isInteger hI
  refine ⟨a*x, ?_, mul_ne_zero a_ne_zero x_ne⟩
  change ((algebraMap R _) a)⁻¹ * (algebraMap R _) (a * x) ∈ I
  rwa [RingHom.map_mul, ← mul_assoc, inv_mul_cancel fa_ne_zero, one_mul]

theorem ClassGroup.mk0_integralRep [IsDedekindDomain R]
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    ClassGroup.mk0 ⟨ClassGroup.integralRep I, ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩
      = ClassGroup.mk I := by
  let a := I.1.2.choose
  have a_ne_zero' := I.1.2.choose_spec.1
  have ha := I.1.2.choose_spec.2
  have fa_ne_zero : (algebraMap R (FractionRing R)) a ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a_ne_zero'
  symm
  apply Quotient.sound
  change @Setoid.r _
    (QuotientGroup.leftRel (toPrincipalIdeal R (FractionRing R)).range) _ _
  rw [canonicalEquiv_self, RingEquiv.coe_monoidHom_refl, Units.map_id, MonoidHom.id_apply,
      MonoidHom.id_apply, QuotientGroup.leftRel_apply]
  refine ⟨Units.mk0 (algebraMap R _ a) fa_ne_zero, ?_⟩
  rw [_root_.eq_inv_mul_iff_mul_eq, eq_comm, mul_comm I]
  apply Units.ext
  simp only [FractionalIdeal.coe_mk0, FractionalIdeal.map_canonicalEquiv_mk0,
    Units.val_mk0, coe_toPrincipalIdeal, Units.val_mul,
    FractionalIdeal.eq_spanSingleton_mul]
  constructor
  · intro zJ' hzJ'
    obtain ⟨zJ, hzJ, rfl⟩ := (mem_coeIdeal R⁰).mp hzJ'
    refine ⟨_, hzJ, ?_⟩
    rw [← mul_assoc, mul_inv_cancel fa_ne_zero, one_mul]
  · intro zI' hzI'
    obtain ⟨y, hy⟩ := ha zI' hzI'
    rw [← Algebra.smul_def, mem_coeIdeal]
    refine' ⟨y, _, hy⟩
    show (algebraMap R _ a)⁻¹ * algebraMap R _ y ∈ (I : FractionalIdeal R⁰ (FractionRing R))
    rwa [hy, Algebra.smul_def, ← mul_assoc, inv_mul_cancel fa_ne_zero, one_mul]

theorem ClassGroup.mk0_surjective [IsDedekindDomain R] :
    Function.Surjective (ClassGroup.mk0 : (Ideal R)⁰ → ClassGroup R) := by
  rintro ⟨I⟩
  refine ⟨⟨ ClassGroup.integralRep I.1, ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩, ?_⟩
  rw [ClassGroup.mk0_integralRep, ClassGroup.Quot_mk_eq_mk]
#align class_group.mk0_surjective ClassGroup.mk0_surjective

theorem ClassGroup.mk_eq_one_iff {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk I = 1 ↔ (I : Submodule R K).IsPrincipal := by
  rw [← (ClassGroup.equiv K).injective.eq_iff]
  simp only [equiv_mk, canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl, QuotientGroup.mk'_apply,
    _root_.map_one, QuotientGroup.eq_one_iff, MonoidHom.mem_range, ext_iff, coe_toPrincipalIdeal,
    coe_mapEquiv, MulEquiv.refl_apply]
  refine ⟨fun ⟨x, hx⟩ => ⟨⟨x, by rw [← hx, coe_spanSingleton]⟩⟩, ?_⟩
  intro hI
  obtain ⟨x, hx⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hI
  have hx' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
    apply Subtype.coe_injective
    simp only [val_eq_coe, hx, coe_spanSingleton]
  refine ⟨Units.mk0 x ?_, ?_⟩
  · intro x_eq; apply Units.ne_zero I; simp [hx', x_eq]
  · simp [hx']
#align class_group.mk_eq_one_iff ClassGroup.mk_eq_one_iff

theorem ClassGroup.mk0_eq_one_iff [IsDedekindDomain R] {I : Ideal R} (hI : I ∈ (Ideal R)⁰) :
    ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ I.IsPrincipal :=
  ClassGroup.mk_eq_one_iff.trans (coeSubmodule_isPrincipal R _)
#align class_group.mk0_eq_one_iff ClassGroup.mk0_eq_one_iff

/-- The class group of principal ideal domain is finite (in fact a singleton).

See `ClassGroup.fintypeOfAdmissibleOfFinite` for a finiteness proof that works for rings of integers
of global fields.
-/
noncomputable instance [IsPrincipalIdealRing R] : Fintype (ClassGroup R) where
  elems := {1}
  complete := by
    refine ClassGroup.induction (R := R) (FractionRing R) (fun I => ?_)
    rw [Finset.mem_singleton]
    exact ClassGroup.mk_eq_one_iff.mpr (I : FractionalIdeal R⁰ (FractionRing R)).isPrincipal

/-- The class number of a principal ideal domain is `1`. -/
theorem card_classGroup_eq_one [IsPrincipalIdealRing R] : Fintype.card (ClassGroup R) = 1 := by
  rw [Fintype.card_eq_one_iff]
  use 1
  refine ClassGroup.induction (R := R) (FractionRing R) (fun I => ?_)
  exact ClassGroup.mk_eq_one_iff.mpr (I : FractionalIdeal R⁰ (FractionRing R)).isPrincipal
#align card_class_group_eq_one card_classGroup_eq_one

/-- The class number is `1` iff the ring of integers is a principal ideal domain. -/
theorem card_classGroup_eq_one_iff [IsDedekindDomain R] [Fintype (ClassGroup R)] :
    Fintype.card (ClassGroup R) = 1 ↔ IsPrincipalIdealRing R := by
  constructor; swap; · intros; convert card_classGroup_eq_one (R := R)
  rw [Fintype.card_eq_one_iff]
  rintro ⟨I, hI⟩
  have eq_one : ∀ J : ClassGroup R, J = 1 := fun J => (hI J).trans (hI 1).symm
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact bot_isPrincipal
  · exact (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hI)).mp (eq_one _)
#align card_class_group_eq_one_iff card_classGroup_eq_one_iff
