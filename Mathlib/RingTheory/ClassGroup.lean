/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.RingTheory.DedekindDomain.Ideal

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


variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

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

variable {R K}

@[simp]
theorem coe_toPrincipalIdeal (x : Kˣ) :
    (toPrincipalIdeal R K x : FractionalIdeal R⁰ K) = spanSingleton _ (x : K) := by
  simp only [toPrincipalIdeal]; rfl

@[simp]
theorem toPrincipalIdeal_eq_iff {I : (FractionalIdeal R⁰ K)ˣ} {x : Kˣ} :
    toPrincipalIdeal R K x = I ↔ spanSingleton R⁰ (x : K) = I := by
  simp only [toPrincipalIdeal]; exact Units.ext_iff

theorem mem_principal_ideals_iff {I : (FractionalIdeal R⁰ K)ˣ} :
    I ∈ (toPrincipalIdeal R K).range ↔ ∃ x : K, spanSingleton R⁰ x = I := by
  simp only [MonoidHom.mem_range, toPrincipalIdeal_eq_iff]
  constructor <;> rintro ⟨x, hx⟩
  · exact ⟨x, hx⟩
  · refine ⟨Units.mk0 x ?_, hx⟩
    rintro rfl
    simp [I.ne_zero.symm] at hx

instance PrincipalIdeals.normal : (toPrincipalIdeal R K).range.Normal :=
  Subgroup.normal_of_comm _

end

variable (R)
variable [IsDomain R]

/-- The ideal class group of `R` is the group of invertible fractional ideals
modulo the principal ideals. -/
def ClassGroup :=
  (FractionalIdeal R⁰ (FractionRing R))ˣ ⧸ (toPrincipalIdeal R (FractionRing R)).range

noncomputable instance : CommGroup (ClassGroup R) :=
  QuotientGroup.Quotient.commGroup (toPrincipalIdeal R (FractionRing R)).range

noncomputable instance : Inhabited (ClassGroup R) := ⟨1⟩

variable {R}

/-- Send a nonzero fractional ideal to the corresponding class in the class group. -/
noncomputable def ClassGroup.mk : (FractionalIdeal R⁰ K)ˣ →* ClassGroup R :=
  (QuotientGroup.mk' (toPrincipalIdeal R (FractionRing R)).range).comp
    (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)))

lemma ClassGroup.mk_def (I : (FractionalIdeal R⁰ K)ˣ) :
  ClassGroup.mk I =
    (QuotientGroup.mk' (toPrincipalIdeal R (FractionRing R)).range)
      (Units.map (FractionalIdeal.canonicalEquiv R⁰ K (FractionRing R)) I) := rfl

-- Can't be `@[simp]` because it can't figure out the quotient relation.
theorem ClassGroup.Quot_mk_eq_mk (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    Quot.mk _ I = ClassGroup.mk I := by
  rw [ClassGroup.mk_def, canonicalEquiv_self, RingEquiv.coe_monoidHom_refl, Units.map_id,
    MonoidHom.id_apply, QuotientGroup.mk'_apply]
  rfl

theorem ClassGroup.mk_eq_mk {I J : (FractionalIdeal R⁰ <| FractionRing R)ˣ} :
    ClassGroup.mk I = ClassGroup.mk J ↔
      ∃ x : (FractionRing R)ˣ, I * toPrincipalIdeal R (FractionRing R) x = J := by
  rw [mk_def, mk_def, QuotientGroup.mk'_eq_mk']
  simp [RingEquiv.coe_monoidHom_refl, MonoidHom.mem_range, -toPrincipalIdeal_eq_iff]

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
    exact ⟨_, _, sec_fst_ne_zero x.ne_zero,
      sec_snd_ne_zero (R := R) le_rfl (x : FractionRing R), hJ⟩
  · rintro ⟨x, y, hx, hy, h⟩
    have : IsUnit (mk' (FractionRing R) x ⟨y, mem_nonZeroDivisors_of_ne_zero hy⟩) := by
      simpa only [isUnit_iff_ne_zero, ne_eq, mk'_eq_zero_iff_eq_zero] using hx
    refine ⟨this.unit, ?_⟩
    rw [mul_comm, ← Units.eq_iff, Units.val_mul, coe_toPrincipalIdeal]
    convert
      (mk'_mul_coeIdeal_eq_coeIdeal (FractionRing R) <| mem_nonZeroDivisors_of_ne_zero hy).2 h

theorem ClassGroup.mk_eq_one_of_coe_ideal {I : (FractionalIdeal R⁰ <| FractionRing R)ˣ}
    {I' : Ideal R} (hI : (I : FractionalIdeal R⁰ <| FractionRing R) = I') :
    ClassGroup.mk I = 1 ↔ ∃ x : R, x ≠ 0 ∧ I' = Ideal.span {x} := by
  rw [← map_one (ClassGroup.mk (R := R) (K := FractionRing R)),
    ClassGroup.mk_eq_mk_of_coe_ideal hI]
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

@[simp]
theorem ClassGroup.equiv_mk (K' : Type*) [Field K'] [Algebra R K'] [IsFractionRing R K']
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.equiv K' (ClassGroup.mk I) =
      QuotientGroup.mk' _ (Units.mapEquiv (↑(FractionalIdeal.canonicalEquiv R⁰ K K')) I) := by
  -- `simp` can't apply `ClassGroup.mk_def` and `rw` can't unfold `ClassGroup`.
  rw [ClassGroup.equiv, ClassGroup.mk_def]
  simp only [ClassGroup, QuotientGroup.congr_mk']
  congr
  rw [← Units.eq_iff, Units.coe_mapEquiv, Units.coe_mapEquiv, Units.coe_map]
  exact FractionalIdeal.canonicalEquiv_canonicalEquiv _ _ _ _ _

@[simp]
theorem ClassGroup.mk_canonicalEquiv (K' : Type*) [Field K'] [Algebra R K'] [IsFractionRing R K']
    (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mk (Units.map (↑(canonicalEquiv R⁰ K K')) I : (FractionalIdeal R⁰ K')ˣ) =
      ClassGroup.mk I := by
  rw [ClassGroup.mk_def, ClassGroup.mk_def, ← MonoidHom.comp_apply (Units.map _),
      ← Units.map_comp, ← RingEquiv.coe_monoidHom_trans,
      FractionalIdeal.canonicalEquiv_trans_canonicalEquiv]

/-- Send a nonzero integral ideal to an invertible fractional ideal. -/
noncomputable def FractionalIdeal.mk0 [IsDedekindDomain R] :
    (Ideal R)⁰ →* (FractionalIdeal R⁰ K)ˣ where
  toFun I := Units.mk0 I (coeIdeal_ne_zero.mpr <| mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  map_one' := by simp
  map_mul' x y := by simp

@[simp]
theorem FractionalIdeal.coe_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    (FractionalIdeal.mk0 K I : FractionalIdeal R⁰ K) = I := rfl

theorem FractionalIdeal.canonicalEquiv_mk0 [IsDedekindDomain R] (K' : Type*) [Field K']
    [Algebra R K'] [IsFractionRing R K'] (I : (Ideal R)⁰) :
    FractionalIdeal.canonicalEquiv R⁰ K K' (FractionalIdeal.mk0 K I) =
    FractionalIdeal.mk0 K' I := by
  simp only [FractionalIdeal.coe_mk0, FractionalIdeal.canonicalEquiv_coeIdeal]

@[simp]
theorem FractionalIdeal.map_canonicalEquiv_mk0 [IsDedekindDomain R] (K' : Type*) [Field K']
    [Algebra R K'] [IsFractionRing R K'] (I : (Ideal R)⁰) :
    Units.map (↑(FractionalIdeal.canonicalEquiv R⁰ K K')) (FractionalIdeal.mk0 K I) =
      FractionalIdeal.mk0 K' I :=
  Units.ext (FractionalIdeal.canonicalEquiv_mk0 K K' I)

/-- Send a nonzero ideal to the corresponding class in the class group. -/
noncomputable def ClassGroup.mk0 [IsDedekindDomain R] : (Ideal R)⁰ →* ClassGroup R :=
  ClassGroup.mk.comp (FractionalIdeal.mk0 (FractionRing R))

@[simp]
theorem ClassGroup.mk_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    ClassGroup.mk (FractionalIdeal.mk0 K I) = ClassGroup.mk0 I := by
  rw [ClassGroup.mk0, MonoidHom.comp_apply, ← ClassGroup.mk_canonicalEquiv K (FractionRing R),
    FractionalIdeal.map_canonicalEquiv_mk0]

@[simp]
theorem ClassGroup.equiv_mk0 [IsDedekindDomain R] (I : (Ideal R)⁰) :
    ClassGroup.equiv K (ClassGroup.mk0 I) =
      QuotientGroup.mk' (toPrincipalIdeal R K).range (FractionalIdeal.mk0 K I) := by
  rw [ClassGroup.mk0, MonoidHom.comp_apply, ClassGroup.equiv_mk]
  congr 1
  simp [← Units.eq_iff]

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
      rw [hx, IsFractionRing.mk'_eq_div, map_zero, zero_div]
    · exact (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal _ hy).mp h
  · rintro ⟨x, y, hx, hy, h⟩
    have hy' : y ∈ R⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hy
    refine ⟨IsLocalization.mk' _ x ⟨y, hy'⟩, ?_, ?_⟩
    · contrapose! hx
      rwa [mk'_eq_iff_eq_mul, zero_mul, ← (algebraMap R (FractionRing R)).map_zero,
        (IsFractionRing.injective R (FractionRing R)).eq_iff] at hx
    · exact (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal _ hy').mpr h

/-- Maps a nonzero fractional ideal to an integral representative in the class group. -/
noncomputable def ClassGroup.integralRep (I : FractionalIdeal R⁰ (FractionRing R)) :
    Ideal R := I.num

theorem ClassGroup.integralRep_mem_nonZeroDivisors
    {I : FractionalIdeal R⁰ (FractionRing R)} (hI : I ≠ 0) :
    I.num ∈ (Ideal R)⁰ := by
  rwa [mem_nonZeroDivisors_iff_ne_zero, ne_eq, FractionalIdeal.num_eq_zero_iff]

theorem ClassGroup.mk0_integralRep [IsDedekindDomain R]
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    ClassGroup.mk0 ⟨ClassGroup.integralRep I, ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩
      = ClassGroup.mk I := by
  rw [← ClassGroup.mk_mk0 (FractionRing R), eq_comm, ClassGroup.mk_eq_mk]
  have fd_ne_zero : (algebraMap R (FractionRing R)) I.1.den ≠ 0 := by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (SetLike.coe_mem _)
  refine ⟨Units.mk0 (algebraMap R _ I.1.den) fd_ne_zero, ?_⟩
  apply Units.ext
  rw [mul_comm, val_mul, coe_toPrincipalIdeal, val_mk0]
  exact FractionalIdeal.den_mul_self_eq_num' R⁰ (FractionRing R) I

theorem ClassGroup.mk0_surjective [IsDedekindDomain R] :
    Function.Surjective (ClassGroup.mk0 : (Ideal R)⁰ → ClassGroup R) := by
  rintro ⟨I⟩
  refine ⟨⟨ClassGroup.integralRep I.1, ClassGroup.integralRep_mem_nonZeroDivisors I.ne_zero⟩, ?_⟩
  rw [ClassGroup.mk0_integralRep, ClassGroup.Quot_mk_eq_mk]

theorem ClassGroup.mk_eq_one_iff {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk I = 1 ↔ (I : Submodule R K).IsPrincipal := by
  rw [← (ClassGroup.equiv K).injective.eq_iff]
  simp only [equiv_mk, canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl, QuotientGroup.mk'_apply,
    map_one, QuotientGroup.eq_one_iff, MonoidHom.mem_range, Units.ext_iff,
    coe_toPrincipalIdeal, coe_mapEquiv, MulEquiv.refl_apply]
  refine ⟨fun ⟨x, hx⟩ => ⟨⟨x, by rw [← hx, coe_spanSingleton]⟩⟩, ?_⟩
  intro hI
  obtain ⟨x, hx⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hI
  have hx' : (I : FractionalIdeal R⁰ K) = spanSingleton R⁰ x := by
    apply Subtype.coe_injective
    simp only [val_eq_coe, hx, coe_spanSingleton]
  refine ⟨Units.mk0 x ?_, ?_⟩
  · intro x_eq; apply Units.ne_zero I; simp [hx', x_eq]
  · simp [hx']

theorem ClassGroup.mk0_eq_one_iff [IsDedekindDomain R] {I : Ideal R} (hI : I ∈ (Ideal R)⁰) :
    ClassGroup.mk0 ⟨I, hI⟩ = 1 ↔ I.IsPrincipal :=
  ClassGroup.mk_eq_one_iff.trans (coeSubmodule_isPrincipal R _)

theorem ClassGroup.mk0_eq_mk0_inv_iff [IsDedekindDomain R] {I J : (Ideal R)⁰} :
    ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ↔
      ∃ x ≠ (0 : R), I * J = Ideal.span {x} := by
  rw [eq_inv_iff_mul_eq_one, ← map_mul, ClassGroup.mk0_eq_one_iff,
    Submodule.isPrincipal_iff, Submonoid.coe_mul]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨a, ?_, ha⟩, fun ⟨a, _, ha⟩ ↦ ⟨a, ha⟩⟩
  by_contra!
  rw [this, Submodule.span_zero_singleton] at ha
  exact nonZeroDivisors.coe_ne_zero _ <| J.prop _ ha

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
