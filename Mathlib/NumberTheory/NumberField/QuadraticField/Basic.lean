/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.QuadraticAlgebra

/-!
# Quadratic fields

A quadratic field is a number field of degree `2` over `ℚ`, that is, a field of characteristic
zero which is a quadratic extension of `ℚ` in the sense of `Algebra.IsQuadraticExtension`.

## Main results

* `NumberField.QuadraticField.isFundamentalDiscr_discr`: the discriminant of a quadratic field
  is a fundamental discriminant;
* `NumberField.QuadraticField.nonempty_algEquiv_quadraticAlgebra_discr`: every quadratic field
  is `ℚ(√(discr K))`;
* `NumberField.QuadraticField.nonempty_algEquiv_iff_discr_eq`: the discriminant is a complete
  invariant of quadratic fields;
* `NumberField.QuadraticField.discr_quadraticAlgebra`: every fundamental discriminant other
  than `1` is the discriminant of a quadratic field;
* `NumberField.QuadraticField.isTotallyReal_iff_discr_pos` and
  `NumberField.QuadraticField.isTotallyComplex_iff_discr_neg`: a quadratic field is totally real,
  resp. totally complex, iff its discriminant is positive, resp. negative.

## Implementation notes

`QuadraticAlgebra ℚ (d : ℚ) 0` is a field, hence a number field, exactly when `d` is not a
rational square. The results on `ℚ(√d)` therefore take a `[Fact (¬ IsSquare (d : ℚ))]` assumption,
which is what tells Mathlib that their discriminant is defined. For `d` squarefree and
different from `1`, `not_isSquare_intCast` below proves `¬ IsSquare (d : ℚ)`.
-/

public section

open NumberField Int

open scoped QuadraticAlgebra

instance NumberField.of_isQuadraticExtension (K : Type*) [Field K] [CharZero K]
    [Algebra.IsQuadraticExtension ℚ K] : NumberField K where

namespace NumberField.QuadraticField

variable (K : Type*) [Field K] [CharZero K] [h : Algebra.IsQuadraticExtension ℚ K]

instance : Algebra.IsQuadraticExtension ℤ (𝓞 K) where
  finrank_eq_two' := by rw [RingOfIntegers.rank, h.finrank_eq_two]

variable {K}

/-- A ring isomorphism between the ring of integers of `K` and `QuadraticAlgebra ℤ a b` extends
to their fraction fields. -/
noncomputable def algEquivOfRingEquiv {a b : ℤ}
    (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    K ≃ₐ[ℚ] QuadraticAlgebra ℚ a b :=
  (IsFractionRing.ringEquivOfRingEquiv f).equivRatAlgEquiv _ _

section discr

/-- If the ring of integers of `K` is `QuadraticAlgebra ℤ a b`, the discriminant of `K` is the
discriminant of that quadratic algebra. -/
theorem discr_eq_quadraticAlgebra_discr {a b : ℤ}
    (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    discr K = QuadraticAlgebra.discr a b := by
  rw [← discr_eq_discr K ((QuadraticAlgebra.basis a b).map f.toIntAlgEquiv.symm),
    Module.Basis.coe_map, RingEquiv.symm_toIntAlgEquiv, AlgEquiv.coe_toLinearEquiv,
    ← Algebra.discr_eq_discr_of_algEquiv, ← Algebra.discr_quadraticAlgebra]
  rfl

variable (K)

/-- The discriminant of a quadratic field is a fundamental discriminant. -/
theorem isFundamentalDiscr_discr : Int.IsFundamentalDiscr (discr K) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  rw [discr_eq_quadraticAlgebra_discr f.toRingEquiv]
  exact QuadraticAlgebra.Int.isIntegrallyClosed_iff.mp <| IsIntegrallyClosed.of_equiv f.toRingEquiv

/-- The ring of integers of a quadratic field `K` is the quadratic algebra of discriminant
`discr K`, see `Int.IsFundamentalDiscr.discr_ediv_four_emod_four`. -/
theorem nonempty_algEquiv_ringOfIntegers :
    Nonempty (𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (discr K / 4) (discr K % 4)) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  refine ⟨f.trans (Nonempty.some ?_)⟩
  rw [QuadraticAlgebra.nonempty_algEquiv_int_iff,
    (isFundamentalDiscr_discr K).discr_ediv_four_emod_four,
    discr_eq_quadraticAlgebra_discr f.toRingEquiv]

/-- Every quadratic field is `ℚ(√(discr K))`. -/
theorem nonempty_algEquiv_quadraticAlgebra_discr :
    Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (discr K : ℚ) 0) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  exact ⟨(algEquivOfRingEquiv f.toRingEquiv).trans <|
    (QuadraticAlgebra.algEquivDiscrZero (a : ℚ) (b : ℚ)).trans <|
      QuadraticAlgebra.equivOfEq (by rw [QuadraticAlgebra.Int.discr_intCast,
        discr_eq_quadraticAlgebra_discr f.toRingEquiv]) rfl⟩

/-- The discriminant of a quadratic field is not `1`. A more general version is the
Hermite-Minkowski theorem, see `NumberField.abs_discr_gt_two`. -/
theorem discr_ne_one : discr K ≠ 1 := by
  by_contra! h
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  exact QuadraticAlgebra.Int.isDomain_iff.mp (f.symm.toMulEquiv.isDomain _)
    (discr_eq_quadraticAlgebra_discr f.toRingEquiv ▸ h ▸ IsSquare.one)

/-- `√(discr K)` lies in `K`. -/
theorem exists_sq_eq_discr : ∃ x : K, x ^ 2 = discr K := by
  let e := (nonempty_algEquiv_quadraticAlgebra_discr K).some
  exact ⟨e.symm ω, by simp [← map_pow, QuadraticAlgebra.omega_pow_two_eq_add]⟩

/-- The discriminant of a quadratic field is not a square. -/
theorem not_isSquare_discr : ¬ IsSquare (discr K) :=
  (Int.IsFundamentalDiscr.eq_one_of_isSquare (isFundamentalDiscr_discr K)).mt <| discr_ne_one K

/-- **Stickelberger's theorem**, for quadratic fields: the discriminant is congruent to
`0` or `1` modulo `4`. -/
theorem discr_emod_four : discr K % 4 = 0 ∨ discr K % 4 = 1 :=
  (isFundamentalDiscr_discr K).1

variable (F : Type*) [Field F] [CharZero F] [Algebra.IsQuadraticExtension ℚ F]

/-- The discriminant is a complete invariant of quadratic fields. -/
theorem nonempty_algEquiv_iff_discr_eq :
    Nonempty (K ≃ₐ[ℚ] F) ↔ discr K = discr F := by
  refine ⟨fun ⟨e⟩ ↦ discr_eq_discr_of_algEquiv K e, fun h ↦ ?_⟩
  obtain ⟨e₁⟩ := nonempty_algEquiv_ringOfIntegers K
  obtain ⟨e₂⟩ := nonempty_algEquiv_ringOfIntegers F
  exact ⟨(IsFractionRing.ringEquivOfRingEquiv
    ((h ▸ e₁).trans e₂.symm).toRingEquiv).equivRatAlgEquiv _ _⟩

/-- A squarefree integer `d` other than `1` is not a square in `ℚ`, the hypothesis that makes
`ℚ(√d)` automatically a number field; see the implementation notes for details. -/
theorem not_isSquare_intCast {d : ℤ} (hd : Squarefree d) (hd₁ : d ≠ 1) :
    ¬ IsSquare (d : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨r, rfl⟩
  obtain h | h := Int.isUnit_iff.mp (Squarefree.isUnit_of_pow le_rfl ((pow_two r) ▸ hd)) <;>
  simp [h] at hd₁ ⊢

/-- When the parameters are already those of the maximal order, the discriminant of
`QuadraticAlgebra ℚ a b` is the discriminant of the quadratic algebra. -/
theorem discr_quadraticAlgebra_eq {a b : ℤ}
    (h : Int.IsFundamentalDiscr (QuadraticAlgebra.discr a b))
    (h1 : QuadraticAlgebra.discr a b ≠ 1) :
    -- This is needed to get a number field
    haveI : Fact (¬ IsSquare (QuadraticAlgebra.discr (a : ℚ) (b : ℚ))) :=
      ⟨by rw [QuadraticAlgebra.Int.discr_intCast, Rat.isSquare_intCast_iff]
          exact h.eq_one_of_isSquare.mt h1⟩
    discr (QuadraticAlgebra ℚ a b) = QuadraticAlgebra.discr a b := by
  have : Fact (¬ IsSquare (QuadraticAlgebra.discr (a : ℚ) (b : ℚ))) :=
    ⟨by rw [QuadraticAlgebra.Int.discr_intCast, Rat.isSquare_intCast_iff]
        exact h.eq_one_of_isSquare.mt h1⟩
  exact discr_eq_quadraticAlgebra_discr
    (QuadraticAlgebra.Int.algEquivIntegralClosure h).toRingEquiv.symm

/-- Every fundamental discriminant other than `1` is the discriminant of a quadratic field.
See the implementation notes in the module docstring for the `Fact` assumption. -/
theorem discr_quadraticAlgebra {D : ℤ} [Fact (¬ IsSquare (D : ℚ))]
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) :
    discr (QuadraticAlgebra ℚ (D : ℚ) 0) = D := by
  have hd : QuadraticAlgebra.discr (D / 4) (D % 4) = D := hD.discr_ediv_four_emod_four
  have : Fact (¬ IsSquare (QuadraticAlgebra.discr ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ))) :=
    ⟨by rw [QuadraticAlgebra.Int.discr_intCast, hd]; exact Fact.out⟩
  let e : QuadraticAlgebra ℚ (D : ℚ) 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ (D / 4 : ℤ) (D % 4 : ℤ) := by
    refine (QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two.mpr
      ⟨(isUnit_of_invertible 2).unit, ?_⟩).some
    grind [IsUnit.unit_spec, QuadraticAlgebra.Int.discr_intCast, QuadraticAlgebra.discr_def]
  rw [discr_eq_discr_of_algEquiv _ e, discr_quadraticAlgebra_eq (by rwa [hd]) (by rwa [hd]), hd]

/-- The discriminant of `ℚ(√d)` is `4 * d` when `d` is squarefree and `d ≡ 2, 3 [ZMOD 4]`.
See the implementation notes in the module docstring for the `Fact` assumption. -/
theorem discr_sqrtd {d : ℤ} [Fact (¬ IsSquare (d : ℚ))]
    (hd₁ : Squarefree d) (hd₂ : d % 4 = 2 ∨ d % 4 = 3) :
    discr (QuadraticAlgebra ℚ (d : ℚ) 0) = 4 * d := by
  have h₁ : QuadraticAlgebra.discr d 0 = 4 * d := by simp [QuadraticAlgebra.discr_def]
  have h₂ : (QuadraticAlgebra.discr d 0).IsFundamentalDiscr :=
    h₁ ▸ Int.isFundamentalDiscr_four_mul.mpr ⟨hd₁, hd₂⟩
  simpa [QuadraticAlgebra.discr_def] using discr_quadraticAlgebra_eq h₂ (by grind)

/-- The discriminant of `ℚ(√d)` is `d` itself when `d` is squarefree and `d ≡ 1 [ZMOD 4]`.
See the implementation notes in the module docstring for the `Fact` assumption. -/
theorem discr_half {d : ℤ} [Fact (¬ IsSquare (d : ℚ))]
    (hd : Squarefree d) (hd1 : d ≠ 1) (h : d % 4 = 1) :
    discr (QuadraticAlgebra ℚ (d : ℚ) 0) = d :=
  discr_quadraticAlgebra (Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨h, hd⟩)) hd1

end discr

section embeddings

/-- The complex embeddings of `ℚ(√d)` correspond to the two square roots of `d` in `ℂ`. -/
noncomputable def embeddingEquiv (d : ℚ) :
    (QuadraticAlgebra ℚ d 0 →+* ℂ) ≃ {z : ℂ // z ^ 2 = d} :=
  (RingHom.equivRatAlgHom _ _).trans <| QuadraticAlgebra.lift.symm.trans
    <| Equiv.subtypeEquivRight <| by simp [pow_two]

@[simp]
theorem embeddingEquiv_symm_apply (d : ℚ) (z : {z : ℂ // z ^ 2 = d}) (x y : ℚ) :
    (embeddingEquiv d).symm z (x • 1 + y • ω) = x + y * z := by
  simp [embeddingEquiv, Rat.smul_def]

@[simp]
theorem embeddingEquiv_symm_apply_omega (d : ℚ) (z : {z : ℂ // z ^ 2 = d}) :
    (embeddingEquiv d).symm z ω = z := by
  simp [embeddingEquiv]

/-- An embedding of `ℚ(√d)` is real exactly when `d` is nonnegative. -/
theorem isReal_embeddingEquiv_symm_iff (d : ℚ) [Fact (¬ IsSquare d)] (z : {z : ℂ // z ^ 2 = d}) :
    ComplexEmbedding.IsReal ((embeddingEquiv d).symm z) ↔ 0 ≤ d := by
  simp [ComplexEmbedding.isReal_iff, ← (RingHom.equivRatAlgHom _ _).injective.eq_iff,
    QuadraticAlgebra.algHom_ext_iff, Complex.conj_eq_iff_im, ← Complex.sq_nonneg_iff, z.prop,
    ← Complex.ofReal_ratCast]

variable (K)

/-- A quadratic field is totally real iff its discriminant is positive. -/
theorem isTotallyReal_iff_discr_pos : IsTotallyReal K ↔ 0 < discr K := by
  rw [Int.lt_iff_le_and_ne, and_iff_left (discr_ne_zero K).symm]
  have : Fact (¬ IsSquare (discr K : ℚ)) :=
    ⟨Rat.isSquare_intCast_iff.not.mpr <| not_isSquare_discr K⟩
  obtain ⟨e⟩ := nonempty_algEquiv_quadraticAlgebra_discr K
  rw [isTotallyReal_iff_ofRingEquiv e.toRingEquiv, isTotallyReal_iff,
    (InfinitePlace.mk_surjective _).forall]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (discr K : ℂ) two_pos
  simp +contextual only [InfinitePlace.isReal_mk_iff, (embeddingEquiv _).forall_congr_left,
    isReal_embeddingEquiv_symm_iff, Int.cast_nonneg_iff, Subtype.forall, Rat.cast_intCast]
  exact Set.Nonempty.forall_const ⟨z, hz⟩

/-- A quadratic field is totally complex iff its discriminant is negative. -/
theorem isTotallyComplex_iff_discr_neg : IsTotallyComplex K ↔ discr K < 0 := by
  convert_to ¬ IsTotallyReal K ↔ _
  · rw [← nrRealPlaces_eq_zero_iff, ← nrComplexPlaces_eq_zero_iff]
    grind [h.finrank_eq_two ▸ InfinitePlace.card_add_two_mul_card_eq_rank K]
  rw [isTotallyReal_iff_discr_pos, not_lt_eq, Int.lt_iff_le_and_ne, and_iff_left (discr_ne_zero K)]

end embeddings

end NumberField.QuadraticField
