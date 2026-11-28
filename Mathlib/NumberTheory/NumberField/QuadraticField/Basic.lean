/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
public import Mathlib.FieldTheory.Galois.Quadratic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.CharP.Invertible
import Mathlib.RingTheory.QuadraticAlgebra

/-!
# Quadratic fields

A quadratic field is a number field of degree `2` over `ℚ`, that is, a field of characteristic
zero which is a quadratic extension of `ℚ` in the sense of `Algebra.IsQuadraticExtension`.

## Main results

* `NumberField.QuadraticField.isFundamentalDiscr_discr`: the discriminant of a quadratic field
  is a fundamental discriminant;
* `NumberField.QuadraticField.nonempty_algEquiv_quadraticAlgebra_int`: the ring of integers of a
  quadratic field is the quadratic algebra over `ℤ` of discriminant `discr K`;
* `NumberField.QuadraticField.nonempty_algEquiv_quadraticAlgebra_discr`: every quadratic field
  is `ℚ(√(discr K))`;
* `NumberField.QuadraticField.nonempty_algEquiv_iff_discr_eq`: the discriminant is a complete
  invariant of quadratic fields;
* `NumberField.QuadraticField.discr_quadraticAlgebra`: every fundamental discriminant other
  than `1` is the discriminant of a quadratic field;
* `NumberField.QuadraticField.isTotallyReal_iff_discr_pos` and
  `NumberField.QuadraticField.isTotallyComplex_iff_discr_neg`: a quadratic field is totally real,
  resp. totally complex, iff its discriminant is positive, resp. negative;
* `NumberField.QuadraticField.isCyclotomicExtension_four_of_discr` and
  `NumberField.QuadraticField.isCyclotomicExtension_six_of_discr`: the quadratic fields of
  discriminant `-4` and `-3` are the `4`-th and `6`-th cyclotomic fields.

## Implementation notes

`QuadraticAlgebra ℚ (d : ℚ) 0` is a field, hence a number field, exactly when `d` is not a
rational square. The results on `ℚ(√d)` therefore take a `[Fact (¬ IsSquare (d : ℚ))]` assumption,
which is what tells Mathlib that their discriminant is defined. For `d` squarefree and
different from `1`, `not_isSquare_intCast` below proves `¬ IsSquare (d : ℚ)`.
-/

public section

open NumberField

open scoped QuadraticAlgebra

instance NumberField.of_isQuadraticExtension (K : Type*) [Field K] [CharZero K]
    [Algebra.IsQuadraticExtension ℚ K] : NumberField K where

namespace NumberField.QuadraticField

variable (K : Type*) [Field K] [CharZero K] [Algebra.IsQuadraticExtension ℚ K]

instance : Algebra.IsQuadraticExtension ℤ (𝓞 K) where
  finrank_eq_two' := by rw [RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two]

variable {K}

/-- If the ring of integers of `K` is `QuadraticAlgebra ℤ a b`, the discriminant of `K` is the
discriminant of that quadratic algebra. -/
theorem discr_eq_quadraticAlgebra_discr {a b : ℤ}
    (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    discr K = QuadraticAlgebra.discr a b := by
  rw [← discr_eq_discr K ((QuadraticAlgebra.basis a b).map f.toIntAlgEquiv.symm),
    Module.Basis.coe_map, RingEquiv.symm_toIntAlgEquiv, AlgEquiv.coe_toLinearEquiv,
    ← Algebra.discr_eq_discr_of_algEquiv, ← Algebra.discr_quadraticAlgebra]

variable (K)

/-- The discriminant of a quadratic field is a fundamental discriminant. -/
theorem isFundamentalDiscr_discr : Int.IsFundamentalDiscr (discr K) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  rw [discr_eq_quadraticAlgebra_discr f.toRingEquiv]
  exact QuadraticAlgebra.Int.isIntegrallyClosed_iff.mp <| IsIntegrallyClosed.of_equiv f.toRingEquiv

/-- The ring of integers of a quadratic field `K` is the quadratic algebra of discriminant
`discr K`, see `QuadraticAlgebra.algEquivEdivEmod`. -/
theorem nonempty_algEquiv_quadraticAlgebra_int :
    Nonempty (𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (discr K / 4) (discr K % 4)) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  rw [discr_eq_quadraticAlgebra_discr f.toRingEquiv]
  exact ⟨f.trans (QuadraticAlgebra.algEquivEdivEmod a b)⟩

/-- Every quadratic field is `ℚ(√(discr K))`. -/
theorem nonempty_algEquiv_quadraticAlgebra_discr :
    Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (discr K : ℚ) 0) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  rw [discr_eq_quadraticAlgebra_discr f.toRingEquiv, ← QuadraticAlgebra.discr_intCast]
  exact ⟨(IsFractionRing.ringEquivOfRingEquiv f.toRingEquiv).toRatAlgEquiv.trans
    (QuadraticAlgebra.algEquivDiscrZero (a : ℚ) b)⟩

/-- The square root of `discr K` lies in `K`. -/
theorem exists_sq_eq_discr : ∃ x : K, x ^ 2 = discr K := by
  obtain ⟨e⟩ := nonempty_algEquiv_quadraticAlgebra_discr K
  exact ⟨e.symm ω, by simp [← map_pow, QuadraticAlgebra.omega_pow_two_eq_add]⟩

/-- The discriminant of a quadratic field is not a square. -/
theorem not_isSquare_discr : ¬ IsSquare (discr K) := by
  obtain ⟨a, b, ⟨f⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℤ) (A := 𝓞 K)
  rw [discr_eq_quadraticAlgebra_discr f.toRingEquiv]
  exact QuadraticAlgebra.Int.isDomain_iff.mp (f.symm.toMulEquiv.isDomain _)

variable (F : Type*) [Field F] [CharZero F] [Algebra.IsQuadraticExtension ℚ F]

/-- The discriminant is a complete invariant of quadratic fields. -/
theorem nonempty_algEquiv_iff_discr_eq :
    Nonempty (K ≃ₐ[ℚ] F) ↔ discr K = discr F := by
  refine ⟨fun ⟨e⟩ ↦ discr_eq_discr_of_algEquiv K e, fun h ↦ ?_⟩
  obtain ⟨e₁⟩ := h ▸ nonempty_algEquiv_quadraticAlgebra_int K
  obtain ⟨e₂⟩ := nonempty_algEquiv_quadraticAlgebra_int F
  exact ⟨(IsFractionRing.ringEquivOfRingEquiv (L := F)
    (e₁.trans e₂.symm).toRingEquiv).toRatAlgEquiv⟩

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
      ⟨by rw [QuadraticAlgebra.discr_intCast, Rat.isSquare_intCast_iff]
          exact h.eq_one_of_isSquare.mt h1⟩
    discr (QuadraticAlgebra ℚ a b) = QuadraticAlgebra.discr a b := by
  have : Fact (¬ IsSquare (QuadraticAlgebra.discr (a : ℚ) (b : ℚ))) :=
    ⟨by rw [QuadraticAlgebra.discr_intCast, Rat.isSquare_intCast_iff]
        exact h.eq_one_of_isSquare.mt h1⟩
  exact discr_eq_quadraticAlgebra_discr
    (QuadraticAlgebra.Int.algEquivIntegralClosure h).toRingEquiv.symm

/-- Every fundamental discriminant other than `1` is the discriminant of a quadratic field.
See the implementation notes in the module docstring for the `Fact` assumption. -/
theorem discr_quadraticAlgebra {D : ℤ} [Fact (¬ IsSquare (D : ℚ))]
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) :
    discr (QuadraticAlgebra ℚ (D : ℚ) 0) = D := by
  have hd : QuadraticAlgebra.discr (D / 4) (D % 4) = D :=
    QuadraticAlgebra.discr_ediv_emod hD.emod_four_eq_zero_or_one
  have : Fact (¬ IsSquare (QuadraticAlgebra.discr ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ))) :=
    ⟨by rw [QuadraticAlgebra.discr_intCast, hd]; exact Fact.out⟩
  let e : QuadraticAlgebra ℚ (D : ℚ) 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ (D / 4 : ℤ) (D % 4 : ℤ) := by
    refine (QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two.mpr
      ⟨(isUnit_of_invertible 2).unit, ?_⟩).some
    grind [IsUnit.unit_spec, QuadraticAlgebra.discr_intCast, QuadraticAlgebra.discr_def]
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

section cyclotomic

open Algebra QuadraticAlgebra

/-- In `ℚ(√-4)`, the element `√-4 / 2` is a primitive `4`-th root of unity. -/
theorem isPrimitiveRoot_four_quadraticAlgebra :
    IsPrimitiveRoot ((2⁻¹ : ℚ) • ω : QuadraticAlgebra ℚ (-4) 0) 4 := by
  refine IsPrimitiveRoot.iff_orderOf.mpr ?_
  refine (orderOf_eq_iff (by lia)).mpr ⟨by decide +kernel, fun m _ _ ↦ ?_⟩
  interval_cases m <;> decide +kernel

/-- In `ℚ(√-3)`, the element `(1 + √-3) / 2` is a primitive `6`-th root of unity. -/
theorem isPrimitiveRoot_six_quadraticAlgebra :
    IsPrimitiveRoot ((2⁻¹ : ℚ) • 1 + (2⁻¹ : ℚ) • ω : QuadraticAlgebra ℚ (-3) 0) 6 := by
  refine IsPrimitiveRoot.iff_orderOf.mpr ?_
  refine (orderOf_eq_iff (by lia)).mpr ⟨by decide +kernel, fun m _ _ ↦ ?_⟩
  interval_cases m <;> decide +kernel

instance : IsCyclotomicExtension {4} ℚ (QuadraticAlgebra ℚ (-4) 0) := by
  let ζ := ((2⁻¹ : ℚ) • ω : QuadraticAlgebra ℚ (-4) 0)
  have := IsPrimitiveRoot.adjoin_isCyclotomicExtension ℚ isPrimitiveRoot_four_quadraticAlgebra
  have : ℚ[ζ] = ⊤ := by
    rw [_root_.eq_top_iff, ← adjoin_omega_eq_top, show ω = 2 • ζ by decide +kernel]
    exact adjoin_singleton_le <| Subalgebra.smul_mem _ (self_mem_adjoin_singleton ℚ ζ) _
  exact .equiv _ _ _ ((Subalgebra.equivOfEq _ _ this).trans Subalgebra.topEquiv)

instance : IsCyclotomicExtension {6} ℚ (QuadraticAlgebra ℚ (-3) 0) := by
  let ζ := ((2⁻¹ : ℚ) • 1 + (2⁻¹ : ℚ) • ω : QuadraticAlgebra ℚ (-3) 0)
  have := IsPrimitiveRoot.adjoin_isCyclotomicExtension ℚ isPrimitiveRoot_six_quadraticAlgebra
  have : ℚ[ζ] = ⊤ := by
    rw [_root_.eq_top_iff, ← adjoin_omega_eq_top, show ω = 2 • ζ - 1 by decide +kernel]
    refine adjoin_singleton_le <| Subalgebra.sub_mem ℚ[ζ] ?_ (one_mem _)
    exact Subalgebra.smul_mem _ (self_mem_adjoin_singleton ℚ ζ) _
  exact .equiv _ _ _ ((Subalgebra.equivOfEq _ _ this).trans Subalgebra.topEquiv)

theorem isCyclotomicExtension_four_of_discr (h : discr K = -4) :
    IsCyclotomicExtension {4} ℚ K := by
  have h_equiv := nonempty_algEquiv_quadraticAlgebra_discr K
  rw [h, Int.cast_neg, Int.cast_ofNat] at h_equiv
  exact IsCyclotomicExtension.equiv {4} ℚ _ h_equiv.some.symm

theorem isCyclotomicExtension_six_of_discr (h : discr K = -3) :
    IsCyclotomicExtension {6} ℚ K := by
  have h_equiv := nonempty_algEquiv_quadraticAlgebra_discr K
  rw [h, Int.cast_neg, Int.cast_ofNat] at h_equiv
  exact IsCyclotomicExtension.equiv {6} ℚ _ h_equiv.some.symm

end cyclotomic

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
  exact ⟨fun h ↦ h z hz, fun h _ _ ↦ h⟩

/-- A quadratic field is totally complex iff its discriminant is negative. -/
theorem isTotallyComplex_iff_discr_neg : IsTotallyComplex K ↔ discr K < 0 := by
  convert_to ¬ IsTotallyReal K ↔ _
  · rw [← nrRealPlaces_eq_zero_iff, ← nrComplexPlaces_eq_zero_iff]
    grind [Algebra.IsQuadraticExtension.finrank_eq_two ℚ K ▸
      InfinitePlace.card_add_two_mul_card_eq_rank K]
  rw [isTotallyReal_iff_discr_pos, not_lt, Int.lt_iff_le_and_ne, and_iff_left (discr_ne_zero K)]

/-- The discriminant of a totally real quadratic field is positive. -/
theorem discr_pos [IsTotallyReal K] : 0 < discr K :=
  (isTotallyReal_iff_discr_pos K).mp ‹_›

/-- The discriminant of a totally complex quadratic field is negative. -/
theorem discr_neg [IsTotallyComplex K] : discr K < 0 :=
  (isTotallyComplex_iff_discr_neg K).mp ‹_›

/-- A real quadratic field has two real places. -/
theorem nrRealPlaces_eq_two [IsTotallyReal K] : InfinitePlace.nrRealPlaces K = 2 := by
  rw [← IsTotallyReal.finrank, Algebra.IsQuadraticExtension.finrank_eq_two]

/-- A real quadratic field has two infinite places. -/
theorem card_infinitePlace_eq_two [IsTotallyReal K] : Fintype.card (InfinitePlace K) = 2 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
    nrRealPlaces_eq_two]

/-- A complex quadratic field has one complex place. -/
theorem nrComplexPlaces_eq_one [IsTotallyComplex K] : InfinitePlace.nrComplexPlaces K = 1 := by
  rw [← mul_right_inj' two_ne_zero, ← IsTotallyComplex.finrank,
    Algebra.IsQuadraticExtension.finrank_eq_two]

/-- A complex quadratic field has one infinite place. -/
theorem card_infinitePlace_eq_one [IsTotallyComplex K] : Fintype.card (InfinitePlace K) = 1 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
    zero_add, nrComplexPlaces_eq_one]

open Algebra.IsQuadraticExtension InfinitePlace in
variable {K} in
/-- In a real quadratic field, the conjugation exchanges the two infinite places. -/
theorem conj_smul_infinitePlace_ne_self [IsTotallyReal K] (w : InfinitePlace K) :
    conj ℚ K • w ≠ w := by
  rw [ne_eq, ← mk_embedding w, InfinitePlace.smul_mk, mk_eq_iff, ComplexEmbedding.isReal_iff.mp
    (IsTotallyReal.complexEmbedding_isReal _), or_self, conj_symm,
    ← (RingHom.equivRatAlgHom K ℂ).injective.eq_iff]
  exact comp_conj_ne w.embedding.toRatAlgHom

end embeddings

end NumberField.QuadraticField
