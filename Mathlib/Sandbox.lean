/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Discriminants of quadratic fields

Statements of the next PR, with `sorry`ed proofs.
-/

@[expose] public section

theorem Squarefree.isUnit_of_pow {M : Type*} [Monoid M] {x : M} {n : ℕ} (hn : 2 ≤ n)
    (h : Squarefree (x ^ n)) : IsUnit x := by
  by_contra!
  grind [h.eq_zero_or_one_of_pow_of_not_isUnit this]

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R]

theorem omega_pow_two_eq_add {a b : R} :
    ω ^ 2 = a • (1 : QuadraticAlgebra R a b) + b • ω := by
  rw [sq, omega_mul_omega_eq_add]

/-- Equal parameters give the same quadratic algebra, as an isomorphism which is the identity
on `re` and `im`. -/
@[simps]
def equivOfEq {a b a' b' : R} (ha : a = a') (hb : b = b') :
    QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b' where
  toFun z := ⟨z.re, z.im⟩
  invFun z := ⟨z.re, z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := by ext <;> simp [ha, hb]
  map_add' _ _ := by ext <;> simp
  commutes' _ := by ext <;> simp

end QuadraticAlgebra

section PR42554

open Algebra Module QuadraticAlgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

theorem Algebra.discr_quadraticAlgebra (a b : R) :
    Algebra.discr R (basis a b) = QuadraticAlgebra.discr a b := by
  sorry

variable [StrongRankCondition R] [IsQuadraticExtension R A]
theorem IsQuadraticExtension.exists_algEquiv_quadraticAlgebra :
    ∃ (a b : R), Nonempty (A ≃ₐ[R] QuadraticAlgebra R a b) := by
  sorry

end PR42554

/-! ### For `Mathlib/RingTheory/Discriminant.lean` -/

open  QuadraticAlgebra NumberField

variable {D d : ℤ}

/-! ### Pure arithmetic, for `Mathlib/NumberTheory/FundamentalDiscriminant.lean` -/

namespace Int

theorem IsFundamentalDiscr.eq_one_of_isSquare {D : ℤ} (h : IsFundamentalDiscr D)
    (h' : IsSquare D) : D = 1 := by
  have h_main {r : ℤ} (hr : Squarefree (r * r)) : r * r = 1 := by
    grind [isUnit_iff.mp <| Squarefree.isUnit_of_pow le_rfl (pow_two r ▸ hr)]
  obtain ⟨r, rfl⟩ := h'
  obtain h | h := isFundamentalDiscr_iff_squarefree.mp h
  · exact h_main h.2
  · obtain ⟨s, rfl⟩ : Even r := by
      grind [prime_two.dvd_mul.mp <| dvd_trans (by norm_num : _) <| dvd_iff_emod_eq_zero.mpr h.1]
    rw [show (s + s) * (s + s) / 4 = s * s by grind] at h
    grind

theorem isIntegrallyClosed_iff {a b : ℤ} :
      IsIntegrallyClosed (QuadraticAlgebra ℤ a b) ↔ Int.IsFundamentalDiscr (discr a b) := by
  sorry

theorem isIntegralClosure_iff {a b : ℤ} :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ (QuadraticAlgebra ℚ a b) ↔
      Int.IsFundamentalDiscr (discr a b) := by
  sorry

-- theorem IsFundamentalDiscr.not_isSquare (h : IsFundamentalDiscr D) (h1 : D ≠ 1) :
--    ¬ IsSquare D := sorry

theorem IsFundamentalDiscr.discr_ediv_four_emod_four (h : IsFundamentalDiscr D) :
    discr (D / 4) (D % 4) = D := by
  have : (D % 4) ^ 2 = D % 4 := by grind [h.1]
  rw [discr_def, this, add_comm, mul_ediv_add_emod]

-- theorem not_isSquare_ratCast (h : ¬ IsSquare d) : ¬ IsSquare (d : ℚ) := sorry

end Int

/-! ### Auxiliary results on quadratic algebras -/

namespace QuadraticAlgebra

variable {a b : ℤ}

-- theorem algebra_discr_basis : Algebra.discr ℤ (basis a b) = discr a b := sorry

-- instance {a b : ℚ} : CharZero (QuadraticAlgebra ℚ a b) := by
--  infer_instance

/-- This is `instIsQuadraticExtensionRat` of #42554, stated here so that the statements below
elaborate. The `Fact` is what makes it fire: when `QuadraticAlgebra ℚ a b` is a field, its
`Algebra ℚ`-structure is inferred as `algebraRat`, not as `instAlgebra`, so the unconditional
instance of #42554 does not apply. -/
instance {a b : ℚ} [Fact (¬ IsSquare (discr a b))] :
    Algebra.IsQuadraticExtension ℚ (QuadraticAlgebra ℚ a b) := sorry

end QuadraticAlgebra

/-! ### Abstract quadratic fields -/

instance NumberField.of_isQuadraticExtension (K : Type*) [Field K] [CharZero K]
    [Algebra.IsQuadraticExtension ℚ K] : NumberField K where

variable (K : Type*) [Field K] [CharZero K] [h : Algebra.IsQuadraticExtension ℚ K]

instance : Algebra.IsQuadraticExtension ℤ (𝓞 K) where
  finrank_eq_two' := by rw [RingOfIntegers.rank, h.finrank_eq_two]

variable {K}

theorem toto1 {a b : ℤ} (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    discr K = discr a b := by
  rw [← discr_eq_discr K ((basis a b).map f.toIntAlgEquiv.symm), Module.Basis.coe_map,
    RingEquiv.symm_toIntAlgEquiv, AlgEquiv.coe_toLinearEquiv, ← Algebra.discr_eq_discr_of_algEquiv,
    Algebra.discr_quadraticAlgebra]

noncomputable def algEquivOfRingEquiv {a b : ℤ} (f : 𝓞 K ≃+* QuadraticAlgebra ℤ a b) :
    K ≃ₐ[ℚ] QuadraticAlgebra ℚ a b :=
  (IsFractionRing.ringEquivOfRingEquiv f).equivRatAlgEquiv _ _

variable (K)

theorem NumberField.isFundamentalDiscr_discr : Int.IsFundamentalDiscr (discr K) := by
  obtain ⟨a, b, ⟨f⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  rw [toto1 f.toRingEquiv]
  exact  Int.isIntegrallyClosed_iff.mp <| IsIntegrallyClosed.of_equiv f.toRingEquiv

theorem NumberField.nonempty_algEquiv_ringOfIntegers :
    Nonempty (𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (discr K / 4) (discr K % 4)) := by
  obtain ⟨a, b, ⟨f⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  refine ⟨f.trans (Nonempty.some ?_)⟩
  rw [nonempty_algEquiv_int_iff, (isFundamentalDiscr_discr K).discr_ediv_four_emod_four,
    toto1 f.toRingEquiv]

/-- Every quadratic field is `ℚ(√(discr K))`. -/
theorem NumberField.nonempty_algEquiv_quadraticAlgebra_discr :
    Nonempty (K ≃ₐ[ℚ] QuadraticAlgebra ℚ (discr K : ℚ) 0) := by
  obtain ⟨a, b, ⟨f⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  exact ⟨(algEquivOfRingEquiv f.toRingEquiv).trans <|
    (algEquivDiscrZero (a : ℚ) (b : ℚ)).trans <|
      QuadraticAlgebra.equivOfEq (by rw [Int.discr_intCast, toto1 f.toRingEquiv]) rfl⟩

theorem NumberField.discr_ne_one : discr K ≠ 1 := by
  by_contra! h
  obtain ⟨a, b, ⟨f⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  exact Int.isDomain_iff.mp (f.symm.toMulEquiv.isDomain _) (toto1 f.toRingEquiv ▸ h ▸ IsSquare.one)

/-- `√(discr K)` lies in `K`. -/
theorem NumberField.exists_sq_eq_discr : ∃ x : K, x ^ 2 = (discr K : K) := by
  let e := (nonempty_algEquiv_quadraticAlgebra_discr K).some
  exact ⟨e.symm ω, by simp [← map_pow, omega_pow_two_eq_add]⟩

/-- Stickelberger, for quadratic fields. -/
theorem NumberField.discr_emod_four : discr K % 4 = 0 ∨ discr K % 4 = 1 :=
  (isFundamentalDiscr_discr K).1

/-- The complex embeddings of the standard model are the two square roots of `D`. -/
noncomputable def embeddingEquiv (D : ℤ) :
    (QuadraticAlgebra ℚ (D : ℚ) 0 →+* ℂ) ≃ {z : ℂ // z ^ 2 = D} := sorry

open NumberField

example (D : ℤ) (z : {z : ℂ // z ^ 2 = D}) [Fact (¬ IsSquare (D : ℚ))] :
    ComplexEmbedding.IsReal ((embeddingEquiv D).symm z) ↔ D < 0 := by
  rw [ComplexEmbedding.isReal_iff]
  have : ((embeddingEquiv D).symm z).range = (Algebra.adjoin ℚ {z.1}).toSubring := by
    have := QuadraticAlgebra.range_lift z
    sorry



/-- An embedding of the standard model is real exactly when `D` is nonnegative. This is
`NumberField.ComplexEmbedding.IsReal` unfolded to `conjugate f = f`, which avoids requiring a
`Field` instance on the model — see the `Fact` problem in the plan. -/
theorem QuadraticAlgebra.isReal_embedding_iff (D : ℤ)
    (f : QuadraticAlgebra ℚ (D : ℚ) 0 →ₐ[ℚ] ℂ) :
    (starRingEnd ℂ).comp (f : QuadraticAlgebra ℚ (D : ℚ) 0 →+* ℂ) = f ↔ 0 ≤ D := sorry

theorem NumberField.isTotallyReal_iff_discr_pos : IsTotallyReal K ↔ 0 < discr K := sorry

theorem NumberField.isTotallyComplex_iff_discr_neg : IsTotallyComplex K ↔ discr K < 0 := sorry

variable (F : Type*) [Field F] [CharZero F] [Algebra.IsQuadraticExtension ℚ F]

/-- The discriminant is a complete invariant of quadratic fields. -/
theorem NumberField.nonempty_algEquiv_iff_discr_eq :
    Nonempty (K ≃ₐ[ℚ] F) ↔ discr K = discr F := by
  refine ⟨fun ⟨e⟩ ↦ discr_eq_discr_of_algEquiv K e, fun h ↦ ?_⟩
  obtain ⟨a₁, b₁, ⟨f₁⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 K)
  obtain ⟨a₂, b₂, ⟨f₂⟩⟩ := IsQuadraticExtension.exists_algEquiv_quadraticAlgebra ℤ (𝓞 F)
  rw [toto1 f₁.toRingEquiv, toto1 f₂.toRingEquiv] at h
  refine ⟨(algEquivOfRingEquiv f₁.toRingEquiv).trans <|
    AlgEquiv.trans (RingEquiv.equivRatAlgEquiv _ _ ?_) (algEquivOfRingEquiv f₂.toRingEquiv).symm⟩
  exact IsFractionRing.ringEquivOfRingEquiv (nonempty_algEquiv_int_iff.mpr h).some.toRingEquiv

/-! ### The concrete fields `ℚ(√d)` -/

section concrete

/-- Every fundamental discriminant other than `1` is the discriminant of a quadratic field.
With `nonempty_algEquiv_iff_discr_eq`, this makes the discriminant a bijection between
quadratic fields up to isomorphism and fundamental discriminants other than `1`. -/
theorem NumberField.discr_quadraticAlgebra
    [Fact (¬ IsSquare (QuadraticAlgebra.discr (D : ℚ) 0))]
    (hD : Int.IsFundamentalDiscr D) (hD1 : D ≠ 1) :
    discr (QuadraticAlgebra ℚ (D : ℚ) 0) = D := sorry

variable (hd : Squarefree d) (hd1 : d ≠ 1)

include hd hd1 in
theorem NumberField.discr_sqrtd [Fact (¬ IsSquare (QuadraticAlgebra.discr (d : ℚ) 0))]
    (h : d % 4 = 2 ∨ d % 4 = 3) :
    discr (QuadraticAlgebra ℚ (d : ℚ) 0) = 4 * d := sorry

include hd hd1 in
theorem NumberField.discr_half [Fact (¬ IsSquare (QuadraticAlgebra.discr (d : ℚ) 0))]
    (h : d % 4 = 1) :
    discr (QuadraticAlgebra ℚ (d : ℚ) 0) = d := sorry

end concrete
