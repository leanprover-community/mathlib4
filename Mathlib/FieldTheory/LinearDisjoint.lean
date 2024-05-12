/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.LinearDisjoint
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.RingTheory.AlgebraicIndependent

/-!

# Linearly disjoint of fields

This file contains basics about the linearly disjoint of fields.

## Mathematical background

(<https://en.wikipedia.org/wiki/Linearly_disjoint>) Subalgebras `A`, `B` over a field
`F` inside some field extension `E` of `F` are said to be linearly disjoint over `F` if the
following equivalent conditions are met:

- The map `A ⊗[F] B → A ⊔ B`, `x ⊗ₜ[F] y ↦ x * y` is injective.

- Any `F`-basis of `A` remains linearly independent over `B`.

- If `{ u_i }`, `{ v_j }` are `F`-bases for `A`, `B`, then the products `{ u_i * v_j }` are
  linearly independent over `F`.

Our definition `IntermediateField.LinearDisjoint` is very closed to the second equivalent
definition in the above.

(<https://mathoverflow.net/questions/8324>) For two abstract fields `E` and `K` over `F`, they are
called linearly disjoint over `F` (`LinearDisjoint F E K`), if `E ⊗[F] K` is a field.
In this case, it can be shown that at least one of `E / F` and `K / F` are algebraic, and if this
holds, then it is equivalent to the above `IntermediateField.LinearDisjoint`.

The advantage of `LinearDisjoint` is that it is preserved under algebra isomorphisms, while for
`IntermediateField.LinearDisjoint` this is not so easy to prove, in fact it's wrong if both of the
extensions are not algebraic.

## Main definitions

- ...

## Main results

- ...

## Tags

linearly disjoint, linearly independent, tensor product

## TODO

- ...

-/

open scoped Classical TensorProduct

open FiniteDimensional IntermediateField

noncomputable section

universe u v w

namespace IntermediateField

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

variable (A B : IntermediateField F E)

variable (L : Type w) [Field L] [Algebra F L] [Algebra L E] [IsScalarTower F L E]

/-- If `A` is an intermediate field of `E / F`, and `E / L / F` is a field extension tower,
then `A` and `L` are linearly disjoint, if they are linearly disjoint as subalgebras of `E`. -/
@[mk_iff]
protected structure LinearDisjoint : Prop where
  subalgebra : A.toSubalgebra.LinearDisjoint (IsScalarTower.toAlgHom F L E).range

variable {A B L}

theorem linearDisjoint_iff' :
    A.LinearDisjoint B ↔ A.toSubalgebra.LinearDisjoint B.toSubalgebra := by
  rw [linearDisjoint_iff]
  congr!
  ext; simp

/-- Linearly disjoint is symmetric. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  linearDisjoint_iff'.2 (linearDisjoint_iff'.1 H).symm

/-- Linearly disjoint is symmetric. -/
theorem linearDisjoint_symm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

namespace LinearDisjoint

variable (A) in
theorem of_self_right : A.LinearDisjoint F :=
  ⟨.of_bot_right _⟩

variable (A) in
theorem of_bot_right : A.LinearDisjoint (⊥ : IntermediateField F E) :=
  linearDisjoint_iff'.2 (.of_bot_right _)

variable (F E L) in
theorem of_bot_left : (⊥ : IntermediateField F E).LinearDisjoint L :=
  ⟨.of_bot_left _⟩

/-- If `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `A` remains
linearly independent over `L`. -/
theorem map_linearIndependent_left (H : A.LinearDisjoint L)
    {ι : Type*} {a : ι → A} (ha : LinearIndependent F a) :
    LinearIndependent L (A.val ∘ a) :=
  (H.1.map_linearIndependent_left_of_flat ha).map_of_injective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (by simp) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

/-- If there exists an `F`-basis of `A` which remains linearly independent over `L`, then
`A` and `L` are linearly disjoint. -/
theorem of_map_linearIndependent_left {ι : Type*} (a : Basis ι F A)
    (H : LinearIndependent L (A.val ∘ a)) :
    A.LinearDisjoint L := by
  rw [linearDisjoint_iff]
  refine Subalgebra.LinearDisjoint.of_map_linearIndependent_left _ _ a ?_
  exact H.map_of_surjective_injective
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)) (AddMonoidHom.id E)
    (AlgEquiv.surjective _) (by simp) (fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)

/-- If `A` and `B` are linearly disjoint, then any `F`-linearly independent family on `B` remains
linearly independent over `A`. -/
theorem map_linearIndependent_right (H : A.LinearDisjoint B)
    {ι : Type*} {b : ι → B} (hb : LinearIndependent F b) :
    LinearIndependent A (B.val ∘ b) :=
  (linearDisjoint_iff'.1 H).map_linearIndependent_right_of_flat hb

/-- If there exists an `F`-basis of `B` which remains linearly independent over `A`, then
`A` and `B` are linearly disjoint. -/
theorem of_map_linearIndependent_right {ι : Type*} (b : Basis ι F B)
    (H : LinearIndependent A (B.val ∘ b)) :
    A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_map_linearIndependent_right _ _ b H)

/-- If `A` and `L` are linearly disjoint, then any `F`-linearly independent family on `L` remains
linearly independent over `A`. -/
theorem map_linearIndependent_right' (H : A.LinearDisjoint L)
    {ι : Type*} {b : ι → L} (hb : LinearIndependent F b) :
    LinearIndependent A ((algebraMap L E) ∘ b) := by
  have := H.1.map_linearIndependent_right_of_flat <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker
  exact this

/-- If there exists an `F`-basis of `L` which remains linearly independent over `A`, then
`A` and `L` are linearly disjoint. -/
theorem of_map_linearIndependent_right' {ι : Type*} (b : Basis ι F L)
    (H : LinearIndependent A ((algebraMap L E) ∘ b)) :
    A.LinearDisjoint L := by
  rw [linearDisjoint_iff]
  exact .of_map_linearIndependent_right _ _
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

/-- If `A` and `B` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `B`, the products `{ u_i * v_j }`
are linearly independent over `F`. -/
theorem map_linearIndependent_mul (H : A.LinearDisjoint B)
    {κ ι : Type*} {a : κ → A} {b : ι → B} (ha : LinearIndependent F a)
    (hb : LinearIndependent F b) : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1 :=
  (linearDisjoint_iff'.1 H).map_linearIndependent_mul_of_flat_left ha hb

/-- If `A` and `L` are linearly disjoint, then for any `F`-linearly independent families
`{ u_i }`, `{ v_j }` of `A`, `L`, the products `{ u_i * v_j }`
are linearly independent over `F`. -/
theorem map_linearIndependent_mul' (H : A.LinearDisjoint L)
    {κ ι : Type*} {a : κ → A} {b : ι → L} (ha : LinearIndependent F a)
    (hb : LinearIndependent F b) :
    LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2) := by
  have := H.1.map_linearIndependent_mul_of_flat_left ha <| hb.map' _
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.ker
  exact this

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `B`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `B` are linearly disjoint. -/
theorem of_map_linearIndependent_mul {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F B)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * (b i.2).1) : A.LinearDisjoint B :=
  linearDisjoint_iff'.2 (.of_map_linearIndependent_mul _ _ a b H)

/-- If there are `F`-bases `{ u_i }`, `{ v_j }` of `A`, `L`, such that the products
`{ u_i * v_j }` are linearly independent over `F`, then `A` and `L` are linearly disjoint. -/
theorem of_map_linearIndependent_mul' {κ ι : Type*} (a : Basis κ F A) (b : Basis ι F L)
    (H : LinearIndependent F fun (i : κ × ι) ↦ (a i.1).1 * algebraMap L E (b i.2)) :
    A.LinearDisjoint L := by
  rw [linearDisjoint_iff]
  exact .of_map_linearIndependent_mul _ _ a
    (b.map (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv) H

theorem of_le_left {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (h : A' ≤ A) : A'.LinearDisjoint L :=
  ⟨H.1.of_le_left_of_flat h⟩

theorem of_le_right {B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (h : B' ≤ B) : A.LinearDisjoint B' :=
  linearDisjoint_iff'.2 ((linearDisjoint_iff'.1 H).of_le_right_of_flat h)

theorem of_le_right' (H : A.LinearDisjoint L) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A.LinearDisjoint L' := by
  refine ⟨H.1.of_le_right_of_flat ?_⟩
  convert AlgHom.range_comp_le_range (IsScalarTower.toAlgHom F L' L) (IsScalarTower.toAlgHom F L E)
  ext x
  exact IsScalarTower.algebraMap_apply L' L E x

/-- If `A` and `B` are linearly disjoint, `A'` and `B'` are contained in `A` and `B`,
respectively, then `A'` and `B'` are also linearly disjoint. -/
theorem of_le {A' B' : IntermediateField F E} (H : A.LinearDisjoint B)
    (hA : A' ≤ A) (hB : B' ≤ B) : A'.LinearDisjoint B' :=
  H.of_le_left hA |>.of_le_right hB

theorem of_le' {A' : IntermediateField F E} (H : A.LinearDisjoint L)
    (hA : A' ≤ A) (L' : Type*) [Field L']
    [Algebra F L'] [Algebra L' L] [IsScalarTower F L' L]
    [Algebra L' E] [IsScalarTower F L' E] [IsScalarTower L' L E] : A'.LinearDisjoint L' :=
  H.of_le_left hA |>.of_le_right' L'

/-- If `A` and `B` are linearly disjoint over `F`, then their intersection is equal to `F`. -/
theorem inf_eq_bot (H : A.LinearDisjoint B) :
    A ⊓ B = ⊥ := toSubalgebra_injective (linearDisjoint_iff'.1 H).inf_eq_bot

/-- If `A` and `A` itself are linearly disjoint over `F`, then it is equal to `F`. -/
theorem eq_bot_of_self (H : A.LinearDisjoint A) : A = ⊥ :=
  inf_of_le_left (le_refl A) ▸ H.inf_eq_bot

-- TODO: move to suitable place
theorem _root_.IntermediateField.rank_sup_le_of_isAlgebraic
    (halg : Algebra.IsAlgebraic F A ∨ Algebra.IsAlgebraic F B) :
    Module.rank F ↥(A ⊔ B) ≤ Module.rank F A * Module.rank F B := by
  have := A.toSubalgebra.rank_sup_le_of_free B.toSubalgebra
  rw [← sup_toSubalgebra_of_isAlgebraic A B halg] at this
  exact this

-- TODO: move to suitable place
theorem _root_.Localization.card_le' {M : Type u} [CommMonoid M] (S : Submonoid M) :
    Cardinal.mk (Localization S) ≤ Cardinal.mk M * Cardinal.mk S := by
  let i : M × S → Localization S := (Localization.r S).toQuotient
  have h : Function.Surjective i := Quotient.surjective_Quotient_mk''
  simpa using Cardinal.mk_le_of_surjective h

-- TODO: move to suitable place
theorem _root_.Localization.card_le {M : Type u} [CommMonoid M] (S : Submonoid M) :
    Cardinal.mk (Localization S) ≤ Cardinal.mk M * Cardinal.mk M :=
  (Localization.card_le' S).trans (by gcongr; exact Cardinal.mk_subtype_le _)

-- TODO: move to suitable place
theorem _root_.FractionRing.card_le (R : Type u) [CommRing R] :
    Cardinal.mk (FractionRing R) ≤ Cardinal.mk R * Cardinal.mk R := Localization.card_le _

-- TODO: move to suitable place
theorem _root_.transcendental_iff
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {x : A} :
    Transcendental R x ↔ ∀ p : Polynomial R, Polynomial.aeval x p = 0 → p = 0 := by
  rw [Transcendental, IsAlgebraic, not_exists]
  congr! 1; tauto

-- TODO: move to suitable place
theorem _root_.transcendental_iff_injective_aeval
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {x : A} :
    Transcendental R x ↔ Function.Injective (Polynomial.aeval (R := R) x) := by
  rw [transcendental_iff, injective_iff_map_eq_zero]

-- TODO: move to suitable place
theorem _root_.transcendental_iff_ker_eq_bot
    {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {x : A} :
    Transcendental R x ↔ RingHom.ker (Polynomial.aeval (R := R) x) = ⊥ := by
  rw [transcendental_iff_injective_aeval, RingHom.injective_iff_ker_eq_bot]

-- TODO: move to suitable place
theorem _root_.transcendental_iff_algebraicIndependent
    {R A : Type*} {x : A} [CommRing R] [CommRing A] [Algebra R A] :
    Transcendental R x ↔ AlgebraicIndependent R ![x] := by
  rw [transcendental_iff_injective_aeval, algebraicIndependent_iff_injective_aeval]
  let i := (MvPolynomial.finSuccEquiv R 0).toRingEquiv.trans <|
    Polynomial.mapEquiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv
  have key : (MvPolynomial.aeval (R := R) ![x]).toRingHom =
      (Polynomial.aeval (R := R) x).toRingHom.comp i.toRingHom := by
    ext y
    · simp [i]
    · fin_cases y; simp [i]
  change _ ↔ Function.Injective (MvPolynomial.aeval (R := R) ![x]).toRingHom
  rw [key]; simp

-- TODO: move to suitable place
theorem _root_.AlgebraicIndependent.transcendental {ι R A : Type*} {x : ι → A}
    [CommRing R] [CommRing A] [Algebra R A] (h : AlgebraicIndependent R x) (i : ι) :
    Transcendental R (x i) := by
  replace h := h.comp ![i] (Function.injective_of_subsingleton _)
  replace h : AlgebraicIndependent R ![x i] := by rwa [← FinVec.map_eq] at h
  rwa [transcendental_iff_algebraicIndependent]

-- TODO: move to suitable place
theorem _root_.MvPolynomial.algebraicIndependent_X (σ : Type u) (R : Type v) [CommRing R] :
    AlgebraicIndependent R (MvPolynomial.X (R := R) (σ := σ)) := by
  rw [AlgebraicIndependent, MvPolynomial.aeval_X_left]
  exact Function.injective_id

-- TODO: move to suitable place
theorem _root_.MvPolynomial.transcendental_X {σ : Type u} (R : Type v) [CommRing R] (i : σ) :
    Transcendental R (MvPolynomial.X (R := R) i) :=
  (MvPolynomial.algebraicIndependent_X σ R).transcendental i

-- TODO: move to suitable place
theorem _root_.Polynomial.transcendental_X (R : Type v) [CommRing R] :
    Transcendental R (Polynomial.X (R := R)) := by
  simp [transcendental_iff]

-- TODO: move to suitable place
theorem _root_.transcendental_algebraMap_iff {R S A : Type*} [CommRing R] [CommRing S] [Ring A]
    [Algebra R A] [Algebra R S] [Algebra S A] [IsScalarTower R S A] {a : S}
    (h : Function.Injective (algebraMap S A)) :
    Transcendental R ((algebraMap S A) a) ↔ Transcendental R a := by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

-- TODO: move to suitable place
theorem _root_.Transcendental.linearIndependent_sub_inv
    {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E} (H : Transcendental F x) :
    LinearIndependent F fun a ↦ (x - algebraMap F E a)⁻¹ := by
  rw [transcendental_iff] at H
  refine linearIndependent_iff'.2 fun s m hm i hi ↦ ?_
  have hnz (a : F) : x - algebraMap F E a ≠ 0 := fun h ↦
    Polynomial.X_sub_C_ne_zero a <| H (.X - .C a) (by simp [h])
  let b := s.prod fun j ↦ x - algebraMap F E j
  have h1 : ∀ i ∈ s, m i • (b * (x - algebraMap F E i)⁻¹) =
      m i • (s.erase i).prod fun j ↦ x - algebraMap F E j := fun i hi ↦ by
    simp_rw [b, ← s.prod_erase_mul _ hi, mul_inv_cancel_right₀ (hnz i)]
  replace hm := congr(b * $(hm))
  simp_rw [mul_zero, Finset.mul_sum, mul_smul_comm, Finset.sum_congr rfl h1] at hm
  let p : Polynomial F := s.sum fun i ↦ .C (m i) * (s.erase i).prod fun j ↦ .X - .C j
  replace hm := congr(Polynomial.aeval i $(H p (by simp_rw [← hm, p, map_sum, map_mul, map_prod,
    map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.smul_def])))
  have h2 : ∀ j ∈ s.erase i, m j * ((s.erase j).prod fun x ↦ i - x) = 0 := fun j hj ↦ by
    have := Finset.mem_erase_of_ne_of_mem (Finset.ne_of_mem_erase hj).symm hi
    simp_rw [← (s.erase j).prod_erase_mul _ this, sub_self, mul_zero]
  simp_rw [map_zero, p, map_sum, map_mul, map_prod, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.id.map_eq_self, ← s.sum_erase_add _ hi,
    Finset.sum_eq_zero h2, zero_add] at hm
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (Finset.prod_ne_zero_iff.2 fun j hj ↦
    sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm) hm

-- TODO: move to suitable place
theorem _root_.rank_fractionRing_mvPolynomial_eq {σ : Type u} {F : Type v} [Field F] [Nonempty σ] :
    Module.rank F (FractionRing (MvPolynomial σ F)) =
      max (max (Cardinal.lift.{u} (Cardinal.mk F)) (Cardinal.lift.{v} (Cardinal.mk σ)))
        Cardinal.aleph0 := by
  refine le_antisymm ?_ ?_
  · refine (rank_le_card _ _).trans ?_
    convert FractionRing.card_le (MvPolynomial σ F) using 1
    rw [MvPolynomial.cardinal_mk_eq_max_lift]
    exact (Cardinal.mul_eq_self (le_max_right _ _)).symm
  · have hinj := NoZeroSMulDivisors.algebraMap_injective (MvPolynomial σ F)
      (FractionRing (MvPolynomial σ F))
    have h1 := IsScalarTower.toAlgHom F (MvPolynomial σ F) (FractionRing (MvPolynomial σ F))
      |>.toLinearMap.rank_le_of_injective hinj
    simp_rw [Cardinal.lift_id'.{u, v} _ ▸ (MvPolynomial.basisMonomials σ F).mk_eq_rank.symm] at h1
    rw [Cardinal.lift_umax.{u, v}, Cardinal.mk_finsupp_nat, Cardinal.lift_max,
      Cardinal.lift_aleph0, max_le_iff] at h1
    obtain ⟨i⟩ := ‹Nonempty σ›
    let x := algebraMap (MvPolynomial σ F) (FractionRing (MvPolynomial σ F)) (MvPolynomial.X i)
    have hx : Transcendental F x := (transcendental_algebraMap_iff hinj).2
      (MvPolynomial.transcendental_X F i)
    have h2 := hx.linearIndependent_sub_inv.cardinal_lift_le_rank
    rw [Cardinal.lift_id'.{v, u} _, Cardinal.lift_umax.{v, u}] at h2
    exact max_le_iff.2 ⟨max_le_iff.2 ⟨h2, h1.1⟩, h1.2⟩

-- TODO: move to suitable place
/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M`, `T` respectively,
an isomorphism `h : R ≃ₐ[A] P` such that `h(M) = T` induces an isomorphism of localizations
`S ≃ₐ[A] Q`. -/
@[simps!]
def _root_.IsLocalization.algEquivOfAlgEquiv
    {A : Type*} [CommSemiring A]
    {R : Type*} [CommSemiring R] [Algebra A R] {M : Submonoid R} (S : Type*)
    [CommSemiring S] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [IsLocalization M S]
    {P : Type*} [CommSemiring P] [Algebra A P] {T : Submonoid P} (Q : Type*)
    [CommSemiring Q] [Algebra A Q] [Algebra P Q] [IsScalarTower A P Q] [IsLocalization T Q]
    (h : R ≃ₐ[A] P) (H : Submonoid.map h M = T) : S ≃ₐ[A] Q :=
  {
    IsLocalization.ringEquivOfRingEquiv S Q h.toRingEquiv H with
    commutes' := fun _ ↦ by dsimp; rw [IsScalarTower.algebraMap_apply A R S, IsLocalization.map_eq,
      RingHom.coe_coe, AlgEquiv.commutes, IsScalarTower.algebraMap_apply A P Q]
  }

/-- TODO: generalize `FractionRing.algEquiv` -/
@[simps!]
def _root_.FractionRing.algEquiv!!!
    (A : Type*) [CommRing A] (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    FractionRing A ≃ₐ[A] K :=
  Localization.algEquiv (nonZeroDivisors A) K

-- TODO: move to suitable place
theorem _root_.MulEquiv.map_nonZeroDivisors {R S : Type*} [MonoidWithZero R] [MonoidWithZero S]
    (h : R ≃* S) : Submonoid.map h (nonZeroDivisors R) = nonZeroDivisors S := by
  ext x
  simp_rw [Submonoid.mem_map, mem_nonZeroDivisors_iff]
  refine ⟨fun h1 z h2 ↦ ?_, fun h1 ↦ ⟨h.symm x, ⟨fun y h2 ↦ ?_, by simp⟩⟩⟩
  · obtain ⟨y, h1, rfl⟩ := h1
    replace h1 := h1 (h.symm z) (by simpa using congr(h.symm $(h2)))
    simpa using congr(h $(h1))
  replace h1 := h1 (h y) (by simpa using congr(h $(h2)))
  simpa using congr(h.symm $(h1))

-- TODO: move to suitable place
/-- If `S`, `Q` are fraction rings of `R` and `P` respectively,
an isomorphism `h : R ≃ₐ[A] P` induces an isomorphism of fraction rings
`S ≃ₐ[A] Q`. -/
@[simps!]
def _root_.IsFractionRing.algEquivOfAlgEquiv
    {A : Type*} [CommSemiring A]
    {R : Type*} [CommRing R] [Algebra A R] (S : Type*)
    [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [IsFractionRing R S]
    {P : Type*} [CommRing P] [Algebra A P] (Q : Type*)
    [CommRing Q] [Algebra A Q] [Algebra P Q] [IsScalarTower A P Q] [IsFractionRing P Q]
    (h : R ≃ₐ[A] P) : S ≃ₐ[A] Q :=
  IsLocalization.algEquivOfAlgEquiv S Q h h.toMulEquiv.map_nonZeroDivisors

-- TODO: move to suitable place
theorem _root_.IntermediateField.mem_adjoin_range_iff
    (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]
    {ι : Type*} (i : ι → E) (x : E) :
    x ∈ IntermediateField.adjoin F (Set.range i) ↔
    ∃ (r s : MvPolynomial ι F), x = MvPolynomial.aeval i r / MvPolynomial.aeval i s := by
  simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring,
    Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range, exists_exists_eq_and]
  tauto

-- TODO: move to suitable place
/-- Canonical isomorphism between rational functions and the
intermediate field generated by algebraically independent elements. -/
def _root_.AlgebraicIndependent.algEquivField {ι F E : Type*} {x : ι → E} [Field F] [Field E]
    [Algebra F E] (hx : AlgebraicIndependent F x) :
    FractionRing (MvPolynomial ι F) ≃ₐ[F] ↥(IntermediateField.adjoin F (Set.range x)) := by
  letI (S : Set E) : Algebra (Algebra.adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  letI (S : Set E) : Module (Algebra.adjoin F S) (IntermediateField.adjoin F S) := Algebra.toModule
  letI (S : Set E) : SMul (Algebra.adjoin F S) (IntermediateField.adjoin F S) := Algebra.toSMul
  haveI (S : Set E) : IsFractionRing (Algebra.adjoin F S) (IntermediateField.adjoin F S) := {
    map_units' := fun y ↦ by
      have : y.1 ≠ 0 := fun h ↦ by simpa [h] using mem_nonZeroDivisors_iff.1 y.2 1
      refine Ne.isUnit fun h ↦ ?_
      apply_fun algebraMap _ E at h using Subtype.val_injective
      exact this (Subtype.val_injective h)
    surj' := fun z ↦ by
      have h := z.2
      simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
        Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring] at h
      obtain ⟨x1, h1, x2, h2, h⟩ := h
      by_cases hzero : x2 = 0
      · have : z = 0 := Subtype.val_injective (by rw [← h, hzero, div_zero]; rfl)
        exact ⟨⟨0, 1⟩, by simp [this]⟩
      use ⟨⟨_, h1⟩, ⟨⟨_, h2⟩, mem_nonZeroDivisors_of_ne_zero fun h ↦ hzero congr(Subtype.val $h)⟩⟩
      exact Subtype.val_injective ((div_eq_iff hzero).1 h).symm
    exists_of_eq := fun h ↦ by use 1; rw [Subtype.val_injective congr(algebraMap _ E $(h))]
  }
  exact IsFractionRing.algEquivOfAlgEquiv _ _ hx.aevalEquiv

-- TODO: move to suitable place
theorem _root_.AlgebraicIndependent.algebraMap_algEquivField {ι F E : Type*} {x : ι → E}
    [Field F] [Field E] [Algebra F E] (hx : AlgebraicIndependent F x) (p : MvPolynomial ι F) :
    algebraMap _ E (hx.algEquivField (algebraMap _ _ p)) = MvPolynomial.aeval x p := by
  letI (S : Set E) : Algebra (Algebra.adjoin F S) (IntermediateField.adjoin F S) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin F S)).toRingHom.toAlgebra
  letI (S : Set E) : Module (Algebra.adjoin F S) (IntermediateField.adjoin F S) := Algebra.toModule
  letI (S : Set E) : SMul (Algebra.adjoin F S) (IntermediateField.adjoin F S) := Algebra.toSMul
  haveI (S : Set E) : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S) E :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  simp_rw [AlgebraicIndependent.algEquivField, IsFractionRing.algEquivOfAlgEquiv_apply,
    IsLocalization.map_eq, RingHom.coe_coe, ← IsScalarTower.algebraMap_apply,
    hx.algebraMap_aevalEquiv]

-- -- TODO: move to suitable place
-- variable (A B) in
-- theorem _root_.IntermediateField.rank_sup_le :
--     Module.rank F ↥(A ⊔ B) ≤ Module.rank F A * Module.rank F B := by
--   sorry

-- TODO: move to suitable place
variable (A B) in
theorem _root_.IntermediateField.finrank_sup_le :
    finrank F ↥(A ⊔ B) ≤ finrank F A * finrank F B := by
  by_cases h : FiniteDimensional F A
  · have := Subalgebra.finrank_sup_le_of_free A.toSubalgebra B.toSubalgebra
    change _ ≤ finrank F A * finrank F B at this
    rwa [← sup_toSubalgebra_of_left A B] at this
  rw [FiniteDimensional, ← Module.rank_lt_alpeh0_iff, not_lt] at h
  have := LinearMap.rank_le_of_injective _ <| Submodule.inclusion_injective <|
    show Subalgebra.toSubmodule A.toSubalgebra ≤ Subalgebra.toSubmodule (A ⊔ B).toSubalgebra by simp
  rw [show finrank F A = 0 from Cardinal.toNat_apply_of_aleph0_le h,
    show finrank F ↥(A ⊔ B) = 0 from Cardinal.toNat_apply_of_aleph0_le (h.trans this), zero_mul]

-- TODO: need IntermediateField.rank_sup_le

-- theorem rank_sup (H : A.LinearDisjoint B) :
--     Module.rank F ↥(A ⊔ B) = Module.rank F A * Module.rank F B := by
--   have h := le_sup_toSubalgebra A B
--   exact (rank_sup_le A B).antisymm <| (linearDisjoint_iff'.1 H).rank_sup_of_free.ge.trans <|
--     (Subalgebra.inclusion h).toLinearMap.rank_le_of_injective (Subalgebra.inclusion_injective h)

-- theorem finrank_sup (H : A.LinearDisjoint B) :
--     finrank F ↥(A ⊔ B) = finrank F A * finrank F B := by
--   simpa only [map_mul] using congr(Cardinal.toNat $(H.rank_sup))

/-- If `A` and `L` have coprime degree over `F`, then they are linearly disjoint. -/
theorem of_finrank_coprime (H : (finrank F A).Coprime (finrank F L)) :
    A.LinearDisjoint L := by
  rw [linearDisjoint_iff]
  letI : Field (AlgHom.range (IsScalarTower.toAlgHom F L E)) :=
    show Field (AlgHom.fieldRange (IsScalarTower.toAlgHom F L E)) from inferInstance
  refine .of_finrank_coprime_of_free ?_
  rwa [(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L E)).toLinearEquiv.finrank_eq] at H

end LinearDisjoint

end IntermediateField

-- section Absolute

-- variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

-- variable (K : Type w) [Field K] [Algebra F K]

-- /-- Two abstract fields `E` and `K` over `F` are called linearly disjoint, if their
-- tensor product over `F` is a field. -/
-- def LinearDisjoint := IsField (E ⊗[F] K)

-- set_option linter.unusedVariables false in
-- variable {F E K} in
-- /-- If two abstract fields `E` and `K` over `F` are linearly disjoint, then at least one of
-- `E / F` and `K / F` are algebraic. -/
-- proof_wanted LinearDisjoint.isAlgebraic (H : LinearDisjoint F E K) :
--     Algebra.IsAlgebraic F E ∨ Algebra.IsAlgebraic F K

-- end Absolute
