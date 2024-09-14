/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.Algebra.Field
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.NormalClosure
import Mathlib.FieldTheory.Galois


/-!
# Liouville's theorem

A proof of Liouville's theorem. Follows Integration in Finite Terms, Maxwell Rosenlicht
-- TODO: Add BibTex

## Liouville field extension

This file defines Liouville field extensions, which are field extensions which satisfy
a slight generalization of Liouville's theorem. Note that this definition doesn't appear in the
literature, and we introduce it as part of the formalization of Liouville's theorem.
-/

open Differential algebraMap IntermediateField Finset Polynomial

/--
We say that a field extension `K / F` is Liouville if, whenever an element a ∈ F can be written as
`a = v + ∑ cᵢ * logDeriv uᵢ` for `v, cᵢ, uᵢ ∈ K` and `cᵢ` constant, it can also be written in that
way with `v, cᵢ, uᵢ ∈ F`.
-/
class IsLiouville (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] : Prop where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) :
    ∃ (ι' : Type) (_ : Fintype ι') (c' : ι' → F) (_ : ∀ x, (c' x)′ = 0)
      (u' : ι' → F) (v' : F), a = ∑ x, c' x * logDeriv (u' x) + v'′

instance IsLiouville.rfl (F : Type*) [Field F] [Differential F] : IsLiouville F F where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → F) (v : F) (h : a = ∑ x, c x * logDeriv (u x) + v′) :=
    ⟨ι, _, c, hc, u, v, h⟩

lemma IsLiouville.trans {F : Type*} {K : Type*} {A : Type*} [Field F]
    [Field K] [Field A] [Algebra F K] [Algebra K A] [Algebra F A]
    [Differential F] [Differential K] [Differential A]
    [DifferentialAlgebra F K] [DifferentialAlgebra K A] [DifferentialAlgebra F A]
    [IsScalarTower F K A] [Differential.ContainConstants F K]
    (inst1 : IsLiouville F K) (inst2 : IsLiouville K A) : IsLiouville F A where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → A) (v : A) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    obtain ⟨ι'', _, c'', hc', u'', v', h'⟩ := inst2.is_liouville (a : K) ι
        ((↑) ∘ c)
        (fun _ ↦ by simp only [Function.comp_apply, ← coe_deriv, lift_map_eq_zero_iff, hc])
        ((↑) ∘ u) v (by simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply])
    have hc (x : ι'') := mem_range_of_deriv_eq_zero F (hc' x)
    choose c' hc using hc
    apply inst1.is_liouville a ι'' c' _ u'' v'
    rw [h']
    · simp [hc]
    · intro
      apply_fun ((↑) : F → K)
      simp only [Function.comp_apply, coe_deriv, hc, algebraMap.coe_zero]
      apply hc'
      apply NoZeroSMulDivisors.algebraMap_injective

section Algebraic
/-
The case of Liouville's theorem for algebraic extension.
-/

variable {F : Type*} [CommRing F] [IsDomain F] [CharZero F] in
lemma not_dvd_derivative (p : F[X]) (hp : 0 < p.natDegree) :
    ¬p ∣ derivative p := by
  apply not_dvd_of_natDegree_lt
  · intro nh
    simp [natDegree_eq_zero_of_derivative_eq_zero nh] at hp
  apply natDegree_derivative_lt
  omega

noncomputable instance adjoinRootDifferentialField {F : Type*} [Field F] [Differential F]
    [CharZero F]
    (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic] : Differential (AdjoinRoot p) where
  deriv := Derivation.liftOfSurjective (A := F[X]) (R := ℤ) (M := AdjoinRoot p)
    (AdjoinRoot.mk p).toIntAlgHom AdjoinRoot.mk_surjective
    (implicitDeriv <| AdjoinRoot.modByMonicHom Fact.out <|
      implicitDeriv' F (AdjoinRoot.root p)) (fun x hx ↦ by
      simp_all only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero]
      obtain ⟨q, rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold implicitDeriv implicitDeriv'
      simp only [ne_eq, show p ≠ 0 from Irreducible.ne_zero Fact.out, not_false_eq_true,
        AdjoinRoot.minpoly_root, show p.Monic from Fact.out, Monic.leadingCoeff, inv_one, map_one,
        mul_one, AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
        Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add,
        map_mul, AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀, add_neg_cancel]
      simp only [ne_eq, AdjoinRoot.mk_eq_zero]
      apply not_dvd_derivative p (Irreducible.natDegree_pos Fact.out)
    )

variable {F : Type*} [Field F] [Differential F] [CharZero F]

instance adjoinRootDifferentialAlgebra {p : F[X]} [Fact (Irreducible p)]
    [Fact p.Monic] : DifferentialAlgebra F (AdjoinRoot p) where
  deriv_algebraMap a := by
    change (Derivation.liftOfSurjective ..) ((AdjoinRoot.mk p).toIntAlgHom (C a)) = _
    rw [Derivation.liftOfSurjective_apply, implicitDeriv_C]
    rfl

section FD

variable {K : Type*} [Field K] [Algebra F K]
variable [FiniteDimensional F K]

noncomputable def finiteDifferential
    (k : K) (h : F⟮k⟯ = ⊤) : Differential K :=
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.of_finite ..).isIntegral⟩
  Differential.equiv (IntermediateField.adjoinRootEquivAdjoin F
    (IsAlgebraic.of_finite F k).isIntegral |>.trans (IntermediateField.equivOfEq h) |>.trans
    IntermediateField.topEquiv).symm.toRingEquiv

lemma finiteDifferentialAlgebra (k : K) (h : F⟮k⟯ = ⊤) :
    letI := finiteDifferential k h
    DifferentialAlgebra F K := by
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.of_finite ..).isIntegral⟩
  apply DifferentialAlgebra.equiv

noncomputable instance (B : IntermediateField F K) [FiniteDimensional F B] : Differential B :=
  finiteDifferential (Field.exists_primitive_element F B).choose
    (Field.exists_primitive_element F B).choose_spec

instance (B : IntermediateField F K) [FiniteDimensional F B] :
    DifferentialAlgebra F B :=
  finiteDifferentialAlgebra (Field.exists_primitive_element F B).choose
    (Field.exists_primitive_element F B).choose_spec

variable [Differential K] [DifferentialAlgebra F K]

instance (B : IntermediateField F K) [FiniteDimensional F B] :
    DifferentialAlgebra B K where
  deriv_algebraMap a := by
    change (B.val a)′ = B.val a′
    rw [algHom_deriv]
    exact Subtype.val_injective
    apply (IsAlgebraic.of_finite ..).isIntegral

instance IsLiouville.subfield (B : IntermediateField F K)
    [FiniteDimensional F B] [inst : IsLiouville F K] :
    IsLiouville F B where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → B) (v : B) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.is_liouville a ι c hc (B.val ∘ u) (B.val v)
    dsimp only [coe_val, Function.comp_apply]
    conv =>
      rhs
      congr
      · rhs
        intro x
        rhs
        apply logDeriv_algebraMap (u x)
      · apply (deriv_algebraMap v)
    simp_rw [IsScalarTower.algebraMap_apply F B K]
    norm_cast


end FD

variable {K : Type*} [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]

lemma IsLiouville.equiv {K' : Type*} [Field K'] [Differential K'] [Algebra F K']
    [DifferentialAlgebra F K'] [Algebra.IsAlgebraic F K']
    [inst : IsLiouville F K] (e : K ≃ₐ[F] K') : IsLiouville F K' where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → K') (v : K') (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.is_liouville a ι c hc (e.symm ∘ u) (e.symm v)
    apply_fun e.symm at h
    simpa [AlgEquiv.commutes, map_add, map_sum, map_mul, logDeriv, algEquiv_deriv'] using h

variable [CharZero K]

private local instance liouville_algebraic_galois' [FiniteDimensional F K] [IsGalois F K] :
    IsLiouville F K where
  is_liouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    let c' (i : ι) := (c i) / (Fintype.card (K ≃ₐ[F] K))
    let u'' (i : ι) := ∏ x : (K ≃ₐ[F] K), x (u i)
    have : ∀ i, u'' i ∈ fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro i ⟨e, _⟩
      change e (u'' i) = u'' i
      unfold_let u''
      simp only [map_prod]
      apply Fintype.prod_equiv (Equiv.mulLeft e)
      simp
    have ffb := (IsGalois.tfae.out 0 1).mp (inferInstanceAs (IsGalois F K))
    simp_rw [ffb, IntermediateField.mem_bot, Set.mem_range] at this
    choose u' hu' using this
    let v'' := (∑ x : (K ≃ₐ[F] K), x v) / (Fintype.card ((K ≃ₐ[F] K)))
    have : v'' ∈ fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro ⟨e, _⟩
      change e v'' = v''
      unfold_let v''
      simp only [map_div₀, map_sum, map_natCast]
      congr 1
      apply Fintype.sum_equiv (Equiv.mulLeft e)
      simp
    rw [ffb, IntermediateField.mem_bot] at this
    obtain ⟨v', hv'⟩ := this
    exists ι, inferInstance, c', ?_, u', v'
    · intro x
      simp [c', Derivation.leibniz_div, hc]
    · apply_fun (algebraMap F K)
      case inj =>
        exact NoZeroSMulDivisors.algebraMap_injective F K
      simp only [map_add, map_sum, map_mul, ← logDeriv_algebraMap, hu', ← deriv_algebraMap, hv']
      unfold_let u'' v'' c'
      clear c' u'' u' hu' v'' v' hv'
      dsimp only
      push_cast
      rw [Derivation.leibniz_div_const, smul_eq_mul, inv_mul_eq_div]
      case h =>
        simp
      simp only [map_sum, div_mul_eq_mul_div]
      rw [← sum_div, ← add_div]
      field_simp
      conv =>
        enter [2, 1, 2, x, 2]
        tactic =>
          change _ = ∑ e : K ≃ₐ[F] K, logDeriv (e (u x))
          by_cases h : u x = 0
          · rw [logDeriv_prod_of_eq_zero]
            simp [h]
          · simp [logDeriv_prod, h]
      simp_rw [mul_sum]
      rw [sum_comm, ← sum_add_distrib]
      trans ∑ _ : (K ≃ₐ[F] K), a
      · simp [mul_comm]
      · rcongr e
        apply_fun e at h
        simp only [AlgEquiv.commutes, map_add, map_sum, map_mul] at h
        convert h using 2
        · rcongr x
          simp [logDeriv, algEquiv_deriv']
        · rw [algEquiv_deriv']

instance liouville_algebraic_galois [FiniteDimensional F K] :
    IsLiouville F K :=
  let map := (IsAlgClosed.lift (M := AlgebraicClosure F) (R := F) (S := K))
  let K' := map.fieldRange
  haveI : FiniteDimensional F K' :=
    LinearMap.finiteDimensional_range map.toLinearMap
  let K'' := normalClosure F K' (AlgebraicClosure F)
  let B : IntermediateField F K'' := IntermediateField.restrict
    (F := K') (IntermediateField.le_normalClosure ..)
  have kequiv : K ≃ₐ[F] ↥B := (show K ≃ₐ[F] K' from AlgEquiv.ofInjectiveField map).trans
    (IntermediateField.restrict_algEquiv _)
  IsLiouville.equiv kequiv.symm

end Algebraic
