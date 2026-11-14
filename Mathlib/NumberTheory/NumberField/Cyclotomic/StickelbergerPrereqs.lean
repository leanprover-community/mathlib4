/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.AddCharacter.Trace
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.MulChar.Teichmuller
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Prerequisites for Stickelberger's theorem

This file gathers, for the time being, the results needed in
`Mathlib.NumberTheory.NumberField.Cyclotomic.Stickelberger` that are not yet in Mathlib. They are
meant to be moved to their proper places.
-/

public section

open NumberField

section Actions

theorem MulSemiringAction.toRingHom_mul {G R : Type*} [Monoid G] [Semiring R]
    [MulSemiringAction G R] (g h : G) :
    MulSemiringAction.toRingHom G R (g * h) =
      (MulSemiringAction.toRingHom G R g).comp (MulSemiringAction.toRingHom G R h) :=
  RingHom.ext fun x ↦ mul_smul g h x

theorem MulSemiringAction.toRingHom_one {G R : Type*} [Monoid G] [Semiring R]
    [MulSemiringAction G R] :
    MulSemiringAction.toRingHom G R 1 = RingHom.id R :=
  RingHom.ext fun x ↦ one_smul G x

/-- The multiplicity is invariant under a group acting by multiplicative automorphisms. -/
theorem multiplicity_smul {G α : Type*} [Group G] [Monoid α] [MulDistribMulAction G α] (g : G)
    {a b : α} : multiplicity (g • a) (g • b) = multiplicity a b :=
  multiplicity_map_eq (MulDistribMulAction.toMulEquiv α g)

/-- The multiplicity of a prime in a finite product is the sum of the multiplicities. -/
theorem Finset.multiplicity_prod {α β : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    {p : α} (hp : Prime p) (s : Finset β) (f : β → α) (hfin : FiniteMultiplicity p (∏ x ∈ s, f x)) :
    multiplicity p (∏ x ∈ s, f x) = ∑ x ∈ s, multiplicity p (f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has] at hfin
    rw [Finset.prod_insert has, Finset.sum_insert has, multiplicity_mul hp hfin,
      ih hfin.mul_right]

end Actions

section ZModFiniteField

/-- A ring homomorphism commutes with the cast from `ZMod n`. -/
theorem ZMod.map_cast {n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (k : ZMod n) :
    f (ZMod.cast k) = ZMod.cast k := by
  cases n
  · exact map_intCast f k
  · exact map_natCast f k.val

/-- The trace does not care whether the base ring is `ZMod p` or a ring isomorphic to it. -/
theorem ZMod.cast_trace_eq_trace {p : ℕ} {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] [Algebra (ZMod p) C] (e : A ≃+* ZMod p) (x : C) :
    ZMod.cast (Algebra.trace (ZMod p) C x) = Algebra.trace A C x := by
  have : Subsingleton (A →+* C) := ⟨fun f g ↦ RingHom.ext fun y ↦ by
    obtain ⟨z, rfl⟩ := e.symm.surjective y
    exact congr($(Subsingleton.elim (f.comp (e.symm : ZMod p →+* A)) (g.comp e.symm)) z)⟩
  rw [Algebra.trace_eq_of_equiv_equiv e (RingEquiv.refl C) (Subsingleton.elim _ _) x]
  exact e.eq_symm_apply.mpr (ZMod.ringHom_map_cast (e : A →+* ZMod p) _)

theorem ZMod.orderOf_pow_sub_one (a k : ℕ) (ha : 1 < a) :
    orderOf (a : ZMod (a ^ k - 1)) = k := by
  have key (n : ℕ) : (a : ZMod (a ^ k - 1)) ^ n = 1 ↔ k ∣ n := by
    rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod (a ^ k - 1)), ZMod.natCast_eq_natCast_iff,
      Nat.ModEq.comm, Nat.modEq_iff_dvd, ← Nat.cast_sub (Nat.one_le_pow _ _ (by lia : 0 < a)),
      Int.natCast_dvd_natCast, Nat.pow_sub_one_dvd_pow_sub_one_iff ha]
  exact Nat.dvd_antisymm (orderOf_dvd_iff_pow_eq_one.mpr ((key k).mpr dvd_rfl))
    ((key _).mp (pow_orderOf_eq_one _))

namespace FiniteField

open Finset

variable (K : Type*) [Field K] [Fintype K]

local notation "q" => Fintype.card K

/-- The sum of `x⁻¹ * x ^ (i + 1)` as `x` ranges over a finite field of cardinality `q` is equal
to `-1` if `q - 1 ∣ i`, and to `0` otherwise. -/
theorem sum_inv_mul_pow_succ (i : ℕ) :
    ∑ x : K, x⁻¹ * x ^ (i + 1) = if q - 1 ∣ i then -1 else 0 := by
  classical
  rw [Fintype.sum_eq_sum_compl_add 0, inv_zero, zero_mul, add_zero,
    sum_congr rfl (g := (· ^ i)), Fintype.sum_compl_zero, sum_pow_units K i]
  exact fun x hx ↦ by rw [pow_succ', inv_mul_cancel_left₀ (by simpa using hx)]

end FiniteField

end ZModFiniteField

section Arithmetic

/-- Euler's totient function as an arithmetic function with values in `ℤ`. -/
@[expose] def ArithmeticFunction.totient : ArithmeticFunction ℤ where
  toFun n := Nat.totient n
  map_zero' := by simp

@[simp]
theorem ArithmeticFunction.totient_apply (n : ℕ) :
    totient n = Nat.totient n := rfl

open Nat in
theorem ArithmeticFunction.isMultiplicative_totient :
    IsMultiplicative totient :=
  IsMultiplicative.iff_ne_zero.mpr ⟨by simp, fun _ _ h ↦ by simp [Nat.totient_mul h]⟩

theorem Nat.totient_lcm_mul_totient_gcd (m n : ℕ) :
    totient (lcm m n) * totient (gcd m n) = totient m * totient n := by
  have :=  ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply
    ArithmeticFunction.isMultiplicative_totient (x := m) (y := n)
  rwa [ArithmeticFunction.totient_apply, ArithmeticFunction.totient_apply,
    ArithmeticFunction.totient_apply, ArithmeticFunction.totient_apply, ← Nat.cast_mul,
    ← Nat.cast_mul, Nat.cast_inj] at this

theorem Nat.digits_base_pow_sub_one {b : ℕ} (hb : 1 < b) (l : ℕ) :
    b.digits (b ^ l - 1) = List.replicate l (b - 1) := by
  suffices b ^ l - 1 = Nat.ofDigits b (List.replicate l (b - 1)) by
    rw [this, Nat.digits_ofDigits _ hb _ (by grind) (by grind)]
  induction l with
    | zero => simp
    | succ l hl =>
        rw [List.replicate_succ, Nat.ofDigits_cons, ← hl, add_comm (b - 1), Nat.mul_sub, mul_one,
          ← Nat.pow_succ', ← Nat.add_sub_assoc hb.le,
          Nat.sub_add_cancel (Nat.le_self_pow l.succ_ne_zero b)]

theorem Nat.digits_eq_replicate_base_sub_one_iff {b : ℕ} (hb : 1 < b) {n k : ℕ} :
    b.digits n = List.replicate k (b - 1) ↔ n = b ^ k - 1 := by
  refine ⟨?_, fun h ↦ by rw [h, digits_base_pow_sub_one hb]⟩
  intro h
  have := congr_arg (Nat.ofDigits b) h
  rwa [ofDigits_digits, ← digits_base_pow_sub_one hb, ofDigits_digits] at this

theorem Nat.ofDigits_eq_base_pow_length_sub_one_iff {b : ℕ} {L : List ℕ} (hb : 1 < b)
    (hL : ∀ x ∈ L, x < b) :
    ofDigits b L = b ^ L.length - 1 ↔ L = List.replicate L.length (b - 1) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← (setInvOn_digitsAppend_ofDigits hb L.length).1 ⟨rfl, hL⟩,
      digitsAppend_eq_digits_iff_le.mpr,
      (digits_eq_replicate_base_sub_one_iff hb).mpr h,  List.length_replicate]
    rw [h, digits_base_pow_sub_one hb, List.length_replicate]
  · rw [← ofDigits_digits b (b ^ L.length - 1), digits_base_pow_sub_one hb L.length, ← h]

theorem Nat.ofDigits_eq_sum (b : ℕ) (L : List ℕ) :
    ofDigits b L = ∑ i : Fin L.length, L[i] * b ^ (i : ℕ) := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp [List.mapIdx_eq_zipIdx_map, ← Fin.sum_univ_fun_getElem,
    ← Fin.sum_congr' _ List.length_zipIdx.symm]

theorem Nat.ofDigits_digitsAppend (b l n : ℕ) : ofDigits b (digitsAppend b l n) = n := by
  rw [ofDigits_eq_sum_mapIdx, mapIdx_digitsAppend_sum_eq]

/-- Multiplying by `b` modulo `b ^ L.length - 1` rotates the digits of `L` to the right by one
place. -/
theorem Nat.base_mul_ofDigits_modEq {b : ℕ} (hb : 0 < b) (L : List ℕ) :
    b * ofDigits b L ≡ ofDigits b (L.rotate (L.length - 1)) [MOD b ^ L.length - 1] := by
  obtain rfl | ⟨L', c, rfl⟩ := L.eq_nil_or_concat
  · simp [Nat.ofDigits_nil]
  rw [List.concat_eq_append, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.rotate_append_length_eq, ofDigits_append, ofDigits_append, ofDigits_singleton,
    List.length_singleton, pow_one, mul_add, ← mul_assoc, ← pow_succ',
    ← Nat.sub_add_cancel (by grind : 1 ≤ b ^ L'.length.succ), add_mul, one_mul, ← add_assoc,
    ← add_rotate]
  exact add_modulus_mul_modEq_iff.mpr rfl

/-- Multiplying by `b ^ i` modulo `b ^ L.length - 1` rotates the digits of `L` to the right by `i`
places. -/
theorem Nat.base_pow_mul_ofDigits_modEq {b : ℕ} (hb : 0 < b) (L : List ℕ) {i : ℕ}
    (hi : i ≤ L.length) :
     b ^ i * ofDigits b L ≡ ofDigits b (L.rotate (L.length - i)) [MOD b ^ L.length - 1] := by
  induction i with
  | zero => simpa using ofDigits_modEq' b b _ rfl L
  | succ n hn =>
    have h := (Nat.ModEq.mul_left b (hn (by lia))).trans <|
      (List.length_rotate _ _) ▸ Nat.base_mul_ofDigits_modEq hb _
    rwa [← mul_assoc, ← pow_succ', List.rotate_rotate, tsub_add_eq_add_tsub (by lia),
      add_tsub_assoc_of_le (by lia), ← List.rotate_rotate, List.rotate_length,
      ← tsub_add_eq_tsub_tsub_swap] at h

theorem List.sum_getElem_rotate {R : Type*} [AddCommMonoid R] (L : List R) (x : Fin L.length) :
    ∑ i : Fin L.length, (L.rotate i)[x] = L.sum := by
  have : NeZero L.length := Fin.neZero x
  rw [← (Equiv.sum_comp (Equiv.addLeft x) fun i ↦ L[i]).trans (Fin.sum_univ_getElem L)]
  simp [Fin.val_add, List.getElem_rotate]

/-- Adding up all the rotations of `L` puts each digit once in each position. -/
theorem Nat.sum_ofDigits_rotate (b : ℕ) (L : List ℕ) :
    ∑ i ∈ Finset.range L.length, Nat.ofDigits b (L.rotate i) =
      L.sum * ∑ i ∈ Finset.range L.length, b ^ i := by
  simp_rw [Nat.ofDigits_eq_sum, ← Fin.sum_congr' _ (L.length_rotate _).symm, Fin.val_cast,
    Fin.getElem_fin, Fin.val_cast]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, Finset.sum_range, ← Fin.getElem_fin,  List.sum_getElem_rotate,
    Finset.mul_sum]

/-- If the digits of `L` are not all equal to `b - 1`, the same holds for any rotation of `L`. -/
theorem Nat.ofDigits_rotate_lt {b : ℕ} {L : List ℕ} (hb : 1 < b) (hL : ∀ x ∈ L, x < b)
    (hx : ofDigits b L < b ^ L.length - 1) (n : ℕ) :
    ofDigits b (L.rotate n) < b ^ L.length - 1 := by
  contrapose! hx
  obtain hl | hl := L.length.eq_zero_or_pos
  · simp [hl]
  refine le_of_eq ?_
  rw [eq_comm, ofDigits_eq_base_pow_length_sub_one_iff hb hL, ← List.rotate_eq_rotate,
    List.rotate_replicate, ← List.length_rotate _ n,
    ← ofDigits_eq_base_pow_length_sub_one_iff hb (by simpa [List.mem_rotate]),
    List.length_rotate, (LE.le.ge_iff_eq hx).mp]
  exact le_sub_one_of_lt <|
    List.length_rotate _ _ ▸ ofDigits_lt_base_pow_length hb (by simpa [List.mem_rotate])

theorem Nat.sub_one_mul_sum_mul_pow_mod_eq {b l x : ℕ} (hb : 1 < b) (hx : x < b ^ l - 1) :
    (b - 1) * ∑ i ∈ Finset.range l, x * b ^ i % (b ^ l - 1) =
      (b ^ l - 1) * (Nat.digits b x).sum := by
  let L := Nat.digitsAppend b l x
  have hl : (b.digitsAppend l x).length = l := by rw [length_digitsAppend hb _ (by lia)]
  calc
    _ = (b - 1) * ∑ i ∈ Finset.range l, b ^ i * ofDigits b L % (b ^ l - 1) := by
      simp_rw [mul_comm x, L, ofDigits_digitsAppend b l x]
    _ = (b - 1) * ∑ i ∈ Finset.range l, ofDigits b (L.rotate (L.length - i)) := by
      refine congr_arg ((b - 1) * ·) <| Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← hl, base_pow_mul_ofDigits_modEq (by lia) _ (by grind)]
      refine mod_eq_of_lt (ofDigits_rotate_lt hb (fun _ hx ↦ lt_of_mem_digitsAppend hb _ _ hx) ?_ _)
      rwa [ofDigits_digitsAppend, hl]
    _ = (b - 1) * ∑ i ∈ Finset.range l, ofDigits b (L.rotate i) := by
      rw [Finset.sum_range, Finset.sum_range]
      nth_rewrite 2 [← Equiv.sum_comp (Equiv.neg (Fin _))]
      congr with i
      rw [Equiv.neg_apply, Fin.val_neg', ← List.rotate_mod L, hl]
    _ = L.sum * (∑ i ∈ Finset.range L.length, b ^ i) * (b - 1) := by
      rw [← sum_ofDigits_rotate, mul_comm, hl]
    _ = (b ^ l - 1) * (b.digits x).sum := by
      rw [digitsAppend_sum_eq_digits_sum, mul_assoc, geom_sum_mul_of_one_le hb.le, hl, mul_comm]

end Arithmetic

section FieldTheory

theorem smul_eq_galRestrict_apply (A : Type*) {K L B : Type*} [CommRing A] [Field K] [Field L]
    [CommRing B] [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L] [MulSemiringAction Gal(L/K) B]
    [SMulDistribClass Gal(L/K) B L] (σ : Gal(L/K)) (x : B) :
    σ • x = galRestrict A K L B σ x := by
  apply FaithfulSMul.algebraMap_injective B L
  rw [algebraMap.smul', AlgEquiv.smul_def, algebraMap_galRestrict_apply]

@[simp]
theorem IsFractionRing.map_algebraMap {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [CommRing L] [Algebra B L] [IsFractionRing B L]
    {j : A →+* B} (hj : Function.Injective j) (x : A) :
    IsFractionRing.map hj (algebraMap A K x) = algebraMap B L (j x) := by simp [map]

theorem IntermediateField.linearDisjoint_iff_linearDisjoint_fieldRange {F E : Type*} [Field F]
    [Field E] [Algebra F E] (A : IntermediateField F E) (L : Type*) [Field L] [Algebra F L]
    [Algebra L E] [IsScalarTower F L E] :
    A.LinearDisjoint L ↔ A.LinearDisjoint (IsScalarTower.toAlgHom F L E).fieldRange := by
  rw [linearDisjoint_iff', AlgHom.fieldRange_toSubalgebra]

open Module in
lemma IntermediateField.finrank_sup_eq_of_inf_eq_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) [IsGalois F K] [FiniteDimensional F K] [FiniteDimensional F L]
    [Algebra K ↑(K ⊔ L)] [IsScalarTower F K ↑(K ⊔ L)] (hinf : K ⊓ L = ⊥) :
    finrank K ↑(K ⊔ L) = finrank F L := by
  rw [← mul_right_inj', ← (LinearDisjoint.of_inf_eq_bot hinf).finrank_sup, finrank_mul_finrank]
  exact finrank_pos.ne'

set_option maxHeartbeats 500000 in
-- The proof goes through several `extendScalars` and `inclusion` algebra structures.
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
open Module in
theorem IntermediateField.finrank_sup_mul_finrank_inf_eq {k L : Type*} [Field k] [Field L] [Algebra
  k L]
    (E F : IntermediateField k L) [FiniteDimensional k E] [FiniteDimensional k F] [IsGalois k E] :
    finrank k ↑(E ⊔ F) * finrank k ↑(E ⊓ F) = finrank k E * finrank k F := by
  let : Algebra E ↑(E ⊔ F) := (inclusion le_sup_left).toRingHom.toAlgebra
  have : FiniteDimensional k ↑(E ⊓ F) := FiniteDimensional.of_injective
    (IntermediateField.inclusion inf_le_left).toLinearMap
    (RingHom.injective _)
  suffices h : finrank E ↑(E ⊔ F) = finrank ↑(E ⊓ F) F by
    rwa [← finrank_mul_finrank k E ↑(E ⊔ F), ← finrank_mul_finrank k ↑(E ⊓ F) F, mul_assoc,
      mul_right_inj' finrank_pos.ne', mul_comm, mul_right_inj' finrank_pos.ne']
  let : Algebra ↑(E ⊓ F) ↑(E ⊔ F) := (inclusion inf_le_sup).toRingHom.toAlgebra
  have : IsScalarTower ↑(E ⊓ F) E ↑(E ⊔ F) := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional ↑(E ⊓ F) E := FiniteDimensional.right k _ _
  have : FiniteDimensional ↑(E ⊓ F) F := FiniteDimensional.right k _ _
  have : finrank ↑(E ⊓ F) E ≠ 0 := finrank_pos.ne'
  rw [← mul_right_inj' this, finrank_mul_finrank]
  let E' : IntermediateField ↑(E ⊓ F) L := E.extendScalars (F := E ⊓ F) inf_le_left
  let F' : IntermediateField ↑(E ⊓ F) L := F.extendScalars (F := E ⊓ F) inf_le_right
  let : Algebra E' ↑(E' ⊔ F') := (inclusion le_sup_left).toRingHom.toAlgebra
  let e' : E ≃ₐ[↑(E ⊓ F)] E' := AlgEquiv.refl
  let f' : F ≃ₐ[↑(E ⊓ F)] F' := AlgEquiv.refl
  let h : ↑(E' ⊔ F') ≃ₗ[↑(E ⊓ F)] ((E ⊔ F).extendScalars (F := E ⊓ F) inf_le_sup) :=
    LinearEquiv.ofEq ↑(E' ⊔ F').toSubalgebra.toSubmodule
      ((E ⊔ F).extendScalars (F := E ⊓ F) inf_le_sup).toSubalgebra.toSubmodule
        (by simpa using (extendScalars_sup (F := E ⊓ F) inf_le_left inf_le_right))
  have : IsGalois ↑(E ⊓ F) E' := by
    have : IsGalois ↑(E ⊓ F) E := IsGalois.tower_top_of_isGalois k _ _
    exact IsGalois.of_algEquiv e'
  have : FiniteDimensional ↑(E ⊓ F) E' := Module.Finite.equiv e'.toLinearEquiv
  have : FiniteDimensional ↑(E ⊓ F) F' := Module.Finite.equiv f'.toLinearEquiv
  calc finrank ↑(E ⊓ F) ↑(E ⊔ F)
      = finrank ↑(E ⊓ F) ↑(E' ⊔ F') := ?_
    _ = finrank ↑(E ⊓ F) E' * finrank E' ↑(E' ⊔ F') := by rw [finrank_mul_finrank]
    _ = finrank ↑(E ⊓ F) E * finrank E' ↑(E' ⊔ F') := by rw [e'.toLinearEquiv.finrank_eq]
    _ = finrank ↑(E ⊓ F) E * finrank ↑(E ⊓ F) F' := by
        rw [← finrank_sup_eq_of_inf_eq_bot E' F']
        ext; simp [E', F', mem_bot]
    _ = finrank ↑(E ⊓ F) E * finrank ↑(E ⊓ F) F := by rw [f'.toLinearEquiv.finrank_eq]
  · rw [LinearEquiv.finrank_eq (M := ↑(E ⊔ F)) (N := ↑(E' ⊔ F'))]
    exact (LinearEquiv.refl ↑(E ⊓ F) ↑(E ⊔ F)).trans h.symm

/-- `restrictHom` is `AlgEquiv.restrictNormal`. -/
theorem IsGaloisGroup.restrictHom_eq_restrictNormal (K E L : Type*) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [FiniteDimensional K L]
    [FiniteDimensional K E] [IsGalois K L] [IsGalois K E] (σ : Gal(L/K)) :
    IsGaloisGroup.restrictHom Gal(L/K) Gal(E/K) K E L σ = σ.restrictNormal E := by
  ext x
  apply (algebraMap E L).injective
  rw [← AlgEquiv.smul_def, IsGaloisGroup.algebraMap_restrictHom_smul, AlgEquiv.smul_def,
    AlgEquiv.restrictNormal_commutes]

section restrictHom_eq

variable (G G' A B C A' B' C' : Type*) [Group G] [Group G'] [Finite G] [Finite G']
  [CommRing A] [CommRing B] [CommRing C] [IsDomain C] [Algebra A B] [Algebra A C] [Algebra B C]
  [IsScalarTower A B C] [FaithfulSMul B C]
  [MulSemiringAction G C] [IsGaloisGroup G A C] [MulSemiringAction G' B] [IsGaloisGroup G' A B]
  [CommRing A'] [CommRing B'] [CommRing C'] [IsDomain C'] [Algebra A' B'] [Algebra A' C']
  [Algebra B' C'] [IsScalarTower A' B' C'] [FaithfulSMul B' C']
  [MulSemiringAction G C'] [IsGaloisGroup G A' C'] [MulSemiringAction G' B']
  [IsGaloisGroup G' A' B']
  [Algebra B B'] [Algebra C C'] [Algebra B C'] [IsScalarTower B B' C'] [IsScalarTower B C C']
  [FaithfulSMul B B'] [SMulDistribClass G C C'] [SMulDistribClass G' B B']

/-- `restrictHom` does not depend on the tower `C/B/A` used to define it, as long as the
actions of `G` and `G'` are compatible with the maps `B → B'` and `C → C'`. -/
theorem IsGaloisGroup.restrictHom_eq_restrictHom :
    IsGaloisGroup.restrictHom G G' A B C = IsGaloisGroup.restrictHom G G' A' B' C' := by
  ext g
  have : FaithfulSMul G' B := IsGaloisGroup.faithful A
  refine eq_of_smul_eq_smul (α := B) fun x ↦ ?_
  apply FaithfulSMul.algebraMap_injective B B'
  apply FaithfulSMul.algebraMap_injective B' C'
  rw [← IsScalarTower.algebraMap_apply B B' C', IsScalarTower.algebraMap_apply B C C',
    IsGaloisGroup.algebraMap_restrictHom_smul, algebraMap.smul',
    ← IsScalarTower.algebraMap_apply B C C', algebraMap.smul',
    IsGaloisGroup.algebraMap_restrictHom_smul, ← IsScalarTower.algebraMap_apply B B' C']

end restrictHom_eq

end FieldTheory

section Ideals

namespace Ideal

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Module.Free ℤ S]
  [Module.Finite ℤ S]

/-- A rational prime `p` dividing `absNorm I` lies under a maximal ideal containing `I`. -/
theorem exists_isMaximal_le_of_prime_dvd_absNorm {p : ℕ} (hp : p.Prime) {I : Ideal S}
    (hpI : p ∣ I.absNorm) : ∃ P : Ideal S, P.IsMaximal ∧ I ≤ P ∧ (p : S) ∈ P := by
  obtain ⟨P, hPmax, hPunder, hPI⟩ := exists_isMaximal_dvd_of_dvd_absNorm' hp I hpI
  refine ⟨P, hPmax, Ideal.dvd_iff_le.mp hPI, ?_⟩
  have hmem : (p : ℤ) ∈ P.under ℤ := hPunder ▸ mem_span_singleton_self (p : ℤ)
  rw [mem_under] at hmem
  simpa using hmem

/-- If `I` is coprime to the ideal `(n)` for `n : ℕ`, then `absNorm I` is coprime to `n`. -/
theorem coprime_absNorm_of_isCoprime_span_singleton {n : ℕ} {I : Ideal S}
    (h : IsCoprime I (Ideal.span {(n : S)})) : Nat.Coprime I.absNorm n := by
  by_contra hc
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hc
  obtain ⟨P, hPmax, hIP, hpP⟩ :=
    exists_isMaximal_le_of_prime_dvd_absNorm hp (hpg.trans (Nat.gcd_dvd_left _ _))
  refine hPmax.ne_top (top_le_iff.mp ?_)
  rw [← Ideal.isCoprime_iff_sup_eq.mp h]
  refine sup_le hIP ((span_singleton_le_iff_mem _).mpr ?_)
  obtain ⟨c, hc'⟩ : (p : S) ∣ (n : S) := Nat.cast_dvd_cast (hpg.trans (Nat.gcd_dvd_right _ _))
  rw [hc']
  exact mul_mem_right c P hpP

end Ideal

theorem Ideal.pow_liesOver_of_le_ramificationIdx {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) (P : Ideal S) [P.LiesOver p]
    {i : ℕ} (hi : i + 1 ≤ Ideal.ramificationIdx' p P) :
    (P ^ (i + 1)).LiesOver p := by
  rw [liesOver_iff]
  apply le_antisymm
  · exact le_trans le_comap_pow_ramificationIdx' <| comap_mono (pow_le_pow_right hi)
  · refine le_trans (comap_mono <| pow_le_pow_right (Nat.le_add_left 1 i)) ?_
    rw [pow_one, ← Ideal.under_def, ← Ideal.over_def P p]

instance Ideal.Quotient.isScalarTower_of_liesOver_liesOver {A B C : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] (Q : Ideal C)
    (P : Ideal B) (p : Ideal A) [Q.LiesOver P] [P.LiesOver p] [Q.LiesOver p] :
    IsScalarTower (A ⧸ p) (B ⧸ P) (C ⧸ Q) := by
  refine IsScalarTower.of_algebraMap_eq fun x ↦ Quotient.inductionOn' x fun x ↦ ?_
  have : Quotient.mk'' x = Ideal.Quotient.mk p x := rfl
  simp [this, Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]

theorem Ideal.prime_of_isMaximal {R : Type*} [CommRing R] [CharZero R]
    [Algebra.IsIntegral ℤ R] [IsDedekindDomain R] (I : Ideal R) [I.IsMaximal] :
    Prime I := by
  refine (prime_iff_isPrime (IsMaximal.ne_bot_of_isIntegral_int I)).mpr <| IsMaximal.isPrime' I

theorem Ideal.liesOver_of_absNorm_dvd_prime_pow {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra.IsIntegral ℤ R] (I : Ideal R) [I.IsPrime] {p k : ℕ}
    [hp : Fact (Nat.Prime p)] (hI : Ideal.absNorm I ∣ p ^ k) :
    I.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : NeZero I := ⟨by
    contrapose hI
    rw [hI, map_zero, Nat.zero_dvd]
    exact NeZero.ne (p ^ k)⟩
  have := (Int.absNorm_under_dvd_absNorm I).trans hI
  rw [Ideal.liesOver_iff, ← Nat.prime_eq_prime_of_dvd_pow (Nat.absNorm_under_prime I)
    hp.out this, Int.ideal_span_absNorm_eq_self]

namespace Ideal

variable {R : Type*} (A : Type*) (B : Type*) [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (p : Ideal R)

/-- In a tower `A/B/R`, the primes of `B` over `p` correspond to the pairs `(P, 𝔓)` with `P` a
prime of `A` over `p` and `𝔓` a prime of `B` over `P`. -/
@[expose] def equivPrimesOverPrimesOver :
    p.primesOver B ≃ Σ P : p.primesOver A, P.1.primesOver B where
  toFun 𝔓 := ⟨primesOver.mk p (𝔓.1.under A), primesOver.mk _ 𝔓.1⟩
  invFun P :=
    have := LiesOver.trans P.2.1 P.1.1 p
    primesOver.mk p P.2.1
  right_inv P := Sigma.subtype_ext (Subtype.ext (over_def P.2.1 P.1.1).symm) rfl

@[simp]
theorem coe_equivPrimesOverPrimesOver_symm_apply (x : Σ P : p.primesOver A, P.1.primesOver B) :
    ((equivPrimesOverPrimesOver A B p).symm x : Ideal B) = x.2 :=
  rfl

end Ideal

end Ideals

section ClassGroupAction

namespace FractionalIdeal

noncomputable section ExtendedAction

variable {R : Type*} [CommRing R] {S : Submonoid R} (P : Type*) [CommRing P] [Algebra R P]
  [IsLocalization S P]

theorem extended_id (I : FractionalIdeal S P) :
    I.extended P (f := RingHom.id R)
      (fun _ h ↦ Submonoid.mem_comap.mpr h : S ≤ S.comap (RingHom.id R)) = I := by
  simp only [← coeToSubmodule_inj, coeToSubmodule_extended_eq_span, IsLocalization.map_id,
    Set.image_id']
  exact Submodule.span_eq _

theorem canonicalEquiv_apply (P' : Type*) [CommRing P'] [Algebra R P'] [IsLocalization S P']
    (I : FractionalIdeal S P) :
    canonicalEquiv S P P' I = map (IsLocalization.algEquiv S P P').toAlgHom I := by
  ext; simp

theorem canonicalEquiv_eq_extended (P' : Type*) [CommRing P'] [Algebra R P'] [IsLocalization S P']
    (I : FractionalIdeal S P) :
    canonicalEquiv S P P' I = I.extended P'
      (fun _ h ↦ Submonoid.mem_comap.mpr h : S ≤ S.comap (RingHom.id R)) := by
  rw [canonicalEquiv_apply, ← coeToSubmodule_inj, coe_map, coeToSubmodule_extended_eq_span,
    ← Submodule.span_eq (Submodule.map _ _)]
  rfl

variable {G : Type*} [Group G] [MulSemiringAction G R]
  (hS : ∀ g : G, S ≤ S.comap (MulSemiringAction.toRingHom G R g))

/-- The `G`-action on `FractionalIdeal S P` by extension along `MulSemiringAction.toRingHom`. -/
abbrev extendedSMul : SMul G (FractionalIdeal S P) where
  smul g I := I.extended P (hS g)

theorem extendedSMul_def (g : G) (I : FractionalIdeal S P) :
    letI := extendedSMul P hS
    g • I = I.extended P (hS g) := rfl

/-- The `G`-action on `FractionalIdeal S P` induced by an action on `R` preserving `S`. -/
abbrev extendedMulDistribMulAction : MulDistribMulAction G (FractionalIdeal S P) :=
{ __ := extendedSMul P hS
  smul_one _ := extended_one _ _
  one_smul I := by
    simp_rw [extendedSMul_def, MulSemiringAction.toRingHom_one]
    exact extended_id _ I
  smul_mul _ _ _ := extended_mul _ _ _ _
  mul_smul g h I := by
    simp_rw [extendedSMul_def, MulSemiringAction.toRingHom_mul]
    exact (extended_extended _ (hS h) I (hS g)).symm }

end ExtendedAction

section FractionField

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]
  {K : Type*} [CommRing K] [Algebra R K] [IsFractionRing R K]

/-- The `G`-action on `R` induces a `G`-action on the fractional ideals of `K`. -/
noncomputable instance : MulDistribMulAction G (FractionalIdeal R⁰ K) :=
  extendedMulDistribMulAction _
    fun g _ hs ↦ Submonoid.mem_comap.mpr (smul_mem_nonZeroDivisors g hs)

theorem smul_def (g : G) (I : FractionalIdeal R⁰ K) :
    g • I = I.extended K (f := MulSemiringAction.toRingHom G R g) (N := R⁰)
      (fun _ hs ↦ Submonoid.mem_comap.mpr (smul_mem_nonZeroDivisors g hs)) := rfl

theorem canonicalEquiv_smul (K' : Type*) [CommRing K'] [Algebra R K'] [IsFractionRing R K'] (g : G)
    (I : FractionalIdeal R⁰ K) :
    canonicalEquiv R⁰ K K' (g • I) = g • canonicalEquiv R⁰ K K' I := by
  rw [canonicalEquiv_eq_extended, canonicalEquiv_eq_extended, smul_def, smul_def,
    extended_extended, extended_extended]

open scoped Pointwise in
/-- The coercion `Ideal R → FractionalIdeal R⁰ K` is `G`-equivariant: the action on ideals and the
action on fractional ideals are compatible. -/
@[simp]
theorem coeIdeal_smul (g : G) (I : Ideal R) :
    (↑(g • I) : FractionalIdeal R⁰ K) = g • (I : FractionalIdeal R⁰ K) := by
  rw [smul_def, extended_coeIdeal_eq_map, Ideal.pointwise_smul_def]

variable [MulSemiringAction G K] [SMulDistribClass G R K]

/-- The localization of `toRingHom G R g` is the action of `g` on `K`. -/
theorem _root_.IsLocalization.map_toRingHom_apply (g : G) (x : K) :
    IsLocalization.map K (MulSemiringAction.toRingHom G R g)
      (fun _ hs ↦ Submonoid.mem_comap.mpr (smul_mem_nonZeroDivisors g hs) :
        R⁰ ≤ R⁰.comap (MulSemiringAction.toRingHom G R g)) x = g • x :=
  RingHom.congr_fun (g := MulSemiringAction.toRingHom G K g)
    (IsLocalization.ringHom_ext R⁰ <| RingHom.ext fun a ↦ by
      simp [algebraMap.smul']) x

/-- The action on fractional ideals is compatible with `spanSingleton`. -/
theorem spanSingleton_smul (g : G) (x : K) :
    g • spanSingleton R⁰ x = spanSingleton R⁰ (g • x) := by
  rw [smul_def, extended_spanSingleton, IsLocalization.map_toRingHom_apply]

end FractionField

end FractionalIdeal

namespace ClassGroup

open scoped nonZeroDivisors Pointwise

open FractionalIdeal

variable {G R : Type*} [Group G] [CommRing R] [IsDedekindDomain R] [MulSemiringAction G R]

noncomputable instance : MulSemiringAction G (FractionRing R) :=
  IsFractionRing.mulSemiringAction G R (FractionRing R)

attribute [local instance] Units.mulDistribMulActionRight

/-- The `G`-action on fractional ideals preserves the principal ideals. -/
theorem principalIdeals_le_comap (g : G) :
    (toPrincipalIdeal R (FractionRing R)).range ≤
      (toPrincipalIdeal R (FractionRing R)).range.comap
        (MulDistribMulAction.toMulAut G (FractionalIdeal R⁰ (FractionRing R))ˣ g).toMonoidHom := by
  intro I hI
  rw [mem_principal_ideals_iff] at hI
  obtain ⟨x, hx⟩ := hI
  rw [Subgroup.mem_comap, mem_principal_ideals_iff]
  exact ⟨g • x, by rw [← spanSingleton_smul, hx]; rfl⟩

/-- The action of `g` on the class group, as a group homomorphism: descend the pointwise action
on the units of fractional ideals along the quotient by principal ideals. -/
@[expose] noncomputable def mapAut (g : G) : ClassGroup R →* ClassGroup R :=
  QuotientGroup.map (toPrincipalIdeal R (FractionRing R)).range
    (toPrincipalIdeal R (FractionRing R)).range
    (MulDistribMulAction.toMulAut G _ g).toMonoidHom (principalIdeals_le_comap g)

noncomputable instance : SMul G (ClassGroup R) where
  smul g := mapAut g

theorem smul_mk (g : G) (u : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    g • ClassGroup.mk (FractionRing R) u = ClassGroup.mk (FractionRing R) (g • u) := by
  rw [← Quot_mk_eq_mk, ← Quot_mk_eq_mk]
  rfl

theorem smul_mk' {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (g : G)
    (u : (FractionalIdeal R⁰ K)ˣ) :
    g • ClassGroup.mk K u = ClassGroup.mk K (g • u) := by
  rw [← mk_canonicalEquiv K (FractionRing R), smul_mk, ← mk_canonicalEquiv K (FractionRing R)]
  congr
  simp [Units.ext_iff, canonicalEquiv_smul]

theorem _root_.FractionalIdeal.smul_mk0 {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (g : G) (I : (Ideal R)⁰) :
    g • FractionalIdeal.mk0 K I = FractionalIdeal.mk0 K (g • I) := by
  ext1
  rw [Units.coe_smul, coe_mk0, coe_mk0, nonZeroDivisors.val_smul, coeIdeal_smul]

theorem smul_mk0 (g : G) (I : (Ideal R)⁰) : g • mk0 I = mk0 (g • I) := by
  rw [← mk_mk0 (K := FractionRing R), smul_mk, FractionalIdeal.smul_mk0, mk_mk0]

noncomputable instance : MulDistribMulAction G (ClassGroup R) where
  one_smul c := by
    obtain ⟨I, rfl⟩ := mk0_surjective c
    rw [smul_mk0, one_smul]
  mul_smul g h c := by
    obtain ⟨I, rfl⟩ := mk0_surjective c
    rw [smul_mk0, smul_mk0, smul_mk0, mul_smul]
  smul_one g := map_one (mapAut g)
  smul_mul g c d := map_mul (mapAut g) c d

end ClassGroup

end ClassGroupAction

section Cyclotomic

instance {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    HasEnoughRootsOfUnity (𝓞 K) n :=
  ⟨⟨_, (IsCyclotomicExtension.zeta_spec n ℚ K).toInteger_isPrimitiveRoot⟩, inferInstance⟩

theorem NumberField.isUnit_iff_natAbs_norm {K : Type*} [Field K] [NumberField K] {x :
  RingOfIntegers K} :
    IsUnit x ↔ (Algebra.norm ℤ x).natAbs = 1 := by
  rw [isUnit_iff_norm, ← Rat.natCast_injective.eq_iff, RingOfIntegers.coe_norm,
    Nat.cast_natAbs, Nat.cast_one, ← Algebra.coe_norm_int, Int.cast_abs]

theorem IsPrimitiveRoot.isIntegral' {n : ℕ} {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
    {μ : L} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) :
    IsIntegral K μ :=
  IsIntegral.tower_top (h.isIntegral hpos)

open NumberField in
theorem IsCyclotomicExtension.Rat.isCoprime_discr_of_coprime (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (K₁ K₂ : Type*) [Field K₁] [Field K₂] [NumberField K₁] [NumberField K₂]
    [IsCyclotomicExtension {n₁} ℚ K₁] [IsCyclotomicExtension {n₂} ℚ K₂] (h : n₁.Coprime n₂) :
    IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) := by
  rw [Int.isCoprime_iff_nat_coprime, natAbs_discr  n₁ K₁, natAbs_discr  n₂ K₂]
  refine Nat.Coprime.coprime_div_left ?_ (Nat.prod_primeFactors_pow_totient_ediv_dvd _)
  refine Nat.Coprime.coprime_div_right ?_ (Nat.prod_primeFactors_pow_totient_ediv_dvd _)
  exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ h)

theorem IsCyclotomicExtension.Rat.linearDisjoint_of_coprime (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    {E : Type*} [Field E] [NumberField E] (K₁ : IntermediateField ℚ E) [NumberField K₁] (K₂ : Type*)
    [Field K₂] [NumberField K₂] [Algebra K₂ E] [IsCyclotomicExtension {n₁} ℚ K₁]
    [IsCyclotomicExtension {n₂} ℚ K₂] (h : n₁.Coprime n₂) :
    K₁.LinearDisjoint K₂ := by
  have : IsCyclotomicExtension {n₂} ℚ (IsScalarTower.toAlgHom ℚ K₂ E).fieldRange :=
    .equiv _ ℚ K₂ (IsScalarTower.toAlgHom ℚ K₂ E).equivFieldRange
  have : IsGalois ℚ K₁ := IsCyclotomicExtension.isGalois {n₁} ℚ K₁
  rw [IntermediateField.linearDisjoint_iff_linearDisjoint_fieldRange]
  exact NumberField.linearDisjoint_of_isGalois_isCoprime_discr E _ _ <|
    isCoprime_discr_of_coprime n₁ n₂ K₁ _ h

open IntermediateField in
set_option backward.isDefEq.respectTransparency false in
theorem IsCyclotomicExtension.Rat.gcd_inf {K : Type*} [Field K] [NumberField K]
    (n₁ n₂ : ℕ) (F₁ F₂ : IntermediateField ℚ K) [h₁ : IsCyclotomicExtension {n₁} ℚ F₁]
    [h₂ : IsCyclotomicExtension {n₂} ℚ F₂] [NeZero n₁] [NeZero n₂] :
    IsCyclotomicExtension {n₁.gcd n₂} ℚ ↑(F₁ ⊓ F₂) := by
  let d := n₁.gcd n₂
  have : NeZero d := ⟨Nat.gcd_ne_zero_left (NeZero.ne _)⟩
  have : NeZero (n₁.lcm n₂) := ⟨Nat.lcm_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  obtain ⟨ζ₁, hζ₁⟩ := h₁.1 rfl (NeZero.ne n₁)
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective F₁ K)
  obtain ⟨s, hs⟩ := n₁.gcd_dvd_left n₂
  let ζ := (algebraMap F₁ K ζ₁) ^ s
  have hζ : IsPrimitiveRoot ζ d := hζ₁.pow (NeZero.pos n₁) (by rwa [mul_comm])
  have : IsCyclotomicExtension {d} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  rw [isCyclotomicExtension_singleton_iff_eq_adjoin d ℚ K _ hζ, eq_comm]
  rw [eq_iff_finrank_eq_of_le]
  · have : IsGalois ℚ F₁ := h₁.isGalois
    have := isCyclotomicExtension_lcm_sup ℚ K n₁ n₂ F₁ F₂
    have : Module.finrank ℚ ↑(F₁ ⊔ F₂) ≠ 0 := Module.finrank_pos.ne'
    rw [← mul_right_inj' this, finrank_sup_mul_finrank_inf_eq,
      IsCyclotomicExtension.Rat.finrank n₁ F₁,
      IsCyclotomicExtension.Rat.finrank n₂ F₂,
        IsCyclotomicExtension.Rat.finrank (n₁.lcm n₂) ↑(F₁ ⊔ F₂),
      IsCyclotomicExtension.Rat.finrank d ℚ⟮ζ⟯, Nat.totient_lcm_mul_totient_gcd]
  · obtain ⟨ζ₂, hζ₂⟩ := h₂.1 rfl (NeZero.ne n₂)
    replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective F₂ K)
    rw [(isCyclotomicExtension_singleton_iff_eq_adjoin n₁ ℚ K _ hζ₁).mp h₁,
      (isCyclotomicExtension_singleton_iff_eq_adjoin n₂ ℚ K _ hζ₂).mp h₂, adjoin_simple_le_iff,
        mem_inf]
    constructor
    · exact pow_mem (mem_adjoin_simple_self ℚ _) s
    · obtain ⟨t, _,
      ht⟩ := hζ₂.eq_pow_of_pow_eq_one <| (hζ.pow_eq_one_iff_dvd n₂).mpr (n₁.gcd_dvd_right n₂)
      rw [← ht]
      exact pow_mem (mem_adjoin_simple_self ℚ _) t

open IsCyclotomicExtension.Rat in
theorem IsCyclotomicExtension.Rat.map_galEquivZMod_symm_apply {E F : Type*} [Field E] [Field F]
    [NumberField E] [NumberField F] {n : ℕ} [NeZero n] [hE : IsCyclotomicExtension {n} ℚ E]
    [hF : IsCyclotomicExtension {n} ℚ F] (f : E →+* F) (a : (ZMod n)ˣ) (x : E) :
    f ((galEquivZMod n E).symm a x) = (galEquivZMod n F).symm a (f x) := by
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ E
  have hζp := IsCyclotomicExtension.zeta_pow n ℚ E
  suffices f.toRatAlgHom.comp ((galEquivZMod n E).symm a) =
    ((galEquivZMod n F).symm a).toAlgHom.comp f.toRatAlgHom from AlgHom.congr_fun this x
  refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ) ?_
  simp only [Set.eqOn_singleton, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, RingHom.toRatAlgHom_apply,
    Function.comp_apply]
  rw [galEquivZMod_apply_of_pow_eq n _ _ hζp,
    galEquivZMod_apply_of_pow_eq n _ _ (by rw [← map_pow, hζp, map_one]), map_pow,
    MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

open IsCyclotomicExtension.Rat in
theorem IsCyclotomicExtension.Rat.map_galEquivZMod_symm_smul {E F : Type*} [Field E] [Field F]
    [NumberField E] [NumberField F] {n : ℕ} [NeZero n]
    [hE : IsCyclotomicExtension {n} ℚ E] [hF : IsCyclotomicExtension {n} ℚ F]
    {f : 𝓞 E →+* 𝓞 F} (hf : Function.Injective f) (a : (ZMod n)ˣ) (x : 𝓞 E) :
    f ((galEquivZMod n E).symm a • x) = (galEquivZMod n F).symm a • (f x) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 F) F
  rw [← IsFractionRing.map_algebraMap (K := E) hf]
  have := map_galEquivZMod_symm_apply (F := F) (IsFractionRing.map hf) a (algebraMap (𝓞 E) E x)
  rwa [IsFractionRing.map_algebraMap] at this

end Cyclotomic

section Stickelberger

noncomputable section

local instance {p f : ℕ} [hp : Fact p.Prime] [NeZero f] : NeZero (p ^ f - 1) :=
  ⟨Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (NeZero.ne f) hp.out.one_lt)⟩

local instance {p f : ℕ} [hp : Fact p.Prime] [NeZero f] : Fact ((p ^ f - 1).Coprime p) := ⟨by
  rw [← Nat.coprime_pow_right_iff (NeZero.pos f), Nat.coprime_self_sub_left NeZero.one_le]
  exact Nat.gcd_one_left _⟩

namespace Stickelberger

open Ideal NumberField IntermediateField IsDedekindDomain

variable {p : ℕ} (n : ℕ)

local notation3 "𝒑" => span {(p : ℤ)}

variable {L : Type*} [Field L] [NumberField L] {K F : IntermediateField ℚ L}

variable (P : Ideal (𝓞 K)) (𝓟 : Ideal (𝓞 L)) [P.HasTeichmullerLift n]

variable {ζ : 𝓞 F} (hζ : IsPrimitiveRoot ζ p)

attribute [local instance] ZMod.algebra

attribute [local instance] Ideal.Quotient.field

variable {P 𝓟} in
theorem cast_trace_eq_algebraMap_trace [P.LiesOver 𝒑] [CharP (𝓞 K ⧸ P) p]
    [Algebra (ℤ ⧸ 𝒑) (𝓞 L ⧸ 𝓟 ^ 2)] (x : 𝓞 K ⧸ P) :
    (Algebra.trace (ZMod p) (𝓞 K ⧸ P) x).cast =
      algebraMap _ (𝓞 L ⧸ 𝓟 ^ 2) (Algebra.trace (ℤ ⧸ 𝒑) (𝓞 K ⧸ P) x) := by
  rw [← ZMod.cast_trace_eq_trace (Int.quotientSpanNatEquivZMod p), ZMod.map_cast]

section Teichmuller

variable {n P} [NeZero n] [IsCyclotomicExtension {n} ℚ K]

protected theorem teichmuller_ne_one (hn : n ≠ 1) :
    MulChar.teichmuller P n ≠ 1 :=
  fun h ↦ hn (by rw [← MulChar.orderOf_teichmuller (I := P) (n := n), h, orderOf_one])

theorem ringHomComp_teichmuller_zpow_ne_one {a : ℤ}
    (ha : ¬ (n : ℤ) ∣ a) :
    (MulChar.teichmuller P n ^ a).ringHomComp (algebraMap (𝓞 K) (𝓞 L)) ≠ 1 := by
  rw [MulChar.ringHomComp_ne_one_iff]
  · rwa [ne_eq, ← orderOf_dvd_iff_zpow_eq_one, MulChar.orderOf_teichmuller]
  · exact RingOfIntegers.algebraMap.injective K L

end Teichmuller

section

variable [hp : Fact p.Prime] [IsCyclotomicExtension {p} ℚ F]
    [P.LiesOver (span {(p : ℤ)})]

include hζ in
theorem zeta_sub_one_mem [𝓟.IsPrime] [𝓟.LiesOver 𝒑] : algebraMap (𝓞 F) (𝓞 L) ζ - 1 ∈ 𝓟 := by
  rw [← map_one (f := algebraMap (𝓞 F) (𝓞 L)), ← map_sub, ← mem_comap,
    ← Ideal.under_def, IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p F
      (IsPrimitiveRoot.coe_submonoidClass_iff.mpr hζ) (under (𝓞 F) 𝓟)]
  exact Submodule.mem_span_singleton_self _

end

theorem not_dvd_pow_self_sub_one (p f : ℕ) [hp : Fact (p.Prime)] (hf : f ≠ 0) :
    ¬ p ∣ p ^ f - 1 := by
  have : NeZero f := ⟨hf⟩
  rw [Nat.dvd_sub_iff_right NeZero.one_le (p.div_pow_of_pos f _), Nat.dvd_one]
  · exact hp.out.ne_one
  · by_contra! h
    aesop

/-- A prime of `𝓞 L` above `p` has ramification index `p - 1` over `p`. -/
theorem ramificationIdx_eq_sub_one (f : ℕ) [hp : Fact p.Prime] [NeZero f]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] (𝓠 : Ideal (𝓞 L)) [𝓠.IsPrime] [𝓠.LiesOver 𝒑] :
    𝓠.ramificationIdx ℤ = p - 1 := by
  simpa using @IsCyclotomicExtension.Rat.ramificationIdx_eq (p * (p ^ f - 1)) (p ^ f - 1) p 0 hp L
    _ _ 𝓠 _ _ _ (by ring) (not_dvd_pow_self_sub_one p f (NeZero.ne f))

/-- Version of `ramificationIdx_eq_sub_one` over a prime `𝔮` of `𝓞 k` above `p` instead of over
`p`. -/
theorem ramificationIdx_eq_sub_one' {f m d : ℕ} [hp : Fact p.Prime] [NeZero f] [NeZero m]
    [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L] {k : IntermediateField ℚ L}
    [IsCyclotomicExtension {m} ℚ k] (hmd : p ^ f - 1 = m * d) (𝔮 : Ideal (𝓞 k)) [𝔮.IsMaximal]
    [𝔮.LiesOver 𝒑] {𝓠 : Ideal (𝓞 L)} [𝓠.IsPrime] [𝓠.LiesOver 𝔮] :
    𝓠.ramificationIdx (𝓞 k) = p - 1 := by
  have : 𝓠.LiesOver 𝒑 := LiesOver.trans 𝓠 𝔮 𝒑
  have hm : ¬ p ∣ m := fun h ↦ not_dvd_pow_self_sub_one p f (NeZero.ne f) (h.trans ⟨d, hmd⟩)
  have h𝓠 : 𝓠.ramificationIdx ℤ = p - 1 := ramificationIdx_eq_sub_one f 𝓠
  have tower := ramificationIdx_tower (R := ℤ) 𝔮 𝓠
  rw [h𝓠,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p k 𝔮 hm, one_mul] at tower
  exact tower.symm

/-- A prime of `𝓞 L` above `p` is unramified over the prime of `𝓞 F` below it. -/
theorem ramificationIdx_under_eq_one (p f : ℕ) [hp : Fact p.Prime] [NeZero f]
    [IsCyclotomicExtension {p} ℚ F] [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]
    (𝓠 : Ideal (𝓞 L)) [𝓠.IsPrime] [𝓠.LiesOver (span {(p : ℤ)})] :
    𝓠.ramificationIdx (𝓞 F) = 1 := by
  have h𝓠 : 𝓠.ramificationIdx ℤ = p - 1 := ramificationIdx_eq_sub_one f 𝓠
  have tower := ramificationIdx_tower (R := ℤ) (under (𝓞 F) 𝓠) 𝓠
  rw [h𝓠,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p F _] at tower
  exact (Nat.mul_eq_left (Nat.sub_ne_zero_of_lt hp.out.one_lt)).mp tower.symm

section

variable [hp : Fact p.Prime] (f : ℕ) [NeZero f] [IsCyclotomicExtension {p} ℚ F]
  [P.LiesOver (span {(p : ℤ)})] [𝓟.IsMaximal] [𝓟.LiesOver P]

theorem three_le_pow [hp' : Fact (Odd p)] : 3 ≤ p ^ f := by
  refine le_trans (Nat.le_pow (NeZero.pos f)) ?_
  exact (Nat.pow_le_pow_iff_left (NeZero.ne f)).mpr <| (Nat.Prime.odd_iff hp.out).mp hp'.out

variable {f P 𝓟 hζ}

variable [IsCyclotomicExtension {p * (p ^ f - 1)} ℚ L]

variable (f P hζ) in
include f P hζ in
/-- `ζ - 1` generates the prime of `𝓞 F` below `𝓟`, which is unramified in `L`. -/
theorem zeta_sub_one_notMem_sq : algebraMap (𝓞 F) (𝓞 L) ζ - 1 ∉ 𝓟 ^ 2 := by
  have : 𝓟.LiesOver 𝒑 := LiesOver.trans 𝓟 P 𝒑
  have hspan : under (𝓞 F) 𝓟 = span {ζ - 1} :=
    IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p F
      (IsPrimitiveRoot.coe_submonoidClass_iff.mpr hζ) (under (𝓞 F) 𝓟)
  have h : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (span {ζ - 1}) ≠ ⊥ := by
    apply map_ne_bot_of_ne_bot
    simpa [sub_eq_zero] using hζ.ne_one hp.out.one_lt
  rw [← map_one (f := algebraMap (𝓞 F) (𝓞 L)), ← map_sub, ← dvd_span_singleton,
    ← Set.image_singleton, ← map_span, FiniteMultiplicity.pow_dvd_iff_le_multiplicity
    (Ideal.finiteMultiplicity IsPrime.ne_top' h), ← hspan,
    ← IsDedekindDomain.ramificationIdx_eq_multiplicity (under (𝓞 F) 𝓟) 𝓟 (hspan ▸ h),
    ramificationIdx_under_eq_one p f]
  exact Nat.not_succ_le_self 1

end

section

variable {n} {m d : ℕ} [NeZero n] [NeZero (m * p)]

open IsCyclotomicExtension

variable (p F) in
theorem modEq_one_of_apply_eq_pow (hmd : n = m * d) (E : IntermediateField ℚ L)
    [IsCyclotomicExtension {m * p} ℚ E] (η : L) (hη : IsPrimitiveRoot η n)
    (τ : Gal(L/E)) (a : ℕ) (hτ : τ η = η ^ a) :
    a ≡ 1 [MOD m] := by
  let ν := algebraMap E L (zeta (m * p) ℚ E ^ p)
  have hν : IsPrimitiveRoot ν m := by
    refine IsPrimitiveRoot.map_of_injective ?_ (FaithfulSMul.algebraMap_injective E L)
    exact (zeta_spec (m * p) ℚ E).pow (NeZero.pos _) (by rw [mul_comm])
  obtain ⟨k, _, hk⟩ := hη.eq_pow_of_pow_eq_one (by rw [hmd, pow_mul, hν.pow_eq_one, one_pow])
  have := congr_arg τ hk
  rw [map_pow, hτ, AlgEquiv.commutes, pow_right_comm, hk] at this
  rwa [hν.eq_orderOf, ← (hν.isOfFinOrder (by lia)).pow_eq_pow_iff_modEq, pow_one]

end

section

open scoped Pointwise

open IsCyclotomicExtension.Rat

variable {m : ℕ} {k : IntermediateField ℚ L} (𝔭 : Ideal (𝓞 k))

section

variable (m) [IsCyclotomicExtension {m} ℚ k]

include m in
theorem primesOver_mem_orbit [𝔭.IsPrime] [𝔭.LiesOver 𝒑] (𝔮 : 𝒑.primesOver (𝓞 k)) :
    (𝔮 : Ideal (𝓞 k)) ∈ MulAction.orbit Gal(k/ℚ) 𝔭 := by
  have := IsCyclotomicExtension.isGalois {m} ℚ k
  rw [Algebra.IsInvariant.orbit_eq_primesOver ℤ _ _ 𝒑 𝔭]
  exact 𝔮.2

end

variable {𝓟 𝔭}

theorem restrictNormal_smul_eq [IsGalois ℚ k] [IsGalois ℚ L] [h𝓟 : 𝓟.LiesOver 𝔭]
    {𝔮 : 𝒑.primesOver (𝓞 k)} {𝓠 : (𝔮 : Ideal (𝓞 k)).primesOver (𝓞 L)} {τ : Gal(L/F)}
    (hτ : τ • 𝓟 = 𝓠) :
    (τ.restrictScalars ℚ).restrictNormal k • 𝔭 = 𝔮 := by
  rw [← IsGaloisGroup.restrictHom_eq_restrictNormal,
    ← IsGaloisGroup.restrictHom_eq_restrictHom Gal(L/ℚ) Gal(k/ℚ) ℤ (𝓞 k) (𝓞 L) ℚ k L,
    (liesOver_iff _ _).mp h𝓟, IsGaloisGroup.restrictHom_smul_under, (liesOver_iff _ _).mp 𝓠.2.2,
    ← hτ]
  rfl

variable [hp : Fact (Nat.Prime p)] [IsCyclotomicExtension {p} ℚ F] [𝓟.IsMaximal]

variable (p) in
/-- There is a single prime of `𝓞 F` above `p`, so any prime of `𝓞 L` above `p` lies over the prime
of `𝓞 F` below `𝓟`. -/
theorem liesOver_under_of_liesOver [𝓟.LiesOver 𝒑] {𝓠 : Ideal (𝓞 L)} [𝓠.IsPrime]
    [𝓠.LiesOver 𝒑] : 𝓠.LiesOver (under (𝓞 F) 𝓟) := by
  obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp (ncard_primesOver_of_prime p F)
  have h₁ : under (𝓞 F) 𝓟 ∈ primesOver 𝒑 (𝓞 F) := ⟨inferInstance, inferInstance⟩
  have h₂ : under (𝓞 F) 𝓠 ∈ primesOver 𝒑 (𝓞 F) := ⟨inferInstance, inferInstance⟩
  rw [hQ] at h₁ h₂
  exact (liesOver_iff _ _).mpr (h₁.trans h₂.symm)

end

section

variable [hp : Fact (p.Prime)]

attribute [local instance] Ideal.Quotient.field in
/-- In `K = ℚ(μ_(p ^ f - 1))`, a prime `P` above `p` has residue degree `f`, since `p` has order `f`
modulo `p ^ f - 1`. So `(𝓞 K ⧸ P)ˣ` has `p ^ f - 1` elements, and the `(p ^ f - 1)`-th roots of
unity of `𝓞 K` reduce bijectively onto it: the Teichmüller character of `P` is defined. -/
theorem hasTeichmullerLift {f : ℕ} [NeZero f]
    {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p ^ f - 1} ℚ K]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver 𝒑] :
    P.HasTeichmullerLift (p ^ f - 1) := by
  refine .of_card_of_isPrime ?_
  rw [Nat.card_units, tsub_left_inj Nat.card_pos NeZero.one_le, ← absNorm_eq_natCard,
    ← absNorm_pow_inertiaDeg 𝒑, absNorm_eq_natCard, Int.card_ideal_quot,
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := p ^ f - 1) p K P,
    ZMod.orderOf_pow_sub_one _ _ hp.out.one_lt]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mp (Fact.out : (p ^ f - 1).Coprime p).symm

end

end Stickelberger

end

end Stickelberger
