/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Algebra.Order.Group.Action.Synonym
import Mathlib.FieldTheory.Fixed
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Frobenius Elements

In algebraic number theory, if `L/K` is a finite Galois extension of number fields, with rings of
integers `𝓞L/𝓞K`, and if `q` is prime ideal of `𝓞L` lying over a prime ideal `p` of `𝓞K`, then
there exists unique a **Frobenius element** `Frob p` in `Gal(L/K)` with the property that
`Frob p x ≃ x ^ #(𝓞K/p) (mod q)` for all `x ∈ 𝓞L`.

This file proves the existence of Frobenius elements in a much more general setting.

## Main statements



## Implementation notes


-/

open scoped Pointwise

section ForMathlib

instance Ideal.IsPrime.smul {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    {P : Ideal R} [P.IsPrime] (g : G) : (g • P).IsPrime :=
  Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv _ _ g)

lemma Finset.smul_prod_perm
    {A : Type*} [CommMonoid A] {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G A]
    (a : A) (g0 : G) : g0 • (∏ g : G, g • a) = ∏ g : G, g • a := by
  simp_rw [Finset.smul_prod', smul_smul]
  exact Finset.prod_bijective (fun g ↦ g0 * g)
    (Group.mulLeft_bijective g0) (by simp) (fun g _ ↦ rfl)

-- PRed
lemma le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) (n : ℕ) : a ≤ g ^ n • a := by
  induction' n with n hn
  · rw [pow_zero, one_smul]
  · rw [pow_succ', mul_smul]
    exact h.trans (smul_mono_right g hn)

-- PRed
instance {G : Type*} [Monoid G] {α : Type*} [Preorder α]
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] :
    CovariantClass G αᵒᵈ HSMul.hSMul LE.le :=
  ⟨fun g _ _ h ↦ smul_mono_right (α := α) g h⟩

-- PRed
lemma pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a ≤ a) (n : ℕ) : g ^ n • a ≤ a :=
  le_pow_smul (α := αᵒᵈ) h n

-- PRed
lemma smul_eq_of_le_smul
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) : g • a = a := by
  have key := smul_mono_right g (le_pow_smul h (Nat.card G - 1))
  rw [smul_smul, ← pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm key h

-- PRed
lemma smul_eq_of_smul_le
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a ≤ a) : g • a = a :=
  smul_eq_of_le_smul (α := αᵒᵈ) h

end ForMathlib

section part_a

lemma comap_smul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (P : Ideal B) (g : G) : (g • P).comap (algebraMap A B) = P.comap (algebraMap A B) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]

-- (Part a of Théorème 2 in section 2 of chapter 5 of Bourbaki Alg Comm)
theorem part_a (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime]
    (hPQ : Ideal.comap (algebraMap A B) P = Ideal.comap (algebraMap A B) Q)
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a) :
    ∃ g : G, Q = g • P := by
  cases nonempty_fintype G
  have : ∀ (P Q : Ideal B) [P.IsPrime] [Q.IsPrime],
      P.comap (algebraMap A B) = Q.comap (algebraMap A B) → ∃ g ∈ (⊤ : Finset G), Q ≤ g • P := by
    intro P Q hP hQ hPQ
    rw [← Ideal.subset_union_prime 1 1 (fun _ _ _ _ ↦ hP.smul _)]
    intro b hb
    suffices h : ∃ g ∈ Finset.univ, g • b ∈ P by
      obtain ⟨g, -, hg⟩ := h
      apply Set.mem_biUnion (Finset.mem_univ g⁻¹) (Ideal.mem_inv_pointwise_smul_iff.mpr hg)
    obtain ⟨a, ha⟩ := hAB (∏ g : G, g • b) (Finset.smul_prod_perm b)
    rw [← hP.prod_mem_iff, ha, ← P.mem_comap, hPQ, Q.mem_comap, ← ha, hQ.prod_mem_iff]
    exact ⟨1, Finset.mem_univ 1, (one_smul G b).symm ▸ hb⟩
  obtain ⟨g, -, hg⟩ := this P Q hPQ
  obtain ⟨g', -, hg'⟩ := this Q (g • P) ((comap_smul P g).trans hPQ).symm
  have hg'' := hg.trans hg'
  have key := smul_eq_of_le_smul hg''
  rw [key] at hg'
  exact ⟨g, le_antisymm hg hg'⟩

end part_a

section lifting

variable (A B : Type*)
  [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B]
  (K L : Type*) [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]

-- PRed
@[simp] lemma IsFractionRing.fieldEquivOfRingEquiv_commutes (f : B ≃+* B) (b : B) :
    IsFractionRing.fieldEquivOfRingEquiv f (algebraMap B L b) = algebraMap B L (f b) := by
  simp only [IsFractionRing.fieldEquivOfRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq]

-- PRed
noncomputable def lift (f : B ≃ₐ[A] B) : L ≃ₐ[K] L where
  __ := IsFractionRing.fieldEquivOfRingEquiv f.toRingEquiv
  commutes' := by
    intro x
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
      EquivLike.coe_coe]
    rw [map_div₀, map_div₀]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B L]
    rw [IsFractionRing.fieldEquivOfRingEquiv_commutes]
    rw [IsFractionRing.fieldEquivOfRingEquiv_commutes]
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]

-- PRed
noncomputable def liftHom : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L) where
  toFun := lift A B K L
  map_one' := by
    ext x
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    simp [lift, IsFractionRing.fieldEquivOfRingEquiv]
  map_mul' := fun f g ↦ by
    ext x
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    simp [lift, IsFractionRing.fieldEquivOfRingEquiv]

-- PRed
lemma liftHom_commutes (f : B ≃ₐ[A] B) (b : B) :
    liftHom A B K L f (algebraMap B L b) = algebraMap B L (f b) := by
  simp [liftHom, lift, IsFractionRing.fieldEquivOfRingEquiv]

end lifting

section MulSemiringAction

variable {G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Group G]

-- PRed
@[simps]
def MulSemiringAction.ofAlgEquivHom (h : G →* A ≃ₐ[R] A) : MulSemiringAction G A where
  smul := fun g r ↦ h g r
  one_smul := DFunLike.ext_iff.mp (map_one h)
  mul_smul := fun g g' ↦ DFunLike.ext_iff.mp (map_mul h g g')
  smul_zero := fun g ↦ map_zero (h g)
  smul_add := fun g ↦ map_add (h g)
  smul_one := fun g ↦ map_one (h g)
  smul_mul := fun g ↦ map_mul (h g)

variable [MulSemiringAction G A] [SMulCommClass G R A]

-- PRed
@[simps]
def MulSemiringAction.toAlgEquivHom : G →* A ≃ₐ[R] A where
  toFun := MulSemiringAction.toAlgEquiv R A
  map_one' := by ext; rw [toAlgEquiv_apply, one_smul]; rfl
  map_mul' := fun f g ↦ by ext; rw [toAlgEquiv_apply, mul_smul]; rfl

end MulSemiringAction

section MulSemiringAction

variable {G : Type*} (R : Type*) [Semiring R] [Group G]

-- PRed
def MulSemiringAction.ofHom (h : G →* R ≃+* R) : MulSemiringAction G R where
  smul := fun g r ↦ h g r
  one_smul := DFunLike.ext_iff.mp (map_one h)
  mul_smul := fun g g' ↦ DFunLike.ext_iff.mp (map_mul h g g')
  smul_zero := fun g ↦ map_zero (h g)
  smul_add := fun g ↦ map_add (h g)
  smul_one := fun g ↦ map_one (h g)
  smul_mul := fun g ↦ map_mul (h g)

variable [MulSemiringAction G R]

-- PRed
def MulSemiringAction.toHom : G →* R ≃+* R  where
  toFun := MulSemiringAction.toRingEquiv G R
  map_one' := by ext; rw [toRingEquiv_apply, one_smul]; rfl
  map_mul' := fun f g ↦ by ext; rw [toRingEquiv_apply, mul_smul]; rfl

end MulSemiringAction

section fixedfield

/-- `MulSemiringAction.toAlgHom` is bijective. -/
theorem toAlgHom_bijective' (G F : Type*) [Field F] [Group G] [Finite G] [MulSemiringAction G F]
    [FaithfulSMul G F] : Function.Bijective
      (MulSemiringAction.toAlgEquivHom _ _ : G →* F ≃ₐ[FixedPoints.subfield G F] F) := by
  refine ⟨fun _ _ h ↦ (FixedPoints.toAlgHom_bijective G F).injective ?_,
    fun f ↦ ((FixedPoints.toAlgHom_bijective G F).surjective f).imp (fun _ h ↦ ?_)⟩
      <;> rwa [DFunLike.ext_iff] at h ⊢

/-- `MulSemiringAction.toAlgHom` is surjective. -/
theorem toAlgHom_surjective (G F : Type*) [Field F] [Group G] [Finite G] [MulSemiringAction G F] :
    Function.Surjective
      (MulSemiringAction.toAlgEquivHom _ _ : G →* F ≃ₐ[FixedPoints.subfield G F] F) := by
  let f : G →* F ≃ₐ[FixedPoints.subfield G F] F :=
    MulSemiringAction.toAlgEquivHom (FixedPoints.subfield G F) F
  let Q := G ⧸ f.ker
  let _ : MulSemiringAction Q F := MulSemiringAction.ofAlgEquivHom _ _ (QuotientGroup.kerLift f)
  have : FaithfulSMul Q F := ⟨by
    intro q₁ q₂
    refine Quotient.inductionOn₂' q₁ q₂ (fun g₁ g₂ h ↦ QuotientGroup.eq.mpr ?_)
    rwa [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, AlgEquiv.ext_iff]⟩
  intro f
  obtain ⟨q, hq⟩ := (toAlgHom_bijective' Q F).surjective
    (AlgEquiv.ofRingEquiv (f := f) (fun ⟨x, hx⟩ ↦ f.commutes' ⟨x, fun g ↦ hx g⟩))
  revert hq
  refine QuotientGroup.induction_on q (fun g hg ↦ ⟨g, ?_⟩)
  rwa [AlgEquiv.ext_iff] at hg ⊢

end fixedfield

section integrallemma

theorem Polynomial.nonzero_const_if_isIntegral (R S : Type*) [CommRing R] [Ring S] [Algebra R S]
    [h : Algebra.IsAlgebraic R S] [NoZeroDivisors S] (s : S) (hs : s ≠ 0) :
    ∃ (q : Polynomial R), q.coeff 0 ≠ 0 ∧ aeval s q = 0 := by
  obtain ⟨p, hp0, hp⟩ := h.isAlgebraic s
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  rw [C_0, sub_zero] at hpq hq
  rw [hpq, map_mul, aeval_X_pow, mul_eq_zero, or_iff_right (pow_ne_zero _ hs)] at hp
  exact ⟨q, mt X_dvd_iff.mpr hq, hp⟩

theorem Algebra.exists_dvd_nonzero_if_isIntegral (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.IsAlgebraic R S] [NoZeroDivisors S] (s : S) (hs : s ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ s ∣ (algebraMap R S) r := by
  obtain ⟨q, hq0, hq⟩ := Polynomial.nonzero_const_if_isIntegral R S s hs
  have key := map_dvd (Polynomial.aeval s) (Polynomial.X_dvd_sub_C (p := q))
  rw [map_sub, hq, zero_sub, dvd_neg, Polynomial.aeval_X, Polynomial.aeval_C] at key
  exact ⟨q.coeff 0, hq0, key⟩

end integrallemma

-- Charpoly of a finite group acting on a ring
section charpoly

open Polynomial

variable {B : Type*} [CommRing B] (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B]

noncomputable def MulSemiringAction.charpoly (b : B) : B[X] :=
  ∏ g : G, (X - C (g • b))

namespace MulSemiringAction.Charpoly

theorem charpoly_eq (b : B) : charpoly G b = ∏ g : G, (X - C (g • b)) := rfl

theorem charpoly_eq_prod_smul (b : B) : charpoly G b = ∏ g : G, g • (X - C b) := by
  simp only [smul_sub, smul_C, smul_X, charpoly_eq]

theorem monic_charpoly (b : B) : (charpoly G b).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_sub_C _)

theorem eval_charpoly (b : B) : (charpoly G b).eval b = 0 := by
  rw [charpoly_eq, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  rw [one_smul, eval_sub, eval_C, eval_X, sub_self]

variable {G}

theorem smul_charpoly (σ : G) (b : B) : σ • (charpoly G b) = charpoly G b := by
  rw [charpoly_eq_prod_smul, Finset.smul_prod_perm]

private theorem smul_coeff_charpoly (b : B) (n : ℕ) (g : G) :
    g • (charpoly G b).coeff n = (charpoly G b).coeff n := by
  rw [← coeff_smul, smul_charpoly]

end MulSemiringAction.Charpoly

end charpoly

-- Charpoly of a finite group acting on an algebra extension
section charpoly

namespace MulSemiringAction.Charpoly

open Polynomial BigOperators

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Fintype G] [MulSemiringAction G B]

theorem reduction
    (hinv : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b) (b : B) :
    ∃ M : A[X], M.Monic ∧ M.map (algebraMap A B) = charpoly G b := by
  let f : ℕ → A := fun k ↦ (hinv ((charpoly G b).coeff k) (smul_coeff_charpoly b k)).choose
  have hf : ∀ k, algebraMap A B (f k) = (charpoly G b).coeff k :=
    fun k ↦ (hinv ((charpoly G b).coeff k) (smul_coeff_charpoly b k)).choose_spec
  use X ^ (charpoly G b).natDegree + ∑ k ∈ Finset.range (charpoly G b).natDegree, C (f k) * X ^ k
  constructor
  · apply Polynomial.monic_X_pow_add
    rw [← Fin.sum_univ_eq_sum_range]
    apply Polynomial.degree_sum_fin_lt
  · simp_rw [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, hf]
    exact (monic_charpoly G b).as_sum.symm

variable (P : Ideal A) (Q : Ideal B) [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]

theorem reduction_isIntegral
    (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b) :
    Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) where
  isIntegral q := by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    change IsIntegral (A ⧸ P) (algebraMap B (B ⧸ Q) b)
    obtain ⟨f, hf1, hf2⟩ := reduction G hFull' b
    refine ⟨f.map (algebraMap A (A ⧸ P)), hf1.map (algebraMap A (A ⧸ P)), ?_⟩
    rw [← eval_map, map_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq A B (B ⧸ Q), ← map_map, hf2, eval_map, eval₂_at_apply,
        eval_charpoly, map_zero]

end MulSemiringAction.Charpoly

end charpoly

section stabilizerAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]

def stabilizerAction : MulAction.stabilizer G Q →* ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) where
  toFun g :=
  { __ := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv G B g) g.2.symm
    commutes' := fun q ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      simp [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] }
  map_one' := AlgEquiv.ext (fun q ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp)
  map_mul' g h := AlgEquiv.ext (fun q ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp [mul_smul])

end stabilizerAction

section CRT

variable {B : Type*} [CommRing B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  (Q : Ideal B) [Q.IsPrime]

-- technical CRT lemma
theorem lem1 [DecidableEq (Ideal B)] :
    ∃ a b : B, (∀ g : G, g • a = a) ∧ (a ∉ Q) ∧
    (∀ g : G, algebraMap B (B ⧸ Q) (g • b) =
      algebraMap B (B ⧸ Q) (if g • Q = Q then a else 0)) := by
  obtain ⟨_⟩ := nonempty_fintype G
  let P := ((Finset.univ : Finset G).filter (fun g ↦ g • Q ≠ Q)).inf (fun g ↦ g • Q)
  have h1 : ¬ P ≤ Q := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨g, hg1, hg2⟩
    exact (Finset.mem_filter.mp hg1).2 (smul_eq_of_smul_le hg2)
  obtain ⟨b, hbP, hbQ⟩ := SetLike.not_le_iff_exists.mp h1
  replace hbP : ∀ g : G, g • Q ≠ Q → b ∈ g • Q :=
    fun g hg ↦ (Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ g, hg⟩) : P ≤ g • Q) hbP
  let f := MulSemiringAction.charpoly G b
  obtain ⟨q, hq, hq0⟩ :=
    (f.map (algebraMap B (B ⧸ Q))).exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      (Polynomial.map_monic_ne_zero (MulSemiringAction.Charpoly.monic_charpoly G b)) 0
  rw [map_zero, sub_zero] at hq hq0
  let j := (f.map (algebraMap B (B ⧸ Q))).rootMultiplicity 0
  let k := q.natDegree
  let r := ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j))
  have hr : r.map (algebraMap B (B ⧸ Q)) = q := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range_succ_iff]
    split_ifs with hn
    · rw [← Polynomial.coeff_map, hq, Polynomial.coeff_X_pow_mul]
    · rw [map_zero, eq_comm, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_le hn)]
  have hf : f.eval b = 0 := MulSemiringAction.Charpoly.eval_charpoly G b
  have hr : r.eval b ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq] at hbQ ⊢
    replace hf := congrArg (algebraMap B (B ⧸ Q)) hf
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map] at hf ⊢
    rwa [map_zero, hq, ← hr, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      mul_eq_zero, or_iff_right (pow_ne_zero _ hbQ)] at hf
  let a := f.coeff j
  have ha : ∀ g : G, g • a = a := MulSemiringAction.Charpoly.smul_coeff_charpoly b j
  have hr' : ∀ g : G, g • Q ≠ Q → a - r.eval b ∈ g • Q := by
    intro g hg
    have hr : r = ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j)) := rfl
    rw [← Ideal.neg_mem_iff, neg_sub, hr, Finset.sum_range_succ', Polynomial.eval_add,
        Polynomial.eval_monomial, zero_add, pow_zero, mul_one, add_sub_cancel_right]
    simp only [ ← Polynomial.monomial_mul_X]
    rw [← Finset.sum_mul, Polynomial.eval_mul_X]
    exact Ideal.mul_mem_left (g • Q) _ (hbP g hg)
  refine ⟨a, a - r.eval b, ha, ?_, fun h ↦ ?_⟩
  · rwa [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, ← Polynomial.coeff_map,
      ← zero_add j, hq, Polynomial.coeff_X_pow_mul, ← Polynomial.X_dvd_iff]
  · rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem,
      ← Ideal.smul_mem_pointwise_smul_iff (a := h⁻¹), smul_sub, inv_smul_smul]
    simp only [← eq_inv_smul_iff (g := h), eq_comm (a := Q)]
    split_ifs with hh
    · rwa [ha, sub_sub_cancel_left, hh, Q.neg_mem_iff]
    · rw [smul_zero, sub_zero]
      exact hr' h⁻¹ hh

theorem lem2 [DecidableEq (Ideal B)] (b₀ : B)
    (hx : ∀ g : G, g • Q = Q → algebraMap B (B ⧸ Q) (g • b₀) = algebraMap B (B ⧸ Q) b₀) :
    ∃ a b : B, (∀ g : G, g • a = a) ∧ (a ∉ Q) ∧
    (∀ g : G, algebraMap B (B ⧸ Q) (g • b) =
      algebraMap B (B ⧸ Q) (if g • Q = Q then a * b₀ else 0)) := by
  obtain ⟨a, b, ha1, ha2, hb⟩ := lem1 G Q
  refine ⟨a, b * b₀, ha1, ha2, fun g ↦ ?_⟩
  rw [smul_mul', map_mul, hb]
  specialize hb g
  split_ifs with hg
  · rw [map_mul, hx g hg]
  · rw [map_zero, zero_mul]

end CRT

section polylemma

open Polynomial

theorem lem3 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [NoZeroDivisors S]
    {a : S} {i j : ℕ} {p : Polynomial R} (h : p.map (algebraMap R S) = (X - C a) ^ i * X ^ j)
    (f : S ≃ₐ[R] S) (hi : i ≠ 0) :
    f a = a := by
  by_cases ha : a = 0
  · rw [ha, map_zero]
  have hf := congrArg (eval a) (congrArg (Polynomial.mapAlgHom f.toAlgHom) h)
  rw [coe_mapAlgHom, map_map, f.toAlgHom.comp_algebraMap, h] at hf
  simp_rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C,
    eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hi, zero_mul,
    zero_eq_mul, or_iff_left (pow_ne_zero j ha), pow_eq_zero_iff hi, sub_eq_zero] at hf
  exact hf.symm

end polylemma

section part_b

section redo_part_b

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [Q.IsPrime]
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [NoZeroSMulDivisors (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

open IsScalarTower Polynomial in
theorem lem4 (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b)
    (f : L ≃ₐ[K] L) (b : B ⧸ Q)
    (hx : ∀ g : MulAction.stabilizer G Q, stabilizerAction G P Q g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  classical
  cases nonempty_fintype G
  revert hx
  obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
  intro hx
  rw [← Ideal.Quotient.algebraMap_eq]
  obtain ⟨a, b, ha1, ha2, hb⟩ := lem2 G Q b₀ (fun g hg ↦ hx ⟨g, hg⟩)
  obtain ⟨M, _, key⟩ := MulSemiringAction.Charpoly.reduction G hAB b
  replace key := congrArg (map (algebraMap B (B ⧸ Q))) key
  rw [map_map, ← algebraMap_eq, algebraMap_eq A (A ⧸ P) (B ⧸ Q),
      ← map_map, MulSemiringAction.charpoly, Polynomial.map_prod] at key
  have key₀ : ∀ g : G, (X - C (g • b)).map (algebraMap B (B ⧸ Q)) =
      if g • Q = Q then X - C (algebraMap B (B ⧸ Q) (a * b₀)) else X := by
    intro g
    rw [Polynomial.map_sub, map_X, map_C, hb]
    split_ifs
    · rfl
    · rw [map_zero, map_zero, sub_zero]
  simp only [key₀, Finset.prod_ite, Finset.prod_const] at key
  replace key := congrArg (map (algebraMap (B ⧸ Q) L)) key
  rw [map_map, ← algebraMap_eq, algebraMap_eq (A ⧸ P) K L,
      ← map_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_sub,
      map_X, map_C] at key
  replace key := lem3 key f (Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr
    ⟨Finset.mem_univ 1, one_smul G Q⟩))
  simp only [map_mul] at key
  obtain ⟨a, rfl⟩ := hAB a ha1
  rwa [← algebraMap_apply A B (B ⧸ Q), algebraMap_apply A (A ⧸ P) (B ⧸ Q),
      ← algebraMap_apply, algebraMap_apply (A ⧸ P) K L, f.commutes, mul_right_inj'] at key
  rwa [← algebraMap_apply, algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      ← algebraMap_apply A (A ⧸ P) (B ⧸ Q), algebraMap_apply A B (B ⧸ Q),
      Ne, NoZeroSMulDivisors.algebraMap_eq_zero_iff, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]

end redo_part_b

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

noncomputable def fullHom : MulAction.stabilizer G Q →* (L ≃ₐ[K] L) :=
  MonoidHom.comp (liftHom (A ⧸ P) (B ⧸ Q) K L) (stabilizerAction G P Q)

theorem fullHom_surjective1
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b)
    (f : L ≃ₐ[K] L) (x : L) (hx : ∀ g : MulAction.stabilizer G Q, fullHom G P Q K L g x = x) :
    f x = x := by
  obtain ⟨_⟩ := nonempty_fintype G
  have : NoZeroSMulDivisors (A ⧸ P) L := by
    simp only [NoZeroSMulDivisors.iff_algebraMap_injective,
        injective_iff_map_eq_zero,
        IsScalarTower.algebraMap_eq (A ⧸ P) K L,
        RingHom.comp_apply,
        NoZeroSMulDivisors.algebraMap_eq_zero_iff]
    simp
  have : NoZeroSMulDivisors (A ⧸ P) (B ⧸ Q) := by
    rw [NoZeroSMulDivisors.iff_algebraMap_injective] at this ⊢
    rw [IsScalarTower.algebraMap_eq (A ⧸ P) (B ⧸ Q) L] at this
    exact Function.Injective.of_comp this
  have key : ∃ (a : A ⧸ P) (b : B ⧸ Q), a ≠ 0 ∧
      x = (algebraMap (B ⧸ Q) L b) / (algebraMap (A ⧸ P) L a) := by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) x
    replace hy : y ≠ 0 := by
      rintro rfl
      exact zero_not_mem_nonZeroDivisors hy
    have : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) :=
      MulSemiringAction.Charpoly.reduction_isIntegral G P Q hAB
    obtain ⟨a, ha, b, hb⟩ := Algebra.exists_dvd_nonzero_if_isIntegral (A ⧸ P) (B ⧸ Q) y hy
    refine ⟨a, x * b, ha, ?_⟩
    rw [IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L, hb]
    simp only [map_mul]
    rw [mul_div_mul_right]
    rw [Ne, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
    rintro rfl
    rw [mul_zero] at hb
    rw [NoZeroSMulDivisors.algebraMap_eq_zero_iff] at hb
    exact ha hb
  obtain ⟨a, b, ha, rfl⟩ := key
  simp only [map_div₀, IsScalarTower.algebraMap_apply (A ⧸ P) K L,
    AlgEquiv.commutes] at hx ⊢
  have key : algebraMap (A ⧸ P) L a ≠ 0 := by
    rwa [Ne, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
  simp only [← IsScalarTower.algebraMap_apply (A ⧸ P) K L] at hx ⊢
  simp only [div_left_inj' key] at hx ⊢
  refine lem4 G P Q K L hAB f b ?_
  intro g
  specialize hx g
  apply IsFractionRing.injective (B ⧸ Q) L
  rw [fullHom] at hx
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hx
  rw [← hx]
  symm
  apply liftHom_commutes

theorem fullHom_surjective
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, algebraMap A B a = b) :
    Function.Surjective (fullHom G P Q K L : MulAction.stabilizer G Q →* (L ≃ₐ[K] L)) := by
  let action : MulSemiringAction (MulAction.stabilizer G Q) L :=
    MulSemiringAction.ofAlgEquivHom _ _
      (fullHom G P Q K L : MulAction.stabilizer G Q →* (L ≃ₐ[K] L))
  have key := toAlgHom_surjective (MulAction.stabilizer G Q) L
  intro f
  obtain ⟨g, hg⟩ := key (AlgEquiv.ofRingEquiv (f := f)
    (fun x ↦ fullHom_surjective1 G P Q K L hAB f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

end part_b
