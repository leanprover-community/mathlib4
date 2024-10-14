import Mathlib.Algebra.Order.Group.Action.Synonym
import Mathlib.FieldTheory.Fixed
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.Ideal.Pointwise

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

lemma le_pow_smul {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) (n : ℕ) : a ≤ g ^ n • a := by
  induction' n with n hn
  · rw [pow_zero, one_smul]
  · rw [pow_succ', mul_smul]
    exact h.trans (smul_mono_right g hn)

instance {G : Type*} [Monoid G] {α : Type*} [Preorder α]
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le] :
    CovariantClass G αᵒᵈ HSMul.hSMul LE.le :=
  ⟨fun g _ _ h ↦ smul_mono_right (α := α) g h⟩

lemma pow_smul_le {G : Type*} [Monoid G] {α : Type*} [Preorder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : g • a ≤ a) (n : ℕ) : g ^ n • a ≤ a :=
  le_pow_smul (α := αᵒᵈ) h n

lemma smul_eq_of_le_smul
    {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) : g • a = a := by
  have key := smul_mono_right g (le_pow_smul h (Nat.card G - 1))
  rw [smul_smul, ← pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm key h

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

@[simp] lemma IsFractionRing.fieldEquivOfRingEquiv_commutes (f : B ≃+* B) (b : B) :
    IsFractionRing.fieldEquivOfRingEquiv f (algebraMap B L b) = algebraMap B L (f b) := by
  simp only [IsFractionRing.fieldEquivOfRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq]

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

lemma liftHom_commutes (f : B ≃ₐ[A] B) (b : B) :
    liftHom A B K L f (algebraMap B L b) = algebraMap B L (f b) := by
  simp [liftHom, lift, IsFractionRing.fieldEquivOfRingEquiv]

end lifting

section MulSemiringAction

variable {G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Group G]

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

@[simps]
def MulSemiringAction.toAlgEquivHom : G →* A ≃ₐ[R] A where
  toFun := MulSemiringAction.toAlgEquiv R A
  map_one' := by ext; rw [toAlgEquiv_apply, one_smul]; rfl
  map_mul' := fun f g ↦ by ext; rw [toAlgEquiv_apply, mul_smul]; rfl

end MulSemiringAction

section MulSemiringAction

variable {G : Type*} (R : Type*) [Semiring R] [Group G]

def MulSemiringAction.ofHom (h : G →* R ≃+* R) : MulSemiringAction G R where
  smul := fun g r ↦ h g r
  one_smul := DFunLike.ext_iff.mp (map_one h)
  mul_smul := fun g g' ↦ DFunLike.ext_iff.mp (map_mul h g g')
  smul_zero := fun g ↦ map_zero (h g)
  smul_add := fun g ↦ map_add (h g)
  smul_one := fun g ↦ map_one (h g)
  smul_mul := fun g ↦ map_mul (h g)

variable [MulSemiringAction G R]

def MulSemiringAction.toHom : G →* R ≃+* R  where
  toFun := MulSemiringAction.toRingEquiv G R
  map_one' := by ext; rw [toRingEquiv_apply, one_smul]; rfl
  map_mul' := fun f g ↦ by ext; rw [toRingEquiv_apply, mul_smul]; rfl

end MulSemiringAction

section fixedfield

/-- `MulSemiringAction.toAlgHom` is bijective. -/
theorem toAlgHom_bijective' (G F : Type*) [Field F] [Group G] [Finite G]
    [MulSemiringAction G F] [FaithfulSMul G F] :
    Function.Bijective
      (MulSemiringAction.toAlgEquivHom _ _ : G →* F ≃ₐ[FixedPoints.subfield G F] F) := by
  constructor
  · intro f g h
    apply (FixedPoints.toAlgHom_bijective G F).injective
    convert h
    simp [DFunLike.ext_iff]
  · intro f
    obtain ⟨g, h⟩ := (FixedPoints.toAlgHom_bijective G F).surjective f
    use g
    convert h
    simp [DFunLike.ext_iff]

/-- `MulSemiringAction.toAlgHom` is surjective. -/
theorem toAlgHom_surjective (G F : Type*) [Field F] [Group G] [Finite G]
    [MulSemiringAction G F] :
    Function.Surjective
      (MulSemiringAction.toAlgEquivHom _ _ : G →* F ≃ₐ[FixedPoints.subfield G F] F) := by
  let f : G →* F ≃ₐ[FixedPoints.subfield G F] F := MulSemiringAction.toAlgEquivHom _ _
  let H := f.ker
  let Q := G ⧸ H
  let h : Q →* F ≃ₐ[FixedPoints.subfield G F] F := QuotientGroup.kerLift f
  let action : MulSemiringAction Q F := MulSemiringAction.ofAlgEquivHom _ _ h
  have : FaithfulSMul Q F := ⟨by
    intro q₁ q₂
    refine Quotient.inductionOn₂' q₁ q₂ ?_
    intro g₁ g₂ h
    apply QuotientGroup.eq.mpr
    rwa [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, AlgEquiv.ext_iff]⟩
  have key' : FixedPoints.subfield Q F ≤ FixedPoints.subfield G F := fun x h g ↦ h g
  intro f
  obtain ⟨q, hq⟩ := (toAlgHom_bijective' Q F).surjective
    (AlgEquiv.ofRingEquiv (f := f) (fun ⟨g, hg⟩ ↦ f.commutes' ⟨g, key' hg⟩))
  revert hq
  refine Quotient.inductionOn' q ?_
  intro g hg
  simp only [AlgEquiv.ext_iff] at hg ⊢
  exact ⟨g, hg⟩

end fixedfield

section integrallemma

-- this only requires algebraic, not integral
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

-- maybe separate out x = b / a as separate lemma

end integrallemma

section charpoly

open Polynomial BigOperators

variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] --[SMulCommClass G A B]


variable (G) in
/-- The characteristic polynomial of an element `b` of a `G`-semiring `B`
is the polynomial `∏_{g ∈ G} (X - g • b)` (here `G` is finite; junk
returned in the infinite case) .-/
noncomputable def MulSemiringAction.CharacteristicPolynomial.F (b : B) : B[X] :=
  ∏ᶠ τ : G, (X - C (τ • b))

namespace MulSemiringAction.CharacteristicPolynomial

theorem F_spec (b : B) : F G b = ∏ᶠ τ : G, (X - C (τ • b)) := rfl

section F_API

variable [Finite G]

theorem F_monic [Nontrivial B] (b : B) : (F G b).Monic := by
  have := Fintype.ofFinite G
  rw [Monic, F_spec, finprod_eq_prod_of_fintype, leadingCoeff_prod'] <;> simp

theorem F_natdegree [Nontrivial B] (b : B) : (F G b).natDegree = Nat.card G := by
  have := Fintype.ofFinite G
  rw [F_spec, finprod_eq_prod_of_fintype, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_eq_nat_card,
    nsmul_eq_mul, mul_one, Nat.cast_id]

variable (G) in
theorem F_degree [Nontrivial B] (b : B) : (F G b).degree = Nat.card G := by
  have := Fintype.ofFinite G
  rw [degree_eq_iff_natDegree_eq_of_pos Nat.card_pos, F_natdegree]

theorem F_smul_eq_self (σ : G) (b : B) : σ • (F G b) = F G b := calc
  σ • F G b = σ • ∏ᶠ τ : G, (X - C (τ • b)) := by rw [F_spec]
  _         = ∏ᶠ τ : G, σ • (X - C (τ • b)) := smul_finprod' _
  _         = ∏ᶠ τ : G, (X - C ((σ * τ) • b)) := by simp [smul_sub, smul_smul]
  _         = ∏ᶠ τ' : G, (X - C (τ' • b)) := finprod_eq_of_bijective (fun τ ↦ σ * τ)
                                               (Group.mulLeft_bijective σ) (fun _ ↦ rfl)
  _         = F G b := by rw [F_spec]

theorem F_eval_eq_zero (b : B) : (F G b).eval b = 0 := by
  let foo := Fintype.ofFinite G
  simp [F_spec,finprod_eq_prod_of_fintype,eval_prod]
  apply @Finset.prod_eq_zero _ _ _ _ _ (1 : G) (Finset.mem_univ 1)
  simp

private theorem F_coeff_fixed (b : B) (n : ℕ) (g : G) :
    g • (F G b).coeff n = (F G b).coeff n := by
  change (g • (F G b)).coeff n = _
  rw [F_smul_eq_self]

end F_API

open scoped algebraMap

noncomputable local instance : Algebra A[X] B[X] :=
  RingHom.toAlgebra (Polynomial.mapRingHom (Algebra.toRingHom))

@[simp, norm_cast]
theorem _root_.coe_monomial (n : ℕ) (a : A) : ((monomial n a : A[X]) : B[X]) = monomial n (a : B) :=
  map_monomial _

section full_descent

variable (hFull : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = a)

-- Remark: the `splitting_of_full` approach is lousy and should be
-- replaced by the commented-out code below (lines 275-296 currently)

/-- This "splitting" function from B to A will only ever be evaluated on
G-invariant elements of B, and the two key facts about it are
that it lifts such an element to `A`, and for reasons of
convenience it lifts `1` to `1`. -/
noncomputable def splitting_of_full
    (b : B) : A := by classical
  exact
  if b = 1 then 1 else
    if h : ∀ σ : G, σ • b = b then (hFull b h).choose
    else 37

theorem splitting_of_full_spec {b : B} (hb : ∀ σ : G, σ • b = b) :
    splitting_of_full hFull b = b := by
  unfold splitting_of_full
  split_ifs with h1
  · rw_mod_cast [h1]
  · exact (hFull b hb).choose_spec.symm

theorem splitting_of_full_one : splitting_of_full hFull 1 = 1 := by
  unfold splitting_of_full
  rw [if_pos rfl]

noncomputable def M (b : B) : A[X] :=
  (∑ x ∈ (F G b).support, monomial x (splitting_of_full hFull ((F G b).coeff x)))

theorem M_deg_le (b : B) : (M hFull b).degree ≤ (F G b).degree := by
  unfold M
  have := Polynomial.degree_sum_le (F G b).support
    (fun x => monomial x (splitting_of_full hFull ((F G b).coeff x)))
  refine le_trans this ?_
  rw [Finset.sup_le_iff]
  intro n hn
  apply le_trans (degree_monomial_le n _) ?_
  exact le_degree_of_mem_supp n hn

variable [Nontrivial B] [Finite G]

theorem M_coeff_card (b : B) :
    (M hFull b).coeff (Nat.card G) = 1 := by
  unfold M
  simp only [finset_sum_coeff]
  have hdeg := F_degree G b
  rw [degree_eq_iff_natDegree_eq_of_pos Nat.card_pos] at hdeg
  rw [ ← hdeg]
  rw [Finset.sum_eq_single_of_mem ((F G b).natDegree)]
  · have : (F G b).Monic := F_monic b
    simp
    simp_all [splitting_of_full_one]
  · refine natDegree_mem_support_of_nonzero ?h.H
    intro h
    rw [h] at hdeg
    have : 0 < Nat.card G := Nat.card_pos
    simp_all
  · intro d _ hd
    exact coeff_monomial_of_ne (splitting_of_full hFull ((F G b).coeff d)) hd

theorem M_deg_eq_F_deg [Nontrivial A] (b : B) : (M hFull b).degree = (F G b).degree := by
  apply le_antisymm (M_deg_le hFull b)
  rw [F_degree]
  have := M_coeff_card hFull b
  refine le_degree_of_ne_zero ?h
  rw [this]
  exact one_ne_zero

theorem M_deg [Nontrivial A] (b : B) : (M hFull b).degree = Nat.card G := by
  rw [M_deg_eq_F_deg hFull b]
  exact F_degree G b

theorem M_monic (b : B) : (M hFull b).Monic := by
  have this1 := M_deg_le hFull b
  have this2 := M_coeff_card hFull b
  have this3 : 0 < Nat.card G := Nat.card_pos
  rw [← F_natdegree b] at this2 this3
  -- then the hypos say deg(M)<=n, coefficient of X^n is 1 in M
  have this4 : (M hFull b).natDegree ≤ (F G b).natDegree := natDegree_le_natDegree this1
  exact Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ this4 this2

omit [Nontrivial B] in
theorem M_spec (b : B) : ((M hFull b : A[X]) : B[X]) = F G b := by
  unfold M
  ext N
  push_cast
  simp_rw [splitting_of_full_spec hFull <| F_coeff_fixed b _]
  simp_rw [finset_sum_coeff, ← lcoeff_apply, lcoeff_apply, coeff_monomial]
  aesop

omit [Nontrivial B] in
theorem M_spec_map (b : B) : (map (algebraMap A B) (M hFull b)) = F G b := by
  rw [← M_spec hFull b]; rfl

omit [Nontrivial B] in
theorem M_eval_eq_zero (b : B) : (M hFull b).eval₂ (algebraMap A B) b = 0 := by
  rw [eval₂_eq_eval_map, M_spec_map, F_eval_eq_zero]

include hFull in
theorem isIntegral : Algebra.IsIntegral A B where
  isIntegral b := ⟨M hFull b, M_monic hFull b, M_eval_eq_zero hFull b⟩

end full_descent

end MulSemiringAction.CharacteristicPolynomial

end charpoly

namespace MulSemiringAction.CharacteristicPolynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
  -- from this, we can prove that P = comap Q
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

open Polynomial
/-
I didn't check that this definition was independent
of the lift `b` of `bbar` (and it might not even be true).
But this doesn't matter, because `G` no longer acts on `B/Q`.
All we need is that `Mbar` is monic of degree `|G|`, is defined over the bottom ring
and kills `bbar`.
-/
variable {Q} in
noncomputable def Mbar
    (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a)
    (bbar : B ⧸ Q) : (A ⧸ P)[X] :=
  Polynomial.map (Ideal.Quotient.mk P) <| M hFull' <| Quotient.out' bbar

variable (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a)

omit [SMulCommClass G A B] [Q.IsPrime] [P.IsPrime] [Algebra (A ⧸ P) (B ⧸ Q)]
  [IsScalarTower A (A ⧸ P) (B ⧸ Q)] in
theorem Mbar_monic [Nontrivial B] (bbar : B ⧸ Q) : (Mbar G P hFull' bbar).Monic := by
  have := M_monic hFull'
  simp [Mbar, (M_monic hFull' _).map]

-- omit [SMulCommClass G A B] [Q.IsPrime] [Algebra (A ⧸ P) (B ⧸ Q)]
--   [IsScalarTower A (A ⧸ P) (B ⧸ Q)] in
-- theorem Mbar_deg [Nontrivial A] [Nontrivial B] (bbar : B ⧸ Q) :
--     degree (Mbar G P hFull' bbar) = Nat.card G := by
--   simp only [Mbar]
--   rw [degree_map_eq_of_leadingCoeff_ne_zero]
--   · exact M_deg hFull' _
--   · rw [(M_monic hFull' _).leadingCoeff]
--     simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true]

/-- docstring -/
theorem Quotient.out_eq'' {R : Type*} [CommRing R] {I : Ideal R} (x : R ⧸ I) :
    Ideal.Quotient.mk I (Quotient.out' x) = x := by
  exact Quotient.out_eq' x

omit [SMulCommClass G A B] [Q.IsPrime] [P.IsPrime] in
theorem Mbar_eval_eq_zero [Nontrivial A] [Nontrivial B] (bbar : B ⧸ Q) :
    eval₂ (algebraMap (A ⧸ P) (B ⧸ Q)) bbar (Mbar G P hFull' bbar) = 0 := by
  have h := congr_arg (algebraMap B (B ⧸ Q)) (M_eval_eq_zero hFull' (Quotient.out' bbar))
  rw [map_zero, hom_eval₂, Ideal.Quotient.algebraMap_eq, Quotient.out_eq''] at h
  simpa [Mbar, eval₂_map, ← Ideal.Quotient.algebraMap_eq,
    ← IsScalarTower.algebraMap_eq A (A ⧸ P) (B ⧸ Q), IsScalarTower.algebraMap_eq A B (B ⧸ Q)]

end CharacteristicPolynomial

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
  -- from this, we can prove that P = comap Q
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

open CharacteristicPolynomial in
omit [SMulCommClass G A B] [Q.IsPrime] [P.IsPrime] in
theorem reduction_isIntegral
    [Nontrivial A] [Nontrivial B]
    (hFull' : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a) :
    Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) where
  isIntegral x := ⟨Mbar G P hFull' x, Mbar_monic G P Q hFull' x, Mbar_eval_eq_zero G P Q hFull' x⟩

end MulSemiringAction

section part_b

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
  -- from this, we can prove that P = comap Q
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

-- these first few lemmas might not be necessary!

-- omit [Algebra A B] [P.IsPrime] [Q.IsPrime] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
--   [IsFractionRing (B ⧸ Q) L] in
-- include K L in
-- theorem APBQ_injective (x : A ⧸ P) : algebraMap (A ⧸ P) (B ⧸ Q) x = 0 ↔ x = 0 := by
--   constructor
--   · intro hx
--     replace hx : algebraMap (A ⧸ P) L x = 0 := by
--       rw [IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L, hx, map_zero]
--     rw [IsScalarTower.algebraMap_apply (A ⧸ P) K L] at hx
--     rw [← map_zero (algebraMap K L), (algebraMap K L).injective.eq_iff] at hx
--     rw [← map_zero (algebraMap (A ⧸ P) K), (IsFractionRing.injective (A ⧸ P) K).eq_iff] at hx
--     exact hx
--   · intro hx
--     rw [hx, map_zero]

-- include K L in
-- omit [P.IsPrime] [Q.IsPrime] [IsFractionRing (B ⧸ Q) L] in
-- theorem comap_Q_eq_P : Q.comap (algebraMap A B) = P := by
--   ext x
--   rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
--   rw [IsScalarTower.algebraMap_apply A (A ⧸ P) (B ⧸ Q), APBQ_injective P Q K L]
--   rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

def quotientRingAction (Q' : Ideal B) (g : G) (hg : g • Q = Q') :
    B ⧸ Q ≃+* B ⧸ Q' :=
  Ideal.quotientEquiv Q Q' (MulSemiringAction.toRingEquiv G B g) hg.symm

def quotientAlgebraAction (g : G) (hg : g • Q = Q) : (B ⧸ Q) ≃ₐ[A ⧸ P] B ⧸ Q where
  __ := quotientRingAction G Q Q g hg
  commutes' := by
    intro a_bar; dsimp
    have ⟨a, ha⟩ := Ideal.Quotient.mk_surjective a_bar
    rw [quotientRingAction]; dsimp
    rw [← ha, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    rw [@Ideal.quotientMap_algebraMap A B _ _ _ B _ Q Q _ ]
    simp

def stabilizerAction :
    MulAction.stabilizer G Q →* ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) where
  toFun gh := quotientAlgebraAction G P Q gh.1 gh.2
  map_one' := by
    apply AlgEquiv.ext
    intro b_bar; dsimp
    unfold quotientAlgebraAction
    unfold quotientRingAction
    have ⟨b, hb⟩ := Ideal.Quotient.mk_surjective b_bar
    rw [← hb, ← Ideal.Quotient.algebraMap_eq]
    simp
  map_mul' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    apply AlgEquiv.ext
    intro b_bar; dsimp
    unfold quotientAlgebraAction
    unfold quotientRingAction
    have ⟨b, hb⟩ := Ideal.Quotient.mk_surjective b_bar
    rw [← hb, ← Ideal.Quotient.algebraMap_eq]
    simp
    rw [smul_smul]

-- not sure if we can make this strategy work without localization...
theorem keylemma0 [DecidableEq (Ideal B)] [Fintype G] :
    IsCoprime Q (∏ g ∈ (Finset.univ : Finset G).filter (fun g ↦ g • Q ≠ Q), g • Q) := by
  let P := ∏ g ∈ (Finset.univ : Finset G).filter (fun g ↦ g • Q ≠ Q), g • Q
  change IsCoprime Q P
  have h1 : ¬ P ≤ Q := by
    rw [Ideal.IsPrime.prod_le inferInstance]
    rintro ⟨g, hg1, hg2⟩
    exact (Finset.mem_filter.mp hg1).2 (smul_eq_of_smul_le hg2)
  obtain ⟨b, hbP, hbQ⟩ := SetLike.not_le_iff_exists.mp h1
  let f := MulSemiringAction.CharacteristicPolynomial.F G b
  sorry

theorem keylemma [DecidableEq (Ideal B)] :
    ∃ b : B, ∀ g : G, algebraMap B (B ⧸ Q) (g • b) = if g • Q = Q then 1 else 0 := by
  classical
  obtain ⟨_⟩ := nonempty_fintype G
  have key := keylemma0 G Q
  rw [Ideal.isCoprime_iff_exists] at key
  obtain ⟨q, hq, p, hp, hqp⟩ := key
  use p
  intro g
  split_ifs with hg
  · rw [← eq_sub_iff_add_eq'] at hqp
    rwa [hqp, smul_sub, smul_one, map_sub, map_one, sub_eq_self,
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, ← hg,
        Ideal.smul_mem_pointwise_smul_iff]
  · let s : Finset G := Finset.univ.filter (fun g ↦ g • Q ≠ Q)
    change p ∈ ∏ g ∈ s, g • Q at hp
    rw [eq_comm, ← inv_smul_eq_iff] at hg
    have hs : g⁻¹ ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ g⁻¹, hg⟩
    have key := Finset.insert_erase hs
    rw [← key, Finset.prod_insert (s.not_mem_erase g⁻¹)] at hp
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    rw [← Ideal.mem_inv_pointwise_smul_iff]
    exact Ideal.mul_le_right hp

open Polynomial in
omit [P.IsPrime] [IsFractionRing (A ⧸ P) K] in
theorem fullHom_surjective2
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a)
    (f : L ≃ₐ[K] L) (b : B ⧸ Q)
    (hx : ∀ g : MulAction.stabilizer G Q, stabilizerAction G P Q g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype G
  have key : ∃ b' : B, ∀ g : G, algebraMap B (B ⧸ Q) (g • b') = if g • Q = Q then b else 0 := by
    revert hx
    refine Quotient.inductionOn' b ?_
    intro b hx
    obtain ⟨b', hb'⟩ := keylemma G Q
    use b * b'
    intro g
    rw [smul_mul', map_mul, hb']
    split_ifs with hg
    · rw [mul_one]
      exact hx ⟨g, hg⟩
    · rw [mul_zero]
  obtain ⟨b', hb'⟩ := key
  have key : (b' : B ⧸ Q) = b := by
    simpa using hb' 1
  subst key
  have key := MulSemiringAction.CharacteristicPolynomial.M_spec_map hAB b'
  replace key := congrArg (map (algebraMap B (B ⧸ Q))) key
  rw [map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq A (A ⧸ P) (B ⧸ Q), ← map_map] at key
  rw [MulSemiringAction.CharacteristicPolynomial.F] at key
  rw [finprod_eq_prod_of_fintype, Polynomial.map_prod] at key
  simp only [Polynomial.map_sub, map_X, map_C, hb'] at key
  have key₀ : ∀ g : G, (X - C (if g • Q = Q then (b' : B ⧸ Q) else 0) : Polynomial (B ⧸ Q)) =
      if g • Q = Q then X - C (b' : B ⧸ Q) else X := by
    intro g
    split_ifs <;> simp
  simp only [key₀] at key
  simp [Finset.prod_ite] at key
  let s : Finset G := (Finset.univ : Finset G).filter (fun g ↦ g • Q = Q)
  have hs : ∀ g : G, g ∈ s ↔ g • Q = Q := fun g ↦ by simp [s]

  replace key := congrArg (map (algebraMap (B ⧸ Q) L)) key
  rw [map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq (A ⧸ P) K L, ← map_map] at key
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_sub,
      map_X, map_C] at key
  have key₀ := congrArg (Polynomial.map (f.toAlgHom : L →+* L)) key
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_sub,
      map_X, map_C] at key₀
  rw [map_map _ (f.toAlgHom : L →+* L), f.toAlgHom.comp_algebraMap] at key₀
  replace key := key.symm.trans key₀
  by_cases h : (b' : B ⧸ Q) = 0
  · simp [h]
  have hs' : s.card ≠ 0 := Finset.card_ne_zero_of_mem ((hs 1).mpr (one_smul G Q))
  replace key := congrArg
    (Polynomial.eval ((algebraMap (B ⧸ Q) L) ((algebraMap B (B ⧸ Q) b')))) key
  simp only [eval_mul ,eval_pow, eval_sub, eval_X, eval_C] at key
  simp only [Ideal.Quotient.algebraMap_eq] at key
  rw [sub_self, zero_pow hs', zero_mul, eq_comm, mul_eq_zero, or_iff_left] at key
  · replace key := pow_eq_zero key
    rw [sub_eq_zero] at key
    exact key.symm
  · apply mt pow_eq_zero
    rw [NoZeroSMulDivisors.algebraMap_eq_zero_iff]
    exact h

noncomputable def fullHom : MulAction.stabilizer G Q →* (L ≃ₐ[K] L) :=
  MonoidHom.comp (liftHom (A ⧸ P) (B ⧸ Q) K L) (stabilizerAction G P Q)

theorem fullHom_surjective1
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a)
    (f : L ≃ₐ[K] L) (x : L) (hx : ∀ g : MulAction.stabilizer G Q, fullHom G P Q K L g x = x) :
    f x = x := by
  have : Nontrivial A := ((algebraMap (A ⧸ P) K).comp (algebraMap A (A ⧸ P))).domain_nontrivial
  have : Nontrivial B := ((algebraMap (B ⧸ Q) L).comp (algebraMap B (B ⧸ Q))).domain_nontrivial
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
    have : Algebra.IsIntegral (A ⧸ P) (B ⧸ Q) := MulSemiringAction.reduction_isIntegral G P Q hAB
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
  refine fullHom_surjective2 G P Q K L hAB f b ?_
  intro g
  specialize hx g
  apply IsFractionRing.injective (B ⧸ Q) L
  rw [fullHom] at hx
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hx
  rw [← hx]
  symm
  apply liftHom_commutes

theorem fullHom_surjective
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a) :
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
