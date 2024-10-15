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

section charpoly

open Polynomial BigOperators

variable {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] --[SMulCommClass G A B]


variable (G) in

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
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

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

section redo_part_b

-- technical CRT lemma
theorem lem1 [DecidableEq (Ideal B)] [Nontrivial B] :
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
  let f := MulSemiringAction.CharacteristicPolynomial.F G b
  let n := f.natDegree
  have hf : f.Monic := MulSemiringAction.CharacteristicPolynomial.F_monic b
  let g := f.map (algebraMap B (B ⧸ Q))
  obtain ⟨q, hq, hq0⟩ :=
    g.exists_eq_pow_rootMultiplicity_mul_and_not_dvd
    (Polynomial.map_monic_ne_zero hf) 0
  let j := g.rootMultiplicity 0
  let k := q.natDegree
  rw [map_zero, sub_zero] at hq hq0
  rw [Polynomial.X_dvd_iff] at hq0
  change g = Polynomial.X ^ j * q at hq
  let a := f.coeff j
  use a
  let r := ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j))
  have hr : r.map (algebraMap B (B ⧸ Q)) = q := by
    ext n
    rw [Polynomial.coeff_map, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range_succ_iff]
    split_ifs with hn
    · rw [← Polynomial.coeff_map]
      change g.coeff (n + j) = q.coeff n
      rw [hq, Polynomial.coeff_X_pow_mul]
    · rw [map_zero, eq_comm]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_le hn)
  use a - r.eval b
  have ha : ∀ g : G, g • a = a := MulSemiringAction.CharacteristicPolynomial.F_coeff_fixed b j
  use ha
  constructor
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq,
        ← Polynomial.coeff_map]
    change g.coeff j ≠ 0
    rwa [← zero_add j, hq, Polynomial.coeff_X_pow_mul]
  · intro h
    by_cases hh : h • Q = Q
    · rw [if_pos hh, smul_sub, ha, map_sub, Ideal.Quotient.algebraMap_eq,
          sub_eq_self, Ideal.Quotient.eq_zero_iff_mem, ← hh]
      rw [Ideal.smul_mem_pointwise_smul_iff, ← Ideal.Quotient.eq_zero_iff_mem,
          ← Ideal.Quotient.algebraMap_eq, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hr]
      have hf : f.eval b = 0 :=
        MulSemiringAction.CharacteristicPolynomial.F_eval_eq_zero b
      replace hf : algebraMap B (B ⧸ Q) (f.eval b) = 0 := by
        rw [hf, map_zero]
      rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map] at hf
      change g.eval _ = 0 at hf
      rw [hq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hf
      refine eq_zero_of_ne_zero_of_mul_left_eq_zero (pow_ne_zero _ ?_) hf
      rwa [Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    · rw [if_neg hh, map_zero, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      have hr : r = ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (f.coeff (i + j)) := rfl
      rw [Finset.sum_range_succ', zero_add] at hr
      simp only [Polynomial.monomial_zero_left, ← Polynomial.monomial_mul_X,
        ← Finset.sum_mul] at hr
      rw [← Ideal.mem_inv_pointwise_smul_iff, hr, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X, Polynomial.eval_C]
      rw [sub_add_cancel_right, neg_mem_iff]
      apply Ideal.mul_mem_left
      apply hbP
      rw [Ne, inv_smul_eq_iff, eq_comm]
      exact hh

theorem lem2 [DecidableEq (Ideal B)] [Nontrivial B] (b₀ : B)
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

open Polynomial in
theorem lem3 {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [NoZeroDivisors S]
    {a : S} {i j : ℕ} {p : Polynomial R} (h : p.map (algebraMap R S) = (X - C a) ^ i * X ^ j)
    (f : S ≃ₐ[R] S) (hi : i ≠ 0) :
    f a = a := by
  by_cases ha : a = 0
  · rw [ha, map_zero]
  have key := congrArg (map f.toAlgHom.toRingHom) h
  rw [map_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_sub,
      map_X, map_C] at key
  rw [← f.toAlgHom.comp_algebraMap] at h
  replace key := congrArg (eval a) (key.symm.trans h)
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hi, zero_mul,
    mul_eq_zero, or_iff_left (pow_ne_zero j ha), pow_eq_zero_iff hi, sub_eq_zero] at key
  exact key.symm

omit [P.IsPrime] [IsFractionRing (B ⧸ Q) L]
open Polynomial in
theorem lem4 (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a)
    (f : L ≃ₐ[K] L) (b : B ⧸ Q)
    (hx : ∀ g : MulAction.stabilizer G Q, stabilizerAction G P Q g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  classical
  cases nonempty_fintype G
  revert hx
  refine Quotient.inductionOn' b ?_
  intro b₀ hx
  change f (algebraMap (B ⧸ Q) L (algebraMap B (B ⧸ Q) b₀)) =
    (algebraMap (B ⧸ Q) L (algebraMap B (B ⧸ Q) b₀))
  cases subsingleton_or_nontrivial B
  · rw [Subsingleton.elim b₀ 0, map_zero, map_zero, map_zero]
  obtain ⟨a, b, ha1, ha2, hb⟩ := lem2 G Q b₀ (fun g hg ↦ hx ⟨g, hg⟩)
  have key := MulSemiringAction.CharacteristicPolynomial.M_spec_map hAB b
  replace key := congrArg (map (algebraMap B (B ⧸ Q))) key
  rw [map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A (A ⧸ P) (B ⧸ Q),
      ← map_map, MulSemiringAction.CharacteristicPolynomial.F, finprod_eq_prod_of_fintype,
      Polynomial.map_prod] at key
  have key₀ : ∀ g : G, (X - C (g • b)).map (algebraMap B (B ⧸ Q)) =
      if g • Q = Q then X - C (algebraMap B (B ⧸ Q) (a * b₀)) else X := by
    intro g
    rw [Polynomial.map_sub, map_X, map_C, hb]
    split_ifs
    · rfl
    · rw [map_zero, map_zero, sub_zero]
  simp only [key₀] at key
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const] at key
  replace key := congrArg (map (algebraMap (B ⧸ Q) L)) key
  rw [map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq (A ⧸ P) K L,
      ← map_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_sub,
      map_X, map_C] at key
  replace key := lem3 key f (Finset.card_ne_zero_of_mem (Finset.mem_filter.mpr
    ⟨Finset.mem_univ 1, one_smul G Q⟩))
  simp only [map_mul] at key
  obtain ⟨a, rfl⟩ := hAB a ha1
  rwa [← IsScalarTower.algebraMap_apply A B (B ⧸ Q),
      IsScalarTower.algebraMap_apply A (A ⧸ P) (B ⧸ Q),
      ← IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L,
      IsScalarTower.algebraMap_apply (A ⧸ P) K L,
      f.commutes, mul_right_inj'] at key
  rw [Ne, NoZeroSMulDivisors.algebraMap_eq_zero_iff,
      NoZeroSMulDivisors.algebraMap_eq_zero_iff]
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A (A ⧸ P) (B ⧸ Q)] at ha2
  contrapose! ha2
  rw [ha2, map_zero]

end redo_part_b

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
