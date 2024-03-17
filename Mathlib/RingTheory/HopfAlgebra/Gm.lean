import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.Data.Polynomial.Laurent
import Mathlib.Data.Polynomial.RingDivision
open scoped LaurentPolynomial TensorProduct
/- Lol none of the zpow stuff is necessary i don't think -/
set_option autoImplicit false

@[simps] def MonoidHom.equivHomUnits (G M : Type*) [Group G] [Monoid M] :
    (G →* M) ≃ (G →* Mˣ) where
  toFun := MonoidHom.toHomUnits
  invFun := fun f => (Units.coeHom _).comp f
  left_inv := fun x => rfl
  right_inv := fun x => by ext; rfl

namespace TensorProduct

noncomputable instance instInvertibleTmul {R A B : Type*}
    [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (x : A) (y : B) [Invertible x] [Invertible y] :
    Invertible (x ⊗ₜ[R] y) where
  invOf := ⅟ x ⊗ₜ ⅟ y
  invOf_mul_self := by simp only [Algebra.TensorProduct.tmul_mul_tmul, invOf_mul_self']; rfl
  mul_invOf_self := by simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_invOf_self']; rfl

@[simp] lemma invOf_tmul {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (x : A) (y : B) [Invertible x] [Invertible y] :
    ⅟ (x ⊗ₜ y) = ⅟ x ⊗ₜ[R] ⅟ y := rfl

lemma tmul_zpow {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (x : A) (y : B) [Invertible x] [Invertible y] (n : ℤ) :
    (unitOfInvertible (x ⊗ₜ[R] y) ^ n : (A ⊗[R] B)ˣ)
      = ((unitOfInvertible x ^ n : Aˣ) : A) ⊗ₜ[R] ((unitOfInvertible y ^ n : Bˣ) : B) := by
  refine' Int.induction_on n (by simp only [zpow_zero, Units.val_one]; rfl)
    (fun i _ => _) (fun i _ => _)
  all_goals
    simp only [← neg_add', ← inv_zpow', ← Int.ofNat_succ, zpow_ofNat,
      Units.val_pow_eq_pow_val, val_inv_unitOfInvertible,
      invOf_tmul, Algebra.TensorProduct.tmul_pow, val_unitOfInvertible]

end TensorProduct

namespace LaurentPolynomial

variable {R : Type*} [CommSemiring R]

def intDegree (p : R[T;T⁻¹]) : ℤ :=
  p.degree.unbot' 0

@[simp] lemma degree_eq_intDegree {p : R[T;T⁻¹]}
    (hp : p ≠ 0) : p.degree = p.intDegree := by
  let ⟨n, hn⟩ := not_forall.1 (mt Option.eq_none_iff_forall_not_mem.2 (mt degree_eq_bot_iff.1 hp))
  have hn : degree p = some n := Classical.not_not.1 hn
  rw [intDegree, hn]; rfl

@[simp] lemma intDegree_zero :
    intDegree (R := R) 0 = 0 := by
  simp only [intDegree, degree_zero, WithBot.unbot'_bot]

@[simp] lemma intDegree_T [Nontrivial R] (m : ℤ) :
    intDegree (T (R := R) m) = m := by
  simp only [intDegree, degree_T, WithBot.unbot'_coe]

@[simp] lemma intDegree_C (r : R) :
    intDegree (C r) = 0 := by
  rcases eq_or_ne r 0 with rfl | h
  · simp only [map_zero, intDegree_zero]
  · simp only [intDegree, degree_C h, WithBot.unbot_zero']

@[simp] lemma intDegree_C_mul_T {r : R} {m : ℤ} (hr : r ≠ 0) :
    intDegree (C r * T m) = m := by
  simp only [intDegree, degree_C_mul_T _ _ hr, WithBot.unbot'_coe]

lemma degree_toLaurent (p : Polynomial R) :
    (Polynomial.toLaurent p).degree = p.degree.map (↑) := by
  rcases eq_or_ne p 0 with h | _
  · simp only [h, map_zero, degree_zero, Polynomial.degree_zero, WithBot.map_bot]
  · simp only [degree, toLaurent_support, Finset.max_eq_sup_coe,
      Polynomial.degree, Finset.sup_map]
    rw [Finset.comp_sup_eq_sup_comp (s := p.support) (WithBot.map Nat.cast) _ _]
    · congr
    · intro x y
      induction x using WithBot.recBotCoe <;> induction y using WithBot.recBotCoe
      <;> simp only [ge_iff_le, le_refl, sup_of_le_left, WithBot.map_bot,
        bot_le, sup_of_le_right, WithBot.map_coe, Monotone.map_sup,
        WithBot.monotone_map_iff, Nat.mono_cast]
    · simp only [WithBot.map_bot]

@[simp] lemma intDegree_toLaurent (p : Polynomial R) :
    (Polynomial.toLaurent p).intDegree = p.natDegree := by
  rcases eq_or_ne p 0 with h | h
  · simp_all only [map_zero, intDegree_zero, Polynomial.natDegree_zero, CharP.cast_eq_zero]
  · refine' WithBot.coe_injective _
    rw [← degree_eq_intDegree (Polynomial.toLaurent_ne_zero.1 h),
      WithBot.coe_nat, degree_toLaurent, Polynomial.degree_eq_natDegree h]
    exact WithBot.map_coe Nat.cast p.natDegree

abbrev leadingCoeff (p : R[T;T⁻¹]) := p p.intDegree

@[simp] lemma leadingCoeff_C (r : R) :
    leadingCoeff (C r) = r := by
  simp only [C_apply, intDegree_C, ↓reduceIte]

@[simp] lemma leadingCoeff_T (m : ℤ) :
    leadingCoeff (T m) = 1 := by
  simp only [T_apply, intDegree_T, ↓reduceIte]

@[simp] lemma leadingCoeff_C_mul_T (r : R) (m : ℤ) :
    leadingCoeff (C r * T (R := R) m) = r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [leadingCoeff, map_zero, zero_mul, intDegree_zero, Finsupp.coe_zero, Pi.zero_apply]
  rw [leadingCoeff, intDegree_C_mul_T hr, ← single_eq_C_mul_T,
    Finsupp.single_eq_same]

@[simp] lemma leadingCoeff_toLaurent (f : Polynomial R) :
    (Polynomial.toLaurent f).leadingCoeff = f.leadingCoeff := by
  unfold leadingCoeff
  simp only [intDegree_toLaurent]
  rcases eq_or_ne f 0 with rfl | _
  · simp only [map_zero, Polynomial.natDegree_zero, CharP.cast_eq_zero, Finsupp.coe_zero,
    Pi.zero_apply, Polynomial.leadingCoeff_zero]
  · simp only [Polynomial.toLaurent, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      Polynomial.toFinsuppIso_apply, AddMonoidAlgebra.mapDomainRingHom_apply, ZeroHom.toFun_eq_coe,
      AddMonoidHom.toZeroHom_coe, Finsupp.mapDomain.addMonoidHom_apply]
    exact Finsupp.mapDomain_apply Int.ofNatHom.injective_nat _ _

@[simp] lemma leadingCoeff_mul_T [NoZeroDivisors R] (p : R[T;T⁻¹]) (m : ℤ) :
    leadingCoeff (p * T m) = leadingCoeff p := by
  induction' p using reduce_to_polynomial_of_mul_T with p p hp
  sorry
  sorry

lemma leadingCoeff_mul [NoZeroDivisors R] (p q : R[T;T⁻¹]) :
    (p * q).leadingCoeff = p.leadingCoeff * q.leadingCoeff := by
  induction' p using reduce_to_polynomial_of_mul_T with f f hf
    <;> induction' q using reduce_to_polynomial_of_mul_T with g g hg
  · simp only [leadingCoeff_toLaurent, ← map_mul, Polynomial.leadingCoeff_mul]
  · simp_all only [leadingCoeff_toLaurent, leadingCoeff_mul_T]
    sorry
  · sorry
  · sorry

lemma ffs {R : Type*} [Semiring R] (p : Polynomial R)
    (hp : p.natDegree = p.natTrailingDegree) :
    p = Polynomial.monomial p.natDegree p.leadingCoeff := by
  by_cases h : p = 0
  · simp_all only [Polynomial.natDegree_zero, Polynomial.natTrailingDegree_zero,
      Polynomial.leadingCoeff_zero, map_zero]
  · ext n
    rw [Polynomial.coeff_monomial]
    split_ifs with hn
    · simp only [← hn, Polynomial.coeff_natDegree]
    · rcases lt_or_gt_of_ne hn with (hn | hn)
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn]
      · rw [hp] at hn
        rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hn]

lemma ffs2 {R : Type*} [Semiring R] [NoZeroDivisors R] (n : ℕ) (r : R)
    (hr : r ≠ 0)
    (p : Polynomial R) (hp : p ∣ Polynomial.monomial n r) :
    p = Polynomial.monomial p.natDegree p.leadingCoeff := by
  rcases hp with ⟨q, h⟩
  refine' ffs _ _
  have hp : p ≠ 0 := (ne_zero_and_ne_zero_of_mul (fun hpq =>
    hr <| (Polynomial.monomial_eq_zero_iff r n).1 (h ▸ hpq))).1
  have hq : q ≠ 0 := (ne_zero_and_ne_zero_of_mul (fun hpq =>
    hr <| (Polynomial.monomial_eq_zero_iff r n).1 (h ▸ hpq))).2
  have h1 := Polynomial.natDegree_mul hp hq
  have h2 := Polynomial.natTrailingDegree_mul hp hq
  rw [← h] at h1 h2
  rw [Polynomial.natDegree_monomial_eq n hr] at h1
  rw [Polynomial.natTrailingDegree_monomial hr, h1] at h2
  refine' ((add_eq_add_iff_eq_and_eq _ _).1 h2.symm).1.symm
    <;> exact Polynomial.natTrailingDegree_le_natDegree _

theorem C_mul_T_eq_of_invertible [Nontrivial R] [NoZeroDivisors R] {p : R[T;T⁻¹]}
    (hp : Invertible p) : C p.leadingCoeff * T p.intDegree = p := by
  rcases exists_T_pow p with ⟨m, f, hf⟩
  rcases exists_T_pow (R := R) ⅟p  with ⟨n, g, hg⟩
  have : f * g = Polynomial.monomial (m + n) 1 := by
    refine' Polynomial.toLaurent_injective _
    simp_rw [map_mul, hf, hg, Polynomial.toLaurent_C_mul_T, map_one, Nat.cast_add, one_mul,
      mul_mul_mul_comm _ (T m), mul_invOf_self, ← T_add, one_mul]
  have hf0 : f ≠ 0 := fun hf0 => one_ne_zero
    ((Polynomial.monomial_eq_zero_iff 1 (m + n)).1 <| by rw [← this, hf0, zero_mul])
  rw [ffs2 (m + n) 1 one_ne_zero f ⟨g, this.symm⟩, ← mul_invOf_eq_iff_eq_mul_right] at hf
  simp_rw [← hf, Polynomial.toLaurent_C_mul_T, invOf_T, mul_T_assoc,
    intDegree_C_mul_T (Polynomial.leadingCoeff_ne_zero.2 hf0),
    leadingCoeff_C_mul_T]

theorem invertible_of_leadingCoeff_of_invertible [Nontrivial R] [NoZeroDivisors R]
    {p : R[T;T⁻¹]} (hp : Invertible p) :
    Invertible p.leadingCoeff := by
  refine' ⟨leadingCoeff ⅟ p, _, _⟩
    <;> simp only [← leadingCoeff_mul, invOf_mul_self', mul_invOf_self']
    <;> exact leadingCoeff_C _

theorem invertible_iff [Nontrivial R] [NoZeroDivisors R] (p : R[T;T⁻¹]) :
    IsUnit p ↔ ∃ (r : R) (m : ℤ), IsUnit r ∧ C r * T m = p :=
  ⟨fun h => ⟨p.leadingCoeff, p.intDegree, (@isUnit_of_invertible _ _ _
    (invertible_of_leadingCoeff_of_invertible h.invertible)), C_mul_T_eq_of_invertible h.invertible⟩,
  fun ⟨r, m, hr, hp⟩ => ⟨⟨C r * T m, C ((hr.unit⁻¹ : Rˣ) : R) * T (-m),
    sorry, sorry⟩, by congr⟩⟩

noncomputable instance {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    HopfAlgebra R A[T;T⁻¹] :=
  inferInstanceAs (HopfAlgebra R (AddMonoidAlgebra A ℤ))

namespace LaurentPolynomial
open scoped LaurentPolynomial

variable (R : Type*) [CommSemiring R] (A : Type*) [Semiring A] [Algebra R A]

lemma fucksake : R[T;T⁻¹] = (ℤ →₀ R) := rfl

/-- Algebra homs out of `R[T;T⁻¹]` are determined by the image of `T`. -/
noncomputable def lift : Aˣ ≃ (R[T;T⁻¹] →ₐ[R] A) :=
  ((zpowersHom _).trans (MonoidHom.equivHomUnits _ _).symm).trans (AddMonoidAlgebra.lift R ℤ A)

variable {A}

lemma lift_apply (x : Aˣ) (f : R[T;T⁻¹]) :
    lift R A x f = f.sum (fun i r => r • ((x ^ i : Aˣ) : A)) := by
  simp only [lift, Equiv.trans_apply, MonoidHom.equivHomUnits_symm_apply,
    AddMonoidAlgebra.lift_apply, MonoidHom.coe_comp, Function.comp_apply, zpowersHom_apply,
    toAdd_ofAdd, Units.coeHom_apply]

lemma lift_eq_lift (x : Aˣ) :
    (lift R A x : R[T;T⁻¹] →ₗ[R] A) = Finsupp.lift A R ℤ (fun n => (x ^ n : Aˣ)) := by
  ext
  simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
    DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
    NonUnitalAlgHom.coe_coe, lift_apply]
  rfl

@[simp] lemma lift_C (x : Aˣ) (r : R) :
    lift R A x (C r) = algebraMap R A r := by
  rw [lift_apply, ← single_eq_C r, Finsupp.sum_single_index] <;>
  simp only [zpow_zero, Units.val_one, Algebra.algebraMap_eq_smul_one, zero_smul]

@[simp] lemma lift_T (x : Aˣ) (i : ℤ) :
    lift R A x (T i) = (x ^ i : Aˣ) := by
  rw [lift_apply, T, Finsupp.sum_single_index] <;>
  simp only [one_smul, zero_smul]

@[simp] lemma lift_symm_apply (f : R[T;T⁻¹] →ₐ[R] A) :
    (lift R A).symm f = f (T 1) := by
  simp only [lift, Equiv.symm_trans_apply, Equiv.symm_symm, MonoidHom.equivHomUnits_apply,
    zpowersHom_symm_apply, MonoidHom.coe_toHomUnits, AddMonoidAlgebra.lift_symm_apply, toAdd_ofAdd,
    single_eq_C_mul_T, _root_.map_one, one_mul]

@[ext] theorem linearMap_ext {M : Type*} [AddCommMonoid M] [Module R M]
    (f g : R[T;T⁻¹] →ₗ[R] M) (h : ∀ n : ℤ, f (T n) = g (T n)) :
    f = g := Finsupp.lhom_ext' fun n => LinearMap.ext_ring <| by
  simpa only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, single_eq_C_mul_T,
    map_one, one_mul] using h n

@[ext] theorem algHom_ext (f g : R[T;T⁻¹] →ₐ[R] A) (h : f (T 1) = g (T 1)) :
    f = g := by
  ext
  simpa only [MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, AddMonoidAlgebra.of_apply,
    toAdd_ofAdd, single_eq_C_mul_T, map_one, one_mul]

noncomputable instance (m n : ℤ) : Invertible (T (R := R) m ⊗ₜ[R] T (R := R) n) := by
  infer_instance

@[simp] lemma T_zpow (m n : ℤ) :
    ((unitOfInvertible (T m) ^ n : R[T;T⁻¹]ˣ) : R[T;T⁻¹]) = T (m * n) := by
  refine' Int.induction_on n (by simp) (fun i _ => _) (fun i _ => _)
  all_goals
    simp only [← neg_add', ← inv_zpow', ← Int.ofNat_succ,
      zpow_ofNat, Units.val_pow_eq_pow_val, val_inv_unitOfInvertible,
      invOf_T, T_pow, mul_neg, mul_comm m, val_unitOfInvertible]

/-lemma comul_eq_lift :
    Coalgebra.comul (R := R) (A := R[T;T⁻¹])
      = lift R (R[T;T⁻¹] ⊗[R] R[T;T⁻¹]) (unitOfInvertible (T 1 ⊗ₜ[R] T 1)) := by
  ext
  conv_lhs =>
    simp only [fucksake, T]
  simp only [AlgHom.toNonUnitalAlgHom_eq_coe, NonUnitalAlgHom.toDistribMulActionHom_eq_coe,
    DistribMulActionHom.coe_toLinearMap, NonUnitalAlgHom.coe_to_distribMulActionHom,
    NonUnitalAlgHom.coe_coe, lift_T, TensorProduct.tmul_zpow, T_zpow, one_mul,
    Finsupp.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul, Finsupp.lsingle_apply,
    map_one]
  rfl-/

@[simp] lemma comul_T (m : ℤ) :
    Coalgebra.comul (R := R) (T (R := R) m) = T m ⊗ₜ[R] T m := by
  simp only [fucksake, T, Finsupp.comul_single, CommSemiring.comul_apply,
    TensorProduct.map_tmul]
  rfl

variable (R)

@[simp] lemma counit_C (r : R) :
    Coalgebra.counit (C r) = r := by
  simp_rw [← single_eq_C, fucksake, Finsupp.counit_single, CommSemiring.counit_apply]

@[simp] lemma counit_T (m : ℤ) :
    Coalgebra.counit (R := R) (T (R := R) m) = 1 := by
  simp only [fucksake, T, Finsupp.counit_single, CommSemiring.counit_apply]

@[simp] lemma counit_C_mul_T (r : R) (m : ℤ) :
    Coalgebra.counit (C r * T m) = r := by
  simp only [Bialgebra.counit_mul, counit_C, counit_T, mul_one]

@[simp] lemma antipode_T (m : ℤ) :
    HopfAlgebra.antipode (R := R) (T m) = T (R := R) (-m) := by
  show HopfAlgebra.antipode (AddMonoidAlgebra.single _ _) = _
  simp only [HopfAlgebra.AddMonoidAlgebra.instHopfAlgebra_antipode,
    HopfAlgebra.AddMonoidAlgebra.antipode_single, CommSemiring.antipode_eq_id]
  rfl

@[simps!] noncomputable def Finsupp.cmapDomain (A : Type*) {α β : Type*}
  [AddCommMonoid A] [Module R A] [Coalgebra R A] (f : α → β) :
  (α →₀ A) →c[R] (β →₀ A) :=
  { Finsupp.lmapDomain _ _ f with
    counit_comp := by ext; simp
    map_comp_comul := Finsupp.lhom_ext' <| fun a => by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
        Finsupp.comul_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      show (TensorProduct.map _ _ ∘ₗ _) _ = _
      congr
      ext
      simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.map_tmul, Finsupp.lsingle_apply, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single] }

noncomputable abbrev MonoidAlgebra.bmapDomain {G H A : Type*} [Monoid G]
    [Monoid H] [Semiring A] [Bialgebra R A] (f : G →* H) :
    MonoidAlgebra A G →b[R] MonoidAlgebra A H :=
  BialgHom.mk'
  (Finsupp.cmapDomain R A f)
  (by simp only [Bialgebra.ffs, MonoidAlgebra.one_def, Finsupp.cmapDomain_toFun,
    Finsupp.mapDomain_single, map_one])
  (Finsupp.lhom_ext fun g a => Finsupp.lhom_ext fun h b => by
    simp only [Bialgebra.ffs, LinearMap.compr₂_apply, CoalgHom.toLinearMap_apply,
      Finsupp.cmapDomain_toFun, LinearMap.compl₁₂_apply, Finsupp.mapDomain_single]
    simp only [← Bialgebra.ffs, LinearMap.mul_apply', MonoidAlgebra.single_mul_single,
      Finsupp.mapDomain_single, map_mul])
  (fun r => by
    simp_rw [MonoidAlgebra.coe_algebraMap, Function.comp_apply, MonoidAlgebra.single,
      Bialgebra.ffs, Finsupp.cmapDomain_toFun, Finsupp.mapDomain_single, map_one])

noncomputable abbrev AddMonoidAlgebra.bmapDomain {G H A : Type*} [AddMonoid G]
    [AddMonoid H] [Semiring A] [Bialgebra R A] (f : G →+ H) :
    AddMonoidAlgebra A G →b[R] AddMonoidAlgebra A H :=
  BialgHom.mk'
  (Finsupp.cmapDomain R A f)
  (by simp only [Bialgebra.ffs2, AddMonoidAlgebra.one_def, Finsupp.cmapDomain_toFun,
    Finsupp.mapDomain_single, map_zero])
  (Finsupp.lhom_ext fun g a => Finsupp.lhom_ext fun h b => by
    simp only [Bialgebra.ffs2, LinearMap.compr₂_apply, CoalgHom.toLinearMap_apply,
      Finsupp.cmapDomain_toFun, LinearMap.compl₁₂_apply, Finsupp.mapDomain_single]
    simp only [← Bialgebra.ffs2, LinearMap.mul_apply', AddMonoidAlgebra.single_mul_single,
      Finsupp.mapDomain_single, map_add])
  (fun r => by
    simp_rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single,
      Bialgebra.ffs2, Finsupp.cmapDomain_toFun, Finsupp.mapDomain_single, map_zero])

noncomputable def zpowBialgHom (m : ℤ) : R[T;T⁻¹] →b[R] R[T;T⁻¹] :=
  AddMonoidAlgebra.bmapDomain _ (zmultiplesHom _ m)

@[simp] lemma zpowBialgHom_T (m n : ℤ) :
    zpowBialgHom R m (T n) = T (n * m) := by
  show Finsupp.mapDomain _ (Finsupp.single _ _) = _
  simp only [zmultiplesHom_apply, smul_eq_mul, Finsupp.mapDomain_single, T]

/-noncomputable def bialgHom_lift_toFun
    [Nontrivial R] (f : R[T;T⁻¹] →c[R] R[T;T⁻¹]) : ℤ :=
    (f (T 1)).intDegree --<| by
  simp only [ne_eq, degree_eq_bot_iff, T]
  intro h
  have : Finsupp.lsum _ _ _ = Finsupp.lsum _ _ _ := f.counit_comp_apply (Finsupp.single 1 1)
  simp only [Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index,
    CommSemiring.counit_apply, h] at this
  exact zero_ne_one this
-/

lemma map_T_eq_T [Nontrivial R] [NoZeroDivisors R] (f : R[T;T⁻¹] →b[R] R[T;T⁻¹]) (m : ℤ) :
    f (T m) = T (f (T m)).intDegree := by
  conv_lhs =>
    rw [← C_mul_T_eq_of_invertible (Invertible.map f (T m))]
  have := f.counit_comp_apply (T m)
  rw [← C_mul_T_eq_of_invertible (Invertible.map f (T m)),
    counit_C_mul_T, counit_T] at this
  simp only [this, map_one, one_mul]

@[simps] noncomputable def bialgEnd_equiv [Nontrivial R] [NoZeroDivisors R] :
    (R[T;T⁻¹] →b[R] R[T;T⁻¹]) ≃ ℤ where
  toFun := fun f => (f (T 1)).intDegree
  invFun := fun n => zpowBialgHom R n
  left_inv := fun x => BialgHom.coe_algHom_injective <| algHom_ext R _ _ <| by
    simp only [AlgHom.coe_coe, zpowBialgHom_T, one_mul, ← map_T_eq_T]
  right_inv := fun n => by
    simp only [zpowBialgHom_T, one_mul, intDegree_T]

-- why have I suffered for so long without just making this
-- seriously why??????????????
lemma Finsupp.lift_single (M R : Type*) [Semiring R] [AddCommMonoid M]
    [Module R M] (X : Type*) (f : X → M) (x : X) (r : R) :
    ((Finsupp.lift M R X) f) (Finsupp.single x r) = r • f x :=
Finsupp.sum_single_index <| by simp only [LinearEquiv.coe_toAddEquiv, AddEquiv.toEquiv_eq_coe,
  EquivLike.coe_coe, AddEquiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, map_zero]

lemma single_eq_T (n : ℤ) : Finsupp.single n (1 : R) = T n := rfl

noncomputable def mulBialgHom {A : Type*} [CommSemiring A] [Bialgebra R A]
    (x y : R[T;T⁻¹] →b[R] A) : R[T;T⁻¹] →b[R] A :=
  { Finsupp.lift A R ℤ (fun n => x (T n) * y (T n)) with
    map_one' := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      rw [← single_zero_one_eq_one]
      simp only [fucksake, Finsupp.lift_single, one_smul, T_zero]
      simp only [← fucksake, map_one, one_mul]
    map_mul' := fun a b => by
      show ((LinearMap.mul R R[T;T⁻¹]).compr₂ (Finsupp.lift A R ℤ _)) a b
        = ((LinearMap.mul R A).compl₁₂ (Finsupp.lift A R ℤ _) (Finsupp.lift A R ℤ _)) a b
      congr
      ext m n
      simp only [LinearMap.mul_apply', LinearMap.compr₂_apply,
        LinearMap.compl₁₂_apply, ← T_add]
      simp_rw [fucksake, ← single_eq_T, Finsupp.lift_single, one_smul,
        ← fucksake, single_eq_T, T_add, map_mul, mul_mul_mul_comm]
    map_zero' := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_zero]
    commutes' := fun r => by
      simp_rw [AddMonoidAlgebra.coe_algebraMap, Algebra.id.map_eq_id, Function.comp_apply,
        RingHom.id_apply, single_eq_C_mul_T, T_zero, mul_one, AddHom.toFun_eq_coe,
        LinearMap.coe_toAddHom, ← single_eq_C]
      simp only [fucksake, Finsupp.lift_single, zero_smul,
        T_zero]
      simp_rw [← fucksake, map_one, one_mul, Algebra.algebraMap_eq_smul_one]
    counit_comp := by
      ext n
      simp_rw [LinearMap.coe_comp, Function.comp_apply, counit_T, ← single_eq_T,
        fucksake, Finsupp.lift_single, one_smul, Bialgebra.counit_mul,
        ← fucksake, BialgHom.counit_comp_apply, fucksake, Finsupp.counit_single,
        Bialgebra.counit_one, mul_one]
    map_comp_comul := by
      ext n
      simp_rw [LinearMap.coe_comp, Function.comp_apply, comul_T, TensorProduct.map_tmul,
      ← single_eq_T, fucksake, Finsupp.lift_single, one_smul, Bialgebra.comul_mul,
      ← fucksake, ← BialgHom.map_comp_comul_apply, single_eq_C_mul_T, map_one, one_mul, comul_T,
      TensorProduct.map_tmul, BialgHom.toLinearMap_apply, Algebra.TensorProduct.tmul_mul_tmul] }

@[simp] lemma mulBialgHom_T {A : Type*} [CommSemiring A] [Bialgebra R A]
    (x y : R[T;T⁻¹] →b[R] A) (m : ℤ) :
    mulBialgHom R x y (T m) = x (T m) * y (T m) := by
  simp only [mulBialgHom, BialgHom.coe_mk]
  simp only [← single_eq_T, fucksake, Finsupp.lift_single, one_smul]

@[simps!] noncomputable def oneBialgHom {A : Type*} [CommSemiring A] [Bialgebra R A] :
    R[T;T⁻¹] →b[R] A :=
  { (Algebra.ofId R A).comp (Bialgebra.counitAlgHom R R[T;T⁻¹]) with
    map_smul' := fun r x => by
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, map_smul, AlgHom.coe_comp,
        Function.comp_apply, Bialgebra.counitAlgHom_apply, RingHom.id_apply]
    counit_comp := by
      ext
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_comp,
        LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        Bialgebra.counitAlgHom_apply, counit_T, map_one, Bialgebra.counit_one]
    map_comp_comul := by
      ext
      simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.coe_comp,
        LinearMap.coe_comp, Function.comp_apply, comul_T, TensorProduct.map_tmul, LinearMap.coe_mk,
        AddHom.coe_mk, Bialgebra.counitAlgHom_apply, counit_T, map_one, Bialgebra.comul_one]
      rfl }

abbrev _root_.Bialgebra.char
    (R : Type*) [CommSemiring R] (A : Type*) [Semiring A] [Bialgebra R A] :=
  R[T;T⁻¹] →b[R] A

noncomputable instance _root_.Bialgebra.instCommMonoidChar
    {A : Type*} [CommSemiring A] [Bialgebra R A] :
    CommMonoid (Bialgebra.char R A) where
  mul := mulBialgHom R
  mul_assoc := fun a b c => by
    simp only [(· * ·)]
    refine' BialgHom.coe_algHom_injective _
    ext
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, AlgHom.coe_coe, Function.comp_apply,
      AddMonoidAlgebra.of_apply, toAdd_ofAdd, single_eq_C_mul_T, map_one, one_mul, mulBialgHom_T,
      mul_assoc]
  one := oneBialgHom R
  one_mul := fun a => by
    show mulBialgHom R (oneBialgHom R) _ = _
    refine' BialgHom.coe_algHom_injective _
    ext
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, AlgHom.coe_coe, Function.comp_apply,
      AddMonoidAlgebra.of_apply, toAdd_ofAdd, single_eq_C_mul_T, map_one, one_mul, mulBialgHom_T,
      oneBialgHom_toFun, counit_T]
  mul_one := fun a => by
    show mulBialgHom R _ (oneBialgHom R) = _
    refine' BialgHom.coe_algHom_injective _
    ext
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, AlgHom.coe_coe, Function.comp_apply,
      AddMonoidAlgebra.of_apply, toAdd_ofAdd, single_eq_C_mul_T, map_one, one_mul, mulBialgHom_T,
      oneBialgHom_toFun, counit_T, mul_one]
  mul_comm := fun a b => by
    simp only [(· * ·)]
    refine' BialgHom.coe_algHom_injective _
    ext
    simp only [MonoidHom.coe_comp, MonoidHom.coe_coe, AlgHom.coe_coe, Function.comp_apply,
      AddMonoidAlgebra.of_apply, toAdd_ofAdd, single_eq_C_mul_T, map_one, one_mul, mulBialgHom_T,
      mul_comm (a _)]

@[simp] lemma mul_def {A : Type*} [CommSemiring A] [Bialgebra R A] (x y : R[T;T⁻¹] →b[R] A) :
    x * y = mulBialgHom R x y := rfl

@[simp] lemma one_def {A : Type*} [CommSemiring A] [Bialgebra R A] :
    (1 : R[T;T⁻¹] →b[R] A) = oneBialgHom R := rfl

-- why does simp keep crashing lean? maybe my api bad
noncomputable def bialgEnd_addEquiv [Nontrivial R] [NoZeroDivisors R] :
    Additive (Bialgebra.char R R[T;T⁻¹]) ≃+ ℤ :=
AddEquiv.symm { (bialgEnd_equiv R).symm.trans Additive.ofMul with
    map_add' := fun x y => by
      dsimp
      rw [← ofMul_mul]
      congr
      refine' BialgHom.coe_algHom_injective (algHom_ext R _ _ _)
      simp only [AlgHom.coe_coe, mul_def, mulBialgHom_T, zpowBialgHom_T,
        one_mul, T_add] }
