module

public import Mathlib.CFT.IsStandardEtale
public import Mathlib.CFT.StandardSmooth
public import Mathlib.CFT.SymmetricPolynomial
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.Flat

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]


open Polynomial

open scoped Finset nonZeroDivisors in
theorem Polynomial.eq_zero_of_degree_lt_of_eval_eq_zero {f : R[X]}
    (s : Finset R) (degree_f_lt : f.degree < ↑(#s)) (eval_f : ∀ x ∈ s, eval x f = 0)
    (hs : (s : Set R).Pairwise (· - · ∈ R⁰)) : f = 0 := by
  classical
  nontriviality R
  induction s using Finset.induction generalizing f with
  | empty => simpa using degree_f_lt
  | insert a s has IH =>
    by_contra hf
    have hfs : f.degree ≤ #s := by
      simp only [degree_eq_natDegree hf, Nat.cast_lt, Nat.cast_le] at degree_f_lt ⊢
      simpa [has, Nat.lt_add_one_iff] using degree_f_lt
    have := IH (f := f /ₘ (X - C a)) ((degree_divByMonic_lt _ (monic_X_sub_C _) hf
      (by simp)).trans_le hfs) (fun x hx ↦ by
      have : (x - a) * eval x (f /ₘ (X - C a)) = 0 := by
        simpa [eval_f a, eval_f x (Finset.mem_insert_of_mem hx)] using
          congr($(modByMonic_add_div f (monic_X_sub_C a)).eval x)
      exact (hs (Finset.mem_insert_of_mem hx) (Finset.mem_insert_self _ _) (by grind):).1 _ this)
      (Set.pairwise_insert.mp (by simpa using hs)).1
    simpa [this, eval_f a, Ne.symm hf] using modByMonic_add_div f (monic_X_sub_C a)

lemma IsPrimitiveRoot.mk_of_natPrime {p : ℕ} (hp : p.Prime) {ζ : R}
    (hζ : ζ ^ p = 1) (hζ' : ζ ≠ 1) : IsPrimitiveRoot ζ p := by
  obtain ⟨k, hk, hζk⟩ := IsPrimitiveRoot.exists_pos hζ hp.ne_zero
  by_cases hk1 : k = 1
  · simpa [hk1, hζ'] using hζk.1
  · exact (hp.dvd_iff_eq hk1).mp (hζk.2 _ hζ) ▸ hζk

lemma IsPrimitiveRoot.cyclotomic_eq_of_isDomain [IsDomain R]
    {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    ∏ i ∈ .range n with n.Coprime i, (X - C (ζ ^ i)) = cyclotomic n R := by
  by_cases hn : n = 0; · simp [hn]
  by_cases hn₁ : n = 1; · simp [hn₁]
  replace hn₁ : 1 < n := by lia
  classical
  let s := ((Finset.range n).filter (n.Coprime ·)).image (ζ ^ ·)
  have hs : s.card = n.totient := by
    rw [Finset.card_image_of_injOn (hζ.injOn_pow.mono (by grind))]
    simp [Nat.totient_eq_card_coprime]
  rw [eq_comm]
  apply Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq s
  · refine (degree_sub_lt ?_ ?_ ?_).trans_le ?_
    · rw [degree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
      simp [degree_X_sub_C, -map_pow, Nat.totient_eq_card_coprime, degree_cyclotomic]
    · rw [ne_eq, ← degree_eq_bot]; simp [degree_cyclotomic]
    · rw [monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _, cyclotomic.monic]
    · simp [degree_cyclotomic, hs]
  · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, map_pow, forall_exists_index,
      and_imp, s]
    rintro _ i hin hni rfl
    rw [((hζ.pow_iff_coprime (Ne.bot_lt hn) _).mpr hni.symm).isRoot_cyclotomic (Ne.bot_lt hn)]
    rw [eval_prod, Finset.prod_eq_zero (i := i) (by simpa [hin])]
    simp

open Polynomial in
lemma cyclotomic_eq_prod_of_eval_eq_zero {R : Type*} [CommRing R]
    {n : ℕ} {ζ : R} (hζ : eval ζ (cyclotomic n R) = 0) :
    ∏ i ∈ .range n with n.Coprime i, (X - C (ζ ^ i)) = cyclotomic n R := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  let f : AdjoinRoot (cyclotomic n ℤ) →+* R := AdjoinRoot.lift (algebraMap ℤ R) ζ
    (by rwa [← eval_map, map_cyclotomic])
  have : IsDomain (AdjoinRoot (cyclotomic n ℤ)) := AdjoinRoot.isDomain_of_prime
    (cyclotomic.irreducible hn.bot_lt).prime
  have : NoZeroSMulDivisors ℤ (AdjoinRoot (cyclotomic n ℤ)) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (cyclotomic.irreducible hn.bot_lt).prime
    (by simp [degree_cyclotomic, hn])
  have : CharZero (AdjoinRoot (cyclotomic n ℤ)) := .of_addMonoidHom
    (algebraMap ℤ _).toAddMonoidHom (by simp) (FaithfulSMul.algebraMap_injective _ _)
  have : IsPrimitiveRoot (AdjoinRoot.root (cyclotomic n ℤ)) n :=
    have : NeZero (n : AdjoinRoot (cyclotomic n ℤ)) := ⟨by simpa⟩
    isRoot_cyclotomic_iff.mp (by
      rw [← map_cyclotomic n (algebraMap ℤ (AdjoinRoot (cyclotomic n ℤ))), IsRoot,
        eval_map_algebraMap]
      simp)
  have := congr($(this.cyclotomic_eq_of_isDomain).map f)
  simpa [Polynomial.map_prod, f] using this

lemma Polynomial.IsRoot.isUnit {p : R[X]} {x : R} (h : p.IsRoot x) (hp : IsUnit (p.coeff 0)) :
    IsUnit x := by
  refine isUnit_of_dvd_unit ?_ hp.neg
  exact ⟨_, .symm <| by simpa [h.eq_zero, add_eq_zero_iff_eq_neg', modByMonic_X,
    ← coeff_zero_eq_eval_zero] using congr($(p.modByMonic_add_div monic_X).eval x)⟩

theorem isUnit_pow_sub_pow_of_isRoot_cyclotomic {p : ℕ} (hp : p.Prime) (hp' : IsUnit (p : R))
    {ζ : R} (hζ : (cyclotomic p R).IsRoot ζ) (i j : Fin p) (hij : i ≠ j) :
    IsUnit (ζ ^ i.1 - ζ ^ j.1) := by
  wlog hij : i < j generalizing i j
  · simpa using (this j i (.symm ‹_›) (lt_of_le_of_ne (le_of_not_gt hij) (.symm ‹_›))).neg
  have := Fact.mk hp
  have : ∏ x ∈ Finset.range p with p.Coprime x, (1 - ζ ^ x) = p := by
    simpa [eval_prod, cyclotomic_prime] using
      congr($(cyclotomic_eq_prod_of_eval_eq_zero hζ).eval 1)
  rw [← Nat.sub_add_cancel (show i.1 ≤ j.1 from hij.le), ← one_mul (ζ ^ i.1), pow_add, ← sub_mul]
  refine .mul (isUnit_of_dvd_unit ?_ (hp'.map (algebraMap R _))) (.pow _ ?_)
  · simp only [Algebra.algebraMap_self, ← this, map_prod, RingHom.id_apply]
    have H : ¬p ∣ j - i := Nat.not_dvd_of_pos_of_lt (by lia) (by lia)
    exact Finset.dvd_prod_of_mem _ (by simp [Nat.sub_lt_of_lt, hp.coprime_iff_not_dvd, H])
  · exact hζ.isUnit (by simp [cyclotomic_coeff_zero _ hp.one_lt])

lemma RingHom.IsIntegralElem.map {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {x : S} (hx : f.IsIntegralElem x) (g : S →+* T) :
    (g.comp f).IsIntegralElem (g x) := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, by simp_rw [← hom_eval₂, eval₂_eq_eval_map] at hx ⊢; simp [hx]⟩

lemma RingHom.IsIntegralElem.of_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} {x : T} (hx : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p.map f, hp.map _, by simpa only [eval₂_eq_eval_map, Polynomial.map_map] using hx⟩

open TensorProduct in
attribute [local instance] Polynomial.algebra in
set_option maxHeartbeats 0 in
theorem isIntegral_coeff_of_isIntegral_aux
    (p : ℕ) (hp : p.Prime) (hp' : IsUnit (p : R)) {f : S[X]} (hfp : f.natDegree < p)
    (hf : IsIntegral R[X] f)
    (n : ℕ) : IsIntegral R (f.coeff n) := by
  classical
  nontriviality R
  nontriviality S
  let R' := AdjoinRoot (cyclotomic p R)
  have inst : Module.Finite R R' := (AdjoinRoot.powerBasis' (cyclotomic.monic p R)).finite
  have inst : Module.Free R R' := .of_basis (AdjoinRoot.powerBasis' (cyclotomic.monic p R)).basis
  have : Nontrivial (S ⊗[R] R') := by
    have : Nonempty (Fin (cyclotomic p R).natDegree) :=
      Fin.pos_iff_nonempty.mp (by simp [natDegree_cyclotomic, hp.pos])
    have := ((AdjoinRoot.powerBasis' (cyclotomic.monic p R)).basis.baseChange S).repr
    rw [AdjoinRoot.powerBasis'_dim] at this
    exact this.nontrivial
  have : Nontrivial (R' ⊗[R] S) := (Algebra.TensorProduct.comm _ _ _).nontrivial
  let ζ : R' := .root _
  have hζ₀ : aeval ζ (cyclotomic p R) = 0 :=
        ((AdjoinRoot.aeval_eq (cyclotomic p R) (f := cyclotomic p R)).trans AdjoinRoot.mk_self)
  have hζ₀' : (cyclotomic p R').IsRoot ζ := by rwa [← eval_map_algebraMap, map_cyclotomic] at hζ₀
  let f' : (R' ⊗[R] S)[X] := f.map Algebra.TensorProduct.includeRight.toRingHom
  let ζ' : R' ⊗[R] S := ζ ⊗ₜ 1
  have hζ'₀ : (cyclotomic p (R' ⊗[R] S)).IsRoot ζ' := by
    simpa using hζ₀'.map (f := algebraMap R' (R' ⊗[R] S))
  have Hsub (i j : Fin p) (hij : i ≠ j) : IsUnit (ζ ^ i.1 - ζ ^ j.1) :=
    isUnit_pow_sub_pow_of_isRoot_cyclotomic hp (by simpa [R'] using hp'.map (algebraMap _ _))
      hζ₀' _ _ hij
  have Hsub' (i j : Fin p) (hij : i ≠ j) : IsUnit (ζ' ^ i.1 - ζ' ^ j.1) :=
    isUnit_pow_sub_pow_of_isRoot_cyclotomic hp (by simpa [R'] using hp'.map (algebraMap _ _))
      hζ'₀ _ _ hij
  have hζ' : IsPrimitiveRoot ζ' p := by
    refine .mk_of_natPrime hp ?_ ?_
    · have := aeval_eq_zero_of_dvd_aeval_eq_zero (cyclotomic.dvd_X_pow_sub_one _ _) hζ'₀
      simpa [sub_eq_zero, ζ'] using this
    · intro e
      have := Fact.mk hp
      have : (p : R' ⊗[R] S) = 0 := by simpa [e, cyclotomic_prime, R'] using hζ'₀
      simpa [this, R'] using (hp'.map (algebraMap R (R' ⊗[R] S))).ne_zero
  have : f' - ∑ i ∈ (Finset.range p).attach, C (f'.eval (ζ' ^ i.1)) *
      ∏ j ∈ ((Finset.range p).erase i).attach, (X - C (ζ' ^ j.1)) *
        C ((Hsub' ⟨i.1, by grind⟩ ⟨j.1, by grind⟩ (by grind)).unit⁻¹).1 = 0 := by
    by_contra H
    refine H (Polynomial.eq_zero_of_degree_lt_of_eval_eq_zero
      ((Finset.range p).image (ζ' ^ ·)) ?_ ?_ ?_)
    · rw [← Polynomial.natDegree_lt_iff_degree_lt H]
      refine (natDegree_sub_le _ _).trans_lt (max_lt (natDegree_map_le.trans_lt ?_) ?_)
      · rwa [Finset.card_image_of_injOn hζ'.injOn_pow, Finset.card_range]
      · refine (natDegree_sum_le _ _).trans_lt ((Finset.fold_max_lt _).mpr ?_)
        simp only [Finset.card_pos, Finset.image_nonempty, Finset.nonempty_range_iff, ne_eq,
          hp.ne_zero, not_false_eq_true, Finset.mem_attach, Function.comp_apply,
          forall_const, Subtype.forall, Finset.mem_range, true_and]
        intro i hip
        grw [natDegree_C_mul_le, natDegree_prod_le]
        refine (Finset.sum_le_sum fun _ _ ↦ (natDegree_mul_C_le _ _).trans
          (natDegree_X_sub_C_le _)).trans_lt ?_
        simpa [Finset.card_image_of_injOn hζ'.injOn_pow] using
          Finset.card_erase_lt_of_mem (Finset.mem_range.mpr hip)
    · simp only [Finset.mem_image, Finset.mem_range, map_pow, eval_sub, eval_finset_sum, eval_mul,
        eval_C, eval_prod, eval_X, eval_pow, sub_eq_zero, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro i hip
      rw [Finset.sum_eq_single ⟨i, Finset.mem_range.mpr hip⟩]
      · simp
      · simp only [Finset.mem_attach, ne_eq, forall_const, Subtype.forall, Finset.mem_range,
          Subtype.mk.injEq]
        intro j hjp hji
        rw [Finset.prod_eq_zero (Finset.mem_attach _ ⟨i, by grind⟩), mul_zero]
        simp
      · simp
    · rw [Finset.coe_image, Set.InjOn.pairwise_image hζ'.injOn_pow, Finset.coe_range]
      refine fun i hi j hj hij ↦ (Hsub' ⟨i, hi⟩ ⟨j, hj⟩ (by simpa)).mem_nonZeroDivisors
  have hf' : IsIntegral R'[X] f' := by
    let φ : S[X] →ₐ[R[X]] (R' ⊗[R] S)[X] :=
      ⟨mapRingHom Algebra.TensorProduct.includeRight.toRingHom,
        fun r ↦ by simp [Polynomial.map_map]⟩
    have : IsScalarTower R[X] R'[X] (R' ⊗[R] S)[X] := .of_algebraMap_eq fun r ↦
      by simp [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact (hf.map φ).tower_top
  have : IsIntegral R' (f'.coeff n) := by
    rw [sub_eq_zero.mp this, finset_sum_coeff]
    refine .sum _ fun i hi ↦ ?_
    rw [coeff_C_mul]
    refine .mul ?_ ?_
    · refine RingHom.IsIntegralElem.of_comp (f := evalRingHom (ζ ^ i.1)) ?_
      convert RingHom.IsIntegralElem.map hf' (evalRingHom (ζ' ^ i.1))
      ext <;> simp [R', ζ']
    · refine isIntegral_coeff_prod _ _ (fun ⟨j, hj⟩ _ k ↦ ?_) _
      obtain ⟨hj₁, hj₂⟩ : j ≠ ↑i ∧ j < p := by simpa using hj
      rw [coeff_mul_C]
      refine .mul ?_ ?_
      · simp only [coeff_sub, coeff_X, coeff_C]
        split_ifs
        · exact .sub isIntegral_one
            (by simpa [ζ'] using isIntegral_algebraMap (A := R' ⊗[R] S) (x := ζ ^ j))
        · simpa using isIntegral_one
        · simpa [ζ'] using isIntegral_algebraMap (A := R' ⊗[R] S) (x := ζ ^ j)
        · simpa using isIntegral_zero
      · convert isIntegral_algebraMap
          (x := (Hsub ⟨i, Finset.mem_range.mp i.2⟩ ⟨j, hj₂⟩ (by simp [hj₁.symm])).unit⁻¹.1)
        convert_to _ = (((Hsub ⟨i, Finset.mem_range.mp i.2⟩ ⟨j, hj₂⟩
          (by simp [hj₁.symm]))).unit.map (algebraMap R' (R' ⊗[R] S)).toMonoidHom)⁻¹.1
        congr 2; ext; simp [ζ', sub_tmul]
  have inst : FaithfulSMul S (S ⊗[R] R') := Module.Free.instFaithfulSMulOfNontrivial _ _
  have : IsIntegral R (1 ⊗ₜ[R] f.coeff n : R' ⊗[R] S) := by simpa [f'] using isIntegral_trans _ this
  exact (this.map (Algebra.TensorProduct.comm _ _ _).toAlgHom).tower_bot (A := S)
    (FaithfulSMul.algebraMap_injective _ _)

open TensorProduct in
attribute [local instance] Polynomial.algebra in
theorem isIntegral_coeff_of_isIntegral {f : S[X]} (hf : IsIntegral R[X] f)
    (n : ℕ) : IsIntegral R (f.coeff n) := by
  obtain ⟨p, hfp, hp⟩ := (f.natDegree + 1).exists_infinite_primes
  obtain ⟨q, hpq, hq⟩ := (p + 1).exists_infinite_primes
  have (p : ℕ) (hp : p.Prime) (hp' : f.natDegree < p) : ∃ i, IsIntegral R (p ^ i * f.coeff n) := by
    let := (Localization.awayMap (algebraMap R S) p).toAlgebra
    have : IsScalarTower R (Localization.Away (p : R)) (Localization.Away (algebraMap R S p)) :=
      .of_algebraMap_eq fun r ↦ by simp [RingHom.algebraMap_toAlgebra, Localization.awayMap,
        IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply]
    have := isIntegral_coeff_of_isIntegral_aux p hp (R := Localization.Away (p : R))
      (by simpa using IsLocalization.Away.algebraMap_isUnit (p : R))
      (S := Localization.Away (algebraMap R S p)) (f := f.map (algebraMap _ _))
      (by grw [natDegree_map_le]; lia) (by
        let φ : S[X] →ₐ[R[X]] (Localization.Away (algebraMap R S p))[X] :=
          ⟨mapRingHom (algebraMap _ _),
            fun r ↦ by simp [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]⟩
        have : IsScalarTower R[X] (Localization.Away (p : R))[X]
          (Localization.Away (algebraMap R S p))[X] :=
          .of_algebraMap_eq fun r ↦
          by simp [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
        exact (hf.map φ).tower_top) n
    obtain ⟨⟨_, i, rfl⟩, hi⟩ := this.exists_multiple_integral_of_isLocalization (.powers (p : R)) _
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map
      (M := .powers (p : R)) (Sₘ := Localization.Away (algebraMap R S p))
      (x := p ^ i * f.coeff n) (by simpa [Submonoid.smul_def, Algebra.smul_def] using hi)
    exact ⟨j + i, by simpa [Algebra.smul_def, pow_add, mul_assoc] using hj⟩
  obtain ⟨i, hi⟩ := this p hp hfp
  obtain ⟨j, hj⟩ := this q hq (by lia)
  have : q.Coprime p := hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hp.pos hpq)
  obtain ⟨a, b, e⟩ := ((this.pow_left j).pow_right i).isCoprime
  replace e : (↑a * ↑q ^ j + ↑b * ↑p ^ i : S) = 1 := by simpa using congr(($e : S))
  have := (hj.smul a).add (hi.smul b)
  simpa [← mul_assoc, ← add_mul, e] using this

attribute [local instance] Polynomial.algebra in
theorem isIntegral_iff_isIntegral_coeff {f : S[X]} :
    IsIntegral R[X] f ↔ ∀ n, IsIntegral R (f.coeff n) := by
  refine ⟨isIntegral_coeff_of_isIntegral, fun H ↦ ?_⟩
  rw [← f.sum_monomial_eq, Polynomial.sum]
  simp only [← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S)]
  exact .sum _ fun i _ ↦ ((H i).map (CAlgHom (R := R))).tower_top.mul (.pow isIntegral_algebraMap _)

variable {B : Type*} [CommRing B] [Algebra R B]

lemma IsIntegral.of_aeval_monic_of_isIntegral_coeff {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} {p : A[X]} (monic : p.Monic) (deg : p.natDegree ≠ 0)
    (hx : IsIntegral R (eval x p)) (hp : ∀ i, IsIntegral R (p.coeff i)) : IsIntegral R x := by
  obtain ⟨q, hqp, hdeg, hq⟩ :=
    lifts_and_natDegree_eq_and_monic (p := p) (f := algebraMap (integralClosure R A) _)
    (p.lifts_iff_coeff_lifts.mpr (by simpa)) monic
  exact isIntegral_trans _ (.of_aeval_monic hq (hdeg ▸ deg)
    (by simpa [← eval_map_algebraMap, hqp] using hx.tower_top))

attribute [local instance] Polynomial.algebra in
/-- Let `S` be an `R`-algebra and `f : S[X]` be a monic polynomial with `R`-integral coefficients.
Suppose `y` in `B = S[X]/f` is `R`-integral, then `f' * y` is the image of some `g : S[X]` with
`R`-integral coefficients. -/
-- We can also know that `deg g = deg f - 1`. Upgrade the lemma if we care.
lemma exists_derivative_mul_eq_and_isIntegral_coeff
    {φ : S[X] →ₐ[R] B} (hφ : Function.Surjective φ) {f : S[X]} (hf : f.Monic)
    (hf' : ∀ i, IsIntegral R (f.coeff i))
    (hfx : RingHom.ker φ.toRingHom = .span {f}) {y : B} (hy : IsIntegral R y) :
    ∃ (g : S[X]), φ f.derivative * y = φ g ∧ ∀ i, IsIntegral R (g.coeff i) := by
  cases subsingleton_or_nontrivial B
  · exact ⟨0, Subsingleton.elim _ _, by simp [isIntegral_zero]⟩
  have hfd : f.natDegree ≠ 0 := by
    rw [ne_eq, hf.natDegree_eq_zero]
    rintro rfl
    simpa using (RingHom.ker_ne_top φ.toRingHom).symm.trans_eq hfx
  classical
  let := (φ.toRingHom.comp C).toAlgebra
  have : IsScalarTower R S B := .of_algebraMap_eq' (φ.comp CAlgHom).comp_algebraMap.symm
  have := (algebraMap S B).domain_nontrivial
  obtain ⟨y, rfl⟩ := hφ y
  let S' := f.SplittingAlgebra
  have hS' : (f.map (algebraMap S S')).Splits := splits_splittingAlgebra _ hf
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hS'
  simp only [hf.map _, Monic.leadingCoeff, map_one, one_mul] at hm
  algebraize [(algebraMap S S').comp (algebraMap R S)]
  have hm' : ∀ a ∈ m, IsIntegral R a := by
    refine fun a ham ↦ .of_aeval_monic_of_isIntegral_coeff (hf.map (algebraMap _ _)) ?_ ?_ ?_
    · rwa [hf.natDegree_map]
    · rw [hm, eval_multiset_prod, Multiset.prod_eq_zero]
      · exact isIntegral_zero
      · simpa using ⟨a, ham, by simp⟩
    · simp only [coeff_map]
      exact fun _ ↦ (hf' _).algebraMap
  have hmc : m.card = f.natDegree := by
    simpa [hf.natDegree_map, natDegree_multiset_prod_of_monic] using congr(($hm).natDegree).symm
  have H : (f.derivative * y %ₘ f).map (algebraMap S S') =
        (m.map fun x ↦ ((m.erase x).map (X - C ·)).prod * C (aeval x y)).sum := by
    have ⟨g, hg⟩ : f.map (algebraMap _ _) ∣ (f.derivative * y).map (algebraMap S S') -
        (m.map fun x ↦ ((m.erase x).map (X - C ·)).prod * C (aeval x y)).sum := by
      rw [Polynomial.map_mul, ← Polynomial.derivative_map, hm, derivative_prod,
        ← Multiset.sum_map_mul_right, ← Multiset.sum_map_sub]
      refine Multiset.dvd_sum ?_
      simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, ← mul_sub,
        Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a ham
      conv_lhs => rw [← Multiset.cons_erase ham]
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
      refine mul_dvd_mul_left _ ?_
      rw [Polynomial.dvd_iff_isRoot]
      simp
    rw [map_modByMonic _ hf]
    refine (div_modByMonic_unique g _ (hf.map _) ⟨(sub_eq_iff_eq_add'.mp hg).symm, ?_⟩).2
    refine degree_lt_degree ?_
    rw [hf.natDegree_map, ← Nat.le_sub_one_iff_lt (Ne.bot_lt hfd)]
    refine (natDegree_multiset_sum_le _).trans (Multiset.max_le_of_forall_le _ _ ?_)
    simp only [Multiset.map_map, Function.comp_apply, Multiset.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    refine fun a ha ↦ (natDegree_mul_C_le _ _).trans ((natDegree_multiset_prod_le _).trans ?_)
    simp [ha, hmc]
  have : IsScalarTower R[X] S[X] S'[X] := .of_algebraMap_eq' (mapRingHom_comp ..).symm
  have H' : IsIntegral R[X] (f.derivative * y %ₘ f) := by
    refine .tower_bot (B := S'[X]) (map_injective _ (FaithfulSMul.algebraMap_injective S S')) ?_
    simp only [algebraMap_def, coe_mapRingHom, H]
    refine .multiset_sum ?_
    simp only [Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine fun a ham ↦ .mul (.multiset_prod ?_) ?_
    · simp only [Multiset.mem_map, isIntegral_iff_isIntegral_coeff, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, coeff_sub]
      exact fun b hbm n ↦ .sub (by simp [coeff_X, apply_ite, isIntegral_one, isIntegral_zero])
        (by simp [coeff_C, apply_ite, isIntegral_zero, hm' b (Multiset.mem_of_mem_erase hbm)])
    · let ψ : B →ₐ[R] S' := AlgHom.liftOfSurjective _ hφ ((aeval a).restrictScalars R) <| by
        rw [hfx, Ideal.span_le]
        suffices (m.map (a - ·)).prod = 0 by simpa [← eval_map_algebraMap, hm, eval_multiset_prod]
        rw [Multiset.prod_eq_zero]
        simpa using ⟨a, ham, by simp⟩
      simpa [isIntegral_iff_isIntegral_coeff, coeff_C, apply_ite, isIntegral_zero, ψ] using hy.map ψ
  refine ⟨_, ?_, isIntegral_iff_isIntegral_coeff.mp H'⟩
  rw [modByMonic_eq_sub_mul_div _ hf, map_sub, map_mul, map_mul,
    show φ f = 0 from hfx.ge (Ideal.mem_span_singleton_self _), zero_mul, sub_zero]

lemma Polynomial.Monic.leadingCoeff_C_mul {R : Type*} [CommRing R] {p : R[X]}
    (hp : p.Monic) (r : R) : (C r * p).leadingCoeff = r := by
  by_cases hr : r = 0; · simp_all
  rw [← Polynomial.coeff_natDegree, natDegree_C_mul_of_mul_ne_zero (by simp_all), coeff_C_mul,
    hp.coeff_natDegree, mul_one]

/-- If `t` is `R`-integral in `S[M⁻¹]` where `M` is a submonoid of `R`,
then `m • t` is integral in `S` for some `m ∈ M`. -/
lemma IsLocalization.Away.exists_isIntegral_smul_of_isIntegral_map
    {R S Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Sₘ] [Algebra R S] [Algebra S Sₘ]
    [Algebra R Sₘ] [IsScalarTower R S Sₘ] {r : S} (hr : IsIntegral R r)
    [IsLocalization.Away r Sₘ] {x : S}
    (hx : IsIntegral R (algebraMap S Sₘ x)) : ∃ n, IsIntegral R (r ^ n * x) := by
  nontriviality S
  obtain ⟨p, hpm, hp⟩ := hx
  simp only [IsScalarTower.algebraMap_eq R S Sₘ, ← hom_eval₂,
    IsLocalization.map_eq_zero_iff (.powers r), Subtype.exists, Submonoid.mem_powers_iff,
    exists_prop, exists_exists_eq_and] at hp
  obtain ⟨m, hm⟩ := hp
  have := isIntegral_trans (R := R) _ (isIntegral_leadingCoeff_smul (R := integralClosure R S)
    (C ⟨r, hr⟩ ^ m * p.map (algebraMap _ _)) x (by simpa [← aeval_def] using hm))
  rw [← map_pow, (hpm.map _).leadingCoeff_C_mul] at this
  exact ⟨m, this⟩

open TensorProduct

attribute [local instance] Polynomial.algebra in
theorem mem_adjoin_map_integralClosure_of_isStandardEtale
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.IsStandardEtale R S]
    (x : S ⊗[R] B) (hx : IsIntegral S x) :
    x ∈ Algebra.adjoin S
      ((integralClosure R B).map Algebra.TensorProduct.includeRight : Subalgebra R (S ⊗[R] B)) := by
  have 𝓟 := Classical.ofNonempty (α := StandardEtalePresentation R S)
  obtain ⟨n, hx⟩ : ∃ n, ∀ m, IsIntegral R ((aeval 𝓟.x 𝓟.g) ^ (n + m) • x) := by
    let e := 𝓟.equivRing.trans 𝓟.equivAwayAdjoinRoot
    let := (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R (AdjoinRoot 𝓟.f) _)).toAlgebra
    have := IsScalarTower.of_algebraMap_eq'
      (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R (AdjoinRoot 𝓟.f) _)).comp_algebraMap.symm
    have := IsLocalization.isLocalization_of_algEquiv (R := AdjoinRoot 𝓟.f) (.powers (.mk _ 𝓟.g))
      { toRingEquiv := e.symm.toRingEquiv, commutes' := by simp [RingHom.algebraMap_toAlgebra] }
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := AdjoinRoot 𝓟.f) (.powers (.mk _ 𝓟.g)) _ hx
    replace hm := fun k : ℕ ↦ (isIntegral_algebraMap (x := AdjoinRoot.mk 𝓟.f 𝓟.g ^ k)).mul hm
    simp only [Submonoid.smul_def, ← @IsScalarTower.algebraMap_smul (AdjoinRoot 𝓟.f) S,
      ← map_pow, ← Algebra.smul_def, ← mul_smul, ← map_mul, ← pow_add, add_comm _ m] at hm
    simp_rw [map_pow] at hm
    have := 𝓟.monic_f.finite_adjoinRoot
    suffices algebraMap (AdjoinRoot 𝓟.f) S (.mk _ 𝓟.g) = aeval 𝓟.x 𝓟.g from
      ⟨m, fun k ↦ this ▸ isIntegral_trans (R := R) _ (hm k)⟩
    simp [RingHom.algebraMap_toAlgebra, e, StandardEtalePair.equivAwayAdjoinRoot,
      ← aeval_def, ← aeval_algHom_apply]
  let 𝓟' := 𝓟.baseChange (A := B)
  let e := 𝓟'.equivRing.trans 𝓟'.equivAwayAdjoinRoot
  obtain ⟨x, rfl⟩ := (Algebra.TensorProduct.comm _ _ _).surjective x
  obtain ⟨x, rfl⟩ := e.symm.surjective x
  obtain ⟨x, ⟨_, m, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (R := AdjoinRoot 𝓟'.f) (.powers (.mk _ 𝓟'.g)) x
  have hfg : IsIntegral R (AdjoinRoot.mk 𝓟'.f 𝓟'.g) := by
    have := 𝓟.monic_f.finite_adjoinRoot
    let e : AdjoinRoot 𝓟.f →ₐ[R] AdjoinRoot 𝓟'.f :=
      AdjoinRoot.mapAlgHom (Algebra.ofId _ _) _ _ (dvd_refl _)
    convert (Algebra.IsIntegral.isIntegral (R := R) (AdjoinRoot.mk 𝓟.f 𝓟.g)).map e
    have : (AdjoinRoot.mk 𝓟'.f).comp (mapRingHom (algebraMap R B)) =
        e.toRingHom.comp (AdjoinRoot.mk _) := by ext <;> simp [e]
    exact congr($this 𝓟.g)
  have heg (g : R[X]) : e (1 ⊗ₜ aeval 𝓟.x g) =
      algebraMap _ _ (AdjoinRoot.mk 𝓟'.f (g.map (algebraMap _ _))) := by
    trans e (aeval (1 ⊗ₜ 𝓟.x) (g.map (algebraMap _ B)))
    · rw [← Algebra.TensorProduct.includeRight_apply, ← aeval_algHom_apply]
      simp [StandardEtalePresentation.baseChange, 𝓟']
    rw [← e.eq_symm_apply]
    simp [e, StandardEtalePair.equivAwayAdjoinRoot, ← aeval_def, ← aeval_algHom_apply]
    rfl
  obtain ⟨k, hk⟩ : ∃ k, IsIntegral R (AdjoinRoot.mk 𝓟'.f 𝓟'.g ^ k * x) := by
    have H : ∀ k, e (1 ⊗ₜ (aeval 𝓟.x 𝓟.g ^ k)) = algebraMap _ _ (AdjoinRoot.mk 𝓟'.f 𝓟'.g ^ k) := by
      intro k; convert congr($(heg 𝓟.g) ^ k) <;>
        simp [← map_pow, 𝓟', StandardEtalePresentation.baseChange]
    have := ((hx m).map (Algebra.TensorProduct.comm _ _ _).symm).map e
    simp only [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, map_mul, Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_apply_apply,
      AlgEquiv.apply_symm_apply] at this
    rw [H, pow_add, map_mul, mul_assoc, IsLocalization.mk'_spec'_mk, ← map_mul] at this
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_isIntegral_smul_of_isIntegral_map hfg this
    refine ⟨k + n, by convert hk using 1; ring_nf⟩
  obtain ⟨y, hy, hRy⟩ := exists_derivative_mul_eq_and_isIntegral_coeff
    (φ := (AdjoinRoot.mkₐ 𝓟'.f).restrictScalars R) AdjoinRoot.mk_surjective 𝓟'.monic_f
    (by simp [𝓟', StandardEtalePresentation.baseChange, isIntegral_algebraMap]) Ideal.mk_ker hk
  simp only [AlgHom.coe_restrictScalars', AdjoinRoot.coe_mkₐ] at hy
  rw [← Subalgebra.mem_toSubmodule, ← Submodule.smul_mem_iff_of_isUnit _
    (𝓟.hasMap.isUnit_derivative_f.mul <| (𝓟.hasMap.2.pow k).mul (𝓟.hasMap.2.pow m))]
  convert_to eval₂ Algebra.TensorProduct.includeRight.toRingHom (𝓟.x ⊗ₜ[R] 1) y ∈ _ using 1
  · convert congr(Algebra.TensorProduct.comm _ _ _ <| e.symm (algebraMap _ _ $hy))
    · apply (Algebra.TensorProduct.comm R B S).symm.injective
      apply e.injective
      simp only [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, map_mul, Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_apply_apply,
        AlgEquiv.apply_symm_apply, map_pow, heg]
      simp_rw [mul_assoc, ← map_pow, show 𝓟.g.map (algebraMap R B) = 𝓟'.g from rfl,
        IsLocalization.mk'_spec'_mk, ← derivative_map]; rfl
    · simp only [← AlgEquiv.coe_algHom, ← AlgHom.coe_toRingHom, ← RingHom.comp_apply,
        ← coe_eval₂RingHom]
      congr 1
      ext <;> simp [e, StandardEtalePair.equivAwayAdjoinRoot]; rfl
  · rw [eval₂_eq_sum_range]
    exact sum_mem fun i hi ↦ Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, hRy _, rfl⟩)
      (pow_mem (Subalgebra.algebraMap_mem _ _) _)

attribute [local instance high] AlgHomClass.toRingHomClass RingHomClass.toAddMonoidHomClass
  AddMonoidHomClass.toAddHomClass in
variable (R S) in
def TensorProduct.toIntegralClosure
    (B : Type*) [CommRing B] [Algebra R B] :
    S ⊗[R] integralClosure R B →ₐ[S] integralClosure S (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (.id _ _) (integralClosure R B).val).codRestrict _ fun x ↦ by
  induction x with
  | zero => simp
  | add x y _ _ => rw [map_add]; exact add_mem ‹_› ‹_›
  | tmul x y =>
    convert ((y.2.map (Algebra.TensorProduct.includeRight
      (R := R) (A := S))).tower_top (A := S)).smul x
    simp [smul_tmul']

open TensorProduct

instance (priority := low) {R A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (s : Subalgebra A B) [Semiring R] [SMul R A] [Module R B] [IsScalarTower R A B] :
    IsScalarTower R s B :=
  .to₁₃₄ _ A _ _

instance (priority := low) {R S A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (s : Subalgebra A B) [Semiring R] [SMul R A] [Module R B] [IsScalarTower R A B]
    [Semiring S] [SMul S A] [Module S B] [IsScalarTower S A B] [SMul R S] [IsScalarTower R S B] :
    IsScalarTower R S s :=
  .to₁₂₃ _ _ _ B

lemma Algebra.IsPushout.tensorProduct_tensorProduct
    (R S A B : Type*) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra R S]
    {_ : Algebra (A ⊗[R] S) (B ⊗[R] S)} {_ : IsScalarTower A (A ⊗[R] S) (B ⊗[R] S)}
    (H : (algebraMap (A ⊗[R] S) (B ⊗[R] S)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.IsPushout A B (A ⊗[R] S) (B ⊗[R] S) := by
  constructor
  convert isBaseChange_tensorProduct_map (R := R) (P := S) _ (IsBaseChange.linearMap A B)
  ext s
  simpa using congr($H s)

lemma IsLocalization.tensorProduct_tensorProduct
    (R S : Type*) [CommRing R] [CommRing S] {A : Type*} [CommRing A] (M : Submonoid A)
    (B : Type*) [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra R S] [IsLocalization M B]
    [Algebra (A ⊗[R] S) (B ⊗[R] S)] [IsScalarTower A (A ⊗[R] S) (B ⊗[R] S)]
    (H : (algebraMap (A ⊗[R] S) (B ⊗[R] S)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[R] S) M) (B ⊗[R] S) :=
  (Algebra.isLocalization_iff_isPushout M _).mpr
    (Algebra.IsPushout.tensorProduct_tensorProduct R S A B H).symm

set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
-- set_option trace.profiler true in
lemma TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway
    {s : Set S} (hs : Ideal.span s = ⊤) (Sᵣ : s → Type*) [∀ r, CommRing (Sᵣ r)]
    [∀ r, Algebra S (Sᵣ r)] [∀ r, Algebra R (Sᵣ r)] [∀ r, IsScalarTower R S (Sᵣ r)]
    [∀ r, IsLocalization.Away r.1 (Sᵣ r)]
    (H : ∀ r, Function.Bijective (toIntegralClosure R (Sᵣ r) B)) :
    Function.Bijective (toIntegralClosure R S B) := by
  have (r : s) : IsLocalizedModule.Away r.1
      (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
        (AlgHom.id R (integralClosure R B))).toLinearMap := by
    let := (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
      (AlgHom.id R (integralClosure R B))).toAlgebra
    refine isLocalizedModule_iff_isLocalization.mpr ?_
    refine IsLocalization.tensorProduct_tensorProduct _ _ (.powers r.1) _ ?_
    ext; simp [RingHom.algebraMap_toAlgebra]
  let φ (r : s) : integralClosure S (S ⊗[R] B) →ₐ[S] integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B) :=
    ((Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)).comp
      (integralClosure S (S ⊗[R] B)).val).codRestrict
        ((integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B)).restrictScalars S) <| by
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
      Subalgebra.mem_restrictScalars, Subtype.forall, mem_integralClosure_iff]
    exact fun a ha ↦ (ha.map _).tower_top
  have (r : s) : IsLocalizedModule.Away r.1 (φ r).toLinearMap := by
    let := (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
          (AlgHom.id R B)).toAlgebra
    let := (φ r).toAlgebra
    have : IsScalarTower (integralClosure S (S ⊗[R] B)) (integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B))
        (Sᵣ r ⊗[R] B) := .of_algebraMap_eq' rfl
    have : IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[R] B) (Submonoid.powers r.1))
        (Sᵣ r ⊗[R] B) := by
      refine IsLocalization.tensorProduct_tensorProduct _ _ (.powers r.1) _ ?_
      ext; simp [RingHom.algebraMap_toAlgebra]
    refine isLocalizedModule_iff_isLocalization.mpr ?_
    exact IsLocalization.integralClosure ..
  refine bijective_of_isLocalized_span s hs (F := (toIntegralClosure R S B).toLinearMap)
    (fun r ↦ (Sᵣ r) ⊗[R] integralClosure R B)
    (fun r ↦ (Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)).toLinearMap)
    (fun r ↦ integralClosure (Sᵣ r) ((Sᵣ r) ⊗[R] B))
    (fun r ↦ (φ r).toLinearMap) fun r ↦ ?_
  convert show Function.Bijective ((toIntegralClosure R (Sᵣ r) B).toLinearMap.restrictScalars S)
    from H r using 1
  congr!
  refine IsLocalizedModule.ext (.powers r.1) (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
    (AlgHom.id R (integralClosure R B))).toLinearMap
    (IsLocalizedModule.map_units (S := .powers r.1) (φ r).toLinearMap) ?_
  ext x
  exact congr($(IsLocalizedModule.map_apply (.powers r.1)
      ((Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
        (AlgHom.id R (integralClosure R B))).toLinearMap)
      (φ r).toLinearMap (toIntegralClosure R S B).toLinearMap (1 ⊗ₜ x)).1)

lemma MvPolynomial.pderiv_sumToIter {σ ι} (p i) :
    (sumToIter R σ ι p).pderiv i = sumToIter R σ ι (p.pderiv (.inl i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q _ _ => simp_all
  | mul_X p n _ => cases n <;> simp_all [pderiv_X, Pi.single_apply, apply_ite]

@[simp]
lemma MvPolynomial.iterToSum_sumToIter {σ ι} (p) :
    iterToSum R σ ι (sumToIter R σ ι p) = p := (MvPolynomial.sumRingEquiv _ _ _).symm_apply_apply _

@[simp]
lemma MvPolynomial.sumToIter_iterToSum {σ ι} (p) :
    sumToIter R σ ι (iterToSum R σ ι p) = p := (MvPolynomial.sumRingEquiv _ _ _).apply_symm_apply _

theorem RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (hf : f.IsStandardSmoothOfRelativeDimension n) :
    ∃ g : MvPolynomial (Fin n) R →+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  classical
  let := Fintype.ofFinite
  obtain ⟨ι, σ, _, _, P, e⟩ := hf
  let := f.toAlgebra
  let e₀ : σ ⊕ Fin n ≃ ι := ((Equiv.ofInjective _ P.map_inj).sumCongr
      (Finite.equivFinOfCardEq (by rw [Nat.card_coe_set_eq, Set.ncard_compl,
        Set.ncard_range_of_injective P.map_inj, ← e, Algebra.Presentation.dimension])).symm).trans
      (Equiv.Set.sumCompl _)
  let e : MvPolynomial σ (MvPolynomial (Fin n) R) ≃ₐ[R] P.Ring :=
    (MvPolynomial.sumAlgEquiv R _ _).symm.trans (MvPolynomial.renameEquiv _ e₀)
  let φ := e.toAlgHom.comp (IsScalarTower.toAlgHom _ (MvPolynomial (Fin n) R) _)
  algebraize [φ.toRingHom, (algebraMap P.Ring S).comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower R (MvPolynomial (Fin n) R) S := .to₁₂₄ _ _ P.Ring _
  refine ⟨algebraMap _ _, (IsScalarTower.algebraMap_eq ..).symm, ?_⟩
  have H : (MvPolynomial.aeval fun x ↦ (algebraMap P.Ring S) (e (MvPolynomial.X x))).toRingHom =
      (algebraMap P.Ring S).comp e.toRingHom := by
    ext
    · simp [e, IsScalarTower.algebraMap_eq R (MvPolynomial (Fin n) R) S]
    · simp [e, @RingHom.algebraMap_toAlgebra (MvPolynomial (Fin n) R) S, φ]
    · simp [e]
  let P' : Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { toGenerators := .ofSurjective (algebraMap _ _ <| e <| .X ·) <| by
      convert P.algebraMap_surjective.comp e.surjective
      exact congr($H)
    relation := e.symm ∘ P.relation
    span_range_relation_eq_ker := by
      rw [Set.range_comp, ← AlgEquiv.coe_ringEquiv e.symm, AlgEquiv.symm_toRingEquiv,
        ← Ideal.map_span, P.span_range_relation_eq_ker, Ideal.map_symm]
      exact congr(RingHom.ker $H).symm
    map := _
    map_inj := Function.injective_id }
  let P' : Algebra.SubmersivePresentation (MvPolynomial (Fin n) R) S σ σ :=
  { __ := P'
    jacobian_isUnit := by
      convert P.jacobian_isUnit using 1
      simp_rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, map_det]
      congr 1
      ext i j
      trans algebraMap P.Ring S (e ((e.symm (P.relation j)).pderiv i))
      · simpa [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, P',
          Algebra.Generators.ofSurjective] using congr($H _)
      suffices e ((e.symm (P.relation j)).pderiv i) = (P.relation j).pderiv (P.map i) by
        simp [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, this]
      simp [e, MvPolynomial.pderiv_sumToIter, ← MvPolynomial.pderiv_rename e₀.injective,
        show e₀ (Sum.inl i) = P.map i from rfl] }
  exact etale_algebraMap.mpr (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mpr
    ⟨_, _, _, inferInstance, P', by simp [Algebra.Presentation.dimension]⟩)

theorem RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsStandardSmooth) :
    ∃ n, ∃ g : MvPolynomial (Fin n) R →+* S, g.comp MvPolynomial.C = f ∧ g.Etale := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := hf
  let := f.toAlgebra
  exact ⟨_, RingHom.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial _
    ⟨_, _, _, ‹_›, P, rfl⟩⟩

instance {M : Submonoid S} [Algebra.FormallyEtale R S] : Algebra.FormallyEtale R (Localization M) :=
  have : Algebra.FormallyEtale S (Localization M) := .of_isLocalization M
  .comp _ S _

/-- Given `S` a finitely presented `R`-algebra, and `p` a prime of `S`. If `S` is smooth over `R`
at `p`, then there exists `f ∉ p` such that `R → S[1/f]` factors through some `R[X₁,...,Xₙ]`,
and that `S[1/f]` is standard etale over `R[X₁,...,Xₙ]`. -/
theorem Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial
    {p : Ideal S} [p.IsPrime] [Algebra.FinitePresentation R S]
    [Algebra.IsSmoothAt R p] :
    ∃ f ∉ p, ∃ (n : ℕ) (_ : Algebra (MvPolynomial (Fin n) R) (Localization.Away f)),
      IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away f) ∧
      Algebra.IsStandardEtale (MvPolynomial (Fin n) R) (Localization.Away f) := by
  classical
  obtain ⟨f, hfp, H⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  obtain ⟨n, φ, hgC, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (algebraMap R (Localization.Away f))
    (by delta RingHom.IsStandardSmooth; convert H; apply Algebra.algebra_ext; exact fun _ ↦ rfl)
  algebraize [φ]
  have := IsScalarTower.of_algebraMap_eq' hgC.symm
  have : (Ideal.map (algebraMap S (Localization.Away f)) p).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
      ((Ideal.disjoint_powers_iff_notMem _ (Ideal.IsPrime.isRadical ‹_›)).mpr hfp)
  obtain ⟨g₀, hg, H⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := (MvPolynomial (Fin n) R))
    (S := (Localization.Away f)) (p.map (algebraMap _ _))
  obtain ⟨g, ⟨_, m, rfl⟩, hg₀⟩ := IsLocalization.exists_mk'_eq (.powers f) g₀
  replace hg : g ∉ p := by simpa [Submonoid.mem_powers_iff, Ideal.IsPrime.mul_mem_iff_mem_or_mem,
    IsLocalization.mk'_mem_map_algebraMap_iff, mt (‹p.IsPrime›.mem_of_pow_mem _) hfp,
    ← hg₀] using hg
  have : IsLocalization.Away (f * g) (Localization.Away g₀) := by
    suffices IsLocalization.Away (algebraMap _ (Localization.Away f) g) (Localization.Away g₀) from
      .mul' (Localization.Away f) _ _ _
    refine IsLocalization.Away.of_associated (r := g₀)
      ⟨(IsLocalization.Away.algebraMap_pow_isUnit f m).unit, ?_⟩
    simp only [← hg₀, IsUnit.unit_spec, ← map_pow, mul_comm, IsLocalization.mk'_spec'_mk]
  let e : Localization.Away g₀ ≃ₐ[S] Localization.Away (f * g) :=
    IsLocalization.algEquiv (.powers (f * g)) _ _
  let : Algebra (MvPolynomial (Fin n) R) (Localization.Away (f * g)) :=
    (e.toRingHom.comp (algebraMap (MvPolynomial (Fin n) R) _)).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) (Localization.Away (f * g)) := by
    refine .of_algebraMap_eq' ?_
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
    exact (e.toAlgHom.comp_algebraMap_of_tower (R := R)).symm
  let e' : Localization.Away g₀ ≃ₐ[MvPolynomial (Fin n) R] Localization.Away (f * g) :=
    { __ := e, commutes' r := rfl }
  refine ⟨f * g, ‹p.IsPrime›.mul_notMem ‹_› ‹_›, n, ‹_›, ‹_›, .of_equiv e'⟩

lemma fg_subgroup_pi_z {M : Type*} [Finite M] (H : AddSubgroup (M → ℤ)) : H.FG :=
  (H.toIntSubmodule.fg_iff_addSubgroup_fg).mp (IsNoetherian.noetherian _)

example {K L : Type*} [Field K] [Ring L] [Algebra K L] [Nontrivial L]
    (h : Module.finrank K L = 1) : Function.Bijective (algebraMap K L) :=
  bijective_algebraMap_of_linearEquiv (Module.nonempty_linearEquiv_of_finrank_eq_one h).some

lemma TensorProduct.toIntegralClosure_injective_of_flat [Module.Flat R S] :
    Function.Injective (toIntegralClosure R S B) := by
  refine Function.Injective.of_comp (f := (integralClosure _ _).val) ?_
  rw [← AlgHom.coe_comp, toIntegralClosure, AlgHom.val_comp_codRestrict]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (integralClosure R B).val.toLinearMap Subtype.val_injective

lemma RingHom.IsIntegralElem.of_comp_of_injective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} {x : S} (hg : Function.Injective g)
    (hx : (g.comp f).IsIntegralElem (g x)) :
    f.IsIntegralElem x := by
  obtain ⟨p, hp, hx⟩ := hx
  exact ⟨p, hp, hg <| by simp [hom_eval₂, hx]⟩

lemma MvPolynomial.killCompl_map
    {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] {f : σ → τ}
    (hf : f.Injective) (φ : R →+* S) (p : MvPolynomial _ R) :
    (p.map φ).killCompl hf = (p.killCompl hf).map φ := by
  simp only [← AlgHom.coe_toRingHom, ← RingHom.comp_apply]
  congr
  ext i n
  · simp
  · by_cases h : i ∈ Set.range f <;> simp [MvPolynomial.killCompl, h]

@[simp]
lemma MvPolynomial.optionEquivLeft_symm_C_C (R S₁ : Type*) [CommSemiring R] (x : R) :
    (optionEquivLeft R S₁).symm (.C (.C x)) = .C x := by simp [optionEquivLeft]

@[simp]
lemma MvPolynomial.optionEquivLeft_symm_X (R S₁ : Type*) [CommSemiring R] :
    (optionEquivLeft R S₁).symm .X = .X .none := by simp [optionEquivLeft]

@[elab_as_elim]
lemma Finite.induction_empty_option'.{u} {P : ∀ (α : Type u) [Finite α], Prop}
    (of_equiv : ∀ {α β : Type u} (_ : α ≃ β) [Finite α] [Finite β], P α → P β)
    (h_empty : P PEmpty.{u + 1}) (h_option : ∀ {α : Type u} [Fintype α],
    P α → P (Option α)) (α : Type u) (hα : Finite α) : P α := by
  refine Finite.induction_empty_option (P := fun α ↦ (h : Finite α) → P α) ?_ ?_ ?_ α ‹Finite α›
  · exact fun α β e IH {_} ↦ have := Finite.of_equiv _ e.symm; of_equiv e (IH _)
  · exact fun _ ↦ h_empty
  · exact fun α _ IH {_} ↦ h_option (IH _)

universe w in
attribute [local instance] MvPolynomial.algebraMvPolynomial in
attribute [-simp] AlgEquiv.symm_toRingEquiv in
attribute [simp] MvPolynomial.optionEquivLeft_C MvPolynomial.optionEquivLeft_X_none
  MvPolynomial.optionEquivLeft_X_some in
theorem MvPolynomial.isIntegral_iff_isIntegral_coeff {σ : Type w} {f : MvPolynomial σ S} :
    IsIntegral (MvPolynomial σ R) f ↔ ∀ n, IsIntegral R (f.coeff n) := by
  classical
  refine ⟨fun H n ↦ ?mp, fun H ↦ ?mpr⟩
  case mpr =>
    rw [← f.support_sum_monomial_coeff]
    simp_rw [monomial_eq]
    refine IsIntegral.sum _ fun n _ ↦ .mul ((H n).map (Algebra.ofId _ _)).tower_top
      (.prod _ fun i _ ↦ .pow ?_ _)
    convert isIntegral_algebraMap (x := MvPolynomial.X i)
    simp only [algebraMap_def, map_X]
  unfold IsIntegral at H
  wlog hσ : Finite σ generalizing σ
  · obtain ⟨g, hg⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range (τ := f.vars) f _
      Subtype.val_injective (by simp)
    by_cases hn : n ∈ Set.range (Finsupp.mapDomain ((↑) : f.vars → σ))
    · obtain ⟨n, rfl⟩ := hn
      simp_rw [← hg, coeff_rename_mapDomain _ Subtype.val_injective]
      exact this (f := g) (RingHom.IsIntegralElem.of_comp_of_injective
        (g := (rename ((↑) : f.vars → σ)).toRingHom) (rename_injective _ Subtype.val_injective)
        (.of_comp (f := (killCompl (f := ((↑) : f.vars → σ)) Subtype.val_injective).toRingHom) <| by
        simp only [AlgHom.toRingHom_eq_coe, algebraMap_def, RingHom.coe_coe, hg]
        convert H.map ((rename Subtype.val).comp
          (killCompl (f := ((↑) : f.vars → σ)) Subtype.val_injective)).toRingHom
        · exact RingHom.ext (by simp [MvPolynomial.killCompl_map])
        · nth_rw 1 11 [← hg]; simp)) n (.of_fintype _)
    · rw [← hg, coeff_rename_eq_zero _ _ _ (by grind)]
      exact isIntegral_zero
  induction σ, hσ using Finite.induction_empty_option' with
  | @of_equiv α β e _ _ IH =>
    have := @IH (rename e.symm f) (.of_comp_of_injective (g := (rename e).toRingHom)
      (rename_injective _ e.injective) <| .of_comp (f := (rename e.symm).toRingHom)
        (by convert H <;> aesop)) (n.embDomain e.symm)
    simpa [Finsupp.embDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective] using this
  | h_empty =>
    refine .of_comp_of_injective (g := (isEmptyAlgEquiv _ PEmpty).symm.toRingHom)
      (isEmptyAlgEquiv _ PEmpty).symm.injective
      (.of_comp (f := (isEmptyAlgEquiv _ PEmpty).toRingHom) ?_)
    convert H
    · aesop (add simp MvPolynomial.isEmptyAlgEquiv)
    · obtain rfl := Subsingleton.elim n 0
      have : constantCoeff = (isEmptyAlgEquiv S PEmpty).toRingHom := by aesop
      simpa [-EmbeddingLike.apply_eq_iff_eq, -isEmptyAlgEquiv_apply] using
        congr((isEmptyAlgEquiv S PEmpty.{w + 1}).symm ($this f))
  | @h_option α hα IH =>
    have := IH (_root_.isIntegral_coeff_of_isIntegral (R := MvPolynomial α R)
      (f := optionEquivLeft _ _ f) (.of_comp_of_injective
      (g := (optionEquivLeft _ _).symm.toRingHom) (optionEquivLeft _ _).symm.injective
      (.of_comp (f := (optionEquivLeft _ _).toRingHom) (by
        convert H
        · ext i m
          · aesop
          · cases i <;> aesop
        · aesop))) (n .none)) n.some
    rwa [optionEquivLeft_coeff_some_coeff_none] at this

attribute [local instance] MvPolynomial.algebraMvPolynomial in
lemma TensorProduct.toIntegralClosure_mvPolynomial_bijective {σ : Type*} :
    Function.Bijective (toIntegralClosure R (MvPolynomial σ R) B) := by
  classical
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  rintro ⟨x, hx⟩
  let e : MvPolynomial σ R ⊗[R] B ≃ₐ[MvPolynomial σ R] MvPolynomial σ B :=
    { toRingEquiv := MvPolynomial.scalarRTensorAlgEquiv.toRingEquiv, commutes' r := by
        change MvPolynomial.scalarRTensorAlgEquiv.toRingHom.comp (algebraMap _ _) r = _
        congr 1
        ext <;> simp [MvPolynomial.scalarRTensorAlgEquiv, MvPolynomial.coeff_map,
          ← Algebra.algebraMap_eq_smul_one, apply_ite (algebraMap _ _), MvPolynomial.coeff_X'] }
  have := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp (hx.map e)
  obtain ⟨y, hy⟩ : e x ∈ RingHom.range (MvPolynomial.map (integralClosure R B).val.toRingHom) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr ?_
    simp [Set.subset_def, mem_integralClosure_iff, MvPolynomial.mem_coeffs_iff,
      @forall_comm B, this]
  refine ⟨MvPolynomial.scalarRTensorAlgEquiv.symm y, Subtype.ext <| e.injective (.trans ?_ hy)⟩
  obtain ⟨y, rfl⟩ := (MvPolynomial.scalarRTensorAlgEquiv (R := R)).surjective y
  dsimp [TensorProduct.toIntegralClosure, e]
  simp only [AlgEquiv.symm_apply_apply]
  have : MvPolynomial.scalarRTensorAlgEquiv.toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R (MvPolynomial σ R)) (integralClosure R B).val) =
      (MvPolynomial.mapAlgHom (integralClosure R B).val).comp
      MvPolynomial.scalarRTensorAlgEquiv.toAlgHom := by
    ext <;> simp [-MvPolynomial.mapAlgHom_apply, MvPolynomial.mapAlgHom, MvPolynomial.coeff_map,
      MvPolynomial.scalarRTensorAlgEquiv]
  exact congr($this y)

lemma TensorProduct.toIntegralClosure_bijective_of_tower
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (H : Function.Bijective (toIntegralClosure R S B))
    (H' : Function.Bijective (toIntegralClosure S T (S ⊗[R] B))) :
    Function.Bijective (toIntegralClosure R T B) := by
  let e := (Algebra.TensorProduct.cancelBaseChange ..).symm.trans <|
      (Algebra.TensorProduct.congr (.refl (R := T) (A₁ := T)) (.ofBijective _ H)).trans <|
      (AlgEquiv.ofBijective _ H').trans <|
      (AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.cancelBaseChange ..))
  convert e.bijective
  rw [← e.coe_algHom]
  congr 1
  ext; simp [e, toIntegralClosure]

theorem TensorProduct.toIntegralClosure_bijective_of_isStandardEtale
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.IsStandardEtale R S] :
    Function.Bijective (toIntegralClosure R S B) := by
  have : Algebra.Smooth R S := {}
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  intro ⟨x, hx⟩
  simp only [toIntegralClosure, Subtype.ext_iff, AlgHom.coe_codRestrict, ← AlgHom.mem_range]
  refine Algebra.adjoin_le ?_ (mem_adjoin_map_integralClosure_of_isStandardEtale x hx)
  rintro _ ⟨y, hy : IsIntegral _ _, rfl⟩
  refine ⟨1 ⊗ₜ ⟨y, hy⟩, by simp⟩

theorem TensorProduct.toIntegralClosure_bijective_of_smooth
    {B : Type*} [CommRing B] [Algebra R B] [Algebra.Smooth R S] :
    Function.Bijective (toIntegralClosure R S B) := by
  have (m : PrimeSpectrum S) : ∃ f ∉ m.asIdeal,
      Function.Bijective (toIntegralClosure R (Localization.Away f) B) := by
    obtain ⟨f, hfm, n, _, _, _⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := m.asIdeal)
    exact ⟨f, hfm, toIntegralClosure_bijective_of_tower (S := MvPolynomial (Fin n) R)
      toIntegralClosure_mvPolynomial_bijective toIntegralClosure_bijective_of_isStandardEtale⟩
  choose f hfm hf using this
  refine TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway (R := R)
    (s := Set.range f) (B := B) ?_ (Localization.Away ·.1) (Set.forall_subtype_range_iff.mpr hf)
  by_contra H
  obtain ⟨m, hm, e⟩ := Ideal.exists_le_maximal _ H
  exact hfm ⟨m, inferInstance⟩ (e (Ideal.subset_span (Set.mem_range_self ⟨m, inferInstance⟩)):)
