import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Resultant
import Mathlib.RingTheory.IsAdjoinRoot

variable {R K : Type*} [CommRing R] [Field K]
variable {m n : ℕ}

namespace Polynomial

-- TODO: move this to Resultant.lean once it's not so annoying to build.

/--
We can pick an order for the elements of a multiset and write its product as a `Fin`-indexed product.
-/
@[to_additive]
lemma Multiset.prod_eq_prod_fin {M : Type*} [CommMonoid M] (s : Multiset M) :
    ∃ t : Fin (Multiset.card s) → M, s.prod = ∏ i, t i :=
  s.induction ⟨![], by simp⟩ (fun a s ⟨t, ih⟩ =>
    ⟨fun i => Fin.cons (α := fun _ => M) a t ⟨i, by simpa using i.prop⟩,
     by
      convert (Fin.prod_cons a t).symm
      · simp [ih]
      · simp
      · simp⟩)

/--
We can pick an order for the elements of a multiset and write its product as a `Fin`-indexed product.
-/
@[to_additive]
lemma Multiset.prod_map_eq_prod_fin {α M : Type*} [CommMonoid M] (s : Multiset α) (f : α → M) :
    ∃ t : Fin (Multiset.card s) → α, (s.map f).prod = ∏ i, f (t i) :=
  s.induction ⟨![], by simp⟩ (fun a s ⟨t, ih⟩ =>
    ⟨fun i => Fin.cons (α := fun _ => α) a t ⟨i, by simpa using i.prop⟩,
     calc
      (Multiset.map f (a ::ₘ s)).prod
      _ = ∏ i : Fin (Multiset.card s + 1), f (Fin.cons (α := fun _ => α) a t i) := by
        simp [Fin.prod_univ_succ, ih]
      _ = ∏ i : Fin (Multiset.card (a ::ₘ s)), f _ := Fintype.prod_equiv
        (Fin.castOrderIso (by simp)).toEquiv _ _ (by
          intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · rfl
          · simp only [Fin.cons_succ, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
              Fin.val_succ, ← Fin.succ_mk, Fin.is_lt])⟩)

@[simp] lemma Multiset.prod_toList_map {α M : Type*} [CommMonoid M] (s : Multiset α) (f : α → M) :
    (s.toList.map f).prod = (s.map f).prod := by
  rw [← Multiset.prod_toList]
  apply List.Perm.prod_eq (Multiset.coe_eq_coe.mp _)
  rw [Multiset.coe_toList, ← Multiset.map_coe, Multiset.coe_toList]

@[simp] lemma List.prod_get {α M : Type*} [CommMonoid M] (s : List α) (f : α → M) :
    ∏ i, f (s.get i) = (s.map f).prod := by
  induction s
  · simp
  · simp [Fin.prod_univ_succ]

theorem resultant_eq_of_splits [Infinite K] (f g : K[X]) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hf : f.Splits (RingHom.id _)) (hg : g.Splits (RingHom.id _)) :
    resultant f g =
      (-1)^(f.natDegree * g.natDegree) * leadingCoeff f ^ g.natDegree * leadingCoeff g ^ f.natDegree *
        (f.roots.map (fun ai => (g.roots.map fun bj => (ai - bj)).prod)).prod := by
    conv_lhs =>
      rw [eq_prod_roots_of_splits_id hf, eq_prod_roots_of_splits_id hg]
    rw [← Multiset.prod_toList_map, ← List.prod_get]
    rw [← Multiset.prod_toList_map, ← List.prod_get]
    rw [← Multiset.prod_toList_map, ← List.prod_get]
    rw [resultant_eq_prod_roots]
    congr <;> simp [splits_iff_card_roots.mp hf, splits_iff_card_roots.mp hg]
    · simpa
    · simpa

theorem resultant_eq_zero_iff_gcd [DecidableEq K] (f g : K[X])
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    resultant f g = 0 ↔ 0 < (gcd f g).natDegree := by
  have : f * (g / gcd f g) + g * -(f / gcd f g) = 0 := by
    rw [mul_neg,
        ← EuclideanDomain.mul_div_assoc _ (gcd_dvd_right f g),
        ← EuclideanDomain.mul_div_assoc _ (gcd_dvd_left f g),
        mul_comm, add_right_neg]

  rw [resultant_eq_zero_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hab0, h⟩
    by_contra hdeg
    rw [not_lt, Nat.le_zero] at hdeg
    rw [add_eq_zero_iff_eq_neg, ← mul_neg] at h
    sorry
  · intro h
    have hgcd0 : gcd f g ≠ 0 := fun hgcd0 => by simp [hgcd0] at h
    obtain ⟨f', hf'⟩ := gcd_dvd_left f g
    obtain ⟨g', hg'⟩ := gcd_dvd_right f g
    have hf'0 : f' ≠ 0 := fun hf'0 => hf0 <| by rw [hf', hf'0, mul_zero]
    have hg'0 : g' ≠ 0 := fun hg'0 => hg0 <| by rw [hg', hg'0, mul_zero]
    refine ⟨⟨_, mem_degreeLT.mpr ?_⟩, ⟨_, mem_degreeLT.mpr ?_⟩, ?_, this⟩
    · exact (degree_div_lt hg0 (natDegree_pos_iff_degree_pos.mp h)).trans_le degree_le_natDegree
    · rw [degree_neg]
      exact (degree_div_lt hf0 (natDegree_pos_iff_degree_pos.mp h)).trans_le degree_le_natDegree
    · exact Or.inl (by simpa [Polynomial.div_eq_zero_iff hgcd0] using degree_gcd_le_right _ hg0)

lemma isRoot_rootOfSplits {f : K[X]} (hf : f.Splits (RingHom.id _)) (hdf : degree f ≠ 0) :
    IsRoot f (rootOfSplits _ hf hdf) := by
  simpa using map_rootOfSplits _ hf hdf

theorem resultant_eq_zero_iff_root [DecidableEq K] (f g : K[X]) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfg : (gcd f g).Splits (RingHom.id _)) :
    resultant f g = 0 ↔ ∃ x : K, eval x f = 0 ∧ eval x g = 0 := by
  rw [resultant_eq_zero_iff_gcd _ _ hf0 hg0]
  constructor
  · intro hgcd
    have hgcd' : degree (gcd f g) ≠ 0 := (Polynomial.natDegree_pos_iff_degree_pos.mp hgcd).ne'
    use rootOfSplits (RingHom.id _) hfg hgcd'
    exact ⟨(isRoot_rootOfSplits _ hgcd').dvd (gcd_dvd_left f g),
           (isRoot_rootOfSplits _ hgcd').dvd (gcd_dvd_right f g)⟩
  · rintro ⟨x, hf, hg⟩
    calc
      0 < 1 := zero_lt_one
      _ = natDegree (X - C x) := (natDegree_X_sub_C x).symm
      _ ≤ natDegree (gcd f g) := natDegree_le_of_dvd
            (dvd_gcd (dvd_iff_isRoot.mpr hf) (dvd_iff_isRoot.mpr hg))
            (gcd_ne_zero_of_left hf0)

@[simp] lemma ofVec_toVec (f : R[X]) :
    ofVec (toVec f) = f := by
  ext i
  simp only [coeff_ofVec]
  split_ifs with h
  · simp
  · rw [coeff_eq_zero_of_natDegree_lt (not_lt.mp h)]

@[simp] lemma toVec_map {S : Type*} [CommRing S] (φ : R →+* S) (f : R[X]) (hf0 : φ f.leadingCoeff ≠ 0) :
    toVec (map φ f) = φ ∘ (toVec f) ∘ Fin.cast (by simp [hf0]) := by
  ext i
  simp [toVec]

@[simp] lemma toVec_map' {S : Type*} [CommRing S] [Nontrivial S] (φ : K →+* S) (f : K[X]) :
    toVec (map φ f) = φ ∘ (toVec f) ∘ Fin.cast (by rw [natDegree_map]) := by
  ext i
  simp [toVec]

@[simp] lemma toVec_last (f : R[X]) :
    toVec f (Fin.last _) = f.leadingCoeff := by
  simp [toVec]

lemma resultant_eq_eval_resultantPolynomialCoeff (f g : K[X]) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    resultant f g = MvPolynomial.eval (Sum.elim f.toVec g.toVec) resultantPolynomialCoeff := by
  rw [MvPolynomial.eval_resultantPolynomialCoeff]
  · simp
  · simp [hf0]
  · simp [hg0]

@[simp]
theorem vecRotate_map {S : Type*} [CommRing S] (φ : R → S) (f : Fin n → R) (i) (j) :
    vecRotate (φ ∘ f) i j = φ (vecRotate f i j) := by
  simp [vecRotate]

@[simp]
theorem Fin.pad_map {S : Type*} [CommRing S] (φ : R → S) (f : Fin (n + 1) → R) (x : R) (y : S) (h : φ x = y) :
    Fin.pad (m := m) (φ ∘ f) y = φ ∘ (Fin.pad f x) := by
  ext i
  simp [Fin.pad, ← h]
  split_ifs <;> rfl

@[simp]
theorem sylvesterVec_map {S : Type*} [CommRing S] (φ : R →+* S) (f : Fin (n + 1) → R) (i : Fin m) (j) :
    sylvesterVec (φ ∘ f) i j = φ (sylvesterVec f i j) := by
  rw [sylvesterVec, Fin.pad_map φ f 0 0 (map_zero φ), vecRotate_map, sylvesterVec]

@[simp]
theorem sylvesterMatrixVec_map {S : Type*} [CommRing S] (φ : R →+* S) (f : Fin (n + 1) → R) (g : Fin (m + 1) → R) :
    sylvesterMatrixVec (φ ∘ f) (φ ∘ g) = (sylvesterMatrixVec f g).map φ := by
  ext i j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp [sylvesterMatrixVec]
  · simp [sylvesterMatrixVec]

@[simp]
theorem sylvesterMatrix_map {L : Type*} [Field L] (φ : K →+* L) (f g : K[X]) :
    sylvesterMatrix (map φ f) (map φ g) = ((sylvesterMatrix f g).submatrix (finCongr (by simp)) (finCongr (by simp))).map φ := by
  ext i j
  simp [sylvesterMatrix]

theorem resultant_map {L : Type*} [Field L] (φ : K →+* L) (f g : K[X]) :
    resultant (f.map φ) (g.map φ) = φ (resultant f g) := by
  by_cases hf0 : f = 0 <;> by_cases hg0 : g = 0
  · simp [hf0, hg0]
  · rw [hf0, Polynomial.map_zero, ← map_zero C, C_resultant, natDegree_map,
        ← map_zero C, C_resultant, map_pow, map_zero]
  · rw [hg0, Polynomial.map_zero, ← map_zero C, resultant_C, natDegree_map,
        ← map_zero C, resultant_C, map_pow, map_zero]
  rw [resultant, resultant, sylvesterMatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simp

@[simp]
lemma map_gcd {L : Type*} [Field L] {φ : K →+* L}
    [DecidableEq K] [DecidableEq L] [CharZero K] (f g : K[X]) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    gcd (map φ f) (map φ g) = map φ (gcd f g) := sorry

theorem resultant_eq_zero_iff_root' {L : Type*} [Field L] {φ : K →+* L}
    [DecidableEq K] [DecidableEq L] [CharZero K] (f g : K[X]) (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hfg : (gcd f g).Splits φ) :
    resultant f g = 0 ↔ ∃ x : L, eval₂ φ x f = 0 ∧ eval₂ φ x g = 0 := by
  rw [← (RingHom.injective φ).eq_iff, ← resultant_map φ f g, map_zero, resultant_eq_zero_iff_root]
  · exact exists_congr (fun _ => by rw [eval_map, eval_map])
  · simp [hf0]
  · simp [hg0]
  · rw [map_gcd, splits_map_iff, RingHom.id_comp]
    · assumption
    · assumption
    · assumption

theorem resultant_eq_zero_iff_exists_root [CharZero K] (φ : K →+* L) (splits φ f) (splits φ g) : resultant f g = 0 \iff \ex x : L, f.eval x = 0 \and g.eval x = 0

theorem resultant_eq_zero_iff_exists_root [CharZero K] : resultant f g = 0 \iff \ex x : AlgebraicClosure K, f.aeval x = 0 \and g.aeval x = 0

lemma hom_eval {S : Type*} [CommSemiring S] (f : R →+* S) (p : R[X]) (x : R) :
    f (eval x p) = eval₂ f (f x) p := by
  rw [eval, hom_eval₂, RingHom.comp_id]

lemma prod_X_sub_C_resultant {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → K) (g : K[X]) :
    resultant (∏ i in s, (X - C (t i))) g =
      (-1) ^ (s.card * g.natDegree) * ∏ i in s, eval (t i) g := by
  by_cases hg0 : g = 0
  · simp [hg0, resultant_zero']
  have : Splits (algebraMap K (AlgebraicClosure K)) g := (IsAlgClosed.splits_codomain g)
  apply RingHom.injective (algebraMap K (AlgebraicClosure K))
  simp only [map_mul, map_pow, map_neg, map_one, ← resultant_map, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_prod, hom_eval,
    ← Polynomial.eval_map]
  rw [eq_prod_roots_of_splits this,
      Finset.prod_eq_multiset_prod, ← one_mul (s.val.map _).prod, ← map_one C,
      resultant_multiset_eq_prod_roots]
  simp only [Finset.card_val,
    one_pow, mul_one, Finset.prod_map_val, eval_mul, eval_C, Finset.prod_mul_distrib,
    Finset.prod_const, eval_multiset_prod, Multiset.map_map,
    Function.comp_apply, eval_sub, eval_X]
  rw [← natDegree_eq_of_degree_eq_some (degree_eq_card_roots _ this), mul_assoc]
  · assumption
  · exact one_ne_zero
  · exact (map_ne_zero_iff _ (RingHom.injective _)).mpr (leadingCoeff_ne_zero.mpr hg0)

lemma resultant_prod_X_sub_C {ι : Type*} [DecidableEq ι] (f : K[X]) (s : Finset ι) (u : ι → K) :
    resultant f (∏ i in s, (X - C (u i))) = ∏ i in s, eval (u i) f := by
  rw [resultant_swap, prod_X_sub_C_resultant, mul_comm s.card, natDegree_prod_X_sub_C, ← mul_assoc,
      ← mul_pow, neg_mul_neg, one_mul, one_pow, one_mul]

/--
The discriminant of a polynomial `f` is defined as the resultant of `f` and its derivative `f'`.
-/
noncomputable def discriminant (f : R[X]) : R :=
  resultant f (derivative f)

@[simp] lemma discriminant_zero : discriminant (0 : R[X]) = 1 := zero_resultant_zero

@[simp] lemma discriminant_one : discriminant (1 : R[X]) = 1 := one_resultant _

@[simp] lemma discriminant_C (x : R) : discriminant (C x) = 1 := by
  rw [discriminant, C_resultant, derivative_C, natDegree_zero, pow_zero]

@[simp] lemma discriminant_X_add_C (a b : R) (ha : a ≠ 0) : discriminant (C a * X + C b) = a := by
  simp [discriminant, ha]

@[simp]
theorem natDegree_derivative_eq {R : Type*} [Semiring R] [NoZeroSMulDivisors ℕ R]
    (p : Polynomial R) : (derivative p).natDegree = p.natDegree - 1 := by
  obtain (hp | hp) := Nat.eq_zero_or_pos p.natDegree
  · rw [eq_C_of_natDegree_eq_zero hp, derivative_C, natDegree_zero, natDegree_C, Nat.zero_sub]
  exact natDegree_eq_of_degree_eq_some (degree_derivative_eq p hp)

@[simp] lemma discriminant_C_mul [CharZero R] [NoZeroDivisors R] (x : R) (hx0 : x ≠ 0)
    (p : R[X]) :
    discriminant (C x * p) = x ^ (p.natDegree + (p.natDegree - 1)) * discriminant p := by
  by_cases hp0 : natDegree p = 0
  · rw [eq_C_of_natDegree_eq_zero hp0, ← map_mul C, discriminant_C, natDegree_C, Nat.zero_sub,
        add_zero, pow_zero, one_mul, discriminant_C]
  by_cases hp1 : natDegree p = 1
  · obtain ⟨a, ha, b, rfl⟩ := natDegree_eq_one.mp hp1
    rw [mul_add, ← mul_assoc, ← map_mul C, ← map_mul C]
    simp [-map_mul, mul_ne_zero hx0 ha, natDegree_C_mul, ha]
  rw [discriminant, derivative_mul, derivative_C, zero_mul, zero_add, C_mul_resultant,
      resultant_C_mul, ← discriminant, ← mul_assoc, ← pow_add, natDegree_C_mul hx0,
      natDegree_derivative_eq, add_comm]
  · assumption
  · rw [natDegree_C_mul hx0, natDegree_derivative_eq, ne_eq, Nat.sub_eq_zero_iff_le, not_le]
    exact lt_of_le_of_ne (Nat.pos_of_ne_zero hp0) (Ne.symm hp1)

-- TODO: rename me to `derivative_prod` and `derivative_prod` to `derivative_multisetProd`.
theorem derivative_prod' {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → R[X]} :
    derivative (∏ i in s, f i) =
      ∑ i in s, (∏ i in s.erase i, f i) * derivative (f i) :=
  derivative_prod

lemma derivative_prod_X_sub_C {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → R) :
    derivative (∏ i in s, (X - C (t i))) = ∑ i in s, ∏ j in s.erase i, (X - C (t j)) := by
  rw [derivative_prod']
  exact Finset.sum_congr rfl (by simp)

lemma natDegree_add_eq_of_leadingCoeff_add_ne_zero {p q : R[X]}
    (hcoeff : leadingCoeff p + leadingCoeff q ≠ 0) :
    natDegree (p + q) = max (natDegree p) (natDegree q) := by
  apply le_antisymm (natDegree_add_le _ _)
  obtain (lt | eq | gt) := lt_trichotomy (natDegree p) (natDegree q)
  · rw [natDegree_add_eq_right_of_natDegree_lt lt, max_eq_right_of_lt lt]
  · rw [eq, max_self]
    refine le_of_not_gt (mt ?_ hcoeff)
    intro lt
    rw [leadingCoeff, leadingCoeff, eq, ← coeff_add]
    exact coeff_eq_zero_of_natDegree_lt lt
  · rw [natDegree_add_eq_left_of_natDegree_lt gt, max_eq_left_of_lt gt]

lemma natDegree_sum_eq {ι : Type*} [DecidableEq ι] {s : Finset ι} {p : ι → R[X]}
    (h0 : s.Nonempty)
    (hdeg : ∀ i ∈ s, natDegree (p i) = n) (hcoeff : ∑ i in s, leadingCoeff (p i) ≠ 0) :
    natDegree (∑ i in s, p i) = n := by
  induction s using Finset.cons_induction
  case empty =>
    contradiction
  case cons a s h ih =>
    obtain (rfl | hs0) := s.eq_empty_or_nonempty
    · simp [hdeg]
    rw [Finset.sum_cons] at hcoeff ⊢
    obtain ⟨hdega, hdegs⟩ : (p a).natDegree = n ∧ ∀ i ∈ s, (p i).natDegree = n := by
      simpa using hdeg
    by_cases hsum0 : ∑ b ∈ s, p b = 0
    · rwa [hsum0, add_zero]
    by_cases hcoeff' : ∑ i ∈ s, (p i).leadingCoeff = 0
    · rw [natDegree_add_eq_left_of_natDegree_lt (lt_of_le_of_ne _ _), hdega]
      · refine (natDegree_sum_le _ _).trans ?_
        rw [Finset.fold_congr (g := fun _ => n), Finset.fold_const]
        · simp [hs0.ne_empty, hdega]
        · simp
        · intro i hi
          exact hdegs _ hi
      · rw [hdega]
        intro h
        have := (Finset.sum_congr rfl (fun i hi => by rw [← coeff_natDegree, hdegs _ hi])).trans hcoeff'
        rw [← finset_sum_coeff, ← h, coeff_natDegree, leadingCoeff_eq_zero] at this
        contradiction
    have : (∑ i ∈ s, p i).natDegree = n := ih hs0 hdegs hcoeff'
    rw [natDegree_add_eq_of_leadingCoeff_add_ne_zero, hdega, this, max_self]
    · simp only [← coeff_natDegree, hdega, this, finset_sum_coeff] at hcoeff ⊢
      rwa [Finset.sum_congr rfl (fun i hi => by rw [hdegs _ hi])] at hcoeff

-- TODO: can we drop the CharZero assumption?
lemma discriminant_prod_X_sub_C [CharZero K] {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → K) :
    discriminant (∏ i in s, (X - C (t i))) = ∏ i in s, ∏ j in s.erase i, (t i - t j) := by
  obtain (rfl | hs0) := s.eq_empty_or_nonempty
  · simp
  rw [discriminant, derivative_prod_X_sub_C, prod_X_sub_C_resultant,
      natDegree_sum_eq (n := s.card - 1) hs0, Even.neg_pow, one_pow, one_mul]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  simp [eval_finset_sum, eval_prod]
  refine Finset.sum_eq_single _
      (fun j _ hji => Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji.symm, hi⟩) (sub_self _))
      (fun h => (h hi).elim)
  · exact Nat.even_mul_pred_self s.card
  · intro i hi
    rw [natDegree_prod_X_sub_C, Finset.card_erase_of_mem hi]
  · simpa only [leadingCoeff_prod_X_sub_C, Finset.sum_const, nsmul_one, ne_eq, Nat.cast_eq_zero,
        Finset.card_eq_zero] using hs0.ne_empty

@[simp]
theorem discriminant_map {L : Type*} [Field L] (φ : K →+* L) (f : K[X]) :
    discriminant (f.map φ) = φ (discriminant f) := by
  rw [discriminant, derivative_map, resultant_map, discriminant]

theorem Splits.eq_fin_prod_roots {L : Type*} [Field L] {φ : K →+* L} {f : K[X]}
    (h : Splits φ f) :
    f.map φ = C (φ f.leadingCoeff) * ∏ i : Fin (Multiset.card (roots (f.map φ))),
      (X - C ((roots (f.map φ)).toList.get (i.cast (Multiset.length_toList _).symm))) := by
  conv_lhs => rw [eq_prod_roots_of_splits h]
  congr 1
  rw [← Fintype.prod_equiv (finCongr (Multiset.length_toList _)) _ _ (fun _ => rfl)]
  simp only [finCongr_apply, Fin.cast_trans, Fin.cast_eq_self]
  refine Eq.trans ?_ (List.finset_prod_get (map φ f).roots.toList (fun x => X - C x)).symm
  exact (Multiset.prod_toList _).symm.trans (List.Perm.prod_eq (Multiset.toList_map _ _))

lemma Finset.Iio_union_Ioi {α : Type*} [Fintype α] [LinearOrder α]
    [LocallyFiniteOrderBot α] [LocallyFiniteOrderTop α] [DecidableEq α] (a : α) :
    (Finset.Iio a) ∪ (Finset.Ioi a) = Finset.univ.erase a :=
  Finset.ext (fun _ =>
    ⟨fun h => Finset.mem_erase.mpr ⟨(Finset.mem_union.mp h).casesOn
        (fun h => (Finset.mem_Iio.mp h).ne) (fun h => (Finset.mem_Ioi.mp h).ne'), Finset.mem_univ _⟩,
      fun h => Finset.mem_union.mpr ((lt_or_gt_of_ne (Finset.mem_erase.mp h).1).imp
        Finset.mem_Iio.mpr Finset.mem_Ioi.mpr)⟩)

lemma Fintype.card_subtype_congr {α : Type*} {p q : α → Prop} (e : ∀ x, p x ↔ q x)
    [Fintype (Subtype p)] [Fintype (Subtype q)] :
    Fintype.card (Subtype p) = Fintype.card (Subtype q) :=
  Fintype.card_congr ((Equiv.refl _).subtypeEquiv e)

-- TODO: promote me to instance?
def Subtype.fintypeOr {α : Type*} {p q : α → Prop} [Fintype (Subtype p)] [Fintype (Subtype q)] :
    Fintype { x // p x ∨ q x } := by
  sorry

theorem Multiset.card_subtype_mem {α : Type*} [DecidableEq α] (s : Multiset α)
    [DecidablePred (fun x => x ∈ s)] :
    Fintype.card { x // x ∈ s } = Multiset.card s.dedup := by
  induction s using Multiset.induction
  case empty =>
    simp
  case cons a s ih =>
    by_cases h : a ∈ s
    · rw [Fintype.card_subtype_congr (q := (· ∈ s)), ih, Multiset.dedup_cons_of_mem h]
      · simp [h]
    · have : Fintype { x // x = a ∨ x ∈ s } := Subtype.fintypeOr
      rw [Fintype.card_subtype_congr (q := fun x => x = a ∨ x ∈ s),
          Fintype.card_subtype_or_disjoint, Fintype.card_subtype_eq, ih,
          Multiset.dedup_cons_of_not_mem h, Multiset.card_cons, add_comm]
      · rintro p hpeq hpmem x hx
        obtain rfl := hpeq _ hx
        exact h (hpmem _ hx)
      · exact fun _ => Multiset.mem_cons

instance {K : Type*} [Field K] : IsIntegrallyClosed K :=
  (isIntegrallyClosed_iff K).mpr (fun {x} _ => ⟨x, rfl⟩)

lemma Finset.prod_univ_prod_Iio {α : Type*} [Fintype α] [LinearOrder α]
    [LocallyFiniteOrderBot α] [LocallyFiniteOrderTop α] [DecidableEq α] (f : α → R) :
    ∏ i : α, ∏ j in Finset.Iio i, (f i - f j) = ∏ i : α, ∏ j in Finset.Ioi i, (f j - f i) :=
  Finset.prod_comm' (by simp)

@[simps]
def List.equivFin {α : Type*} [DecidableEq α] {s : List α} (hs : s.Nodup) :
    { x // x ∈ s } ≃ Fin s.length where
  toFun x := ⟨s.indexOf (x : α), List.indexOf_lt_length.mpr x.2⟩
  invFun i := ⟨s.get i, s.get_mem i _⟩
  left_inv x := by ext; simp
  right_inv i := by ext; exact List.get_indexOf hs i

@[simp] lemma Multiset.nodup_toList {α : Type*} {s : Multiset α} :
    s.toList.Nodup ↔ s.Nodup := by
  rw [← Multiset.coe_toList s, Multiset.coe_nodup, Multiset.coe_toList]

@[simps!]
noncomputable def Multiset.equivFin {α : Type*} {s : Multiset α} (hs : s.Nodup) :
    { x // x ∈ s } ≃ Fin (Multiset.card s) := by
  classical
  exact ((Equiv.refl _).subtypeEquiv (by simp)).trans
    ((List.equivFin (Multiset.nodup_toList.mpr hs)).trans
    (finCongr (by simp)))

lemma Fin.sum_card_sub_one_sub_self {n : ℕ} :
    ∑ i : Fin n, (n - 1 - (i : ℕ)) = n * (n - 1) / 2 := by
  obtain (⟨⟩ | n) := n
  · simp
  · simp only [← Finset.sum_range, add_tsub_cancel_right, Finset.sum_flip (f := fun x => x),
      Finset.sum_range_id]

theorem Algebra.discr_of_isAdjoinRootMonic {K : Type*} [Field K] [Algebra ℚ K] {T : ℚ[X]}
    (f : IsAdjoinRootMonic K T) (hT : Irreducible T) :
    Algebra.discr ℚ (f.powerBasis).basis = (-1) ^ (T.natDegree * (T.natDegree - 1) / 2) * Polynomial.discriminant T := by
  classical
  have hT0 : T ≠ 0 := f.Monic.ne_zero
  have : FiniteDimensional ℚ K := Module.Finite.of_basis f.powerBasis.basis
  apply RingHom.injective (algebraMap ℚ (AlgebraicClosure ℚ))
  rw [map_mul]
  let _ : Fintype (K →ₐ[ℚ] AlgebraicClosure ℚ) := PowerBasis.AlgHom.fintype f.powerBasis
  have ft_aroots : ∀ T : ℚ[X], Fintype ({y // y ∈ aroots T (AlgebraicClosure ℚ)}) := fun _ =>
    Multiset.Subtype.fintype _
  have nd_aroots : (aroots T (AlgebraicClosure ℚ)).Nodup :=
    (nodup_aroots_iff_of_splits hT0 (IsAlgClosed.splits_codomain (k := AlgebraicClosure ℚ) T)).mpr hT.separable
  have nd_aroots' : (aroots (minpoly ℚ f.root) (AlgebraicClosure ℚ)).Nodup :=
    (nodup_aroots_iff_of_splits (minpoly.ne_zero f.isIntegral_root)
      (IsAlgClosed.splits_codomain (k := AlgebraicClosure ℚ) _)).mpr
    (minpoly.irreducible f.isIntegral_root).separable
  have card_aroots : Multiset.card (aroots T (AlgebraicClosure ℚ)) = natDegree T := by
    rw [aroots, ← natDegree_eq_of_degree_eq_some (degree_eq_card_roots hT0 _)]
    · apply IsAlgClosed.splits_codomain
  let e : Fin f.powerBasis.dim ≃ (K →ₐ[ℚ] AlgebraicClosure ℚ) := by
    refine (finCongr ?_).trans ((Multiset.equivFin nd_aroots').symm.trans (PowerBasis.liftEquiv' f.powerBasis).symm)
    rw [f.minpoly_eq hT, card_aroots, f.powerBasis_dim]
  have e_apply : ∀ i, e i f.root =
      (T.aroots (AlgebraicClosure ℚ)).toList.get (Fin.cast (by simp [card_aroots]) i) := by
    intro i
    simp only [e, Equiv.trans_apply, finCongr_apply, PowerBasis.liftEquiv', PowerBasis.liftEquiv]
    simp only [IsAdjoinRootMonic.powerBasis_gen, IsAdjoinRootMonic.powerBasis_dim,
        Equiv.symm_trans_apply, Equiv.subtypeEquiv_symm, Equiv.refl_symm, Equiv.subtypeEquiv_apply,
        Multiset.equivFin_symm_apply_coe, Fin.coe_cast, Equiv.refl_apply, Equiv.coe_fn_symm_mk,
        List.get_eq_getElem]
    simp_rw [← f.powerBasis_gen, f.powerBasis.lift_gen, f.powerBasis_gen, f.minpoly_eq hT]
  rw [Algebra.discr_powerBasis_eq_prod _ _ _ e]
  · conv_rhs => rw [← discriminant_map, Splits.eq_fin_prod_roots (IsAlgClosed.splits_codomain _)]
    rw [f.Monic.leadingCoeff, map_one, map_one, one_mul, discriminant_prod_X_sub_C,
        ← Fintype.prod_equiv (finCongr (natDegree_eq_of_degree_eq_some (degree_eq_card_roots _ _)))
          _ _ (fun _ => rfl)]
    conv_rhs => rw [Finset.prod_congr rfl (fun i _ => by
      rw [← Finset.prod_equiv (s := Finset.univ.erase i)
            (finCongr (natDegree_eq_of_degree_eq_some (degree_eq_card_roots hT0 (IsAlgClosed.splits_codomain _))))
            (by simp [-finCongr_apply])
            (fun _ _ => rfl),
          ← Finset.Iio_union_Ioi, Finset.prod_union]
      · exact (Finset.disjoint_Ioi_Iio _).symm
      · exact hT0
      · apply IsAlgClosed.splits_codomain)]
    simp only [IsAdjoinRootMonic.powerBasis_dim, IsAdjoinRootMonic.powerBasis_gen, pow_two,
      Finset.prod_mul_distrib, finCongr_apply, Fin.cast_trans, Fin.coe_cast]
    rw [mul_left_comm]
    congr 1
    · rw [Finset.prod_univ_prod_Iio]
      refine Fintype.prod_congr _ _ (fun i => Finset.prod_congr rfl (fun j hj => ?_))
      erw [e_apply, e_apply]
    · refine Eq.trans (Fintype.prod_congr _ _ (fun i => Finset.prod_congr rfl (fun j hj => by
        erw [e_apply, e_apply, ← neg_sub, ← neg_one_mul]))) ?_
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Fin.card_Ioi, Finset.prod_pow_eq_pow_sum, Fin.sum_card_sub_one_sub_self,
        map_pow, map_neg, map_one]

theorem Algebra.discr_of_isAdjoinRootMonic {T : ℤ[X]} (f : IsAdjoinRootMonic R T) :
    Algebra.discr ℤ (f.powerBasis).basis = Polynomial.discriminant T := by
  sorry
