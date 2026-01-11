module

-- public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.Group.NatPowAssoc
-- public import Mathlib.Algebra.Lie.OfAssociative
-- public import Mathlib.Data.FunLike.Fintype
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic
-- public import Mathlib.Order.BourbakiWitt
public import Mathlib.RingTheory.DedekindDomain.Factorization
-- public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
-- public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

section IsPrimitiveRoot

theorem IsPrimitiveRoot.isOfFinOrder {M : Type*} [CommMonoid M] {ζ : M} {k : ℕ} [NeZero k]
    (hζ : IsPrimitiveRoot ζ k) : IsOfFinOrder ζ :=
  ⟨k, NeZero.pos k, (isPeriodicPt_mul_iff_pow_eq_one _).mpr hζ.pow_eq_one⟩

end IsPrimitiveRoot

section Ideal

open Pointwise Ideal in
theorem Ideal.smul_span {R M : Type*} [Semiring R] [Monoid M] [MulSemiringAction M R] (m : M)
    (s : Set R) : m • Ideal.span s = Ideal.span (m • s) := by
  simp [pointwise_smul_def, map_span]

theorem Ideal.map_comap_of_bijective {R S : Type*} {F : Type*} [Semiring R] [Semiring S]
    [FunLike F R S] (f : F) [RingHomClass F R S] (hf : Function.Bijective f) {I : Ideal S} :
    map f (comap f I) = I :=
  le_antisymm map_comap_le <| (comap_le_iff_le_map f hf).mp fun _ ↦ id

def Ideal.mapEquiv {R S : Type*} {F : Type*} [CommSemiring R] [CommSemiring S] [EquivLike F R S]
    [RingEquivClass F R S] (f : F) : Ideal R ≃+* Ideal S where
  __ := Ideal.mapHom f
  invFun := Ideal.mapHom (RingEquivClass.toRingEquiv f).symm
  left_inv _ := by
    simpa using Ideal.comap_map_of_bijective _ <| RingEquiv.bijective _
  right_inv _ := by
    simpa using Ideal.map_comap_of_bijective _ <| RingEquiv.bijective _

@[simp]
theorem Ideal.mapEquiv_apply {R S : Type*} {F : Type*} [CommSemiring R] [CommSemiring S]
    [EquivLike F R S] [RingEquivClass F R S] (f : F) (I : Ideal R) :
    Ideal.mapEquiv f I = Ideal.mapHom f I := rfl

end Ideal

section Int

open Ideal

theorem Int.liesOver_of_prime_pow_mem {R : Type*} [CommRing R] [IsDomain R] [Algebra.IsIntegral ℤ R]
    (I : Ideal R) [I.IsPrime] [NeZero I] {p a : ℕ} (hp : p.Prime) (hI : (p : R) ^ a ∈ I) :
    I.LiesOver (span {(p : ℤ)}) := by
  suffices p = absNorm (under ℤ I) by
    rw [this]
    exact Int.liesOver_span_absNorm I
  have h : (absNorm (under ℤ I)).Prime := Nat.absNorm_under_prime I
  rw [eq_comm, ← Nat.prime_dvd_prime_iff_eq h hp, ]
  apply h.dvd_of_dvd_pow
  rwa [← Int.natCast_dvd_natCast, ← Int.cast_mem_ideal_iff, Nat.cast_pow, Int.cast_pow,
    Int.cast_natCast]

end Int

section UniqueFactorizationMonoid

namespace UniqueFactorizationMonoid

open Classical in
theorem associated_iff_count_normalizedFactors_eq_count_normalizedFactors
    {α : Type*} [CancelCommMonoidWithZero α] [NormalizationMonoid α] [UniqueFactorizationMonoid α]
    {x y : α} (hx : x ≠ 0) (hy : y ≠ 0) :
    Associated x y ↔
      ∀ p, Prime p →
        Multiset.count p (normalizedFactors x) = Multiset.count p (normalizedFactors y) := by
  rw [associated_iff_normalizedFactors_eq_normalizedFactors hx hy, Multiset.ext]
  refine forall_congr' fun p ↦ ?_
  by_cases hp : Prime p
  · simp [hp]
  · simp only [hp, IsEmpty.forall_iff, iff_true]
    rw [Multiset.count_eq_zero.mpr, Multiset.count_eq_zero.mpr]
    <;> exact (prime_of_normalized_factor _).mt hp

theorem map_normalizedFactors {α : Type*} [CancelCommMonoidWithZero α] [NormalizationMonoid α]
    [UniqueFactorizationMonoid α] {β : Type*} [CancelCommMonoidWithZero β] [NormalizationMonoid β]
    [UniqueFactorizationMonoid β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β] {f : F}
    (he : ∀ (x : α), normalize (f x) = f (normalize x)) (a : α) :
    Multiset.map f (normalizedFactors a) = normalizedFactors (f a) := by
  classical
  by_cases ha : a = 0
  · simp [ha]
  refine Multiset.ext'_iff.mpr fun p ↦ ?_
  have h : p ∈ normalizedFactors (f a) ↔ p ∈ Multiset.map f (normalizedFactors a) := by
    rw [Multiset.mem_map]
    refine ⟨fun hp ↦ ⟨(normalizedFactorsEquiv he a).symm ⟨p, hp⟩, Subtype.prop _, by simp⟩, ?_⟩
    rintro ⟨q, hq, rfl⟩
    exact ((normalizedFactorsEquiv he a) ⟨q, hq⟩).prop
  by_cases hp : p ∈ normalizedFactors (f a)
  · rw [← ENat.coe_inj, ← normalize_normalized_factor p hp,
      ← emultiplicity_eq_count_normalizedFactors (irreducible_of_normalized_factor p hp)
      (by rwa [AddEquivClass.map_ne_zero_iff]), (EquivLike.inv_apply_eq (b := p) (e := f)).mp rfl,
      emultiplicity_map_eq, emultiplicity_eq_count_normalizedFactors _ ha, he,
      Multiset.count_map_eq_count' _ _ (EmbeddingLike.injective' f)]
    exact (irreducible_of_normalized_factor p hp).map (MulEquivClass.toMulEquiv f).symm
  · rw [Multiset.count_eq_zero.mpr hp, Multiset.count_eq_zero.mpr (h.not.mp hp)]

end UniqueFactorizationMonoid

section IsPrimitiveRoot

theorem IsPrimitiveRoot.autToPow_eq_iff (R : Type*) {S : Type*} [CommRing S] [IsDomain S] {μ : S}
    {n : ℕ} (hμ : IsPrimitiveRoot μ n) [CommRing R] [Algebra R S] [NeZero n] (f : S ≃ₐ[R] S)
    (m : ZMod n) :
    autToPow R hμ f = m ↔ f μ = μ ^ m.val := by
  rw [coe_autToPow_apply]
  have t₀ := (map_rootsOfUnity_eq_pow_self f hμ.toRootsOfUnity).choose_spec
  have t₁ : orderOf hμ.toRootsOfUnity = n := by
    rw [← Subgroup.orderOf_coe]
    rw [← IsPrimitiveRoot.iff_orderOf]
    exact coe_units_iff.mp hμ
  rw [show m = m.val by  aesop]
  simp_rw [ZMod.natCast_eq_natCast_iff', ← t₁]
  rw [← pow_inj_mod]
  rw [Subtype.ext_iff]
  rw [Subgroup.coe_pow]
  rw [Units.ext_iff]
  rw [Units.val_pow_eq_pow_val, ← t₀]
  simp only [val_toRootsOfUnity_coe, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
  simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]

end IsPrimitiveRoot

open Nat List

theorem Nat.ofDigits_digitsAppend (b l n : ℕ) :
    ofDigits b (digitsAppend b l n) = n := by
  sorry
  -- rw [ofDigits_append_replicate_zero, ofDigits_digits]

theorem Nat.ofDigits_eq_sum (b : ℕ) (L : List ℕ) :
    ofDigits b L = ∑ j : Fin (L.length), L[j] * b ^ j.val := by
  induction L with
  | nil => simp
  | cons head tail ih =>
      simp [ofDigits_cons, ih, length_cons, Fin.sum_univ_succ, pow_succ, ← mul_assoc,
        ← Finset.sum_mul, mul_comm b _]

theorem Nat.ofDigits_eq_base_pow_length_sub_one_iff {b : ℕ} {l : List ℕ} (hb : 1 < b)
    (hl : ∀ x ∈ l, x < b) :
    ofDigits b l = b ^ l.length - 1 ↔ ∀ x ∈ l, x = b - 1 := by
  induction l with
  | nil => simp
  | cons head tail ih =>
      have h_tail : ∀ x ∈ tail, x < b := fun x hx ↦ hl x <| mem_cons_of_mem head hx
      specialize ih h_tail
      simp only [length_cons, pow_succ', ofDigits_cons, mem_cons, forall_eq_or_imp, ← ih]
      refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ ?_⟩
      · rw [eq_tsub_iff_add_eq_of_le (by bound)] at h
        have : Nat.ofDigits b tail < b ^ List.length tail := ofDigits_lt_base_pow_length hb h_tail
        have : head < b := hl _ mem_cons_self
        have h_head: head = b - 1 := eq_tsub_of_add_eq (by nlinarith)
        refine ⟨h_head, ?_⟩
        rwa [h_head, ← Nat.sub_add_comm hb.le, Nat.sub_add_cancel (le_add_right_of_le hb.le),
          add_comm, ← eq_tsub_iff_add_eq_of_le (by bound), ← mul_sub_one,
          Nat.mul_left_cancel_iff (by positivity)] at h
      · rw [h2, h1, Nat.mul_sub_one, add_comm, Nat.sub_add_sub_cancel (by bound) hb.le]

theorem Nat.ofDigits_lt_base_pow_length_sub_one_iff {b : ℕ} {l : List ℕ} (hb : 1 < b)
    (hl : ∀ x ∈ l, x < b) :
    ofDigits b l < b ^ l.length - 1 ↔ ∃ x ∈ l, x < b - 1 := by
  convert (Nat.ofDigits_eq_base_pow_length_sub_one_iff hb hl).not
  · have := ofDigits_lt_base_pow_length hb hl
    grind
  · grind

theorem List.sum_eq_of_mem_fixedLengthDigits {b l : ℕ} (hb : 1 < b) (hl : l ≠ 0) {L : List ℕ}
    (hL : L ∈ List.fixedLengthDigits hb l) (hL' : ofDigits b L < b ^ l - 1) :
    L.sum = (b - 1 : ℚ) *
        ∑ i ∈ Finset.range l, Int.fract ((b : ℚ) ^ i * (Nat.ofDigits b L) / (b ^ l - 1)) := by
  sorry
  -- simp_rw [show l = L.length by aesop] at hL hL' hl ⊢
  -- have : NeZero L.length := ⟨hl⟩
  -- have h₁ : 1 < (b : ℚ) ^ L.length := one_lt_pow₀ (by rwa [one_lt_cast]) (NeZero.ne _)
  -- have h_main {i : Fin L.length} : Int.fract ((b : ℚ) ^ i.val *
  --     (∑ j : Fin L.length, L[j] * b ^ j.val) / (b ^ L.length - 1)) =
  --       (∑ j : Fin L.length, L[j]* b ^ (Equiv.addRight j i).val) / (b ^ L.length - 1) := by
  --   refine Int.fract_eq_iff.mpr ⟨?_, ?_, ?_⟩
  --   · apply div_nonneg Rat.natCast_nonneg
  --     rw [← Rat.le_iff_sub_nonneg]
  --     exact h₁.le
  --   · refine (div_lt_one (by rwa [← Rat.lt_iff_sub_pos])).mpr ?_
  --     rw [← Nat.cast_pow, ← Nat.cast_pred (by positivity), Nat.cast_lt]
  --     let L' := ofFn ((fun j ↦ L[↑j]) ∘ fun x ↦ x + -i)
  --     have h₁ : L.length = L'.length := by grind
  --     have h₂ {x : ℕ} : x ∈ L' ↔ x ∈ L :=
  --       Perm.mem_iff <| by simpa using
  --         Equiv.Perm.ofFn_comp_perm (Equiv.addRight i).symm (fun j ↦ L[j])
  --     simp_rw [h₁]
  --     replace hL := ((mem_fixedLengthDigits_iff hb).mp hL).2
  --     convert_to ofDigits b L' < b ^ L'.length - 1
  --     · rw [ofDigits_eq_sum, ← ((Equiv.addLeft i).trans (finCongr h₁)).sum_comp]
  --       simp [L']
  --     · rw [ofDigits_lt_base_pow_length_sub_one_iff hb hL] at hL'
  --       obtain ⟨x, hx, hx'⟩ := hL'
  --       refine (ofDigits_lt_base_pow_length_sub_one_iff hb fun x hx ↦ ?_).mpr ⟨x, by rwa [h₂], hx'⟩
  --       apply hL x
  --       rwa [← h₂]
  --   · simp_rw [eq_comm]
  --     change _ ∈ (Int.castRingHom ℚ).range
  --     rw [Nat.cast_sum, Nat.cast_sum, Finset.mul_sum, ← sub_div, ← Finset.sum_sub_distrib,
  --       Finset.sum_div]
  --     refine Subring.sum_mem _ fun j _ ↦ ?_
  --     simp only [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Equiv.coe_addRight]
  --     rw [mul_rotate', ← mul_sub, mul_div_assoc]
  --     refine Subring.mul_mem _ (natCast_mem _ _) ?_
  --     rw [← pow_add, add_comm, ← Nat.mod_add_div (i + j) L.length, Fin.val_add, pow_add, pow_mul,
  --       ← _root_.mul_sub_one, mul_div_assoc, ← geom_sum_eq h₁.ne']
  --     refine Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ _) _) ?_
  --     exact Subring.sum_mem _ fun k _ ↦ Subring.pow_mem _ (Subring.pow_mem _ (natCast_mem _ _) _) _
  -- simp_rw [Finset.sum_range, Nat.ofDigits_eq_sum, h_main, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow,
  --   Finset.sum_div]
  -- rw [Finset.sum_comm]
  -- simp_rw [← Finset.sum_div, ← Finset.mul_sum]
  -- conv_rhs =>
  --   enter [2, 1, 2, j, 2]
  --   rw [Equiv.sum_comp (Equiv.addRight j) fun i : Fin L.length ↦ (b : ℚ) ^ i.val,
  --     ← Finset.sum_range, geom_sum_eq (by aesop)]
  -- rw [← Finset.sum_mul, mul_div_assoc, div_div_cancel_left', mul_comm, inv_mul_cancel_right₀]
  -- · aesop
  -- · rw [sub_ne_zero, cast_ne_one]
  --   exact hb.ne'
  -- · rw [sub_ne_zero]
  --   exact h₁.ne'

theorem Nat.sum_digits_eq_mul_sum {a b l : ℕ} (hb : 1 < b) (hl : l ≠ 0) (ha : a < b ^ l - 1) :
    (b.digits a).sum =
      (b - 1 : ℚ) * ∑ i ∈ Finset.range l, Int.fract ((b : ℚ) ^ i * a / (b ^ l - 1)) := by
  have h : b.digitsAppend l a ∈ fixedLengthDigits hb l :=
    (Nat.bijOn_digitsAppend' hb l).mapsTo <| by grind
  sorry
  -- rw [show (b.digits a).sum = (b.digitsAppend l a).sum by simp]
  -- convert List.sum_eq_of_mem_fixedLengthDigits hb hl h ?_
  -- · rw [ofDigits_digitsAppend]
  -- · rwa [ofDigits_digitsAppend]

theorem Nat.Prime.three_le_of_odd {p : ℕ} (h₁ : Nat.Prime p) (h₂ : Odd p) : 3 ≤ p :=
  Nat.lt_of_le_of_ne h₁.two_le (by grind)

theorem Nat.digits_pow_sub_one {b : ℕ} (hb : 1 < b) (l : ℕ) :
    b.digits (b ^ l - 1) = List.replicate l (b - 1) := by
  suffices b ^ l - 1 = Nat.ofDigits b (List.replicate l (b - 1)) by
    rw [this, Nat.digits_ofDigits _ hb _ (by grind) (by grind)]
  induction l with
    | zero => simp
    | succ l hl =>
        rw [List.replicate_succ, Nat.ofDigits_cons, ← hl, add_comm (b - 1), Nat.mul_sub, mul_one,
          ← Nat.pow_succ', ← Nat.add_sub_assoc hb.le,
          Nat.sub_add_cancel (Nat.le_self_pow l.succ_ne_zero b)]

@[simp]
theorem WithZero.coe_prod {α ι : Type*} [CommMonoid α] (s : Finset ι) (f : ι → α) :
    ↑((∏ x ∈ s, f x : α) : WithZero α) = ∏ x ∈ s, ↑(f x : WithZero α) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha hi =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, coe_mul, hi]

theorem WithZero.exp_sum {M ι : Type*} [AddCommMonoid M] (s : Finset ι) (f : ι → M) :
    WithZero.exp (∑ x ∈ s, f x) = ∏ x ∈ s, WithZero.exp (f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha hi =>
      rw [Finset.sum_insert ha, exp_add, hi, Finset.prod_insert ha]

theorem WithZero.log_prod {M ι : Type*} [AddCommMonoid M] (s : Finset ι)
    (f : ι → (WithZero (Multiplicative M))) (hs : ∀ x ∈ s, f x ≠ 0) :
    (∏ x ∈ s, f x).log = ∑ x ∈ s, (f x).log := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha hi =>
      have :  ∀ x ∈ s, f x ≠ 0 := fun x hx ↦ hs x <| Finset.mem_insert_of_mem hx
      rw [Finset.prod_insert ha, log_mul, hi this, Finset.sum_insert ha]
      · exact hs _ <| Finset.mem_insert_self a s
      · exact Finset.prod_ne_zero_iff.mpr this
section ringChar

theorem ringChar_prime (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] [Finite R] :
    Nat.Prime (ringChar R) :=
  CharP.char_prime_of_ne_zero R <| CharP.ringChar_ne_zero_of_finite R

theorem ringChar_zero_or_prime (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    ringChar R = 0 ∨ Nat.Prime (ringChar R) := by
  rw [or_iff_not_imp_left]
  exact fun h ↦  CharP.char_prime_of_ne_zero R h

end ringChar

section JacobiSum

theorem jacobiSum_ne_zero {F F' : Type*} [Field F] [Fintype F] [Field F'] {χ ψ : MulChar F F'}
    (hF₁ : Fintype.card F ≠ (2 : F')) (hF₂ : ringChar F' ≠ ringChar F) :
    jacobiSum χ ψ ≠ 0 := by
  by_cases h : χ = 1 ∧ ψ = 1
  · rwa [h.1, h.2, jacobiSum_one_one, sub_ne_zero]
  rw [not_and] at h
  by_cases hχ : χ = 1
  · rw [hχ, jacobiSum_one_nontrivial (h hχ), neg_ne_zero]
    exact one_ne_zero
  by_cases hψ : ψ = 1
  · rw [hψ, jacobiSum_comm, jacobiSum_one_nontrivial hχ, neg_ne_zero]
    exact one_ne_zero
  by_cases h : ψ = χ⁻¹
  · rw [h, jacobiSum_nontrivial_inv hχ, neg_ne_zero]
    intro h
    have := congr_arg (· ^ 2) h
    dsimp at this
    rw [zero_pow, ← map_pow, neg_one_pow_two, map_one] at this
    · exact one_ne_zero this
    · exact two_ne_zero
  have := jacobiSum_mul_jacobiSum_inv hF₂ hχ hψ (by rwa [ne_eq, mul_eq_one_iff_eq_inv'])
  have : (Fintype.card F : F') ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff]
    have hF : Nat.Prime (ringChar F) := ringChar_prime F
    have : Fact (Nat.Prime (ringChar F)) := ⟨hF⟩
    obtain (hF' | hF') := ringChar_zero_or_prime F'
    · rw [hF', Nat.zero_dvd]
      exact Fintype.card_ne_zero
    · have : Fact (Nat.Prime (ringChar F') ):= ⟨hF'⟩
      rwa [← prime_dvd_char_iff_dvd_card, Nat.prime_dvd_prime_iff_eq hF' hF]
  grind

end JacobiSum

section IsPrimitiveRoot

theorem IsPrimitiveRoot.eq_neg_one_of_two_right' {R : Type*} [CommRing R] [NoZeroDivisors R]
    {ζ : Rˣ} (h : IsPrimitiveRoot ζ 2) : ζ = -1 := by
  simp [Units.ext_iff, (IsPrimitiveRoot.coe_units_iff.mpr h).eq_neg_one_of_two_right]

end IsPrimitiveRoot

section Associates

@[simp]
theorem Associates.count_top {α : Type*} [CancelCommMonoidWithZero α] [DecidableEq (Associates α)]
    [(p : Associates α) → Decidable (Irreducible p)] {p : Associates α} :
    Associates.count p ⊤ = 0 := by
  unfold Associates.count
  split_ifs <;> rfl

end Associates


section IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

/--
The image of an element of `HeightOneSpectrum R` by a ring equivalence `R ≃+* S` as an
element of `HeightOneSpectrum S`.
-/
@[simps]
def mapEquiv {R S : Type*} [CommRing R] [CommRing S]
    {F : Type*} [EquivLike F R S] [RingEquivClass F R S] (e : F)
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    IsDedekindDomain.HeightOneSpectrum S where
  asIdeal := v.asIdeal.map e
  isPrime := Ideal.map_isPrime_of_equiv e
  ne_bot := (Ideal.map_eq_bot_iff_of_injective (EmbeddingLike.injective' e)).not.mpr v.ne_bot

open Associates UniqueFactorizationMonoid Classical in
theorem aux {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R S] [NoZeroSMulDivisors R S] [Algebra.IsIntegral R S] (v : HeightOneSpectrum R)
    (w : HeightOneSpectrum S) [h₀ : w.asIdeal.LiesOver v.asIdeal] (I : Ideal R) :
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.map (algebraMap R S) I)).factors =
    Ideal.ramificationIdx (algebraMap R S) v.asIdeal w.asIdeal *
      (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  by_cases hI : I = ⊥
  · simp_rw [hI, Ideal.map_bot, ← Ideal.zero_eq_bot, mk_zero, Associates.factors_zero]
    simp
  rw [factors_mk _ hI, factors_mk _ (Ideal.map_ne_bot_of_ne_bot hI),
    count_some (irreducible_mk.mpr v.irreducible), count_some (irreducible_mk.mpr w.irreducible)]
  rw [← Multiset.count_map_eq_count' _ _ Subtype.val_injective, map_subtype_coe_factors']
  rw [← Multiset.count_map_eq_count' _ _ Subtype.val_injective, map_subtype_coe_factors']
  rw [factors_eq_normalizedFactors, Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal R))]
  rw [factors_eq_normalizedFactors, Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal S))]
  have := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (f := algebraMap R S)
    (p := v.asIdeal) (P := w.asIdeal) (Ideal.map_ne_bot_of_ne_bot v.ne_bot) w.isPrime w.ne_bot
  rw [← prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction
    (fun I ↦ Multiset.count w.asIdeal (normalizedFactors (Ideal.map (algebraMap R S) I)) =
        Ideal.ramificationIdx (algebraMap R S) v.asIdeal w.asIdeal *
          Multiset.count v.asIdeal (normalizedFactors I)) _ ?_ ?_ ?_
  · intro I J hI hJ
    by_cases hIJ : I * J = ⊥
    · simp_rw [hIJ, Ideal.map_bot, ← Ideal.zero_eq_bot, normalizedFactors_zero]
      simp
    rw [← Ideal.zero_eq_bot, ← ne_eq, mul_ne_zero_iff] at hIJ
    rw [Ideal.map_mul, normalizedFactors_mul (Ideal.map_ne_bot_of_ne_bot hIJ.1)
      (Ideal.map_ne_bot_of_ne_bot hIJ.2), Multiset.count_add, hI, hJ, ← mul_add,
      ← Multiset.count_add, ← normalizedFactors_mul hIJ.1 hIJ.2]
  · simp_rw [Ideal.one_eq_top, Ideal.map_top, ← Ideal.one_eq_top, normalizedFactors_one]
    simp only [Multiset.notMem_zero, not_false_eq_true, Multiset.count_eq_zero_of_notMem, mul_zero]
  · intro P hP
    have hP' : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
    rw [mem_normalizedFactors_iff hI] at hP
    have : P.IsMaximal := by
      refine Ideal.IsPrime.isMaximal ?_ hP'
      refine Ideal.isPrime_of_prime ?_
      exact hP.1
    rw [normalizedFactors_irreducible hP.1.irreducible, normalize_eq,
      Ideal.map_algebraMap_eq_finset_prod_pow hP', Finset.prod_eq_multiset_prod,
      normalizedFactors_multiset_prod, Multiset.map_map]
    · simp_rw [Function.comp_apply, normalizedFactors_pow]
      rw [Finset.sum_map_val, Multiset.count_sum']
      have : ∀ x ∈ (P.primesOver S).toFinset, Irreducible x := by
        intro x hx
        rw [Set.mem_toFinset] at hx
        apply Prime.irreducible
        apply Ideal.prime_of_isPrime
        · apply Ideal.ne_bot_of_mem_primesOver hP' hx
        · exact hx.1
      simp_rw +contextual [Multiset.count_nsmul, normalizedFactors_irreducible (this _ _),
        normalize_eq, Multiset.count_singleton]
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Set.mem_toFinset]
      by_cases hP : v.asIdeal = P
      · rw [hP, if_pos, if_pos rfl]
        refine ⟨w.isPrime, ?_⟩
        rwa [← hP]
      · rw [if_neg, if_neg hP]
        intro h
        have := h.2
        rw [Ideal.liesOver_iff] at this h₀
        have := h₀.trans this.symm
        exact hP this
    · simp
      intro x hx
      rw [← Ideal.zero_eq_bot]
      rw [pow_eq_zero_iff]
      · exact Ideal.ne_bot_of_mem_primesOver hP' hx
      · have := hx.1
        have := hx.2
        apply Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ hP'

open Associates UniqueFactorizationMonoid in
theorem intValuation_algebraMap {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain R]
    [IsDedekindDomain S] [Algebra R S] [NoZeroSMulDivisors R S] [Algebra.IsIntegral R S]
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (h : Ideal.ramificationIdx (algebraMap R S) v.asIdeal w.asIdeal ≠ 0) (r : R) :
    w.intValuation (algebraMap R S r) =
      (v.intValuation r) ^ Ideal.ramificationIdx (algebraMap R S) v.asIdeal w.asIdeal := by
  classical
  by_cases hr : r = 0
  · simpa [hr] using (zero_pow h).symm
  rw [intValuation_def, intValuation_def, if_neg hr, if_neg]
  · simp only [WithZero.exp_neg, inv_pow, ← WithZero.exp_nsmul, Int.nsmul_eq_mul, inv_inj,
      WithZero.exp_inj, ← Nat.cast_mul]
    rw [Nat.cast_inj]
    rw [← aux, Ideal.map_span]
    simp
  rw [← ne_eq]
  rwa [map_ne_zero_iff]
  exact FaithfulSMul.algebraMap_injective R S

theorem intValuation_pow_le_iff_not_dvd {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) (n : ℕ) :
    WithZero.exp (-↑n) ≤ v.intValuation r ↔ ¬ v.asIdeal ^ (n + 1) ∣ Ideal.span {r} := by
  have {a} {n} (ha : a ≠ 0) :
      a < WithZero.exp (- n) ↔ a ≤ WithZero.exp (- (n + 1)) := by
    rw [← WithZero.exp_log ha, WithZero.exp_le_exp, WithZero.exp_lt_exp]
    grind
  rw [← not_lt, this, ← Nat.cast_add_one, intValuation_le_pow_iff_dvd]
  exact intValuation_ne_zero v r hr

theorem intValuation_pow_le_iff_not_mem {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) (n : ℕ) :
    WithZero.exp (-↑n) ≤ v.intValuation r ↔ ¬ r ∈ v.asIdeal ^ (n + 1) := by
   rw [intValuation_pow_le_iff_not_dvd _ hr, Ideal.dvd_span_singleton]

theorem intValuation_eq_iff {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) (n : ℕ) :
    v.intValuation r = WithZero.exp (-↑n) ↔ r ∈ v.asIdeal ^ n ∧ ¬ r ∈ v.asIdeal ^ (n + 1) := by
  rw [le_antisymm_iff, intValuation_le_pow_iff_mem, intValuation_pow_le_iff_not_mem _ hr]

theorem intValuation_pos {R : Type*} [CommRing R] [IsDedekindDomain R]
    (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) :
    0 < v.intValuation r := by
  rw [intValuation_def, if_neg hr]
  exact WithZero.exp_pos

open Classical Associates UniqueFactorizationMonoid in
theorem IsDedekindDomain.ideal_eq_ideal_iff_count_eq_count {R : Type*} [CommRing R]
    [IsDedekindDomain R] {I J : Ideal R} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I = J ↔ ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      Multiset.count v.asIdeal (normalizedFactors I) =
        Multiset.count v.asIdeal (normalizedFactors J) := by
  rw [← associated_iff_eq, associated_iff_count_normalizedFactors_eq_count_normalizedFactors hI hJ]
  refine ⟨?_, ?_⟩
  · intro h v
    refine h v.asIdeal v.prime
  · intro h p hp
    exact h (IsDedekindDomain.HeightOneSpectrum.ofPrime hp)

end IsDedekindDomain.HeightOneSpectrum

section Ideal

open Ideal

theorem Ideal.liesOver_pow_of_le_ramificationIdx {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : Ideal R) (P : Ideal S) [P.LiesOver p] {e : ℕ} (h₁ : 1 ≤ e)
    (h₂ : e ≤ ramificationIdx (algebraMap R S) p P) : (P ^ e).LiesOver p := by
  rw [liesOver_iff, under_def]
  apply le_antisymm
  · exact le_trans (le_comap_pow_ramificationIdx (p := p) (P := P) (f := algebraMap R S))
      (comap_mono (pow_le_pow_right h₂))
  · rw [over_def P p, under_def]
    convert comap_mono <| pow_le_pow_right h₁
    rw [pow_one]

end Ideal

section Nat

theorem Nat.two_le_div_of_dvd {a b : ℕ} (h₁ : b ∣ a) (h₂ : b ≠ a) (h₃ : a ≠ 0) :
    2 ≤ a / b := by
  obtain ⟨c, rfl⟩ := h₁
  have hb : 0 < b := by grind
  rw [Nat.mul_div_cancel_left _ hb]
  exact (Nat.two_le_iff c).mpr ⟨by grind, by grind⟩

end Nat

section IsPrimitiveRoot

theorem IsPrimitiveRoot.pow_div_gcd {M : Type*} [CommMonoid M] {ζ : M} {n a : ℕ} (ha : a ≠ 0)
    (h : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (ζ ^ a) (n / n.gcd a) := by
  rw [IsPrimitiveRoot.iff_orderOf, orderOf_pow' _ ha, h.eq_orderOf]

end IsPrimitiveRoot

section gaussSum

def gaussSum_map {R R' R'' : Type*} [CommRing R] [Fintype R] [CommRing R'] [CommRing R'']
    (χ : MulChar R R') (ψ : AddChar R R') (f : R' →+* R'') :
    f (gaussSum χ ψ) = gaussSum (χ.ringHomComp f) (f.compAddChar ψ) := by
  unfold gaussSum
  simp [map_sum, map_mul]

@[simp]
theorem MulChar.one_apply_zero {R : Type*} [Nontrivial R] [CommMonoidWithZero R] {R' : Type*}
    [CommMonoidWithZero R'] : (1 : MulChar R R') 0 = 0 := dif_neg not_isUnit_zero

theorem gaussSum_one {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] {R' : Type*}
    [CommRing R'] : gaussSum (1 : MulChar R R') (1 : AddChar R R') = (Fintype.card Rˣ) := by
  classical
  simp [gaussSum, MulChar.sum_one_eq_card_units]

theorem gaussSum_one_left {R : Type*} [Field R] [Fintype R] {R' : Type*} [CommRing R'] [IsDomain R']
    (ψ : AddChar R R') : gaussSum 1 ψ = if ψ = 0 then (Fintype.card R : R') - 1 else -1 := by
  classical
  rw [gaussSum, ← Finset.univ.add_sum_erase _ (Finset.mem_univ 0), MulChar.one_apply_zero,
    zero_mul, zero_add]
  have : ∀ x ∈ Finset.univ.erase (0 : R), (1 : MulChar R R') x = 1 := by
    intro x hx
    exact MulChar.one_apply <| isUnit_iff_ne_zero.mpr <| Finset.ne_of_mem_erase hx
  simp_rw +contextual [this, one_mul]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), AddChar.map_zero_eq_one, AddChar.sum_eq_ite,
    ite_sub, zero_sub]

theorem gaussSum_one_right {R : Type*} [CommRing R] [Fintype R] {R' : Type*} [CommRing R']
    [IsDomain R'] {χ : MulChar R R'} (hχ : χ ≠ 1) : gaussSum χ 1 = 0 := by
  simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hχ

end gaussSum

section NumberField

open NumberField

@[simp]
theorem RingOfIntegers.minpoly_coe {K : Type*} [Field K] (x : 𝓞 K) :
    minpoly ℤ (x : K) = minpoly ℤ x :=
  minpoly.algebraMap_eq RingOfIntegers.coe_injective x

end NumberField

section Ideal.map

theorem Ideal.map_algEquiv {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (I : Ideal A) :
    map f I = map (f : A ≃+* B) I := rfl

theorem Ideal.comap_algEquiv {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : B ≃ₐ[R] A) (I : Ideal A) :
    comap f I = comap (f : B ≃+* A) I := rfl

theorem Ideal.map_ringEquiv {R S : Type*} [Semiring R] [Semiring S] (f : R ≃+* S) (I : Ideal R) :
    map f I = map (f : R →+* S) I := rfl

theorem Ideal.comap_ringEquiv {R S : Type*} [Semiring R] [Semiring S] (f : S ≃+* R) (I : Ideal R) :
    comap f I = comap (f : S →+* R) I := rfl

theorem Ideal.map_eq_iff_eq_comap {R S : Type*} [Semiring R] [Semiring S] {I : Ideal R}
    {J : Ideal S} {f : R ≃+* S} :
    map f I = J ↔ I = comap f J :=
  ⟨fun h ↦ by rw [← h, ← map_symm, ← map_coe f.symm, ← map_coe f, map_of_equiv],
    fun h ↦ by
      rw [h, ← comap_symm, ← comap_coe f.symm, ← comap_coe f]
      exact (RingEquiv.symm_symm f) ▸ comap_of_equiv f.symm⟩

theorem Ideal.map_injective_of_equiv {R S : Type*} [Semiring R] [Semiring S] (f : R ≃+* S) :
    Function.Injective (map f) := by
  intro _ _ h
  rwa [map_eq_iff_eq_comap, comap_map_of_bijective _ f.bijective ] at h

theorem Ideal.comap_injective_of_equiv {R S : Type*} [Semiring R] [Semiring S] (f : R ≃+* S) :
    Function.Injective (comap f) := by
  intro _ _ h
  rw [← map_symm, ← map_symm] at h
  exact Ideal.map_injective_of_equiv f.symm h

end Ideal.map

noncomputable section AlgEquiv.restrictNormal'

variable {A C₁ C₂ : Type*} (K B L M₁ M₂ : Type*) [CommRing A] [CommRing C₁] [Algebra A C₁]
  [Field K]
  [Field M₁] [CommRing C₂] [Algebra A C₂] [Field M₂] [Algebra A K] [IsFractionRing A K]
  [Algebra K M₁] [Algebra K M₂] [Algebra A M₁] [Algebra A M₂]
  [IsScalarTower A K M₁] [Algebra C₁ M₁] [IsScalarTower A C₁ M₁] [IsIntegralClosure C₁ A M₁]
  [Algebra.IsAlgebraic K M₁]
  [IsScalarTower A K M₂] [Algebra C₂ M₂] [IsScalarTower A C₂ M₂] [IsIntegralClosure C₂ A M₂]
  [Algebra.IsAlgebraic K M₂]
  [CommRing B] [Field L]
  [Algebra B L] [Algebra A B] [Algebra K L] [Algebra L M₁] [Algebra L M₂]
  [IsScalarTower K L M₁] [IsScalarTower K L M₂]
  [Normal K L]
  [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [IsIntegralClosure B A L]

/-- Docstring. -/
def AlgEquiv.restrictNormal' (σ : C₁ ≃ₐ[A] C₂) : B ≃ₐ[A] B :=
  galRestrict A K L B ((galLiftEquiv K M₁ M₂ σ).restrictNormal L)

variable [Algebra B C₁] [Algebra B C₂] [Algebra B M₁] [IsScalarTower B C₁ M₁] [Algebra B M₂]
  [IsScalarTower B C₂ M₂] [IsScalarTower B L M₁] [IsScalarTower B L M₂]

@[simp]
theorem AlgEquiv.restrictNormal'_commutes (σ : C₁ ≃ₐ[A] C₂) (x : B) :
    algebraMap B C₂ (σ.restrictNormal' K B L M₁ M₂ x) = σ (algebraMap B C₁ x) := by
  unfold restrictNormal'
  apply IsIntegralClosure.algebraMap_injective C₂ A M₂
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B L M₂,
    algebraMap_galRestrict_apply, AlgEquiv.restrictNormal_commutes,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B C₁ M₁,
    galLiftEquiv_algebraMap_apply]

end AlgEquiv.restrictNormal'

noncomputable section AlgEquiv.liftNormal'

variable {A B₁ B₂ : Type*} (K L₁ L₂ C M) [CommRing A] [CommRing B₁] [Algebra A B₁] [Field K]
  [Field L₁]
  [Algebra A K] [IsFractionRing A K] [Algebra K L₁] [Algebra A L₁] [IsScalarTower A K L₁]
  [CommRing B₂] [Algebra A B₂] [Field L₂] [Algebra K L₂] [Algebra A L₂] [IsScalarTower A K L₂]
  [CommRing C] [Algebra.IsAlgebraic K L₁] [Algebra.IsAlgebraic K L₂]
  [Algebra B₁ L₁] [IsScalarTower A B₁ L₁] [IsIntegralClosure B₁ A L₁]
  [Algebra B₂ L₂] [IsScalarTower A B₂ L₂] [IsIntegralClosure B₂ A L₂]
  [Field M] [Algebra K M] [Algebra L₁ M] [Algebra L₂ M] [IsScalarTower K L₁ M]
  [IsScalarTower K L₂ M] [Normal K M] [Algebra A C] [Algebra A M] [IsScalarTower A K M]
  [Algebra C M] [IsScalarTower A C M] [IsIntegralClosure C A M]

-- /-- Docstring. -/
-- def AlgEquiv.liftNormal' (σ : B₁ ≃ₐ[A] B₂) : C ≃ₐ[A] C :=
--   galRestrict A K M C ((galLiftEquiv K L₁ L₂ σ).liftNormal M)

-- variable [Algebra B₁ C] [Algebra B₂ C] [Algebra B₁ M] [IsScalarTower B₁ C M]
--   [IsScalarTower B₁ L₁ M] [Algebra B₂ M] [IsScalarTower B₂ C M] [IsScalarTower B₂ L₂ M]

-- @[simp]
-- theorem AlgEquiv.liftNormal'_commutes (σ : B₁ ≃ₐ[A] B₂) (x : B₁) :
--     (σ.liftNormal' K L₁ L₂ C M) (algebraMap B₁ C x) = algebraMap B₂ C (σ x) := by
--   unfold liftNormal'
--   apply IsIntegralClosure.algebraMap_injective C A M
--   rw [algebraMap_galRestrict_apply, ← IsScalarTower.algebraMap_apply,
--     ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply B₁ L₁ M,
--     AlgEquiv.liftNormal_commutes, galLiftEquiv_algebraMap_apply, ← IsScalarTower.algebraMap_apply]

-- @[simp]
-- theorem AlgEquiv.restrict_liftNormal' [FaithfulSMul B₁ C] [Normal K L₁] (σ : B₁ ≃ₐ[A] B₁) :
--     (σ.liftNormal' K L₁ L₁ C M).restrictNormal' K B₁ L₁ M M = σ := by
--   ext
--   apply FaithfulSMul.algebraMap_injective B₁ C
--   rw [AlgEquiv.restrictNormal'_commutes, AlgEquiv.liftNormal'_commutes]

end AlgEquiv.liftNormal'

section primesOverGalois

variable {A C₁ C₂ : Type*} [CommRing A]
  [CommRing C₁] [IsIntegrallyClosed C₁] [Algebra A C₁] [Module.Finite A C₁]
  [CommRing C₂] [IsIntegrallyClosed C₂] [Algebra A C₂] [Module.Finite A C₂]
  {K L M₁ M₂ : Type*} [Field K] [Field M₁] [Field M₂] [Algebra A K] [IsFractionRing A K]
  [Algebra C₁ M₁] [IsFractionRing C₁ M₁] [Algebra K M₁] [Algebra A M₁] [IsScalarTower A C₁ M₁]
  [IsScalarTower A K M₁] [FiniteDimensional K M₁]
  [Algebra C₂ M₂] [IsFractionRing C₂ M₂] [Algebra K M₂] [Algebra A M₂] [IsScalarTower A C₂ M₂]
  [IsScalarTower A K M₂] [FiniteDimensional K M₂]
  {B : Type*} [CommRing B] [Field L] [Algebra B L] [Algebra A B]
  [Algebra K L] [Normal K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegralClosure B A L]
  [Algebra B C₁] [Algebra L M₁] [IsScalarTower K L M₁] [Algebra B M₁] [IsScalarTower B L M₁]
  [IsScalarTower B C₁ M₁]
  [Algebra B C₂] [Algebra L M₂] [IsScalarTower K L M₂] [Algebra B M₂] [IsScalarTower B L M₂]
  [IsScalarTower B C₂ M₂]

variable (K L M₁ M₂) in
theorem Ideal.liesOver_iff_map_liesOver_map (P : Ideal B) (Q : Ideal C₁) (σ : C₁ ≃ₐ[A] C₂) :
    (Q.map σ).LiesOver (P.map (σ.restrictNormal' K B L M₁ M₂)) ↔ Q.LiesOver P := by
  rw [liesOver_iff, under_def, liesOver_iff, under_def, map_algEquiv, map_eq_iff_eq_comap,
    comap_ringEquiv, comap_comap, map_algEquiv, ← comap_symm, comap_ringEquiv, comap_comap]
  congr!
  ext
  simp [← AlgEquiv.symm_toRingEquiv]

variable (K L M₁ M₂) in
theorem Ideal.liesOver_iff_comap_liesOver_comap (P : Ideal B) (Q : Ideal C₁) (σ : C₁ ≃ₐ[A] C₁) :
    (Q.comap σ).LiesOver (P.comap (σ.restrictNormal' K B L M₁ M₁)) ↔ Q.LiesOver P := by
  rw [← liesOver_iff_map_liesOver_map K L M₁ M₁ _ _ σ, map_comap_eq_self_of_equiv,
    map_comap_eq_self_of_equiv]

variable [IsDomain A] [IsIntegrallyClosed A] [IsDomain B] [IsIntegrallyClosed B] [Module.Finite A B]
  [IsFractionRing B L] [FiniteDimensional K L] {C M : Type*} [CommRing C]
  [IsIntegrallyClosed C] [Field M] [Algebra C M] [IsFractionRing C M] [Algebra A C] [Algebra B C]
  [Algebra A M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsScalarTower A K M]
  [IsScalarTower A C M] [IsIntegralClosure C A M] [Module.Finite A C] [Algebra B M]
  [IsScalarTower B C M] [FiniteDimensional K M] [IsScalarTower B L M]
  [FaithfulSMul B C]

-- open Ideal in
-- variable (K L M) in
-- theorem Ideal.ncard_primesOver_eq_ncard_primesOver (p : Ideal A) (P₁ P₂ : Ideal B) [P₁.IsPrime]
--     [P₂.IsPrime] [P₁.LiesOver p] [P₂.LiesOver p] [IsGalois K L] [Normal K M] :
--     (P₁.primesOver C).ncard = (P₂.primesOver C).ncard := by
--   obtain ⟨σ, hσ⟩ := exists_map_eq_of_isGalois p P₁ P₂ K L
--   let τ := σ.liftNormal' K L L C M
--   refine Set.ncard_congr ?_ (fun Q ↦ ?_) ?_ ?_
--   · exact fun Q _ ↦ Q.map (σ.liftNormal' K L L C M)
--   · intro ⟨h₁, h₂⟩
--     refine ⟨map_isPrime_of_equiv _, ?_⟩
--     · rwa [← liesOver_iff_map_liesOver_map K L M M _ _ (σ.liftNormal' K L L C M),
--         AlgEquiv.restrict_liftNormal', hσ] at h₂
--   · exact fun _ _ _ _ h ↦ map_injective_of_equiv (AlgEquiv.liftNormal' K L L C M σ).toRingEquiv h
--   · intro Q ⟨hQ₁, hQ₂⟩
--     refine ⟨?_, ⟨?_, ?_⟩ , ?_⟩
--     · exact comap (AlgEquiv.liftNormal' K L L C M σ) Q
--     · exact comap_isPrime _ _
--     · have := liesOver_iff_comap_liesOver_comap (σ := σ.liftNormal' K L L C M)
--         (Q := Q) (P := P₂) (M₁ := M) (L := L) (K := K) ..
--       rwa [← this, AlgEquiv.restrict_liftNormal', ← hσ, comap_map_of_bijective] at hQ₂
--       exact σ.bijective
--     · rw [map_comap_eq_self_of_equiv]









-- end primesOverGalois


section primesOverRestrict

@[simp]
theorem Ideal.primesOverFinset_bot (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    [IsDedekindDomain B] :
    primesOverFinset (⊥ : Ideal A) B = ∅ := by
  classical
  rw [primesOverFinset, map_bot, UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    ← zero_eq_bot, UniqueFactorizationMonoid.normalizedFactors_zero, Multiset.toFinset_eq_empty]

-- variable {A : Type*} [CommSemiring A] (p : Ideal A)

-- def Ideal.primesOverRestrict (B C : Type*) [CommSemiring B] [Semiring C] [Algebra A B]
--     [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
--     p.primesOver C → p.primesOver B :=
--   fun P ↦
--     ⟨comap (algebraMap B C) P, ⟨IsPrime.under B P.1, under_liesOver_of_liesOver B P.1 p⟩⟩

-- @[simp]
-- theorem Ideal.primesOverRestrict_apply (B C : Type*) [CommSemiring B] [Semiring C] [Algebra A B]
--     [Algebra A C] [Algebra B C] [IsScalarTower A B C] (P : p.primesOver C) :
--     p.primesOverRestrict B C P = comap (algebraMap B C) P := rfl

-- theorem Ideal.primesOverRestrict_surjective (B C : Type*) [CommRing B] [CommRing C]
--     [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] [FaithfulSMul B C]
--     [Algebra.IsIntegral B C] :
--     Function.Surjective (p.primesOverRestrict B C) := by
--   intro P
--   have hQ := exists_ideal_over_prime_of_isIntegral P.1 (⊥ : Ideal C)
--     (by simp [comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective B C)])
--   refine ⟨⟨hQ.choose, ⟨hQ.choose_spec.2.1, ?_⟩⟩, ?_⟩
--   · have : hQ.choose.LiesOver P.1 := (liesOver_iff _ _).mpr hQ.choose_spec.2.2.symm
--     exact LiesOver.trans hQ.choose P.1 p
--   · simpa [Subtype.ext_iff] using hQ.choose_spec.2.2

open Ideal in
theorem Ideal.mem_primesOver_of_mem_primesOver_and_liesOver {A : Type*} [CommSemiring A]
    (p : Ideal A) {B C : Type*} [CommSemiring B] [Semiring C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] (P : Ideal B) (Q : Ideal C)
    [P.LiesOver p] :
    Q ∈ p.primesOver C ∧ Q.LiesOver P ↔ Q ∈ P.primesOver C :=
  ⟨fun ⟨⟨h₁, _⟩, h₃⟩ ↦ ⟨h₁, h₃⟩, fun ⟨h₁, h₂⟩ ↦ ⟨⟨h₁, LiesOver.trans Q P p⟩, h₂⟩⟩



-- theorem Ideal.primesOverRestrict_eq_iff (B C : Type*) [CommSemiring B] [Semiring C] [Algebra A B]
--     [Algebra A C] [Algebra B C] [IsScalarTower A B C] (P : p.primesOver B)
--     (Q : p.primesOver C) : p.primesOverRestrict B C Q = P ↔ Q.1.LiesOver P.1 := by
--   sorry

-- theorem Ideal.primesOverRestrict_eq_iff' (B C : Type*) [CommSemiring B] [Semiring C] [Algebra A B]
--     [Algebra A C] [Algebra B C] [IsScalarTower A B C] (P : Ideal B) [P.LiesOver p]
--     (Q : p.primesOver C) : p.primesOverRestrict B C Q = P ↔ Q.1 ∈ P.primesOver C := by
--   simp [primesOver, primesOver.isPrime, liesOver_iff, under_def, eq_comm]

theorem Ideal.card_primesOverFinset_eq_sum_card_primesOverFinset (A B C : Type*) [CommRing A]
    [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C] [Algebra A B]
    [NoZeroSMulDivisors A B] [Algebra A C] [NoZeroSMulDivisors A C] [Algebra B C]
    [NoZeroSMulDivisors B C] [IsScalarTower A B C] (p : Ideal A) [p.IsMaximal] :
    (primesOverFinset p C).card = ∑ P ∈ primesOverFinset p B, (primesOverFinset P C).card := by
  classical
  by_cases hp : p = ⊥
  · simp [hp]
  rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to (t := primesOverFinset p B)
    (g := fun x ↦ comap (algebraMap B C) x)]
  · refine Finset.sum_congr rfl fun P hP ↦ ?_
    rw [← Finset.card_eq_sum_ones]
    refine Finset.card_bijective (fun Q ↦ Q) Function.bijective_id fun Q ↦ ?_
    rw [mem_primesOverFinset_iff hp] at hP
    have hP' : P ≠ ⊥ := by
      have := hP.2
      apply ne_bot_of_liesOver_of_ne_bot hp
    have : P.IsMaximal := by
      have := hP.1
      exact Ring.DimensionLEOne.maximalOfPrime hP' this
    rw [Finset.mem_filter, mem_primesOverFinset_iff hp, mem_primesOverFinset_iff hP',
      ← under_def, eq_comm, ← liesOver_iff]
    have : P.LiesOver p := by
      exact hP.2
    exact mem_primesOver_of_mem_primesOver_and_liesOver p P Q
  · intro Q hQ
    rw [mem_primesOverFinset_iff hp] at hQ ⊢
    have := hQ.1
    have := hQ.2
    exact ⟨IsPrime.under B Q, under_liesOver_of_liesOver B Q p⟩

-- theorem Ideal.ncard_primesOver_eq_sum_ncard_primesOver (A B C : Type*) [CommRing A] [Nontrivial A]
--     [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C] [Algebra A B]
--     [NoZeroSMulDivisors A B] [Algebra A C] [NoZeroSMulDivisors A C] [Algebra B C]
--     [NoZeroSMulDivisors B C] [IsScalarTower A B C] [Algebra.IsIntegral A C]
--     [Algebra.IsIntegral A B] [Algebra.IsIntegral B C] (p : Ideal A) [p.IsMaximal] :
--     (p.primesOver C).ncard = ∑ P : p.primesOver B, (P.1.primesOver C).ncard := by
--   by_cases hp : p = ⊥
--   · simp [hp, primesOver_bot]
--     let _ : Unique (p.primesOver B) := by
--       rw [hp, primesOver_bot]
--       exact Set.uniqueSingleton ⊥
--     rw [Fintype.sum_subsingleton _  ⟨⊥, Ideal.bot_prime, hp ▸ Ideal.bot_liesOver_bot A B⟩,
--       primesOver_bot, Set.ncard_singleton]
--   have (P : p.primesOver B) : P.1 ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp _
--   simp_rw [← coe_primesOverFinset hp C, ← coe_primesOverFinset (this _) C, Set.ncard_coe_finset]
--   rw [card_primesOverFinset_eq_sum_card_primesOverFinset A B C, Finset.sum_subtype]
--   exact fun  _ ↦ by rw [mem_primesOverFinset_iff hp]

end primesOverRestrict


theorem Ideal.eq_of_dvd_of_isPrime {A : Type*} [CommRing A] [IsDedekindDomain A] {I J : Ideal A}
    [hIP : I.IsPrime] [hJP : J.IsPrime] (hJ : J ≠ ⊥) (h : I ∣ J) : I = J := by
  by_cases hI : I = ⊥
  · rw [hI, Ideal.dvd_iff_le, le_bot_iff] at h
    rw [h, hI]
  exact (prime_dvd_prime_iff_eq (prime_of_isPrime hI hIP) (prime_of_isPrime hJ hJP)).mp h

section ExpChar

variable (p : ℕ)

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

attribute [local instance] Ideal.Quotient.field

instance [hp : Fact (Nat.Prime p)] : CharP (ℤ ⧸ 𝒑) p := by
  refine CharP.quotient ℤ p ?_
  rw [mem_nonunits_iff, isUnit_iff_dvd_one, Int.natCast_dvd_ofNat]
  exact Nat.Prime.not_dvd_one hp.out

theorem Int.ideal_span_ne_bot [NeZero p] : 𝒑 ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact NeZero.ne _

instance [NeZero p] : Finite (ℤ ⧸ 𝒑) := by
  refine Ideal.finiteQuotientOfFreeOfNeBot 𝒑 ?_
  exact Int.ideal_span_ne_bot _

end ExpChar

@[simp]
theorem rootsOfUnity_pow_eq_one {M : Type*} [CommMonoid M] (k : ℕ) (ζ : rootsOfUnity k M) :
    ζ ^ k = 1 := by
  rw [Subtype.ext_iff, Subgroup.coe_pow, Subgroup.coe_one, ← mem_rootsOfUnity]
  exact ζ.prop

open Ideal in
theorem Int.mem_ideal_of_liesOver_span {R : Type*} [Ring R] (d : ℤ) (I : Ideal R)
    [h : I.LiesOver (span {d})] : (d : R) ∈ I := by
  simp [Int.cast_mem_ideal_iff, ← (liesOver_iff _ _).mp h]

theorem ZMod.orderOf_mod_self_pow_sub_one {n k : ℕ} (hn : 1 < n) (hk : 0 < k) :
    orderOf (n : ZMod (n ^ k - 1)) = k := by
  have : NeZero n := NeZero.of_gt hn
  refine (orderOf_eq_iff hk).mpr ⟨?_, fun m hm₁ hm₂ ↦ ?_⟩
  · rw [← Nat.cast_npow, ← sub_eq_zero, ← Nat.cast_one (R := ZMod (n ^ k - 1)),
      ← Nat.cast_sub NeZero.one_le]
    exact ZMod.natCast_self _
  · rw [ne_eq, ← Nat.cast_npow, ← sub_eq_zero, ← Nat.cast_one (R := ZMod (n ^ k - 1)),
      ← Nat.cast_sub NeZero.one_le, ZMod.natCast_eq_zero_iff]
    refine (Nat.le_of_dvd ?_).mt (not_le.mpr ?_)
    · exact Nat.zero_lt_sub_of_lt <| Nat.one_lt_pow hm₂.ne' hn
    · exact Nat.sub_lt_sub_iff_right NeZero.one_le (c := 1).mpr <| Nat.pow_lt_pow_right hn hm₁

theorem mem_torsion_iff_isPrimitiveRoot {G : Type*} [CommGroup G] {ζ : G} :
    ζ ∈ CommGroup.torsion G ↔ (∃ k, k ≠ 0 ∧ IsPrimitiveRoot ζ k) := by
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, hn₁, hn₂⟩ ↦ ?_, fun ⟨k, hk₁, hk₂⟩ ↦ ?_⟩
  · exact ⟨orderOf ζ, orderOf_ne_zero_iff.mpr ⟨n, hn₁, (isPeriodicPt_mul_iff_pow_eq_one _).mpr hn₂⟩,
      IsPrimitiveRoot.orderOf ζ⟩
  · exact ⟨k, Nat.zero_lt_of_ne_zero hk₁, hk₂.pow_eq_one⟩

theorem mem_torsion_of_isPrimitiveRoot (k : ℕ) [NeZero k] {G : Type*} [CommGroup G]
    {ζ : G} (hζ : IsPrimitiveRoot ζ k) :
    ζ ∈ CommGroup.torsion G :=
  mem_torsion_iff_isPrimitiveRoot.mpr ⟨k, NeZero.ne _, hζ⟩

@[simp]
lemma RingHom.rangeRestrict_injective_iff {R S : Type*} [Ring R] [Ring S] {f : R →+* S} :
    Function.Injective f.rangeRestrict ↔ Function.Injective f := by
  convert Set.injective_codRestrict _

@[to_additive]
theorem MonoidAlgebra.single_sub {R M : Type*} [Ring R] (a : M) (b₁ b₂ : R) :
    single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  Finsupp.single_sub _ _ _

@[to_additive (attr := simp)]
theorem MonoidAlgebra.fintype_sum_single {k G : Type*} [Fintype G] [Semiring k]
    (f : MonoidAlgebra k G) : ∑ g : G, single g (f g) = f := by
  classical
  rw [← sum_single f, Finsupp.sum_fintype]
  · conv_lhs =>
      enter [2, g, 2]
      rw [Finset.sum_apply']
      simp [single_apply]
  · intro _
    simp

-- lifted from #29517

lemma IsPrimitiveRoot.div_of_dvd {M : Type*} [CommMonoid M] {ζ : M} {n m : ℕ} [NeZero n]
    (hζ : IsPrimitiveRoot ζ n) (h : m ∣ n) :
    IsPrimitiveRoot (ζ ^ (n / m)) m := by
  have hm0 : 0 < m := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp only [zero_dvd_iff] at h
    exact NeZero.out h
  obtain ⟨k, rfl⟩ := id h
  have hk0 : 0 < k := by
    rw [Nat.pos_iff_ne_zero]
    rintro rfl
    simp_all
  simpa [hm0, hk0] using hζ.pow_of_dvd hk0.ne' (dvd_mul_left _ _)

-- These should be generalized

open NumberField in
theorem NumberField.Units.card_rootsOfUnity (K : Type*) [Field K] [NumberField K]
    (n : ℕ) [NeZero n] (hn : n ∣ torsionOrder K) :
    Fintype.card (rootsOfUnity n (𝓞 K)) = n := by
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 K, IsPrimitiveRoot g (torsionOrder K) := by
    rw [← card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot]
    simp_rw [rootsOfUnity_eq_torsion, torsionOrder]
  exact IsPrimitiveRoot.card_rootsOfUnity (hg.div_of_dvd hn)
