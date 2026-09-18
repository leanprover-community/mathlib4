module

public import Mathlib.NumberTheory.NumberField.QuadraticField.Basic
public import Mathlib.Algebra.QuadraticAlgebra.Int
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Sandbox: splitting of primes in quadratic fields

Design in `plan_corps_quadratiques.md`, section "PR « dedekind » et PR « fact »".

Guiding idea: the fibre at `n` is itself a quadratic algebra, so the inert criterion comes from
`isField_iff_not_isSquare_discr` over `ZMod p`, with no `Polynomial` and no Kummer-Dedekind.

`QuadraticAlgebra.adjoin_omega_eq_top` is already in master.

TODO: the namespaces here are inconsistent, some declarations are inside a `namespace` block,
others carry the prefix in their name, and a few sit in no namespace at all. Decide on a
convention and apply it throughout before splitting this file into PRs.
-/

@[expose] public section

open Ideal

open scoped QuadraticAlgebra

/-! ### A prime divides the discriminant exactly when it ramifies -/

-- TODO: for `Mathlib/NumberTheory/NumberField/Discriminant/Different.lean`, next to
-- `not_dvd_discr_iff_forall_liesOver`, of which this is the contrapositive in terms of `e`.
open scoped NumberField Ideal in
/-- A prime divides the discriminant exactly when some prime above it is ramified. -/
theorem NumberField.dvd_discr_iff_exists_two_le_ramificationIdx (K 𝒪 : Type*) [Field K]
    [NumberField K] [CommRing 𝒪] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] [IsDedekindDomain 𝒪]
    [CharZero 𝒪] [Module.Finite ℤ 𝒪] [IsIntegralClosure 𝒪 ℤ K] {p : ℤ} (hp : Prime p) :
    p ∣ NumberField.discr K ↔
      ∃ P : Ideal 𝒪, P.IsMaximal ∧ P.LiesOver (span {p}) ∧ 2 ≤ P.ramificationIdx ℤ := by
  rw [← not_iff_not, NumberField.not_dvd_discr_iff_forall_liesOver K 𝒪 hp]
  simp only [not_exists, not_and, not_le, Order.lt_two_iff]
  exact forall₃_congr fun P _ _ ↦ by grind [ramificationIdx_eq_one_iff, ramificationIdx_pos]

/-! ### Bounding `e`, `f` and `g` by the rank

`Ideal.ramificationIdx_le_finrank`, `Ideal.inertiaDeg_le_finrank` and
`Ideal.card_primesOverFinset_le_finrank` are deprecated in favour of
`Mathlib/RingTheory/RamificationInertia/Basic.lean`, which however has no replacement for them.
All three follow from `Ideal.sum_ramification_inertia_eq_finrank` as the deprecated ones follow
from `Ideal.sum_ramification_inertia`.
-/

namespace Ideal

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsDomain R] [Module.Finite R S] [Module.Flat R S] [Finite (p.primesOver S)]

theorem inertiaDeg_le_finrank' (P : p.primesOver S) :
    P.1.inertiaDeg R ≤ Module.finrank R S := by
  have : Fintype (p.primesOver S) := Fintype.ofFinite (p.primesOver S)
  rw [← sum_ramification_inertia_eq_finrank p S, ← Finset.add_sum_erase _ _ (Finset.mem_univ P)]
  exact le_trans (Nat.le_mul_of_pos_left _ (ramificationIdx_pos P.1 R)) (Nat.le_add_right _ _)

theorem ramificationIdx_le_finrank' (P : p.primesOver S) :
    P.1.ramificationIdx R ≤ Module.finrank R S := by
  have : Fintype (p.primesOver S) := Fintype.ofFinite (p.primesOver S)
  rw [← sum_ramification_inertia_eq_finrank p S, ← Finset.add_sum_erase _ _ (Finset.mem_univ P)]
  exact le_trans (Nat.le_mul_of_pos_right _ (inertiaDeg_pos P.1 R)) (Nat.le_add_right _ _)

/-- The number of primes above `p` is at most the rank. -/
theorem ncard_primesOver_le_finrank' : (p.primesOver S).ncard ≤ Module.finrank R S := by
  have : Fintype (p.primesOver S) := Fintype.ofFinite (p.primesOver S)
  rw [← sum_ramification_inertia_eq_finrank p S, ← Set.fintypeCard_eq_ncard,
    Fintype.card_eq_sum_ones]
  exact Finset.sum_le_sum fun P _ ↦ one_le_mul (ramificationIdx_pos P.1 R) (inertiaDeg_pos P.1 R)

end Ideal

/-! ### Transfer of `IsDedekindDomain` along a ring isomorphism

Mathlib has the transfer for each of the four constituents, but not for the conjunction.
-/

-- TODO: for `Mathlib/RingTheory/DedekindDomain/Basic.lean`, next to
-- `Ring.DimensionLEOne.of_ringEquiv`. An `IsDedekindRing` version belongs there too.
/-- A ring isomorphic to a Dedekind domain is a Dedekind domain. -/
theorem IsDedekindDomain.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S]
    (e : R ≃+* S) : IsDedekindDomain R := by
  have : IsDomain R := e.toMulEquiv.isDomain S
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv S e.symm
  have : Ring.DimensionLEOne R := .of_ringEquiv e
  have : IsIntegrallyClosed R := .of_equiv e.symm
  have : IsDedekindRing R := ⟨⟩
  exact ⟨⟩

/-! ### Base change for `Module.length`

`Mathlib/RingTheory/Length.lean` has `LinearEquiv.length_eq` over one ring and
`Module.length_eq_of_surjective` for one module over two rings, but nothing carrying a length
along a ring isomorphism.
-/

-- TODO: for `Mathlib/RingTheory/Length.lean`, replacing `LinearEquiv.length_eq`, of which this
-- is the semilinear generalisation, with the same proof.
theorem LinearEquiv.length_eq' {A B M N : Type*} [Ring A] [Ring B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] {σ : A →+* B} {σ' : B →+* A}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (e : M ≃ₛₗ[σ] N) :
    Module.length A M = Module.length B N := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]

-- TODO: for `Mathlib/RingTheory/Length.lean`, modelled on `Algebra.finrank_eq_of_equiv_equiv`.
/-- If `M / A` and `M' / A'` are algebras, `i : A ≃+* A'` and `j : M ≃+* M'` are ring isomorphisms
such that `A → A' → M'` and `A → M → M'` commute, then the lengths of `M / A` and `M' / A'`
agree. -/
theorem Module.length_eq_of_equiv_equiv {A M A' M' : Type*} [CommRing A] [CommRing M] [Algebra A M]
    [CommRing A'] [CommRing M'] [Algebra A' M'] (i : A ≃+* A') (j : M ≃+* M')
    (hc : (algebraMap A' M').comp i.toRingHom = j.toRingHom.comp (algebraMap A M)) :
    Module.length A M = Module.length A' M' := by
  have := RingHomInvPair.of_ringEquiv i
  have := RingHomInvPair.symm (i : A →+* A') (i.symm : A' →+* A)
  refine LinearEquiv.length_eq' (σ := (i : A →+* A')) (σ' := (i.symm : A' →+* A))
    { j with map_smul' a x := ?_ }
  have h : algebraMap A' M' (i a) = j (algebraMap A M a) := RingHom.congr_fun hc a
  change j (a • x) = i a • j x
  rw [Algebra.smul_def, map_mul, Algebra.smul_def, h]

/-! ### Transfer of `inertiaDeg` and `ramificationIdx` along an algebra isomorphism

The primed versions of these exist (`Ideal.inertiaDeg'_comap_eq` and friends) but are deprecated,
and the unprimed definitions have no such transfer lemma yet.
-/

namespace Ideal

section

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_isPrime_iff {I : Ideal R} (e : R ≃+* S) : (I.map e).IsPrime ↔ I.IsPrime := by
  refine ⟨fun h ↦ ?_, fun _ ↦ map_isPrime_of_equiv e⟩
  rw [← map_comap_eq_self_of_equiv e.symm I, comap_symm]
  exact map_isPrime_of_equiv _

theorem comap_isPrime_iff {I : Ideal S} (e : R ≃+* S) : (I.comap e).IsPrime ↔ I.IsPrime := by
  rw [← map_isPrime_iff e, map_comap_eq_self_of_equiv]

end

variable {R S S₁ : Type*} [CommRing R] [CommRing S] [CommRing S₁] [Algebra R S] [Algebra R S₁]

theorem inertiaDeg_comap_eq (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    (P.comap e).inertiaDeg R = P.inertiaDeg R := by
  by_cases hP : P.IsPrime
  · let := Localization.AtPrime.algebraOfLiesOver (under R P) P
    let := Localization.AtPrime.algebraOfLiesOver (under R P) (comap e P)
    rw [inertiaDeg_eq (P.under R) (P.comap e), inertiaDeg_eq (P.under R) P]
    exact (residueFieldAlgEquiv' (P.under R) (P.comap e) P e rfl).toLinearEquiv.finrank_eq
  · rw [inertiaDeg_of_not_isPrime _ _ hP, inertiaDeg_of_not_isPrime _ _]
    exact (comap_isPrime_iff e.toRingEquiv).not.mpr hP

theorem inertiaDeg_map_eq (e : S ≃ₐ[R] S₁) (P : Ideal S) :
    (P.map e).inertiaDeg R = P.inertiaDeg R := by
  rw [← inertiaDeg_comap_eq e, comap_map_of_bijective _ e.bijective]

theorem ramificationIdx_comap_eq' (e : S ≃ₐ[R] S₁) (P : Ideal S₁) :
    (P.comap e).ramificationIdx R = P.ramificationIdx R := by
  by_cases hP : P.IsPrime
  · let := Localization.AtPrime.algebraOfLiesOver (under R P) P
    let := Localization.AtPrime.algebraOfLiesOver (under R P) (comap e P)
    let φ := Localization.localRingEquiv (P.comap e) P e rfl
    rw [ramificationIdx_eq (P.under R) (P.comap e), ramificationIdx_eq (P.under R) P]
    have : algebraMap R (Localization.AtPrime P) =
        φ.toRingHom.comp (algebraMap R (Localization.AtPrime (comap e P))) := by
      ext x
      simp [φ, Localization.localRingEquiv_apply (P.comap e) P e rfl,
        IsScalarTower.algebraMap_apply R S (Localization.AtPrime (P.comap e)),
        ← IsScalarTower.algebraMap_apply R S₁]
    congr
    refine Module.length_eq_of_equiv_equiv φ (Ideal.quotientEquiv _ _ φ ?_) rfl
    simp [map_map, this]
  · rw [ramificationIdx_of_not_isPrime _ _ hP, ramificationIdx_of_not_isPrime _ _]
    exact (comap_isPrime_iff e.toRingEquiv).not.mpr hP

theorem ramificationIdx_map_eq' (e : S ≃ₐ[R] S₁) (P : Ideal S) :
    (P.map e).ramificationIdx R = P.ramificationIdx R := by
  rw [← ramificationIdx_comap_eq' e, comap_map_of_bijective _ e.bijective]

end Ideal

-- /-- The coercion `R → R ⧸ I` is the quotient map. -/
-- @[simp]
-- theorem Ideal.Quotient.mk_eq_coe {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
--     Ideal.Quotient.mk I x = (x : R ⧸ I) :=
--   rfl

-- /-- The applied form of `Ideal.Quotient.algebraMap_eq`, which is stated at the level of the
-- functions and so cannot be rewritten with when the map occurs in a dependent position. -/
-- @[simp]
-- theorem Ideal.Quotient.algebraMap_apply {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
--     algebraMap R (R ⧸ I) x = Ideal.Quotient.mk I x :=
--   rfl

-- TODO: for `Mathlib/RingTheory/IntegralDomain.lean`, next to `Finite.isField_of_domain`.
/-- A finite commutative ring is a field exactly when it is a domain. -/
theorem Finite.isField_iff_isDomain (R : Type*) [CommRing R] [Finite R] :
    IsField R ↔ IsDomain R :=
  ⟨fun h ↦ letI := h.toField; inferInstance, fun _ ↦ Finite.isField_of_domain R⟩

/-- An ideal with finite quotient is prime exactly when it is maximal. -/
theorem Ideal.isPrime_iff_isMaximal_of_finite_quotient {R : Type*} [CommRing R] (I : Ideal R)
    [Finite (R ⧸ I)] : I.IsPrime ↔ I.IsMaximal := by
  rw [Quotient.maximal_ideal_iff_isField_quotient, ← Quotient.isDomain_iff_prime,
    Finite.isField_iff_isDomain]

-- TODO: for `Mathlib/Algebra/QuadraticAlgebra/Defs.lean`, next to the `Subsingleton` and
-- `Nontrivial` instances, which come from `equivProd` in the same way.
instance {R : Type*} {a b : R} [Finite R] : Finite (QuadraticAlgebra R a b) :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd a b).symm

-- TODO: for `Mathlib/Data/ZMod/Basic.lean`, next to `ZMod.ringChar_zmod_n`.
/-- `2` is nonzero in `ZMod n` unless `n = 2` (or `n = 1`, where the ring is trivial). -/
theorem ZMod.neZero_two_of_ne_two {n : ℕ} [Nontrivial (ZMod n)] (hn : n ≠ 2) :
    NeZero (2 : ZMod n) :=
  ⟨Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])⟩

/-! ### A characteristic-free field criterion, for `Basic.lean`

Generalises `not_isField_of_isSquare_discr` and `isField_iff_not_isSquare_discr`, which take the
root through the discriminant and so assume `[NeZero (2 : K)]`.
-/

namespace QuadraticAlgebra

/-- A root of `X ^ 2 - b * X - a` in `K` gives a zero divisor, so `QuadraticAlgebra K a b` is
not a field. -/
theorem not_isField_of_exists_sq_eq {K : Type*} [Field K] {a b : K}
    (h : ∃ r : K, r ^ 2 = a + b * r) : ¬ IsField (QuadraticAlgebra K a b) := fun hfield ↦ by
  obtain ⟨r, hr⟩ := h
  let := hfield.toField
  have : (⟨r, -1⟩ : QuadraticAlgebra K a b) * ⟨b - r, -1⟩ = 0 := by ext <;> simp <;> grind
  rcases mul_eq_zero.mp this with h | h <;> simp [QuadraticAlgebra.ext_iff] at h

-- TODO: move next to the `Field` instance in `Basic.lean` (`Basic.lean:595`), of which this is the
-- `Fact`-free restatement. The instance has to stay primitive: rebuilding it from this lemma
-- through `IsField.toField` would choose inverses classically and clash with the `Inv` and `Div`
-- instances that define `z⁻¹ = (norm z)⁻¹ • star z`.
/-- If `X ^ 2 - b * X - a` has no root in `K`, then `QuadraticAlgebra K a b` is a field. -/
theorem isField_of_forall_sq_ne {K : Type*} [Field K] {a b : K}
    (h : ∀ r : K, r ^ 2 ≠ a + b * r) : IsField (QuadraticAlgebra K a b) :=
  letI : Fact (∀ r : K, r ^ 2 ≠ a + b * r) := ⟨h⟩
  Field.toIsField _

/-- `QuadraticAlgebra K a b` is a field exactly when `X ^ 2 - b * X - a` has no root in `K`. -/
theorem isField_iff_forall_sq_ne {K : Type*} [Field K] {a b : K} :
    IsField (QuadraticAlgebra K a b) ↔ ∀ r : K, r ^ 2 ≠ a + b * r :=
  ⟨fun hf r hr ↦ not_isField_of_exists_sq_eq ⟨r, hr⟩ hf, isField_of_forall_sq_ne⟩

-- TODO: for `Basic.lean`, next to `algEquivDualNumber`: the split counterpart, valid over any
-- commutative ring. `algEquivProdOfDiscrSq` should be re-derived from it by a change of generator.
/-- If `ω ^ 2 = u * ω` for a unit `u`, then `u⁻¹ • ω` is a nontrivial idempotent and
`QuadraticAlgebra R 0 u` splits as `R × R`. -/
@[simps]
noncomputable def algEquivProdOfIsUnit (R : Type*) [CommRing R] {u : R} (hu : IsUnit u) :
    QuadraticAlgebra R 0 u ≃ₐ[R] R × R where
  toFun z := (z.re, z.re + u * z.im)
  invFun p := ⟨p.1, ((hu.unit⁻¹ : Rˣ) : R) * (p.2 - p.1)⟩
  left_inv _ := by ext <;> simp; ring_nf ; simp
  right_inv _ := by ext <;> simp; ring_nf; simp [mul_assoc, hu.mul_val_inv]
  map_mul' _ _ := by ext <;> simp; ring
  map_add' _ _ := by ext <;> simp; ring
  commutes' _ := by ext <;> simp

end QuadraticAlgebra

/-! ### A general gap: adjoining over a base that surjects

Nothing to do with quadratic algebras. If `algebraMap R S` is surjective then the `R`-scalars
already exhaust the `S`-scalars, so adjoining a set over `R` and over `S` gives the same
subalgebra. This is what `R[ω] = ⊤` really needs, and mathlib does not seem to have it.
-/

section adjoin

variable (R : Type*) {S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
  [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

theorem adjoin_eq_restrictScalars_adjoin_of_surjective
    (h : Function.Surjective (algebraMap R S)) (s : Set A) :
    Algebra.adjoin R s = (Algebra.adjoin S s).restrictScalars R := by
  rw [Algebra.Subalgebra.restrictScalars_adjoin, right_eq_sup]
  rintro _ ⟨x, rfl⟩
  obtain ⟨r, rfl⟩ := h x
  simp [← IsScalarTower.algebraMap_apply]

end adjoin

namespace QuadraticAlgebra

variable {a b : ℤ} {p : ℕ} [Fact p.Prime]

-- TODO: for `Mathlib/Algebra/QuadraticAlgebra/Int.lean`, to replace `discr_intCast`, which is
-- this for `R = ℚ`; its eight call sites should then use this one, and the prime can go.
/-- The discriminant commutes with the coercion `ℤ → R`. -/
@[simp, norm_cast]
theorem discr_intCast' {R : Type*} [CommRing R] (a b : ℤ) :
    discr (a : R) (b : R) = ((discr a b : ℤ) : R) := by
  simpa using discr_algebraMap (S := R) a b

-- /-- An element vanishes exactly when both its coordinates do. -/
-- theorem eq_zero_iff {R : Type*} [CommRing R] {a b : R} (x : QuadraticAlgebra R a b) :
--     x = 0 ↔ x.re = 0 ∧ x.im = 0 := by
--   simp [QuadraticAlgebra.ext_iff]

theorem mem_map_algebraMap_iff {R : Type*} [CommRing R] {a b : R} (I : Ideal R)
    (x : QuadraticAlgebra R a b) :
    x ∈ I.map (algebraMap R (QuadraticAlgebra R a b)) ↔ x.re ∈ I ∧ x.im ∈ I := by
  refine ⟨fun hx ↦ ?_, fun ⟨hr, hi⟩ ↦ ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        simpa using hr
    | zero => simp
    | add x y _ _ hx hy => exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | smul s x _ hx =>
        refine ⟨?_, ?_⟩
        · simpa using add_mem (mul_mem_left _ _ hx.1) (mul_mem_left _ _ hx.2)
        · simpa using add_mem (add_mem (mul_mem_left _ _ hx.2) (mul_mem_left _ _ hx.1))
            (mul_mem_left _ _ hx.2)
  · rw [← re_smul_add_im_smul x, ← Algebra.algebraMap_eq_smul_one, Algebra.smul_def]
    exact add_mem (mem_map_of_mem _ hr) <| mul_mem_right _ _ (mem_map_of_mem _ hi)

/-! ### Base change along a ring equivalence, and quotients

Names provisional.
-/

section base

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring equivalence of the base carries a quadratic algebra to a quadratic algebra. -/
@[simps]
def baseChangeEquiv (a b : R) (e : R ≃+* S) :
    QuadraticAlgebra R a b ≃+* QuadraticAlgebra S (e a) (e b) where
  toFun z := ⟨e z.re, e z.im⟩
  invFun z := ⟨e.symm z.re, e.symm z.im⟩
  left_inv _ := by ext <;> simp
  right_inv _ := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
  map_add' _ _ := by ext <;> simp

@[simp]
theorem baseChangeEquiv_omega (a b : R) (e : R ≃+* S) :
    baseChangeEquiv a b e ω = ω := by
  ext <;> simp

@[simp]
theorem baseChangeEquiv_smul_one_add_smul_omega (a b : R) (e : R ≃+* S) (x y : R) :
    baseChangeEquiv a b e (x • 1 + y • ω) = e x • 1 + e y • ω := by
  ext <;> simp

end base

section quotientMap

variable {R : Type*} [CommRing R] (a b : R) (I : Ideal R)

@[simps!]
def quotientMap :
    QuadraticAlgebra R a b →ₐ[R] QuadraticAlgebra (R ⧸ I) a b :=
  lift ⟨ω, omega_mul_omega_eq_add⟩

@[simp]
theorem quotientMap_omega : quotientMap a b I ω = ω := by
  simp [quotientMap]

@[simp]
theorem quotientMap_smul_one_add_smul_omega (x y : R) :
    quotientMap a b I (x • 1 + y • ω) = x • 1 + y • ω := by
  simp [quotientMap]

theorem quotientMap_surjective :
    Function.Surjective (quotientMap a b I) := by
  refine (lift_surjective_iff omega_mul_omega_eq_add).mpr ?_
  rw [adjoin_eq_restrictScalars_adjoin_of_surjective R (Ideal.Quotient.mk_surjective (I := I)),
    adjoin_omega_eq_top, Subalgebra.restrictScalars_top]

theorem quotientMap_ker :
    RingHom.ker (quotientMap a b I) = Ideal.map (algebraMap R (QuadraticAlgebra R a b)) I := by
  ext x
  rw [RingHom.mem_ker, mem_map_algebraMap_iff, QuadraticAlgebra.ext_iff]
  simp [← Algebra.algebraMap_eq_smul_one, Quotient.eq_zero_iff_mem]

/-- Quotienting a quadratic algebra by an ideal of the base gives the quadratic algebra over
the quotient base. -/
noncomputable def quotientMapEquiv :
    (QuadraticAlgebra R a b ⧸ I.map (algebraMap R (QuadraticAlgebra R a b))) ≃ₐ[R]
      QuadraticAlgebra (R ⧸ I) (algebraMap R (R ⧸ I) a) (algebraMap R (R ⧸ I) b) :=
  (Ideal.quotientEquivAlgOfEq R (quotientMap_ker a b I).symm).trans <|
    Ideal.quotientKerAlgEquivOfSurjective (quotientMap_surjective a b I)

@[simp]
theorem quotientMapEquiv_mk_re (x : QuadraticAlgebra R a b) :
    (quotientMapEquiv a b I (Ideal.Quotient.mk _ x)).re = Ideal.Quotient.mk I x.re := by
  simp [quotientMapEquiv, ← Algebra.algebraMap_eq_smul_one]

@[simp]
theorem quotientMapEquiv_mk_im (x : QuadraticAlgebra R a b) :
    (quotientMapEquiv a b I (Ideal.Quotient.mk _ x)).im = Ideal.Quotient.mk I x.im := by
  simp [quotientMapEquiv, ← Algebra.algebraMap_eq_smul_one]

@[simp]
theorem quotientMapEquiv_mk_omega :
    quotientMapEquiv a b I (Ideal.Quotient.mk _ ω) = ω := by
  simp [quotientMapEquiv]

@[simp]
theorem quotientMapEquiv_mk_smul_one_add_smul_omega (x y : R) :
    quotientMapEquiv a b I (Ideal.Quotient.mk _ (x • 1 + y • ω)) = x • 1 + y • ω := by
  simp [quotientMapEquiv]

end quotientMap

/-! ### PR "dedekind" -/

open NumberField QuadraticField

theorem conductor_omega_eq_top :
    conductor ℤ (ω : QuadraticAlgebra ℤ a b) = ⊤ :=
  conductor_eq_top_iff_adjoin_eq_top.mpr adjoin_omega_eq_top

theorem isDedekindDomain (h : Int.IsFundamentalDiscr (discr a b)) (h1 : discr a b ≠ 1) :
    IsDedekindDomain (QuadraticAlgebra ℤ a b) := by
  have hns : ¬ IsSquare (discr a b) := h.eq_one_of_isSquare.mt h1
  have : Fact (¬ IsSquare ((discr a b) : ℚ)) :=
    ⟨Int.discr_intCast ▸ Rat.isSquare_intCast_iff.not.mpr hns⟩
  have : IsDomain (QuadraticAlgebra ℤ a b) := Int.isDomain_iff.mpr hns
  have : IsIntegralClosure _ ℤ (QuadraticAlgebra ℚ a b) := Int.isIntegralClosure_iff.mpr h
  exact IsIntegralClosure.isDedekindDomain ℤ ℚ (QuadraticAlgebra ℚ a b) _

/-! ### The residual bridge -/

noncomputable def quotientSpanEquivZMod (a b : ℤ) (n : ℕ) :
    (QuadraticAlgebra ℤ a b ⧸ span {(n : QuadraticAlgebra ℤ a b)}) ≃+*
      QuadraticAlgebra (ZMod n) (a : ZMod n) (b : ZMod n) :=
  (Ideal.quotientEquivAlgOfEq ℤ (by simp [Ideal.map_span])).toRingEquiv.trans <|
    (quotientMapEquiv a b _).toRingEquiv.trans <|
      (baseChangeEquiv _ _ (Int.quotientSpanNatEquivZMod n)).trans
        (equivOfEq (by simp) (by simp)).toRingEquiv

@[simp]
theorem quotientSpanEquivZMod_mk_re (a b : ℤ) (n : ℕ) (x : QuadraticAlgebra ℤ a b) :
    (quotientSpanEquivZMod a b n (Ideal.Quotient.mk _ x)).re = x.re := by
  simp only [quotientSpanEquivZMod, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    quotientEquivAlgOfEq_mk, re_equivOfEq_apply, re_baseChangeEquiv_apply, quotientMapEquiv_mk_re,
    eq_intCast, map_intCast]

@[simp]
theorem quotientSpanEquivZMod_mk_im (a b : ℤ) (n : ℕ) (x : QuadraticAlgebra ℤ a b) :
    (quotientSpanEquivZMod a b n (Ideal.Quotient.mk _ x)).im = (x.im : ZMod n) := by
  simp only [quotientSpanEquivZMod, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    quotientEquivAlgOfEq_mk, im_equivOfEq_apply, im_baseChangeEquiv_apply, quotientMapEquiv_mk_im,
    eq_intCast, map_intCast]

@[simp]
theorem quotientSpanEquivZMod_mk_smul_one_add_smul_omega (a b : ℤ) (n : ℕ) (x y : ℤ) :
    quotientSpanEquivZMod a b n (Ideal.Quotient.mk _ (x • 1 + y • ω)) =
      (x : ZMod n) • 1 + (y : ZMod n) • ω := by
  ext <;> simp

@[simp]
theorem quotientSpanEquivZMod_mk_omega (a b : ℤ) (n : ℕ) :
    quotientSpanEquivZMod a b n (Ideal.Quotient.mk _ ω) = ω := by
  ext <;> simp

/-! ### The fibre at `p`

Supporting material for the `e`/`f` statements: the fibre `QuadraticAlgebra ℤ a b ⧸ (p)` is the
quadratic algebra `QuadraticAlgebra (ZMod p) ā b̄`, and over the field `ZMod p` the discriminant
classifies it into three cases (`isField_iff_not_isSquare_discr` and the `degenerate` section).
Each case reads off `g`, `e` and `f`.
-/

/-- Split at `2`: the fibre is `ZMod 2 × ZMod 2`. -/
noncomputable def quotientTwoEquivProd (ha : Even a) (hb : Odd b) :
    (QuadraticAlgebra ℤ a b ⧸ span {(2 : QuadraticAlgebra ℤ a b)}) ≃+* ZMod 2 × ZMod 2 :=
  (quotientSpanEquivZMod a b 2).trans <|
    ((equivOfEq ha.intCast_zmod_two hb.intCast_zmod_two).trans
      (algEquivProdOfIsUnit (ZMod 2) isUnit_one)).toRingEquiv

-- open scoped DualNumber in
-- /-- Ramified at `2`: the fibre is the dual numbers over `ZMod 2`. -/
-- noncomputable def quotientTwoEquivDualNumberOfEven (hb : Even b) :
--     (QuadraticAlgebra ℤ a b ⧸ span {(2 : QuadraticAlgebra ℤ a b)}) ≃+*
--       DualNumber (ZMod 2) :=
--   (quotientSpanEquivZMod a b 2).trans <| ((equivOfEq rfl hb.intCast_zmod_two).trans <|
--     (changeGeneratorEquiv _ _ 1 ↑a (by simp) (by simp [CharTwo.two_eq_zero])).trans
--       (algEquivDualNumber (ZMod 2))).toRingEquiv

/-- Split: the fibre is `ZMod p × ZMod p`. -/
noncomputable def quotientEquivProd (hp2 : p ≠ 2) {s : ZMod p}
    (hd : (discr a b : ZMod p) = s ^ 2) (hs : s ≠ 0) :
    (QuadraticAlgebra ℤ a b ⧸ span {(p : QuadraticAlgebra ℤ a b)}) ≃+* ZMod p × ZMod p :=
  haveI := ZMod.neZero_two_of_ne_two hp2
  (quotientSpanEquivZMod a b p).trans (algEquivProdOfDiscrSq hd hs).toRingEquiv

-- /-- Ramified: the fibre is the dual numbers over `ZMod p`. -/
-- noncomputable def quotientEquivDualNumber (hp2 : p ≠ 2)
--     (hd : (discr a b : ZMod p) = 0) :
--     (QuadraticAlgebra ℤ a b ⧸ span {(p : QuadraticAlgebra ℤ a b)}) ≃+* DualNumber (ZMod p) :=
--   haveI := ZMod.neZero_two_of_ne_two hp2
--   (quotientSpanEquivZMod a b p).trans (algEquivDualNumberOfDiscrZero hd).toRingEquiv

/-! ### What the `e`/`f` layer consumes

The product formula `g * e * f = 2` reduces the classification to two questions. Ramification is
already settled in mathlib, by `NumberField.not_dvd_discr_iff_isUnramifiedIn`, so all that is left
is to tell inert from split, that is, whether `span {p}` is prime.
-/

instance {n : ℕ} [NeZero n] :
    Finite (QuadraticAlgebra ℤ a b ⧸ span {(n : QuadraticAlgebra ℤ a b)}) :=
  Finite.of_equiv _ (quotientSpanEquivZMod a b n).symm.toEquiv

/-- The case `p = 2`: inert exactly when `a` and `b` are both odd. -/
theorem isPrime_span_two_iff :
    (span {(2 : QuadraticAlgebra ℤ a b)}).IsPrime ↔ Odd a ∧ Odd b := by
  rw [← Nat.cast_two, isPrime_iff_isMaximal_of_finite_quotient,
    Quotient.maximal_ideal_iff_isField_quotient,
    (quotientSpanEquivZMod a b _).toMulEquiv.isField_congr, isField_iff_forall_sq_ne,
    ← ZMod.intCast_eq_one_iff_odd, ← ZMod.intCast_eq_one_iff_odd]
  generalize (a : ZMod 2) = x, (b : ZMod 2) = y
  decide +revert

/-- The case `p = 2`: in the inert case, `span {2}` is the only prime above `2`. -/
theorem eq_span_two_of_liesOver (ha : Odd a) (hb : Odd b)
    {P : Ideal (QuadraticAlgebra ℤ a b)} (hP : P.IsPrime)
    (hPp : P.LiesOver (span {(2 : ℤ)})) :
    P = span {(2 : QuadraticAlgebra ℤ a b)} := by
  rw [show (2 : QuadraticAlgebra ℤ a b) = (2 : ℕ) by rfl]
  refine (Ideal.IsMaximal.eq_of_le ?_ hP.ne_top ?_).symm
  · rw [← isPrime_iff_isMaximal_of_finite_quotient, Nat.cast_two, isPrime_span_two_iff]
    exact ⟨ha, hb⟩
  · simpa [map_span] using map_le_of_le_comap ((liesOver_iff _ _).mp hPp).le

/-- `p` is inert exactly when the discriminant is not a square mod `p`. -/
theorem isPrime_span_iff (hp2 : p ≠ 2) :
    (span {(p : QuadraticAlgebra ℤ a b)}).IsPrime ↔ ¬ IsSquare ((discr a b : ZMod p)) := by
  have := ZMod.neZero_two_of_ne_two hp2
  rw [isPrime_iff_isMaximal_of_finite_quotient, Quotient.maximal_ideal_iff_isField_quotient,
    (quotientSpanEquivZMod a b _).toMulEquiv.isField_congr, isField_iff_not_isSquare_discr]

/-- In the inert case, `span {p}` is the only prime above `p`. -/
theorem eq_span_of_liesOver (hp2 : p ≠ 2) (hd : ¬ IsSquare ((discr a b : ZMod p)))
    {P : Ideal (QuadraticAlgebra ℤ a b)} (hP : P.IsPrime)
    (hPp : P.LiesOver (span {(p : ℤ)})) :
    P = span {(p : QuadraticAlgebra ℤ a b)} := by
  refine (Ideal.IsMaximal.eq_of_le ?_ hP.ne_top ?_).symm
  · rw [← isPrime_iff_isMaximal_of_finite_quotient]
    exact (isPrime_span_iff hp2).mpr hd
  · simpa [map_span] using map_le_of_le_comap ((liesOver_iff _ _).mp hPp).le

end QuadraticAlgebra

/-! ### PR "fact", abstract layer, in the `e`/`f` dialect

Modelled on `Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`: state everything in `𝓞 K`
with `primesOver`, `ramificationIdx` and `inertiaDeg`, rather than with explicit factorisations.
A quadratic field is Galois over `ℚ`, so the `…In` forms are available.
-/

-- TODO: for `Mathlib/NumberTheory/RamificationInertia/Galois.lean`, next to the definitions of
-- `ramificationIdxIn` and `inertiaDegIn`: the eliminators that turn a statement holding for every
-- prime above `p` into the `…In` form, so that the `Classical.choose` never has to be unfolded
-- by hand.

namespace NumberField.QuadraticField

open scoped QuadraticAlgebra

variable (K : Type*) [Field K] [CharZero K] [hKQ : Algebra.IsQuadraticExtension ℚ K]
  (p : ℕ) [hp : Fact p.Prime]

local notation3 "𝒑" => (span {(p : ℤ)})

/-! Following `Cyclotomic/Ideal.lean`: one hypothesis per case, and the three invariants
`g`, `e`, `f` read off as equalities, rather than one `Iff` per invariant. -/

/-- A chosen isomorphism between `𝓞 K` and the quadratic algebra of discriminant `discr K`. -/
noncomputable def algEquivRingOfIntegers :
    𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (discr K / 4) (discr K % 4) :=
  (nonempty_algEquiv_ringOfIntegers K).some

/-- The quadratic algebra modelling `𝓞 K` is a Dedekind domain. -/
instance isDedekindDomain_quadraticAlgebra :
    IsDedekindDomain (QuadraticAlgebra ℤ (discr K / 4) (discr K % 4)) :=
  .of_ringEquiv (algEquivRingOfIntegers K).symm.toRingEquiv


/-! The case `p = 2` first, since it is the one the discriminant criterion below does not cover:
the behaviour is read off `discr K` modulo `8`, inert when `discr K % 8 = 5`, split when
`discr K % 8 = 1`, and ramified when `discr K` is even — that last case being the `ramified`
section below, which is uniform in `p`. -/

section tools

variable {K}

/-- The fundamental identity `g * e * f = 2` for a quadratic field. -/
theorem ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg (P : Ideal (𝓞 K)) [P.IsPrime] :
    ((under ℤ P).primesOver (𝓞 K)).ncard * (P.ramificationIdx ℤ * P.inertiaDeg ℤ) = 2 := by
  rw [← ramificationIdxIn_eq_ramificationIdx (under ℤ P) P Gal(K/ℚ),
    ← inertiaDegIn_eq_inertiaDeg (under ℤ P) P Gal(K/ℚ),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn _ _ Gal(K/ℚ),
    IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two']

end tools
section two

variable {K}

/-- `2` is inert exactly when `discr K % 8 = 5`: `f = 2` at every prime above `2`. -/
theorem inertiaDeg_two_of_discr_emod_eight (h : NumberField.discr K % 8 = 5)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.inertiaDeg ℤ = 2 := by
  sorry

/-- `2` is inert exactly when `discr K % 8 = 5`: `g = 1`. -/
theorem ncard_primesOver_two_of_discr_emod_eight_five (h : NumberField.discr K % 8 = 5) :
    ((span {(2 : ℤ)}).primesOver (𝓞 K)).ncard = 1 :=
  sorry

/-- `2` splits exactly when `discr K % 8 = 1`: `g = 2`. -/
theorem ncard_primesOver_two_of_discr_emod_eight_one (h : NumberField.discr K % 8 = 1) :
    ((span {(2 : ℤ)}).primesOver (𝓞 K)).ncard = 2 :=
  sorry

/-- `2` splits exactly when `discr K % 8 = 1`: `f = 1` at every prime above `2`. -/
theorem inertiaDeg_two_of_discr_emod_eight_one (h : NumberField.discr K % 8 = 1)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.inertiaDeg ℤ = 1 :=
  sorry

end two

section ramified

variable {K p} (hd : (p : ℤ) ∣ NumberField.discr K)

include hd

/-- If `p` divides the discriminant, it is ramified: `e = 2` at every prime above `p`. -/
theorem ramificationIdx_of_dvd_discr (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 2 := by
  refine Nat.le_antisymm ?_ ?_
  · rw [← hKQ.finrank_eq_two, ← RingOfIntegers.rank K]
    exact ramificationIdx_le_finrank' 𝒑 (𝓞 K) ⟨P, ⟨hP₁, hP₂⟩⟩
  · obtain ⟨Q, _, _, _⟩ := (dvd_discr_iff_exists_two_le_ramificationIdx K (𝓞 K)
      (Nat.prime_iff_prime_int.mp hp.out)).mp hd
    rwa [ramificationIdx_eq_of_isGaloisGroup 𝒑 P Q Gal(K/ℚ)]

/-- If `p` divides the discriminant, it is ramified: `f = 1` at every prime above `p`. -/
theorem inertiaDeg_of_dvd_discr (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 1 := by
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [ramificationIdx_of_dvd_discr hd, mul_comm 2, ← mul_assoc, mul_eq_right₀ two_ne_zero] at h
  exact Nat.eq_one_of_mul_eq_one_left h

/-- If `p` divides the discriminant, it is ramified: `g = 1`. -/
theorem ncard_primesOver_of_dvd_discr : (𝒑.primesOver (𝓞 K)).ncard = 1 := by
  obtain ⟨P, _, _⟩ := exists_isPrime_liesOver_of_faithfullyFlat 𝒑 (B := 𝓞 K)
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [ramificationIdx_of_dvd_discr hd, mul_comm 2, ← mul_assoc, mul_eq_right₀ two_ne_zero,
    ← over_def P 𝒑] at h
  exact Nat.eq_one_of_mul_eq_one_right h

end ramified

section inert

variable {K p} (hp2 : p ≠ 2) (hd : ¬ IsSquare ((NumberField.discr K : ZMod p)))

include hp2 hd

/-- If the discriminant is not a square mod `p`, then `p` is inert: `f = 2` at every prime
above `p`. -/
theorem inertiaDeg_of_not_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 2 := by
  let f := algEquivRingOfIntegers K
  rw [← pow_right_inj₀ hp.out.pos hp.out.ne_one, ← inertiaDeg_map_eq f P, pow_inertiaDeg,
    QuadraticAlgebra.eq_span_of_liesOver (P := map f P) hp2 _ (map_isPrime_of_equiv f)
    (map_equiv_liesOver P 𝒑 f), absNorm_span_singleton, Algebra.norm_quadraticAlgebra_apply,
    QuadraticAlgebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast]
  rwa [QuadraticAlgebra.discr_intCast', (isFundamentalDiscr_discr K).discr_ediv_four_emod_four]

/-- If the discriminant is not a square mod `p`, then `p` is inert: `e = 1` at every prime
above `p`. -/
theorem ramificationIdx_of_not_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 1 := by
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [inertiaDeg_of_not_isSquare hp2 hd, ← mul_assoc, mul_eq_right₀ two_ne_zero] at h
  exact Nat.eq_one_of_mul_eq_one_left h

/-- If the discriminant is not a square mod `p`, then `p` is inert: `g = 1`. -/
theorem ncard_primesOver_of_not_isSquare : (𝒑.primesOver (𝓞 K)).ncard = 1 := by
  obtain ⟨P, _, _⟩ := exists_isPrime_liesOver_of_faithfullyFlat 𝒑 (B := 𝓞 K)
  have h := ncard_primesOver_mul_ramificationIdx_mul_inertiaDeg P
  rw [inertiaDeg_of_not_isSquare hp2 hd, ← mul_assoc, mul_eq_right₀ two_ne_zero,
    ← over_def P 𝒑] at h
  exact Nat.eq_one_of_mul_eq_one_right h

end inert

section split

variable {K p} (hp2 : p ≠ 2) (hnd : ¬ (p : ℤ) ∣ NumberField.discr K)
  (hd : IsSquare ((NumberField.discr K : ZMod p)))

include hp2 hnd hd

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `g = 2`. -/
theorem ncard_primesOver_of_isSquare : (𝒑.primesOver (𝓞 K)).ncard = 2 := by

  sorry

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `e = 1` at every prime
above `p`. -/
theorem ramificationIdx_of_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 1 :=
  sorry

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `f = 1` at every prime
above `p`. -/
theorem inertiaDeg_of_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 1 :=
  sorry

end split


end NumberField.QuadraticField
