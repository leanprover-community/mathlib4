module

public import Mathlib.NumberTheory.NumberField.QuadraticField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Ideal.Int

/-!
# Sandbox: splitting of primes in quadratic fields

Design in `plan_corps_quadratiques.md`, section "PR « dedekind » et PR « fact »".

Guiding idea: the fibre at `n` is itself a quadratic algebra, so the inert criterion comes from
`isField_iff_not_isSquare_discr` over `ZMod p`, with no `Polynomial` and no Kummer-Dedekind.

`QuadraticAlgebra.adjoin_omega_eq_top` is already in master.
-/

@[expose] public section

open Ideal

open scoped QuadraticAlgebra

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

open scoped DualNumber in
/-- Ramified at `2`: the fibre is the dual numbers over `ZMod 2`. -/
noncomputable def quotientTwoEquivDualNumberOfEven (hb : Even b) :
    (QuadraticAlgebra ℤ a b ⧸ span {(2 : QuadraticAlgebra ℤ a b)}) ≃+*
      DualNumber (ZMod 2) :=
  (quotientSpanEquivZMod a b 2).trans <| ((equivOfEq rfl hb.intCast_zmod_two).trans <|
    (changeGeneratorEquiv _ _ 1 ↑a (by simp) (by simp [CharTwo.two_eq_zero])).trans
      (algEquivDualNumber (ZMod 2))).toRingEquiv

/-- Split: the fibre is `ZMod p × ZMod p`. -/
noncomputable def quotientEquivProd (hp2 : p ≠ 2) {s : ZMod p}
    (hd : (discr a b : ZMod p) = s ^ 2) (hs : s ≠ 0) :
    (QuadraticAlgebra ℤ a b ⧸ span {(p : QuadraticAlgebra ℤ a b)}) ≃+* ZMod p × ZMod p :=
  haveI := ZMod.neZero_two_of_ne_two hp2
  (quotientSpanEquivZMod a b p).trans (algEquivProdOfDiscrSq hd hs).toRingEquiv

/-- Ramified: the fibre is the dual numbers over `ZMod p`. -/
noncomputable def quotientEquivDualNumber (hp2 : p ≠ 2)
    (hd : (discr a b : ZMod p) = 0) :
    (QuadraticAlgebra ℤ a b ⧸ span {(p : QuadraticAlgebra ℤ a b)}) ≃+* DualNumber (ZMod p) :=
  haveI := ZMod.neZero_two_of_ne_two hp2
  (quotientSpanEquivZMod a b p).trans (algEquivDualNumberOfDiscrZero hd).toRingEquiv

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

theorem Ideal.inertiaDegIn_eq_of_forall {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {p : Ideal A} {n : ℕ} [Nonempty (p.primesOver B)]
    (h : ∀ P : Ideal B, P.IsPrime → P.LiesOver p → P.inertiaDeg A = n) :
    Ideal.inertiaDegIn p B = n := by
  obtain ⟨⟨P, hP, hPp⟩⟩ := ‹Nonempty (p.primesOver B)›
  have hex : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hP, hPp⟩
  rw [Ideal.inertiaDegIn, dite_eq_left hex]
  exact h _ hex.choose_spec.1 hex.choose_spec.2

theorem Ideal.ramificationIdxIn_eq_of_forall {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {p : Ideal A} {n : ℕ} [Nonempty (p.primesOver B)]
    (h : ∀ P : Ideal B, P.IsPrime → P.LiesOver p → P.ramificationIdx A = n) :
    Ideal.ramificationIdxIn p B = n := by
  obtain ⟨⟨P, hP, hPp⟩⟩ := ‹Nonempty (p.primesOver B)›
  have hex : ∃ P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hP, hPp⟩
  rw [Ideal.ramificationIdxIn, dite_eq_left hex]
  exact h _ hex.choose_spec.1 hex.choose_spec.2

namespace NumberField.QuadraticField

open scoped QuadraticAlgebra

variable (K : Type*) [Field K] [CharZero K] [Algebra.IsQuadraticExtension ℚ K]
  (p : ℕ) [hp : Fact p.Prime]

local notation3 "𝒑" => (span {(p : ℤ)})

/-! Following `Cyclotomic/Ideal.lean`: one hypothesis per case, and the three invariants
`g`, `e`, `f` read off as equalities, rather than one `Iff` per invariant. -/

/-! The case `p = 2` first, since it is the one the discriminant criterion below does not cover:
the behaviour is read off `discr K` modulo `8`, inert when `discr K % 8 = 5`, split when
`discr K % 8 = 1`, and ramified when `discr K` is even — that last case being the `ramified`
section below, which is uniform in `p`. -/

section two

variable {K}

/-- `2` is inert exactly when `discr K % 8 = 5`: `f = 2` at every prime above `2`. -/
theorem inertiaDeg_two_of_discr_emod_eight (h : NumberField.discr K % 8 = 5)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.inertiaDeg ℤ = 2 :=
  sorry

/-- `2` is inert exactly when `discr K % 8 = 5`: `f = 2`. -/
theorem inertiaDegIn_two_of_discr_emod_eight (h : NumberField.discr K % 8 = 5) :
    Ideal.inertiaDegIn (span {(2 : ℤ)}) (𝓞 K) = 2 :=
  -- the `Nonempty (primesOver …)` instance is stated for `span {(p : ℤ)}`, not the literal `2`
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

/-- `2` splits exactly when `discr K % 8 = 1`: `f = 1`. -/
theorem inertiaDegIn_two_of_discr_emod_eight_one (h : NumberField.discr K % 8 = 1) :
    Ideal.inertiaDegIn (span {(2 : ℤ)}) (𝓞 K) = 1 :=
  -- the `Nonempty (primesOver …)` instance is stated for `span {(p : ℤ)}`, not the literal `2`
  sorry

end two

section ramified

variable {K p} (hd : (p : ℤ) ∣ NumberField.discr K)

include hd

/-- If `p` divides the discriminant, it is ramified: `e = 2` at every prime above `p`. -/
theorem ramificationIdx_of_dvd_discr (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 2 :=
  sorry

/-- If `p` divides the discriminant, it is ramified: `e = 2`. Uniform in `p`, `p = 2` included. -/
theorem ramificationIdxIn_of_dvd_discr : Ideal.ramificationIdxIn 𝒑 (𝓞 K) = 2 :=
  Ideal.ramificationIdxIn_eq_of_forall
    fun P hP hPp ↦ by
      have := hP
      have := hPp
      exact ramificationIdx_of_dvd_discr hd P

/-- If `p` divides the discriminant, it is ramified: `f = 1` at every prime above `p`. -/
theorem inertiaDeg_of_dvd_discr (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 1 :=
  sorry

/-- If `p` divides the discriminant, it is ramified: `f = 1`. -/
theorem inertiaDegIn_of_dvd_discr : Ideal.inertiaDegIn 𝒑 (𝓞 K) = 1 :=
  Ideal.inertiaDegIn_eq_of_forall
    fun P hP hPp ↦ by
      have := hP
      have := hPp
      exact inertiaDeg_of_dvd_discr hd P

/-- If `p` divides the discriminant, it is ramified: `g = 1`. -/
theorem ncard_primesOver_of_dvd_discr : (𝒑.primesOver (𝓞 K)).ncard = 1 :=
  sorry

end ramified

section inert

variable {K p} (hp2 : p ≠ 2) (hd : ¬ IsSquare ((NumberField.discr K : ZMod p)))

include hp2 hd

/-- If the discriminant is not a square mod `p`, then `p` is inert: `f = 2` at every prime
above `p`. -/
theorem inertiaDeg_of_not_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 2 :=
  sorry

/-- If the discriminant is not a square mod `p`, then `p` is inert: `f = 2`. -/
theorem inertiaDegIn_of_not_isSquare : Ideal.inertiaDegIn 𝒑 (𝓞 K) = 2 :=
  Ideal.inertiaDegIn_eq_of_forall
    fun P hP hPp ↦ by
      have := hP
      have := hPp
      exact inertiaDeg_of_not_isSquare hp2 hd P

/-- If the discriminant is not a square mod `p`, then `p` is inert: `e = 1` at every prime
above `p`. -/
theorem ramificationIdx_of_not_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 1 :=
  sorry

/-- If the discriminant is not a square mod `p`, then `p` is inert: `e = 1`. -/
theorem ramificationIdxIn_of_not_isSquare : Ideal.ramificationIdxIn 𝒑 (𝓞 K) = 1 :=
  Ideal.ramificationIdxIn_eq_of_forall
    fun P hP hPp ↦ by
      have := hP
      have := hPp
      exact ramificationIdx_of_not_isSquare hp2 hd P

/-- If the discriminant is not a square mod `p`, then `p` is inert: `g = 1`. -/
theorem ncard_primesOver_of_not_isSquare : (𝒑.primesOver (𝓞 K)).ncard = 1 :=
  sorry

end inert

section split

variable {K p} (hp2 : p ≠ 2) (hnd : ¬ (p : ℤ) ∣ NumberField.discr K)
  (hd : IsSquare ((NumberField.discr K : ZMod p)))

include hp2 hnd hd

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `g = 2`. -/
theorem ncard_primesOver_of_isSquare : (𝒑.primesOver (𝓞 K)).ncard = 2 :=
  sorry

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `e = 1` at every prime
above `p`. -/
theorem ramificationIdx_of_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.ramificationIdx ℤ = 1 :=
  sorry

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `e = 1`. -/
theorem ramificationIdxIn_of_isSquare : Ideal.ramificationIdxIn 𝒑 (𝓞 K) = 1 :=
  Ideal.ramificationIdxIn_eq_of_forall
    fun P hP hPp ↦ by
      have := hP
      have := hPp
      exact ramificationIdx_of_isSquare hp2 hnd hd P

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `f = 1` at every prime
above `p`. -/
theorem inertiaDeg_of_isSquare (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver 𝒑] :
    P.inertiaDeg ℤ = 1 :=
  sorry

/-- If the discriminant is a nonzero square mod `p`, then `p` splits: `f = 1`. -/
theorem inertiaDegIn_of_isSquare : Ideal.inertiaDegIn 𝒑 (𝓞 K) = 1 :=
  Ideal.inertiaDegIn_eq_of_forall
    fun P hP hPp ↦ by
      have := hP
      have := hPp
      exact inertiaDeg_of_isSquare hp2 hnd hd P

end split


end NumberField.QuadraticField

/-! ### Pure arithmetic, for `FundamentalDiscriminant.lean` -/

theorem Int.IsFundamentalDiscr.emod_eight {D : ℤ} (h : Int.IsFundamentalDiscr D) :
    D % 8 = 0 ∨ D % 8 = 1 ∨ D % 8 = 4 ∨ D % 8 = 5 :=
  sorry
