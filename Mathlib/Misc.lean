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
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.SpecificDegree

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

theorem ncard_primesOver_le_finrank' : (p.primesOver S).ncard ≤ Module.finrank R S := by
  have : Fintype (p.primesOver S) := Fintype.ofFinite (p.primesOver S)
  rw [← sum_ramification_inertia_eq_finrank p S, ← Set.fintypeCard_eq_ncard,
    Fintype.card_eq_sum_ones]
  exact Finset.sum_le_sum fun P _ ↦ one_le_mul (ramificationIdx_pos P.1 R) (inertiaDeg_pos P.1 R)

end Ideal

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

end QuadraticAlgebra
