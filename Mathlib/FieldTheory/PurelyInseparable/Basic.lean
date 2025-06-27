/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.SeparableClosure

/-!

# Basic results about purely inseparable extensions

This file contains basic definitions and results about purely inseparable extensions.

## Main definitions

- `IsPurelyInseparable`: typeclass for purely inseparable field extensions: an algebraic extension
  `E / F` is purely inseparable if and only if the minimal polynomial of every element of `E ∖ F`
  is not separable.

## Main results

- `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`,
  `IsPurelyInseparable.bijective_algebraMap_of_isSeparable`,
  `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`:
  if `E / F` is both purely inseparable and separable, then `algebraMap F E` is surjective
  (hence bijective). In particular, if an intermediate field of `E / F` is both purely inseparable
  and separable, then it is equal to `F`.

- `isPurelyInseparable_iff_pow_mem`: a field extension `E / F` of exponential characteristic `q` is
  purely inseparable if and only if for every element `x` of `E`, there exists a natural number `n`
  such that `x ^ (q ^ n)` is contained in `F`.

- `IsPurelyInseparable.trans`: if `E / F` and `K / E` are both purely inseparable extensions, then
  `K / F` is also purely inseparable.

- `isPurelyInseparable_iff_natSepDegree_eq_one`: `E / F` is purely inseparable if and only if for
  every element `x` of `E`, its minimal polynomial has separable degree one.

- `isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C`: a field extension `E / F` of exponential
  characteristic `q` is purely inseparable if and only if for every element `x` of `E`, the minimal
  polynomial of `x` over `F` is of form `X ^ (q ^ n) - y` for some natural number `n` and some
  element `y` of `F`.

- `isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow`: a field extension `E / F` of exponential
  characteristic `q` is purely inseparable if and only if for every element `x` of `E`, the minimal
  polynomial of `x` over `F` is of form `(X - x) ^ (q ^ n)` for some natural number `n`.

- `isPurelyInseparable_iff_finSepDegree_eq_one`: an extension is purely inseparable
  if and only if it has finite separable degree (`Field.finSepDegree`) one.

- `IsPurelyInseparable.normal`: a purely inseparable extension is normal.

- `separableClosure.isPurelyInseparable`: if `E / F` is algebraic, then `E` is purely inseparable
  over the separable closure of `F` in `E`.

- `separableClosure_le_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` contains
  the separable closure of `F` in `E` if and only if `E` is purely inseparable over it.

- `eq_separableClosure_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` is equal
  to the separable closure of `F` in `E` if and only if it is separable over `F`, and `E`
  is purely inseparable over it.

- `IsPurelyInseparable.injective_comp_algebraMap`: if `E / F` is purely inseparable, then for any
  reduced ring `L`, the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective.
  In particular, a purely inseparable field extension is an epimorphism in the category of fields.

- `IsPurelyInseparable.of_injective_comp_algebraMap`: if `L` is an algebraically closed field
  containing `E`, such that the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is
  injective, then `E / F` is purely inseparable. As a corollary, epimorphisms in the category of
  fields must be purely inseparable extensions.

- `Field.finSepDegree_eq`: if `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to
  `Field.sepDegree F E` as a natural number. This means that the cardinality of `Field.Emb F E`
  and the degree of `(separableClosure F E) / F` are both finite or infinite, and when they are
  finite, they coincide.

- `Field.finSepDegree_mul_finInsepDegree`: the finite separable degree multiply by the finite
  inseparable degree is equal to the (finite) field extension degree.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

open Module Polynomial IntermediateField Field

noncomputable section

universe u v w

section General

variable (F E : Type*) [CommRing F] [Ring E] [Algebra F E]
variable (K : Type*) [Ring K] [Algebra F K]

/-- Typeclass for purely inseparable field extensions: an algebraic extension `E / F` is purely
inseparable if and only if the minimal polynomial of every element of `E ∖ F` is not separable.

We define this for general (commutative) rings and only assume `F` and `E` are fields
if this is needed for a proof. -/
class IsPurelyInseparable : Prop where
  isIntegral : Algebra.IsIntegral F E
  inseparable' (x : E) : IsSeparable F x → x ∈ (algebraMap F E).range

attribute [instance] IsPurelyInseparable.isIntegral

variable {E} in
theorem IsPurelyInseparable.isIntegral' [IsPurelyInseparable F E] (x : E) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral _

theorem IsPurelyInseparable.isAlgebraic [Nontrivial F] [IsPurelyInseparable F E] :
    Algebra.IsAlgebraic F E := inferInstance

variable {E}

theorem IsPurelyInseparable.inseparable [IsPurelyInseparable F E] :
    ∀ x : E, IsSeparable F x → x ∈ (algebraMap F E).range :=
  IsPurelyInseparable.inseparable'

variable {F}

theorem isPurelyInseparable_iff : IsPurelyInseparable F E ↔ ∀ x : E,
    IsIntegral F x ∧ (IsSeparable F x → x ∈ (algebraMap F E).range) :=
  ⟨fun h x ↦ ⟨h.isIntegral' _ x, h.inseparable' x⟩, fun h ↦ ⟨⟨fun x ↦ (h x).1⟩, fun x ↦ (h x).2⟩⟩

variable {K}

/-- Transfer `IsPurelyInseparable` across an `AlgEquiv`. -/
theorem AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] E) [IsPurelyInseparable F K] :
    IsPurelyInseparable F E := by
  refine ⟨⟨fun _ ↦ by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral' F _⟩,
    fun x h ↦ ?_⟩
  rw [IsSeparable, ← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h

theorem AlgEquiv.isPurelyInseparable_iff (e : K ≃ₐ[F] E) :
    IsPurelyInseparable F K ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ e.isPurelyInseparable, fun _ ↦ e.symm.isPurelyInseparable⟩

/-- If `E / F` is an algebraic extension, `F` is separably closed,
then `E / F` is purely inseparable. -/
instance Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed
    {F : Type u} {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsSepClosed F] : IsPurelyInseparable F E :=
  ⟨inferInstance, fun x h ↦ minpoly.mem_range_of_degree_eq_one F x <|
    IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible
      (Algebra.IsIntegral.isIntegral _)) h⟩

variable (F E K)

/-- If `E / F` is both purely inseparable and separable, then `algebraMap F E` is surjective. -/
theorem IsPurelyInseparable.surjective_algebraMap_of_isSeparable
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Surjective (algebraMap F E) :=
  fun x ↦ IsPurelyInseparable.inseparable F x (Algebra.IsSeparable.isSeparable F x)

/-- If `E / F` is both purely inseparable and separable, then `algebraMap F E` is bijective. -/
theorem IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    [Nontrivial E] [NoZeroSMulDivisors F E]
    [IsPurelyInseparable F E] [Algebra.IsSeparable F E] : Function.Bijective (algebraMap F E) :=
  ⟨FaithfulSMul.algebraMap_injective F E, surjective_algebraMap_of_isSeparable F E⟩

variable {F E} in
/-- If a subalgebra of `E / F` is both purely inseparable and separable, then it is equal
to `F`. -/
theorem Subalgebra.eq_bot_of_isPurelyInseparable_of_isSeparable (L : Subalgebra F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (Subalgebra.val _) hy⟩

/-- If an intermediate field of `E / F` is both purely inseparable and separable, then it is equal
to `F`. -/
theorem IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] (L : IntermediateField F E)
    [IsPurelyInseparable F L] [Algebra.IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L E) hy⟩

/-- If `E / F` is purely inseparable, then the separable closure of `F` in `E` is
equal to `F`. -/
theorem separableClosure.eq_bot_of_isPurelyInseparable
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E] :
    separableClosure F E = ⊥ :=
  bot_unique fun x h ↦ IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)

/-- If `E / F` is an algebraic extension, then the separable closure of `F` in `E` is
equal to `F` if and only if `E / F` is purely inseparable. -/
theorem separableClosure.eq_bot_iff
    {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] :
    separableClosure F E = ⊥ ↔ IsPurelyInseparable F E :=
  ⟨fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, fun hs ↦ by
    simpa only [h] using mem_separableClosure_iff.2 hs⟩, fun _ ↦ eq_bot_of_isPurelyInseparable F E⟩

instance isPurelyInseparable_self : IsPurelyInseparable F F :=
  ⟨inferInstance, fun x _ ↦ ⟨x, rfl⟩⟩

section

variable (F : Type u) {E : Type v} [Field F] [Ring E] [IsDomain E] [Algebra F E]
variable (q : ℕ) [ExpChar F q] (x : E)

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, there exists a natural number `n` such that
`x ^ (q ^ n)` is contained in `F`. -/
@[stacks 09HE]
theorem isPurelyInseparable_iff_pow_mem :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [isPurelyInseparable_iff]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨g, h1, n, h2⟩ := (minpoly.irreducible (h x).1).hasSeparableContraction q
    exact ⟨n, (h _).2 <| h1.of_dvd <| minpoly.dvd F _ <| by
      simpa only [expand_aeval, minpoly.aeval] using congr_arg (aeval x) h2⟩
  have hdeg := (minpoly.natSepDegree_eq_one_iff_pow_mem q).2 (h x)
  have halg : IsIntegral F x := by_contra fun h' ↦ by
    simp only [minpoly.eq_zero h', natSepDegree_zero, zero_ne_one] at hdeg
  refine ⟨halg, fun hsep ↦ ?_⟩
  rwa [hsep.natSepDegree_eq_natDegree, minpoly.natDegree_eq_one_iff] at hdeg

theorem IsPurelyInseparable.pow_mem [IsPurelyInseparable F E] :
    ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range :=
  (isPurelyInseparable_iff_pow_mem F q).1 ‹_› x

end

end General

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section Field

/-- If `K / E / F` is a field extension tower such that `K / F` is purely inseparable,
then `E / F` is also purely inseparable. -/
theorem IsPurelyInseparable.tower_bot [Algebra E K] [IsScalarTower F E K]
    [IsPurelyInseparable F K] : IsPurelyInseparable F E := by
  refine ⟨⟨fun x ↦ (isIntegral' F (algebraMap E K x)).tower_bot_of_field⟩, fun x h ↦ ?_⟩
  rw [IsSeparable, ← minpoly.algebraMap_eq (algebraMap E K).injective] at h
  obtain ⟨y, h⟩ := inseparable F _ h
  exact ⟨y, (algebraMap E K).injective (h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm)⟩

/-- If `K / E / F` is a field extension tower such that `K / F` is purely inseparable,
then `K / E` is also purely inseparable. -/
theorem IsPurelyInseparable.tower_top [Algebra E K] [IsScalarTower F E K]
    [h : IsPurelyInseparable F K] : IsPurelyInseparable E K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h ⊢
  intro x
  obtain ⟨n, y, h⟩ := h x
  exact ⟨n, (algebraMap F E) y, h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm⟩

/-- If `E / F` and `K / E` are both purely inseparable extensions, then `K / F` is also
purely inseparable. -/
@[stacks 02JJ "See also 00GM"]
theorem IsPurelyInseparable.trans [Algebra E K] [IsScalarTower F E K]
    [h1 : IsPurelyInseparable F E] [h2 : IsPurelyInseparable E K] : IsPurelyInseparable F K := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  rw [isPurelyInseparable_iff_pow_mem _ q] at h1 h2 ⊢
  intro x
  obtain ⟨n, y, h2⟩ := h2 x
  obtain ⟨m, z, h1⟩ := h1 y
  refine ⟨n + m, z, ?_⟩
  rw [IsScalarTower.algebraMap_apply F E K, h1, map_pow, h2, ← pow_mul, ← pow_add]

namespace IntermediateField

variable (M : IntermediateField F K)

instance isPurelyInseparable_tower_bot [IsPurelyInseparable F K] : IsPurelyInseparable F M :=
  IsPurelyInseparable.tower_bot F M K

instance isPurelyInseparable_tower_top [IsPurelyInseparable F K] : IsPurelyInseparable M K :=
  IsPurelyInseparable.tower_top F M K

end IntermediateField

variable {E}

/-- A field extension `E / F` is purely inseparable if and only if for every element `x` of `E`,
its minimal polynomial has separable degree one. -/
theorem isPurelyInseparable_iff_natSepDegree_eq_one :
    IsPurelyInseparable F E ↔ ∀ x : E, (minpoly F x).natSepDegree = 1 := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  simp_rw [isPurelyInseparable_iff_pow_mem F q, minpoly.natSepDegree_eq_one_iff_pow_mem q]

theorem IsPurelyInseparable.natSepDegree_eq_one [IsPurelyInseparable F E] (x : E) :
    (minpoly F x).natSepDegree = 1 :=
  (isPurelyInseparable_iff_natSepDegree_eq_one F).1 ‹_› x

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, the minimal polynomial of `x` over `F` is of form
`X ^ (q ^ n) - y` for some natural number `n` and some element `y` of `F`. -/
theorem isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q]

theorem IsPurelyInseparable.minpoly_eq_X_pow_sub_C (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y :=
  (isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C F q).1 ‹_› x

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, the minimal polynomial of `x` over `F` is of form
`(X - x) ^ (q ^ n)` for some natural number `n`. -/
theorem isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔
    ∀ x : E, ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_sub_C_pow q]

theorem IsPurelyInseparable.minpoly_eq_X_sub_C_pow (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : ∃ n : ℕ, (minpoly F x).map (algebraMap F E) = (X - C x) ^ q ^ n :=
  (isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow F q).1 ‹_› x

variable (E) in
lemma IsPurelyInseparable.finrank_eq_pow
    (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E] [FiniteDimensional F E] :
    ∃ n, finrank F E = q ^ n := by
  suffices ∀ (F E : Type v) [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
      [IsPurelyInseparable F E] [FiniteDimensional F E], ∃ n, finrank F E = q ^ n by
    simpa using this (⊥ : IntermediateField F E) E q
  intros F E _ _ _ q _ _ _
  generalize hd : finrank F E = d
  induction d using Nat.strongRecOn generalizing F with
  | ind d IH =>
    by_cases h : (⊥ : IntermediateField F E) = ⊤
    · rw [← finrank_top', ← h, IntermediateField.finrank_bot] at hd
      exact ⟨0, ((pow_zero q).trans hd).symm⟩
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_of_le_of_ne bot_le h:)
    obtain ⟨m, y, e⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x
    have : finrank F F⟮x⟯ = q ^ m := by
      rw [adjoin.finrank (Algebra.IsIntegral.isIntegral x), e, natDegree_sub_C, natDegree_X_pow]
    obtain ⟨n, hn⟩ := IH _ (by
      rw [← hd, ← finrank_mul_finrank F F⟮x⟯, Nat.lt_mul_iff_one_lt_left finrank_pos, this]
      by_contra! H
      refine hx (finrank_adjoin_simple_eq_one_iff.mp (le_antisymm (this ▸ H) ?_))
      exact Nat.one_le_iff_ne_zero.mpr Module.finrank_pos.ne') (F⟮x⟯) rfl
    exact ⟨m + n, by rw [← hd, ← finrank_mul_finrank F F⟮x⟯, hn, pow_add, this]⟩

variable (E)

variable {F E} in
/-- If an extension has finite separable degree one, then it is purely inseparable. -/
theorem isPurelyInseparable_of_finSepDegree_eq_one
    (hdeg : finSepDegree F E = 1) : IsPurelyInseparable F E := by
  by_cases H : Algebra.IsAlgebraic F E
  · rw [isPurelyInseparable_iff]
    refine fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, fun hsep ↦ ?_⟩
    have : Algebra.IsAlgebraic F⟮x⟯ E := Algebra.IsAlgebraic.tower_top (K := F) F⟮x⟯
    have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E
    rw [hdeg, mul_eq_one, (finSepDegree_adjoin_simple_eq_finrank_iff F E x
        (Algebra.IsAlgebraic.isAlgebraic x)).2 hsep,
      IntermediateField.finrank_eq_one_iff] at this
    simpa only [this.1] using mem_adjoin_simple_self F x
  · rw [← Algebra.transcendental_iff_not_isAlgebraic] at H
    simp [finSepDegree_eq_zero_of_transcendental F E] at hdeg

namespace IsPurelyInseparable

variable [IsPurelyInseparable F E] (R L : Type*) [CommSemiring R] [Algebra R F] [Algebra R E]

/-- If `E / F` is purely inseparable, then for any reduced ring `L`, the map `(E →+* L) → (F →+* L)`
induced by `algebraMap F E` is injective. In particular, a purely inseparable field extension
is an epimorphism in the category of fields. -/
theorem injective_comp_algebraMap [CommRing L] [IsReduced L] :
    Function.Injective fun f : E →+* L ↦ f.comp (algebraMap F E) := fun f g heq ↦ by
  ext x
  let q := ringExpChar F
  obtain ⟨n, y, h⟩ := IsPurelyInseparable.pow_mem F q x
  replace heq := congr($heq y)
  simp_rw [RingHom.comp_apply, h, map_pow] at heq
  nontriviality L
  haveI := expChar_of_injective_ringHom (f.comp (algebraMap F E)).injective q
  exact iterateFrobenius_inj L q n heq

theorem injective_restrictDomain [CommRing L] [IsReduced L] [Algebra R L] [IsScalarTower R F E] :
    Function.Injective (AlgHom.restrictDomain (A := R) F (C := E) (D := L)) := fun _ _ eq ↦
  AlgHom.coe_ringHom_injective <| injective_comp_algebraMap F E L <| congr_arg AlgHom.toRingHom eq

instance [Field L] [PerfectField L] [Algebra F L] : Nonempty (E →ₐ[F] L) :=
  nonempty_algHom_of_splits fun x ↦ ⟨IsPurelyInseparable.isIntegral' _ _,
    have ⟨q, _⟩ := ExpChar.exists F
    PerfectField.splits_of_natSepDegree_eq_one (algebraMap F L)
      ((minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q).mpr <|
        IsPurelyInseparable.minpoly_eq_X_pow_sub_C F q x)⟩

theorem bijective_comp_algebraMap [Field L] [PerfectField L] :
    Function.Bijective fun f : E →+* L ↦ f.comp (algebraMap F E) :=
  ⟨injective_comp_algebraMap F E L, fun g ↦ let _ := g.toAlgebra
    ⟨_, (Classical.arbitrary <| E →ₐ[F] L).comp_algebraMap⟩⟩

theorem bijective_restrictDomain [Field L] [PerfectField L] [Algebra R L] [IsScalarTower R F E] :
    Function.Bijective (AlgHom.restrictDomain (A := R) F (C := E) (D := L)) :=
  ⟨injective_restrictDomain F E R L, fun g ↦ let _ := g.toAlgebra
    let f := Classical.arbitrary (E →ₐ[F] L)
    ⟨f.restrictScalars R, AlgHom.coe_ringHom_injective f.comp_algebraMap⟩⟩

end IsPurelyInseparable

/-- If `E / F` is purely inseparable, then for any reduced `F`-algebra `L`, there exists at most one
`F`-algebra homomorphism from `E` to `L`. -/
instance instSubsingletonAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type w)
    [CommRing L] [IsReduced L] [Algebra F L] : Subsingleton (E →ₐ[F] L) where
  allEq f g := AlgHom.coe_ringHom_injective <|
    IsPurelyInseparable.injective_comp_algebraMap F E L (by simp_rw [AlgHom.comp_algebraMap])

instance instUniqueAlgHomOfIsPurelyInseparable [IsPurelyInseparable F E] (L : Type w)
    [CommRing L] [IsReduced L] [Algebra F L] [Algebra E L] [IsScalarTower F E L] :
    Unique (E →ₐ[F] L) := uniqueOfSubsingleton (IsScalarTower.toAlgHom F E L)

/-- If `E / F` is purely inseparable, then `Field.Emb F E` has exactly one element. -/
instance instUniqueEmbOfIsPurelyInseparable [IsPurelyInseparable F E] :
    Unique (Emb F E) := instUniqueAlgHomOfIsPurelyInseparable F E _

/-- A purely inseparable extension has finite separable degree one. -/
theorem IsPurelyInseparable.finSepDegree_eq_one [IsPurelyInseparable F E] :
    finSepDegree F E = 1 := Nat.card_unique

/-- A purely inseparable extension has separable degree one. -/
theorem IsPurelyInseparable.sepDegree_eq_one [IsPurelyInseparable F E] :
    sepDegree F E = 1 := by
  rw [sepDegree, separableClosure.eq_bot_of_isPurelyInseparable, IntermediateField.rank_bot]

/-- A purely inseparable extension has inseparable degree equal to degree. -/
theorem IsPurelyInseparable.insepDegree_eq [IsPurelyInseparable F E] :
    insepDegree F E = Module.rank F E := by
  rw [insepDegree, separableClosure.eq_bot_of_isPurelyInseparable, rank_bot']

/-- A purely inseparable extension has finite inseparable degree equal to degree. -/
theorem IsPurelyInseparable.finInsepDegree_eq [IsPurelyInseparable F E] :
    finInsepDegree F E = finrank F E := congr(Cardinal.toNat $(insepDegree_eq F E))

/-- An extension is purely inseparable if and only if it has finite separable degree one. -/
theorem isPurelyInseparable_iff_finSepDegree_eq_one :
    IsPurelyInseparable F E ↔ finSepDegree F E = 1 :=
  ⟨fun _ ↦ IsPurelyInseparable.finSepDegree_eq_one F E,
    fun h ↦ isPurelyInseparable_of_finSepDegree_eq_one h⟩

lemma isSeparable_iff_finInsepDegree_eq_one  :
    Algebra.IsSeparable F K ↔ finInsepDegree F K = 1 := by
  rw [← separableClosure.eq_top_iff, ← IntermediateField.finrank_eq_one_iff_eq_top, finInsepDegree]

variable {F E} in
/-- An algebraic extension is purely inseparable if and only if all of its finite dimensional
subextensions are purely inseparable. -/
theorem isPurelyInseparable_iff_fd_isPurelyInseparable [Algebra.IsAlgebraic F E] :
    IsPurelyInseparable F E ↔
    ∀ L : IntermediateField F E, FiniteDimensional F L → IsPurelyInseparable F L := by
  refine ⟨fun _ _ _ ↦ IsPurelyInseparable.tower_bot F _ E,
    fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ?_⟩
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  refine ⟨hx, fun _ ↦ ?_⟩
  obtain ⟨y, h⟩ := (h _ (adjoin.finiteDimensional hx)).inseparable' _ <|
    show Separable (minpoly F (AdjoinSimple.gen F x)) by rwa [minpoly_eq]
  exact ⟨y, congr_arg (algebraMap _ E) h⟩

/-- A purely inseparable extension is normal. -/
instance IsPurelyInseparable.normal [IsPurelyInseparable F E] : Normal F E where
  toIsAlgebraic := isAlgebraic F E
  splits' x := by
    obtain ⟨n, h⟩ := IsPurelyInseparable.minpoly_eq_X_sub_C_pow F (ringExpChar F) x
    rw [← splits_id_iff_splits, h]
    exact splits_pow _ (splits_X_sub_C _) _

/-- If `E / F` is algebraic, then `E` is purely inseparable over the
separable closure of `F` in `E`. -/
@[stacks 030K "$E/E_{sep}$ is purely inseparable."]
instance separableClosure.isPurelyInseparable [Algebra.IsAlgebraic F E] :
    IsPurelyInseparable (separableClosure F E) E := isPurelyInseparable_iff.2 fun x ↦ by
  set L := separableClosure F E
  refine ⟨(IsAlgebraic.tower_top L (Algebra.IsAlgebraic.isAlgebraic (R := F) x)).isIntegral,
    fun h ↦ ?_⟩
  haveI := (isSeparable_adjoin_simple_iff_isSeparable L E).2 h
  haveI : Algebra.IsSeparable F (restrictScalars F L⟮x⟯) := Algebra.IsSeparable.trans F L L⟮x⟯
  have hx : x ∈ restrictScalars F L⟮x⟯ := mem_adjoin_simple_self _ x
  exact ⟨⟨x, mem_separableClosure_iff.2 <| isSeparable_of_mem_isSeparable F E hx⟩, rfl⟩

open Cardinal in
theorem Field.Emb.cardinal_separableClosure [Algebra.IsAlgebraic F E] :
    #(Field.Emb F <| separableClosure F E) = #(Field.Emb F E) := by
  rw [← (embProdEmbOfIsAlgebraic F (separableClosure F E) E).cardinal_eq,
    mk_prod, mk_eq_one (Emb _ E), lift_one, mul_one, lift_id]

lemma finInsepDegree_eq_pow (q : ℕ) [ExpChar F q] [FiniteDimensional F E] :
    ∃ n, finInsepDegree F E = q ^ n :=
  IsPurelyInseparable.finrank_eq_pow ..

/-- An intermediate field of `E / F` contains the separable closure of `F` in `E`
if `E` is purely inseparable over it. -/
theorem separableClosure_le (L : IntermediateField F E)
    [h : IsPurelyInseparable L E] : separableClosure F E ≤ L := fun x hx ↦ by
  obtain ⟨y, rfl⟩ := h.inseparable' _ <|
    IsSeparable.tower_top L (mem_separableClosure_iff.1 hx)
  exact y.2

/-- If `E / F` is algebraic, then an intermediate field of `E / F` contains the
separable closure of `F` in `E` if and only if `E` is purely inseparable over it. -/
theorem separableClosure_le_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F E) :
    separableClosure F E ≤ L ↔ IsPurelyInseparable L E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ separableClosure_le F E L⟩
  have := separableClosure.isPurelyInseparable F E
  letI := (inclusion h).toAlgebra
  letI : SMul (separableClosure F E) L := Algebra.toSMul
  haveI : IsScalarTower (separableClosure F E) L E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact IsPurelyInseparable.tower_top (separableClosure F E) L E

/-- If an intermediate field of `E / F` is separable over `F`, and `E` is purely inseparable
over it, then it is equal to the separable closure of `F` in `E`. -/
theorem eq_separableClosure (L : IntermediateField F E)
    [Algebra.IsSeparable F L] [IsPurelyInseparable L E] : L = separableClosure F E :=
  le_antisymm (le_separableClosure F E L) (separableClosure_le F E L)

open separableClosure in
/-- If `E / F` is algebraic, then an intermediate field of `E / F` is equal to the separable closure
of `F` in `E` if and only if it is separable over `F`, and `E` is purely inseparable
over it. -/
theorem eq_separableClosure_iff [Algebra.IsAlgebraic F E] (L : IntermediateField F E) :
    L = separableClosure F E ↔ Algebra.IsSeparable F L ∧ IsPurelyInseparable L E :=
  ⟨by rintro rfl; exact ⟨isSeparable F E, isPurelyInseparable F E⟩,
   fun ⟨_, _⟩ ↦ eq_separableClosure F E L⟩

/-- If `L` is an algebraically closed field containing `E`, such that the map
`(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective, then `E / F` is
purely inseparable. As a corollary, epimorphisms in the category of fields must be
purely inseparable extensions. -/
theorem IsPurelyInseparable.of_injective_comp_algebraMap (L : Type w) [Field L] [IsAlgClosed L]
    [Nonempty (E →+* L)] (h : Function.Injective fun f : E →+* L ↦ f.comp (algebraMap F E)) :
    IsPurelyInseparable F E := by
  rw [isPurelyInseparable_iff_finSepDegree_eq_one, finSepDegree, Nat.card_eq_one_iff_unique]
  letI := (Classical.arbitrary (E →+* L)).toAlgebra
  let j : AlgebraicClosure E →ₐ[E] L := IsAlgClosed.lift
  exact ⟨⟨fun f g ↦ DFunLike.ext' <| j.injective.comp_left (congr_arg (⇑) <|
    @h (j.toRingHom.comp f) (j.toRingHom.comp g) (by ext; simp))⟩, inferInstance⟩

end Field

namespace IntermediateField

instance isPurelyInseparable_bot : IsPurelyInseparable F (⊥ : IntermediateField F E) :=
  (botEquiv F E).symm.isPurelyInseparable

end IntermediateField

/-- If `E` is an algebraic closure of `F`, then `F` is separably closed if and only if `E / F` is
purely inseparable. -/
theorem isSepClosed_iff_isPurelyInseparable_algebraicClosure [IsAlgClosure F E] :
    IsSepClosed F ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ inferInstance, fun H ↦ by
    haveI := IsAlgClosure.isAlgClosed F (K := E)
    rwa [← separableClosure.eq_bot_iff, IsSepClosed.separableClosure_eq_bot_iff] at H⟩

variable {F E} in
/-- If `E / F` is an algebraic extension, `F` is separably closed,
then `E` is also separably closed. -/
theorem Algebra.IsAlgebraic.isSepClosed [Algebra.IsAlgebraic F E]
    [IsSepClosed F] : IsSepClosed E :=
  have : Algebra.IsAlgebraic F (AlgebraicClosure E) := .trans F E _
  (isSepClosed_iff_isPurelyInseparable_algebraicClosure E _).mpr
    (IsPurelyInseparable.tower_top F E <| AlgebraicClosure E)

namespace Field

/-- If `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to `Field.sepDegree F E`
as a natural number. This means that the cardinality of `Field.Emb F E` and the degree of
`(separableClosure F E) / F` are both finite or infinite, and when they are finite, they
coincide. -/
@[stacks 09HJ "`sepDegree` is defined as the right hand side of 09HJ"]
theorem finSepDegree_eq [Algebra.IsAlgebraic F E] :
    finSepDegree F E = Cardinal.toNat (sepDegree F E) := by
  have : Algebra.IsAlgebraic (separableClosure F E) E := Algebra.IsAlgebraic.tower_top (K := F) _
  have h := finSepDegree_mul_finSepDegree_of_isAlgebraic F (separableClosure F E) E |>.symm
  haveI := separableClosure.isSeparable F E
  haveI := separableClosure.isPurelyInseparable F E
  rwa [finSepDegree_eq_finrank_of_isSeparable F (separableClosure F E),
    IsPurelyInseparable.finSepDegree_eq_one (separableClosure F E) E, mul_one] at h

/-- The finite separable degree multiply by the finite inseparable degree is equal
to the (finite) field extension degree. -/
theorem finSepDegree_mul_finInsepDegree : finSepDegree F E * finInsepDegree F E = finrank F E := by
  by_cases halg : Algebra.IsAlgebraic F E
  · have := congr_arg Cardinal.toNat (sepDegree_mul_insepDegree F E)
    rwa [Cardinal.toNat_mul, ← finSepDegree_eq F E] at this
  rw [finInsepDegree, finrank_of_infinite_dimensional (K := F) (V := E) fun _ ↦
      halg (Algebra.IsAlgebraic.of_finite F E),
    finrank_of_infinite_dimensional (K := separableClosure F E) (V := E) fun _ ↦
      halg (.trans _ (separableClosure F E) _),
    mul_zero]

end Field

namespace separableClosure

variable [Algebra E K] [IsScalarTower F E K] {F E}

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic and `K / E`
is separable, then `E` adjoin `separableClosure F K` is equal to `K`. It is a special case of
`separableClosure.adjoin_eq_of_isAlgebraic`, and is an intermediate result used to prove it. -/
lemma adjoin_eq_of_isAlgebraic_of_isSeparable [Algebra.IsAlgebraic F E]
    [Algebra.IsSeparable E K] : adjoin E (separableClosure F K : Set K) = ⊤ :=
  top_unique fun x _ ↦ by
    set S := separableClosure F K
    set L := adjoin E (S : Set K)
    have := Algebra.isSeparable_tower_top_of_isSeparable E L K
    let i : S →+* L := Subsemiring.inclusion fun x hx ↦ subset_adjoin E (S : Set K) hx
    let _ : Algebra S L := i.toAlgebra
    let _ : SMul S L := Algebra.toSMul
    have : IsScalarTower S L K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    have := Algebra.IsAlgebraic.trans F E K
    have : IsPurelyInseparable S K := separableClosure.isPurelyInseparable F K
    have := IsPurelyInseparable.tower_top S L K
    obtain ⟨y, rfl⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable L K x
    exact y.2

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then
`E` adjoin `separableClosure F K` is equal to `separableClosure E K`. -/
theorem adjoin_eq_of_isAlgebraic [Algebra.IsAlgebraic F E] :
    adjoin E (separableClosure F K) = separableClosure E K := by
  set S := separableClosure E K
  have h := congr_arg lift (adjoin_eq_of_isAlgebraic_of_isSeparable (F := F) S)
  rw [lift_top, lift_adjoin] at h
  haveI : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← h, ← map_eq_of_separableClosure_eq_bot F (separableClosure_eq_bot E K)]
  simp only [S, coe_map, IsScalarTower.coe_toAlgHom', IntermediateField.algebraMap_apply]

end separableClosure

section

open TensorProduct

section Subalgebra

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] (p : ℕ) [ExpChar A p]

/-- The perfect closure of `R` in `A` are the elements `x : A` such that `x ^ p ^ n`
is in `R` for some `n`, where `p` is the exponential characteristic of `R`. -/
def Subalgebra.perfectClosure : Subalgebra R A where
  carrier := {x : A | ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap R A).rangeS}
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [add_pow_expChar_pow, pow_add, pow_mul, mul_comm (_ ^ n), pow_mul]
    exact add_mem (pow_mem hx _) (pow_mem hy _)
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [mul_pow, pow_add, pow_mul, mul_comm (_ ^ n), pow_mul]
    exact mul_mem (pow_mem hx _) (pow_mem hy _)
  algebraMap_mem' := fun x ↦ ⟨0, by rw [pow_zero, pow_one]; exact ⟨x, rfl⟩⟩

variable {R A p}

theorem Subalgebra.mem_perfectClosure_iff {x : A} :
    x ∈ perfectClosure R A p ↔ ∃ n : ℕ, x ^ p ^ n ∈ (algebraMap R A).rangeS := Iff.rfl

end Subalgebra

variable {k K R : Type*} [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R]

lemma IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar
    [IsPurelyInseparable k K] (q : ℕ) [ExpChar k q] (x : R ⊗[k] K) :
    ∃ n, x ^ q ^ n ∈ (algebraMap R (R ⊗[k] K)).range := by
  nontriviality (R ⊗[k] K)
  obtain (hq|hq) := expChar_is_prime_or_one k q
  induction x with
  | zero => exact ⟨0, 0, by simp [zero_pow_eq, hq.ne_zero]⟩
  | add x y h h' =>
    have : ExpChar (R ⊗[k] K) q := expChar_of_injective_ringHom (algebraMap k _).injective q
    simp_rw [RingHom.mem_range, ← RingHom.mem_rangeS, ← Subalgebra.mem_perfectClosure_iff] at h h' ⊢
    exact add_mem h h'
  | tmul x y =>
    obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k q y
    use n
    have : (x ^ q ^ n) ⊗ₜ[k] (y ^ q ^ n) =
        (x ^ q ^ n) ⊗ₜ[k] (1 : K) * (1 : R) ⊗ₜ[k] (y ^ q ^ n) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.tmul_pow, this]
    refine Subring.mul_mem _ ⟨x ^ q ^ n, rfl⟩ ⟨algebraMap k R a, ?_⟩
    rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul, ha]
  · subst hq
    have : CharZero k := charZero_of_expChar_one' k
    exact ⟨0, (Algebra.TensorProduct.includeLeft_surjective R _ <|
      IsPurelyInseparable.surjective_algebraMap_of_isSeparable k K) _⟩

lemma IsPurelyInseparable.exists_pow_mem_range_tensorProduct [IsPurelyInseparable k K]
    (x : R ⊗[k] K) : ∃ n > 0, x ^ n ∈ (algebraMap R (R ⊗[k] K)).range := by
  let q := ringExpChar k
  obtain ⟨n, hr⟩ := exists_pow_pow_mem_range_tensorProduct_of_expChar q x
  refine ⟨q ^ n, pow_pos ?_ _, hr⟩
  obtain (hq|hq) := expChar_is_prime_or_one k q <;> simp [hq, Nat.Prime.pos]

end
