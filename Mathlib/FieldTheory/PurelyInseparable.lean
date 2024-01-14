/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SeparableClosure

/-!

# Purely inseparable extension

This file contains basics about the purely inseparable extension of fields.

## Main definitions

- `IsPurelyInseparable`: typeclass for purely inseparable field extension: an algebraic extension
  `E / F` is purely inseparable if and only if the minimal polynomial of every element of `E ∖ F`
  is not separable.

## Main results

- `IsPurelyInseparable.surjective_algebraMap_of_isSeparable`,
  `IsPurelyInseparable.bijective_algebraMap_of_isSeparable`,
  `IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable`:
  if `E / F` is both purely inseparable and separable, then `algebraMap F E` is surjective
  (resp. bijective). In particular, if an intermediate field of `E / F` is both purely inseparable
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

- `isPurelyInseparable_iff_finSepDegree_eq_one`: an algebraic extension is purely inseparable
  if and only if it has (finite) separable degree one.

  **TODO:** remove the algebraic assumption.

- `IsPurelyInseparable.normal`: a purely inseparable extension is normal.

- `separableClosure.isPurelyInseparable`: if `E / F` is algebraic, then `E` is purely inseparable
  over the (relative) separable closure of `E / F`.

- `separableClosure_le_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` contains
  the (relative) separable closure of `E / F` if and only if `E` is purely inseparable over it.

- `eq_separableClosure_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` is equal
  to the (relative) separable closure of `E / F` if and only if it is separable over `F`, and `E`
  is purely inseparable over it.

- `IsPurelyInseparable.injective_comp_algebraMap`: if `E / F` is purely inseparable, then for any
  reduced ring `L`, the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective.
  In other words, a purely inseparable field extension is an epimorphism in the category of fields.

- `IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`: if `F` is of exponential
  characteristic `q`, then `F(S) / F` is a purely inseparable extension if and only if for any
  `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`.

- `Field.finSepDegree_eq`: if `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to
  `Field.sepDegree F E` as a natural number. This means that the cardinality of `Field.Emb F E`
  and the degree of `(separableClosure F E) / F` are both finite or infinite, and when they are
  finite, they coincide.

- `finSepDegree_mul_finInsepDegree`: the (finite) separable degree multiply by the (finite)
  inseparable degree is equal to the (finite) field extension degree.

## Tags

separable degree, degree, separable closure, purely inseparable

## TODO

- `IsPurelyInseparable.of_injective_comp_algebraMap`: if `L` is an algebraically closed field
  containing `E`, such that the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is
  injective, then `E / F` is purely inseparable. In other words, epimorphisms in the category of
  fields must be purely inseparable extensions. Need to use the fact that `Emb F E` is infintie
  when `E / F` is (purely) transcendental.

- Prove that the (infinite) separable degree and the (infinite) inseparable degree are
  multiplicative. For the latter one, linearly disjoint argument is needed.

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

section IsPurelyInseparable

/-- Typeclass for purely inseparable field extension: an algebraic extension `E / F` is purely
inseparable if and only if the minimal polynomial of every element of `E ∖ F` is not separable. -/
class IsPurelyInseparable : Prop where
  isIntegral' (x : E) : IsIntegral F x
  inseparable' (x : E) : (minpoly F x).Separable → x ∈ (algebraMap F E).range

theorem IsPurelyInseparable.isAlgebraic [IsPurelyInseparable F E] :
    Algebra.IsAlgebraic F E := fun x ↦ (IsPurelyInseparable.isIntegral' x).isAlgebraic

variable {E}

theorem IsPurelyInseparable.isIntegral [IsPurelyInseparable F E] : Algebra.IsIntegral F E :=
  IsPurelyInseparable.isIntegral'

theorem IsPurelyInseparable.inseparable [IsPurelyInseparable F E] :
    ∀ x : E, (minpoly F x).Separable → x ∈ (algebraMap F E).range :=
  IsPurelyInseparable.inseparable'

variable {F K}

theorem isPurelyInseparable_iff : IsPurelyInseparable F E ↔ ∀ x : E,
    IsIntegral F x ∧ ((minpoly F x).Separable → x ∈ (algebraMap F E).range) :=
  ⟨fun h x ↦ ⟨h.isIntegral' x, h.inseparable' x⟩, fun h ↦ ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩⟩

/-- Transfer `IsPurelyInseparable` across an `AlgEquiv`. -/
theorem AlgEquiv.isPurelyInseparable (e : K ≃ₐ[F] E) [IsPurelyInseparable F K] :
    IsPurelyInseparable F E := by
  refine ⟨fun _ ↦ by rw [← isIntegral_algEquiv e.symm]; exact IsPurelyInseparable.isIntegral F _,
    fun x h ↦ ?_⟩
  rw [← minpoly.algEquiv_eq e.symm] at h
  simpa only [RingHom.mem_range, algebraMap_eq_apply] using IsPurelyInseparable.inseparable F _ h

theorem AlgEquiv.isPurelyInseparable_iff (e : K ≃ₐ[F] E) :
    IsPurelyInseparable F K ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ e.isPurelyInseparable, fun _ ↦ e.symm.isPurelyInseparable⟩

/-- If `E / F` is an algebraic extension, `F` is separably closed,
then `E / F` is purely inseparable. -/
theorem Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed (halg : Algebra.IsAlgebraic F E)
    [IsSepClosed F] : IsPurelyInseparable F E :=
  ⟨halg.isIntegral, fun x h ↦ minpoly.mem_range_of_degree_eq_one F x <|
    IsSepClosed.degree_eq_one_of_irreducible F (minpoly.irreducible (halg x).isIntegral) h⟩

variable (F E K)

/-- If `E / F` is both purely inseparable and separable, then `algebraMap F E` is surjective. -/
theorem IsPurelyInseparable.surjective_algebraMap_of_isSeparable
    [IsPurelyInseparable F E] [IsSeparable F E] : Function.Surjective (algebraMap F E) :=
  fun x ↦ IsPurelyInseparable.inseparable F x (IsSeparable.separable F x)

/-- If `E / F` is both purely inseparable and separable, then `algebraMap F E` is bijective. -/
theorem IsPurelyInseparable.bijective_algebraMap_of_isSeparable
    [IsPurelyInseparable F E] [IsSeparable F E] : Function.Bijective (algebraMap F E) :=
  ⟨(algebraMap F E).injective, surjective_algebraMap_of_isSeparable F E⟩

variable {F E} in
/-- If an intermediate field of `E / F` is both purely inseparable and separable, then it is equal
to `F`. -/
theorem IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable (L : IntermediateField F E)
    [IsPurelyInseparable F L] [IsSeparable F L] : L = ⊥ := bot_unique fun x hx ↦ by
  obtain ⟨y, hy⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable F L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L E) hy⟩

/-- If `E / F` is purely inseparable, then the (relative) separable closure of `E / F` is
equal to `F`. -/
theorem separableClosure.eq_bot_of_isPurelyInseparable [IsPurelyInseparable F E] :
    separableClosure F E = ⊥ :=
  bot_unique fun x h ↦ IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)

/-- If `E / F` is an algebraic extension, then the (relative) separable closure of `E / F` is
equal to `F` if and only if `E / F` is purely inseparable. -/
theorem separableClosure.eq_bot_iff (halg : Algebra.IsAlgebraic F E) :
    separableClosure F E = ⊥ ↔ IsPurelyInseparable F E :=
  ⟨fun h ↦ isPurelyInseparable_iff.2 fun x ↦ have hx := (halg x).isIntegral; ⟨hx, fun hs ↦ by
    simpa only [h] using mem_separableClosure_iff.2 hs⟩,
      fun _ ↦ eq_bot_of_isPurelyInseparable F E⟩

instance isPurelyInseparable_self : IsPurelyInseparable F F :=
  ⟨fun _ ↦ isIntegral_algebraMap, fun x _ ↦ ⟨x, rfl⟩⟩

variable {E}

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, there exists a natural number `n` such that
`x ^ (q ^ n)` is contained in `F`. -/
theorem isPurelyInseparable_iff_pow_mem (q : ℕ) [hF : ExpChar F q] :
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
  rw [hsep.natSepDegree_eq_natDegree, ← adjoin.finrank halg,
    IntermediateField.finrank_eq_one_iff] at hdeg
  simpa only [hdeg] using mem_adjoin_simple_self F x

theorem IsPurelyInseparable.pow_mem (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E] (x : E) :
    ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range :=
  (isPurelyInseparable_iff_pow_mem F q).1 (by assumption) x

variable (E)

/-- If `K / E / F` is a field extension tower such that `K / F` is purely inseparable,
then `E / F` is also purely inseparable. -/
theorem IsPurelyInseparable.tower_bot [Algebra E K] [IsScalarTower F E K]
    [IsPurelyInseparable F K] : IsPurelyInseparable F E := by
  refine ⟨fun x ↦ (isIntegral F (algebraMap E K x)).tower_bot_of_field, fun x h ↦ ?_⟩
  rw [← minpoly.algebraMap_eq (algebraMap E K).injective] at h
  obtain ⟨y, h⟩ := inseparable F _ h
  use y
  apply_fun algebraMap E K using (algebraMap E K).injective
  exact h.symm ▸ (IsScalarTower.algebraMap_apply F E K y).symm

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

variable {E}

/-- A field extension `E / F` is purely inseparable if and only if for every element `x` of `E`,
its minimal polynomial has separable degree one. -/
theorem isPurelyInseparable_iff_natSepDegree_eq_one :
    IsPurelyInseparable F E ↔ ∀ x : E, (minpoly F x).natSepDegree = 1 := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  simp_rw [isPurelyInseparable_iff_pow_mem F q, minpoly.natSepDegree_eq_one_iff_pow_mem q]

theorem IsPurelyInseparable.natSepDegree_eq_one [IsPurelyInseparable F E] (x : E) :
    (minpoly F x).natSepDegree = 1 :=
  (isPurelyInseparable_iff_natSepDegree_eq_one F).1 (by assumption) x

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, the minimal polynomial of `x` over `F` is of form
`X ^ (q ^ n) - y` for some natural number `n` and some element `y` of `F`. -/
theorem isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C (q : ℕ) [hF : ExpChar F q] :
    IsPurelyInseparable F E ↔ ∀ x : E, ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y := by
  simp_rw [isPurelyInseparable_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_eq_X_pow_sub_C q]

theorem IsPurelyInseparable.minpoly_eq_X_pow_sub_C (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E]
    (x : E) : ∃ (n : ℕ) (y : F), minpoly F x = X ^ q ^ n - C y :=
  (isPurelyInseparable_iff_minpoly_eq_X_pow_sub_C F q).1 (by assumption) x

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
  (isPurelyInseparable_iff_minpoly_eq_X_sub_C_pow F q).1 (by assumption) x

variable (E)

-- TODO: remove `halg` assumption
variable {F E} in
/-- If an algebraic extension has (finite) separable degree one, then it is purely inseparable. -/
theorem isPurelyInseparable_of_finSepDegree_eq_one (halg : Algebra.IsAlgebraic F E)
    (hdeg : finSepDegree F E = 1) : IsPurelyInseparable F E := by
  rw [isPurelyInseparable_iff]
  refine fun x ↦ ⟨(halg x).isIntegral, fun hsep ↦ ?_⟩
  have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E <| halg.tower_top F⟮x⟯
  rw [hdeg, mul_eq_one, (finSepDegree_adjoin_simple_eq_finrank_iff F E x (halg x)).2 hsep,
    IntermediateField.finrank_eq_one_iff] at this
  simpa only [this.1] using mem_adjoin_simple_self F x

/-- A purely inseparable extension has (finite) separable degree one. -/
theorem IsPurelyInseparable.finSepDegree_eq_one [IsPurelyInseparable F E] :
    finSepDegree F E = 1 := by
  rw [finSepDegree, Nat.card, Cardinal.toNat_eq_iff Nat.one_ne_zero, Nat.cast_one]
  by_contra h
  obtain ⟨i : E →ₐ[F] _, i' : E →ₐ[F] _, h⟩ := Cardinal.one_lt_iff_nontrivial.1 <|
    Cardinal.one_le_iff_ne_zero.2 (Cardinal.mk_ne_zero (Emb F E)) |>.lt_of_ne' h
  obtain ⟨x, h⟩ : ∃ (x : E), i x ≠ i' x := by_contra fun h' ↦ by
    simp only [ne_eq, not_exists, not_not] at h'
    exact h (AlgHom.ext h')
  have hr (i : E →ₐ[F] (AlgebraicClosure E)) : i x ∈ ((minpoly F x).aroots _).toFinset := by
    rw [Multiset.mem_toFinset, mem_aroots]
    exact ⟨minpoly.ne_zero (isIntegral F x),
      (minpoly.algHom_eq i i.injective x) ▸ minpoly.aeval F (i x)⟩
  have := Finset.one_lt_card_iff.2 ⟨i x, i' x, hr i, hr i', h⟩
  rw [← natSepDegree_eq_of_isAlgClosed] at this
  linarith only [this, IsPurelyInseparable.natSepDegree_eq_one F x]

-- TODO: remove `halg` assumption
/-- An algebraic extension is purely inseparable if and only if it has (finite) separable
degree one. -/
theorem isPurelyInseparable_iff_finSepDegree_eq_one (halg : Algebra.IsAlgebraic F E) :
    IsPurelyInseparable F E ↔ finSepDegree F E = 1 :=
  ⟨fun _ ↦ IsPurelyInseparable.finSepDegree_eq_one F E,
    fun h ↦ isPurelyInseparable_of_finSepDegree_eq_one halg h⟩

variable {F E} in
/-- An algebraic extension is purely inseparable if and only if all of its finite dimensional
subextensions are purely inseparable. -/
theorem isPurelyInseparable_iff_fd_isPurelyInseparable (halg : Algebra.IsAlgebraic F E) :
    IsPurelyInseparable F E ↔
    ∀ L : IntermediateField F E, FiniteDimensional F L → IsPurelyInseparable F L := by
  refine ⟨fun _ _ _ ↦ IsPurelyInseparable.tower_bot F _ E,
    fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ?_⟩
  have hx := (halg x).isIntegral
  refine ⟨hx, fun _ ↦ ?_⟩
  obtain ⟨y, h⟩ := (h _ (adjoin.finiteDimensional hx)).inseparable' _ <|
    show Separable (minpoly F (AdjoinSimple.gen F x)) by rwa [minpoly_eq]
  exact ⟨y, congr_arg (algebraMap _ E) h⟩

/-- A purely inseparable extension is normal. -/
instance IsPurelyInseparable.normal [IsPurelyInseparable F E] : Normal F E := by
  refine ⟨isAlgebraic F E, fun x ↦ ?_⟩
  obtain ⟨q, _⟩ := ExpChar.exists F
  obtain ⟨n, h⟩ := IsPurelyInseparable.minpoly_eq_X_sub_C_pow F q x
  rw [← splits_id_iff_splits, h]
  exact splits_pow _ (splits_X_sub_C _) _

/-- If `E / F` is algebraic, then `E` is purely inseparable over the (relative)
separable closure of `E / F`. -/
theorem separableClosure.isPurelyInseparable (halg : Algebra.IsAlgebraic F E) :
    IsPurelyInseparable (separableClosure F E) E := isPurelyInseparable_iff.2 fun x ↦ by
  set L := separableClosure F E
  refine ⟨(halg.tower_top L x).isIntegral, fun h ↦ ?_⟩
  haveI := (isSeparable_adjoin_simple_iff_separable L E).2 h
  haveI : IsSeparable F (restrictScalars F L⟮x⟯) := IsSeparable.trans F L L⟮x⟯
  have hx : x ∈ restrictScalars F L⟮x⟯ := mem_adjoin_simple_self _ x
  exact ⟨⟨x, mem_separableClosure_iff.2 <| separable_of_mem_isSeparable F E hx⟩, rfl⟩

/-- An intermediate field of `E / F` contains the (relative) separable closure of `E / F`
if `E` is purely inseparable over it. -/
theorem separableClosure_le (L : IntermediateField F E)
    [h : IsPurelyInseparable L E] : separableClosure F E ≤ L := fun x hx ↦ by
  obtain ⟨y, rfl⟩ := h.inseparable' _ <| (mem_separableClosure_iff.1 hx).map_minpoly L
  exact y.2

/-- If `E / F` is algebraic, then an intermediate field of `E / F` contains the (relative)
separable closure of `E / F` if and only if `E` is purely inseparable over it. -/
theorem separableClosure_le_iff (halg : Algebra.IsAlgebraic F E) (L : IntermediateField F E) :
    separableClosure F E ≤ L ↔ IsPurelyInseparable L E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ separableClosure_le F E L⟩
  haveI := separableClosure.isPurelyInseparable F E halg
  letI := (inclusion h).toAlgebra
  letI : Module (separableClosure F E) L := Algebra.toModule
  letI : SMul (separableClosure F E) L := Algebra.toSMul
  haveI : IsScalarTower (separableClosure F E) L E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact IsPurelyInseparable.tower_top (separableClosure F E) L E

/-- If `E / F` is algebraic, then an intermediate field of `E / F` is equal to the (relative)
separable closure of `E / F` if and only if it is separable over `F`, and `E` is purely inseparable
over it. -/
theorem eq_separableClosure_iff (halg : Algebra.IsAlgebraic F E) (L : IntermediateField F E) :
    L = separableClosure F E ↔ IsSeparable F L ∧ IsPurelyInseparable L E :=
  ⟨by rintro rfl; exact ⟨separableClosure.isSeparable F E,
    separableClosure.isPurelyInseparable F E halg⟩, fun ⟨_, _⟩ ↦ le_antisymm
      (le_separableClosure F E L) (separableClosure_le F E L)⟩

/-- If `E / F` is purely inseparable, then for any reduced ring `L`, the map `(E →+* L) → (F →+* L)`
induced by `algebraMap F E` is injective. In particular, a purely inseparable field extension
is an epimorphism in the category of fields. -/
theorem IsPurelyInseparable.injective_comp_algebraMap [IsPurelyInseparable F E]
    (L : Type w) [CommRing L] [IsReduced L] :
    Function.Injective fun f : E →+* L ↦ f.comp (algebraMap F E) := fun f g heq ↦ by
  ext x
  obtain ⟨q, hF⟩ := ExpChar.exists F
  obtain ⟨n, y, h⟩ := IsPurelyInseparable.pow_mem F q x
  replace heq := congr($heq y)
  simp_rw [RingHom.comp_apply, h] at heq
  cases' hF with _ _ hprime _
  · rwa [one_pow, pow_one] at heq
  nontriviality L
  haveI := charP_of_injective_ringHom (f.comp (algebraMap F E)).injective q
  haveI := Fact.mk hprime
  simp_rw [map_pow, ← iterate_frobenius] at heq
  exact (frobenius_inj L q).iterate n heq

-- TODO:
set_option linter.unusedVariables false in
/-- If `L` is an algebraically closed field containing `E`, such that the map
`(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective, then `E / F` is
purely inseparable. In other words, epimorphisms in the category of fields must be
purely inseparable extensions. -/
proof_wanted IsPurelyInseparable.of_injective_comp_algebraMap (L : Type w) [Field L] [IsAlgClosed L]
    (hn : Nonempty (E →+* L)) (h : Function.Injective fun f : E →+* L ↦ f.comp (algebraMap F E)) :
    IsPurelyInseparable F E

end IsPurelyInseparable

namespace IntermediateField

instance isPurelyInseparable_bot : IsPurelyInseparable F (⊥ : IntermediateField F E) :=
  (botEquiv F E).symm.isPurelyInseparable

/-- `F⟮x⟯ / F` is a purely inseparable extension if and only if the mininal polynomial of `x`
has separable degree one. -/
theorem isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ (minpoly F x).natSepDegree = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := IsPurelyInseparable.natSepDegree_eq_one F (AdjoinSimple.gen F x)
    rwa [minpoly_eq] at this
  have hx : IsIntegral F x := by_contra fun h' ↦ by
    simp only [minpoly.eq_zero h', natSepDegree_zero, zero_ne_one] at h
  haveI := adjoin.finiteDimensional hx
  rwa [isPurelyInseparable_iff_finSepDegree_eq_one _ _ (Algebra.IsAlgebraic.of_finite F F⟮x⟯),
    finSepDegree_adjoin_simple_eq_natSepDegree _ _ hx.isAlgebraic]

/-- If `F` is of exponential characteristic `q`, then `F⟮x⟯ / F` is a purely inseparable extension
if and only if `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`. -/
theorem isPurelyInseparable_adjoin_simple_iff_pow_mem (q : ℕ) [hF : ExpChar F q] {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  simp_rw [isPurelyInseparable_adjoin_simple_iff_natSepDegree_eq_one,
    minpoly.natSepDegree_eq_one_iff_pow_mem q]

/-- If `F` is of exponential characteristic `q`, `S` is a finite subset of `E`, such that for any
`x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`, then `F(S) / F` is a purely
inseparable extension. It is a special case of
`IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`, and is an
intermediate result used to prove it. -/
lemma isPurelyInseparable_adjoin_finset_of_pow_mem (q : ℕ) [hF : ExpChar F q]
    (S : Finset E) (h : ∀ x ∈ S, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range) :
    IsPurelyInseparable F (adjoin F (S : Set E)) := by
  refine induction_on_adjoin_finset S (IsPurelyInseparable F ·) inferInstance fun L x hx hL ↦ ?_
  -- I don't know why, but `simp only at hL` is not regarded as an instance
  change IsPurelyInseparable F L at hL
  obtain ⟨n, y, h⟩ := h x hx
  haveI := expChar_of_injective_algebraMap (algebraMap F L).injective q
  replace h := (isPurelyInseparable_adjoin_simple_iff_pow_mem L E q).2 ⟨n, (algebraMap F L) y, h⟩
  exact IsPurelyInseparable.trans F L L⟮x⟯

/-- If `F` is of exponential characteristic `q`, then `F(S) / F` is a purely inseparable extension
if and only if for any `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`. -/
theorem isPurelyInseparable_adjoin_iff_pow_mem (q : ℕ) [hF : ExpChar F q] {S : Set E} :
    IsPurelyInseparable F (adjoin F S) ↔ ∀ x ∈ S, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [isPurelyInseparable_iff_pow_mem _ q]
  refine ⟨fun h x hx ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨n, y, h⟩ := h ⟨x, adjoin.mono F _ _ (Set.singleton_subset_iff.2 hx)
      (mem_adjoin_simple_self F x)⟩
    exact ⟨n, y, congr_arg (algebraMap _ E) h⟩
  obtain ⟨T, h1, h2⟩ := exists_finset_of_mem_adjoin x.2
  obtain ⟨n, y, hx⟩ := (isPurelyInseparable_iff_pow_mem F q).1
    (isPurelyInseparable_adjoin_finset_of_pow_mem F E q T fun x hx ↦ h x (h1 hx)) ⟨x, h2⟩
  refine ⟨n, y, ?_⟩
  apply_fun algebraMap _ E using (algebraMap _ E).injective
  exact show algebraMap F E y = x.1 ^ q ^ n from congr_arg (algebraMap _ E) hx

/-- A compositum of two purely inseparable extensions is purely inseparable. -/
instance isPurelyInseparable_sup (L1 L2 : IntermediateField F E)
    [h1 : IsPurelyInseparable F L1] [h2 : IsPurelyInseparable F L2] :
    IsPurelyInseparable F (L1 ⊔ L2 : IntermediateField F E) := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  rw [← adjoin_self F L1, isPurelyInseparable_adjoin_iff_pow_mem F E q] at h1
  rw [← adjoin_self F L2, isPurelyInseparable_adjoin_iff_pow_mem F E q] at h2
  rw [← adjoin_self F L1, ← adjoin_self F L2, ← gc.l_sup,
    isPurelyInseparable_adjoin_iff_pow_mem F E q]
  intro x h
  simp only [Set.sup_eq_union, Set.mem_union] at h
  rcases h with (h | h)
  exacts [h1 x h, h2 x h]

/-- A compositum of purely inseparable extensions is purely inseparable. -/
instance isPurelyInseparable_iSup {ι : Type*} {t : ι → IntermediateField F E}
    [h : ∀ i, IsPurelyInseparable F (t i)] :
    IsPurelyInseparable F (⨆ i, t i : IntermediateField F E) := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  rw [show (⨆ i, t i : IntermediateField F E) = (⨆ i, adjoin F (t i)) by simp_rw [adjoin_self],
    ← gc.l_iSup, isPurelyInseparable_adjoin_iff_pow_mem F E q]
  intro x hx
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  replace h := h i
  rw [← adjoin_self F (t i), isPurelyInseparable_adjoin_iff_pow_mem F E q] at h
  exact h x hi

-- TODO: move to suitable location
variable {F E} in
theorem extendScalars_adjoin {K : IntermediateField F E} {S : Set E} (h : K ≤ adjoin F S) :
    extendScalars h = adjoin K S := restrictScalars_injective F <| by
  rw [extendScalars_restrictScalars, restrictScalars_adjoin]
  exact le_antisymm (adjoin.mono F S _ <| Set.subset_union_right _ S) <| adjoin_le_iff.2 <|
    Set.union_subset h (subset_adjoin F S)

/-- If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, then
`F(S) = F(S ^ (q ^ n))` for any natural number `n`. -/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E) [IsSeparable F (adjoin F S)]
    (q : ℕ) [ExpChar F q] (n : ℕ) : adjoin F S = adjoin F ((fun x ↦ x ^ q ^ n) '' S) := by
  set L := adjoin F S
  set M := adjoin F ((fun x ↦ x ^ q ^ n) '' S)
  have hi : M ≤ L := by
    rw [adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact pow_mem (subset_adjoin F S hy) _
  letI := (inclusion hi).toAlgebra
  letI : Module M L := Algebra.toModule
  letI : SMul M L := Algebra.toSMul
  haveI : IsScalarTower F M L := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsSeparable M (extendScalars hi) := isSeparable_tower_top_of_isSeparable F M L
  haveI : IsPurelyInseparable M (extendScalars hi) := by
    haveI := expChar_of_injective_algebraMap (algebraMap F M).injective q
    rw [extendScalars_adjoin hi, isPurelyInseparable_adjoin_iff_pow_mem M _ q]
    exact fun x hx ↦ ⟨n, ⟨x ^ q ^ n, subset_adjoin F _ ⟨x, hx, rfl⟩⟩, rfl⟩
  simpa only [extendScalars_restrictScalars, restrictScalars_bot_eq_self] using congr_arg
    (restrictScalars F) (extendScalars hi).eq_bot_of_isPurelyInseparable_of_isSeparable

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F(S) = F(S ^ (q ^ n))` for any subset `S` of `E` and any natural number `n`. -/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' [IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] (n : ℕ) : adjoin F S = adjoin F ((fun x ↦ x ^ q ^ n) '' S) :=
  haveI := isSeparable_tower_bot_of_isSeparable F (adjoin F S) E
  adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q n

-- TODO: prove the converse when `F(S) / F` is finite
/-- If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, then
`F(S) = F(S ^ q)`. -/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable (S : Set E) [IsSeparable F (adjoin F S)]
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((fun x ↦ x ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q 1

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F(S) = F(S ^ q)` for any subset `S` of `E`. -/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable' [IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((fun x ↦ x ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E S q 1

end IntermediateField

variable {F E} in
/-- If `E / F` is an algebraic extension, `F` is separably closed,
then `E` is also separably closed. -/
theorem Algebra.IsAlgebraic.isSepClosed (halg : Algebra.IsAlgebraic F E)
    [IsSepClosed F] : IsSepClosed E := .of_exists_root E fun f hm hi hs ↦ by
  haveI := Fact.mk hi
  have hf := AdjoinRoot.minpoly_root hi.ne_zero
  rw [hm, inv_one, map_one, mul_one] at hf
  rw [← hf, ← isSeparable_adjoin_simple_iff_separable] at hs
  haveI := halg.isPurelyInseparable_of_isSepClosed
  have halg2 := IsSeparable.isAlgebraic E E⟮AdjoinRoot.root f⟯
  haveI := halg.trans halg2 |>.isPurelyInseparable_of_isSepClosed
  have hdeg := finSepDegree_mul_finSepDegree_of_isAlgebraic F _ _ halg2
  simp_rw [IsPurelyInseparable.finSepDegree_eq_one F _,
    finSepDegree_eq_finrank_of_isSeparable E _, one_mul,
    finrank_eq_one_iff (F := E) (E := AdjoinRoot f)] at hdeg
  obtain ⟨x, h⟩ := hdeg ▸ mem_adjoin_simple_self E (AdjoinRoot.root f)
  replace h := congr(aeval $h (minpoly E (AdjoinRoot.root f)))
  erw [minpoly.aeval, hf, aeval_algebraMap_apply,
    ← map_zero (f := algebraMap E (AdjoinRoot f))] at h
  exact ⟨x, (algebraMap E _).injective h⟩

/-- If `E` is an algebraic closure of `F`, then `F` is separably closed if and only if `E / F` is
purely inseparable. -/
theorem isSepClosed_iff_isPurelyInseparable_algebraicClosure [IsAlgClosure F E] :
    IsSepClosed F ↔ IsPurelyInseparable F E := by
  refine ⟨fun _ ↦ Normal.isAlgebraic'.isPurelyInseparable_of_isSepClosed, fun H ↦ ?_⟩
  haveI := IsAlgClosure.alg_closed F (K := E)
  rwa [← separableClosure.eq_bot_iff F E Normal.isAlgebraic',
    IsSepClosed.separableClosure_eq_bot_iff] at H

/-- If `E / F` is a separable extension, `E` is perfect, then `F` is also prefect. -/
theorem perfectField_of_isSeparable_of_perfectField_top [IsSeparable F E] [PerfectField E] :
    PerfectField F := by
  obtain ⟨p, hchar⟩ := CharP.exists F
  by_cases hp : p = 0
  · haveI := (CharP.charP_zero_iff_charZero F).1 (hp ▸ hchar)
    exact PerfectField.ofCharZero F
  haveI := NeZero.mk hp
  haveI := CharP.char_is_prime_of_pos F p
  haveI := charP_of_injective_algebraMap' F E p
  haveI := PerfectField.toPerfectRing E p
  haveI := PerfectRing.ofSurjective F p fun x ↦ by
    haveI : ExpChar F p := ExpChar.prime Fact.out
    obtain ⟨y, h⟩ := surjective_frobenius E p ((algebraMap F E) x)
    haveI := (isPurelyInseparable_adjoin_simple_iff_pow_mem F p (x := y)).2
      ⟨1, x, by rw [← h, pow_one, frobenius_def]⟩
    haveI := isSeparable_tower_bot_of_isSeparable F F⟮y⟯ E
    obtain ⟨z, h'⟩ := F⟮y⟯.eq_bot_of_isPurelyInseparable_of_isSeparable.le <|
      mem_adjoin_simple_self F y
    exact ⟨z, (algebraMap F E).injective (by rw [← h, ← h', frobenius_def, map_pow]; rfl)⟩
  exact PerfectRing.toPerfectField F p

/-- If `E` is an algebraic closure of `F`, then `F` is perfect if and only if `E / F` is
separable. -/
theorem perfectField_iff_isSeparable_algebraicClosure [IsAlgClosure F E] :
    PerfectField F ↔ IsSeparable F E :=
  ⟨fun _ ↦ IsSepClosure.separable, fun _ ↦ haveI : IsAlgClosed E := IsAlgClosure.alg_closed F;
    perfectField_of_isSeparable_of_perfectField_top F E⟩

namespace Field

/-- If `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to `Field.sepDegree F E`
as a natural number. This means that the cardinality of `Field.Emb F E` and the degree of
`(separableClosure F E) / F` are both finite or infinite, and when they are finite, they
coincide. -/
theorem finSepDegree_eq (halg : Algebra.IsAlgebraic F E) :
    finSepDegree F E = Cardinal.toNat (sepDegree F E) := by
  have h := finSepDegree_mul_finSepDegree_of_isAlgebraic F (separableClosure F E) E
    (halg.tower_top _) |>.symm
  haveI := separableClosure.isSeparable F E
  haveI := separableClosure.isPurelyInseparable F E halg
  rwa [finSepDegree_eq_finrank_of_isSeparable F (separableClosure F E),
    IsPurelyInseparable.finSepDegree_eq_one (separableClosure F E) E, mul_one] at h

/-- The (finite) separable degree multiply by the (finite) inseparable degree is equal
to the (finite) field extension degree. -/
theorem finSepDegree_mul_finInsepDegree : finSepDegree F E * finInsepDegree F E = finrank F E := by
  by_cases halg : Algebra.IsAlgebraic F E
  · have := congr_arg Cardinal.toNat (sepDegree_mul_insepDegree F E)
    rwa [Cardinal.toNat_mul, ← finSepDegree_eq F E halg] at this
  change _ * finrank (separableClosure F E) E = _
  rw [finrank_of_infinite_dimensional (K := F) (V := E) fun _ ↦
      halg (Algebra.IsAlgebraic.of_finite F E),
    finrank_of_infinite_dimensional (K := separableClosure F E) (V := E) fun _ ↦
      halg ((separableClosure.isAlgebraic F E).trans (Algebra.IsAlgebraic.of_finite _ E)),
    mul_zero]

end Field

namespace separableClosure

variable [Algebra E K] [IsScalarTower F E K]

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable and `K / E`
is separable, then `E` adjoin `separableClosure F K` is equal to `K`. It is a special case of
`separableClosure.adjoin_eq_of_isAlgebraic`, and is an intermediate result used to prove it. -/
lemma adjoin_eq_of_isPurelyInseparable_of_isSeparable [IsPurelyInseparable F E] [IsSeparable E K] :
    adjoin E (separableClosure F K : Set K) = ⊤ := top_unique fun x _ ↦ by
  set S := separableClosure F K
  set L := adjoin E (S : Set K)
  haveI := isSeparable_tower_top_of_isSeparable E L K
  let i : S →+* L := Subsemiring.inclusion fun x hx ↦ subset_adjoin E (S : Set K) hx
  letI : Algebra S L := i.toAlgebra
  letI : Module S L := Algebra.toModule
  letI : SMul S L := Algebra.toSMul
  haveI : IsScalarTower S L K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsPurelyInseparable S K := separableClosure.isPurelyInseparable F K <|
    (IsPurelyInseparable.isAlgebraic F E).trans (IsSeparable.isAlgebraic E K)
  haveI := IsPurelyInseparable.tower_top S L K
  obtain ⟨y, rfl⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable L K x
  exact y.2

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable, then
`E` adjoin `separableClosure F K` is equal to `separableClosure E K`. It is a special case of
`separableClosure.adjoin_eq_of_isAlgebraic`, and is an intermediate result used to prove it. -/
lemma adjoin_eq_of_isPurelyInseparable [IsPurelyInseparable F E] :
    adjoin E (separableClosure F K) = separableClosure E K := by
  set S := separableClosure E K
  have h := congr_arg IntermediateField.lift (adjoin_eq_of_isPurelyInseparable_of_isSeparable F E S)
  rw [lift_top, lift_adjoin] at h
  haveI : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← h, eq_map_of_separableClosure_eq_bot F (separableClosure_eq_bot E K)]
  rfl

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then
`E` adjoin `separableClosure F K` is equal to `separableClosure E K`. -/
theorem adjoin_eq_of_isAlgebraic (halg : Algebra.IsAlgebraic F E) :
    adjoin E (separableClosure F K) = separableClosure E K := by
  set S := separableClosure F E
  rw [eq_restrictScalars_of_isSeparable F S K]
  haveI : IsPurelyInseparable S E := separableClosure.isPurelyInseparable F E halg
  exact adjoin_eq_of_isPurelyInseparable S E K

end separableClosure
