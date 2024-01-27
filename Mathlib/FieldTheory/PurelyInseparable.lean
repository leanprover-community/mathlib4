/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.SeparableClosure

/-!

# Purely inseparable extension and relative perfect closure

This file contains basics about the purely inseparable extension and the relative perfect closure
of fields.

## Main definitions

- `IsPurelyInseparable`: typeclass for purely inseparable field extension: an algebraic extension
  `E / F` is purely inseparable if and only if the minimal polynomial of every element of `E ∖ F`
  is not separable.

- `perfectClosure`: the relative perfect closure of `F` in `E`, consists of the elements `x` of `E`
  such that there exists a natural number `n` such that `x ^ (ringExpChar F) ^ n` is contained in
  `F`, where `ringExpChar F` is the exponential characteristic of `F`. It is also the maximal
  purely inseparable subextension of `E / F` (`le_perfectClosure_iff`).

  This file only contains very basic results of the relative perfect closure.

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

- `isPurelyInseparable_iff_finSepDegree_eq_one`: an algebraic extension is purely inseparable
  if and only if it has finite separable degree (`Field.finSepDegree`) one.

  **TODO:** remove the algebraic assumption.

- `IsPurelyInseparable.normal`: a purely inseparable extension is normal.

- `separableClosure.isPurelyInseparable`: if `E / F` is algebraic, then `E` is purely inseparable
  over the separable closure of `F` in `E`.

- `separableClosure_le_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` contains
  the separable closure of `F` in `E` if and only if `E` is purely inseparable over it.

- `eq_separableClosure_iff`: if `E / F` is algebraic, then an intermediate field of `E / F` is equal
  to the separable closure of `F` in `E` if and only if it is separable over `F`, and `E`
  is purely inseparable over it.

- `le_perfectClosure_iff`: an intermediate field of `E / F` is contained in the relative perfect
  closure of `F` in `E` if and only if it is purely inseparable over `F`.

- `IsPurelyInseparable.injective_comp_algebraMap`: if `E / F` is purely inseparable, then for any
  reduced ring `L`, the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective.
  In particular, a purely inseparable field extension is an epimorphism in the category of fields.

- `IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`: if `F` is of exponential
  characteristic `q`, then `F(S) / F` is a purely inseparable extension if and only if for any
  `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`.

- `Field.finSepDegree_eq`: if `E / F` is algebraic, then the `Field.finSepDegree F E` is equal to
  `Field.sepDegree F E` as a natural number. This means that the cardinality of `Field.Emb F E`
  and the degree of `(separableClosure F E) / F` are both finite or infinite, and when they are
  finite, they coincide.

- `finSepDegree_mul_finInsepDegree`: the finite separable degree multiply by the finite
  inseparable degree is equal to the (finite) field extension degree.

- `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`: the separable degrees satisfy the
  tower law: $[E:F]_s [K:E]_s = [K:F]_s$.

## Tags

separable degree, degree, separable closure, purely inseparable

## TODO

- `IsPurelyInseparable.of_injective_comp_algebraMap`: if `L` is an algebraically closed field
  containing `E`, such that the map `(E →+* L) → (F →+* L)` induced by `algebraMap F E` is
  injective, then `E / F` is purely inseparable. As a corollary, epimorphisms in the category of
  fields must be purely inseparable extensions. Need to use the fact that `Emb F E` is infinite
  (or just not a singleton) when `E / F` is (purely) transcendental.

- Restate some intermediate result in terms of linearly disjointness.

- Prove that the inseparable degrees satisfy the tower law: $[E:F]_i [K:E]_i = [K:F]_i$.
  Probably an argument using linearly disjointness is needed.

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

/-- If `E / F` is purely inseparable, then the separable closure of `F` in `E` is
equal to `F`. -/
theorem separableClosure.eq_bot_of_isPurelyInseparable [IsPurelyInseparable F E] :
    separableClosure F E = ⊥ :=
  bot_unique fun x h ↦ IsPurelyInseparable.inseparable F x (mem_separableClosure_iff.1 h)

variable {F E} in
/-- If `E / F` is an algebraic extension, then the separable closure of `F` in `E` is
equal to `F` if and only if `E / F` is purely inseparable. -/
theorem separableClosure.eq_bot_iff (halg : Algebra.IsAlgebraic F E) :
    separableClosure F E = ⊥ ↔ IsPurelyInseparable F E :=
  ⟨fun h ↦ isPurelyInseparable_iff.2 fun x ↦ ⟨(halg x).isIntegral, fun hs ↦ by
    simpa only [h] using mem_separableClosure_iff.2 hs⟩, fun _ ↦ eq_bot_of_isPurelyInseparable F E⟩

instance isPurelyInseparable_self : IsPurelyInseparable F F :=
  ⟨fun _ ↦ isIntegral_algebraMap, fun x _ ↦ ⟨x, rfl⟩⟩

variable {E}

/-- A field extension `E / F` of exponential characteristic `q` is purely inseparable
if and only if for every element `x` of `E`, there exists a natural number `n` such that
`x ^ (q ^ n)` is contained in `F`. -/
theorem isPurelyInseparable_iff_pow_mem (q : ℕ) [ExpChar F q] :
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
  (isPurelyInseparable_iff_pow_mem F q).1 ‹_› x

end IsPurelyInseparable

section perfectClosure

/-- The relative perfect closure of `F` in `E`, consists of the elements `x` of `E` such that there
exists a natural number `n` such that `x ^ (ringExpChar F) ^ n` is contained in `F`, where
`ringExpChar F` is the exponential characteristic of `F`. It is also the maximal purely inseparable
subextension of `E / F` (`le_perfectClosure_iff`). -/
def perfectClosure : IntermediateField F E where
  carrier := {x : E | ∃ n : ℕ, x ^ (ringExpChar F) ^ n ∈ (algebraMap F E).range}
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    have := expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
    rw [add_pow_expChar_pow, pow_add, pow_mul, mul_comm (_ ^ n), pow_mul]
    exact add_mem (pow_mem hx _) (pow_mem hy _)
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    use n + m
    rw [mul_pow, pow_add, pow_mul, mul_comm (_ ^ n), pow_mul]
    exact mul_mem (pow_mem hx _) (pow_mem hy _)
  inv_mem' := by
    rintro x ⟨n, hx⟩
    use n; rw [inv_pow]
    apply inv_mem (id hx : _ ∈ (⊥ : IntermediateField F E))
  algebraMap_mem' := fun x ↦ ⟨0, by rw [pow_zero, pow_one]; exact ⟨x, rfl⟩⟩

variable {F E}

theorem mem_perfectClosure_iff {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ (ringExpChar F) ^ n ∈ (algebraMap F E).range := Iff.rfl

theorem mem_perfectClosure_iff_pow_mem (q : ℕ) [ExpChar F q] {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [mem_perfectClosure_iff, ringExpChar.eq F q]

/-- An element is contained in the relative perfect closure if and only if its mininal polynomial
has separable degree one. -/
theorem mem_perfectClosure_iff_natSepDegree_eq_one {x : E} :
    x ∈ perfectClosure F E ↔ (minpoly F x).natSepDegree = 1 := by
  rw [mem_perfectClosure_iff, minpoly.natSepDegree_eq_one_iff_pow_mem (ringExpChar F)]

/-- A field extension `E / F` is purely inseparable if and only if the relative perfect closure of
`F` in `E` is equal to `E`. -/
theorem isPurelyInseparable_iff_perfectClosure_eq_top :
    IsPurelyInseparable F E ↔ perfectClosure F E = ⊤ := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact ⟨fun H ↦ top_unique fun x _ ↦ H x, fun H _ ↦ H.ge trivial⟩

variable (F E)

/-- The relative perfect closure of `F` in `E` is purely inseparable over `F`. -/
instance perfectClosure.isPurelyInseparable : IsPurelyInseparable F (perfectClosure F E) := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  exact fun ⟨_, n, y, h⟩ ↦ ⟨n, y, (algebraMap _ E).injective h⟩

/-- The relative perfect closure of `F` in `E` is algebraic over `F`. -/
theorem perfectClosure.isAlgebraic : Algebra.IsAlgebraic F (perfectClosure F E) :=
  IsPurelyInseparable.isAlgebraic F _

/-- If `E / F` is separable, then the perfect closure of `F` in `E` is equal to `F`. Note that
  the converse is not necessarily true (see ...), even when `E / F` is algebraic. -/
theorem perfectClosure.eq_bot_of_isSeparable [IsSeparable F E] : perfectClosure F E = ⊥ :=
  haveI := isSeparable_tower_bot_of_isSeparable F (perfectClosure F E) E
  eq_bot_of_isPurelyInseparable_of_isSeparable _

/-- An intermediate field of `E / F` is contained in the relative perfect closure of `F` in `E`
if it is purely inseparable over `F`. -/
theorem le_perfectClosure (L : IntermediateField F E) [h : IsPurelyInseparable F L] :
    L ≤ perfectClosure F E := by
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)] at h
  intro x hx
  obtain ⟨n, y, hy⟩ := h ⟨x, hx⟩
  exact ⟨n, y, congr_arg (algebraMap L E) hy⟩

/-- An intermediate field of `E / F` is contained in the relative perfect closure of `F` in `E`
if and only if it is purely inseparable over `F`. -/
theorem le_perfectClosure_iff (L : IntermediateField F E) :
    L ≤ perfectClosure F E ↔ IsPurelyInseparable F L := by
  refine ⟨fun h ↦ ?_, fun _ ↦ le_perfectClosure F E L⟩
  rw [isPurelyInseparable_iff_pow_mem F (ringExpChar F)]
  intro x
  obtain ⟨n, y, hy⟩ := h x.2
  exact ⟨n, y, (algebraMap L E).injective hy⟩

theorem separableClosure_inf_perfectClosure : separableClosure F E ⊓ perfectClosure F E = ⊥ :=
  haveI := (le_separableClosure_iff F E _).mp (inf_le_left (b := perfectClosure F E))
  haveI := (le_perfectClosure_iff F E _).mp (inf_le_right (a := separableClosure F E))
  IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable _

variable {F E K}

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained in
`perfectClosure F K` if and only if `x` is contained in `perfectClosure F E`. -/
theorem map_mem_perfectClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ perfectClosure F K ↔ x ∈ perfectClosure F E := by
  simp_rw [mem_perfectClosure_iff]
  refine ⟨fun ⟨n, y, h⟩ ↦ ⟨n, y, ?_⟩, fun ⟨n, y, h⟩ ↦ ⟨n, y, ?_⟩⟩
  · apply_fun i using i.injective
    rwa [AlgHom.commutes, map_pow]
  simpa only [AlgHom.commutes, map_pow] using congr_arg i h

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of `perfectClosure F K`
under the map `i` is equal to `perfectClosure F E`. -/
theorem perfectClosure.comap_eq_of_algHom (i : E →ₐ[F] K) :
    (perfectClosure F K).comap i = perfectClosure F E := by
  ext x
  exact map_mem_perfectClosure_iff i

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `perfectClosure F E`
under the map `i` is contained in `perfectClosure F K`. -/
theorem perfectClosure.map_le_of_algHom (i : E →ₐ[F] K) :
    (perfectClosure F E).map i ≤ perfectClosure F K :=
  map_le_iff_le_comap.mpr (perfectClosure.comap_eq_of_algHom i).ge

/-- If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `perfectClosure F E`
under the map `i` is equal to in `perfectClosure F K`. -/
theorem perfectClosure.map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (perfectClosure F E).map i.toAlgHom = perfectClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm (fun x hx ↦ ⟨i.symm x,
    (map_mem_perfectClosure_iff i.symm.toAlgHom).2 hx, i.right_inv x⟩)

/-- If `E` and `K` are isomorphic as `F`-algebras, then `perfectClosure F E` and
`perfectClosure F K` are also isomorphic as `F`-algebras. -/
def perfectClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    perfectClosure F E ≃ₐ[F] perfectClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias AlgEquiv.perfectClosure := perfectClosure.algEquivOfAlgEquiv

end perfectClosure

section IsPurelyInseparable

/-- If `K / E / F` is a field extension tower such that `K / F` is purely inseparable,
then `E / F` is also purely inseparable. -/
theorem IsPurelyInseparable.tower_bot [Algebra E K] [IsScalarTower F E K]
    [IsPurelyInseparable F K] : IsPurelyInseparable F E := by
  refine ⟨fun x ↦ (isIntegral F (algebraMap E K x)).tower_bot_of_field, fun x h ↦ ?_⟩
  rw [← minpoly.algebraMap_eq (algebraMap E K).injective] at h
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

variable (E)

-- TODO: remove `halg` assumption
variable {F E} in
/-- If an algebraic extension has finite separable degree one, then it is purely inseparable. -/
theorem isPurelyInseparable_of_finSepDegree_eq_one (halg : Algebra.IsAlgebraic F E)
    (hdeg : finSepDegree F E = 1) : IsPurelyInseparable F E := by
  rw [isPurelyInseparable_iff]
  refine fun x ↦ ⟨(halg x).isIntegral, fun hsep ↦ ?_⟩
  have := finSepDegree_mul_finSepDegree_of_isAlgebraic F F⟮x⟯ E <| halg.tower_top F⟮x⟯
  rw [hdeg, mul_eq_one, (finSepDegree_adjoin_simple_eq_finrank_iff F E x (halg x)).2 hsep,
    IntermediateField.finrank_eq_one_iff] at this
  simpa only [this.1] using mem_adjoin_simple_self F x

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
  cases hF
  · rwa [one_pow, pow_one] at heq
  nontriviality L
  haveI := charP_of_injective_ringHom (f.comp (algebraMap F E)).injective q
  haveI := Fact.mk ‹q.Prime›
  simp_rw [map_pow, ← iterate_frobenius] at heq
  exact (frobenius_inj L q).iterate n heq

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

-- TODO: remove `halg` assumption
/-- An algebraic extension is purely inseparable if and only if it has finite separable
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

/-- If `E / F` is algebraic, then `E` is purely inseparable over the
separable closure of `F` in `E`. -/
theorem separableClosure.isPurelyInseparable (halg : Algebra.IsAlgebraic F E) :
    IsPurelyInseparable (separableClosure F E) E := isPurelyInseparable_iff.2 fun x ↦ by
  set L := separableClosure F E
  refine ⟨(halg.tower_top L x).isIntegral, fun h ↦ ?_⟩
  haveI := (isSeparable_adjoin_simple_iff_separable L E).2 h
  haveI : IsSeparable F (restrictScalars F L⟮x⟯) := IsSeparable.trans F L L⟮x⟯
  have hx : x ∈ restrictScalars F L⟮x⟯ := mem_adjoin_simple_self _ x
  exact ⟨⟨x, mem_separableClosure_iff.2 <| separable_of_mem_isSeparable F E hx⟩, rfl⟩

/-- An intermediate field of `E / F` contains the separable closure of `F` in `E`
if `E` is purely inseparable over it. -/
theorem separableClosure_le (L : IntermediateField F E)
    [h : IsPurelyInseparable L E] : separableClosure F E ≤ L := fun x hx ↦ by
  obtain ⟨y, rfl⟩ := h.inseparable' _ <| (mem_separableClosure_iff.1 hx).map_minpoly L
  exact y.2

/-- If `E / F` is algebraic, then an intermediate field of `E / F` contains the
separable closure of `F` in `E` if and only if `E` is purely inseparable over it. -/
theorem separableClosure_le_iff (halg : Algebra.IsAlgebraic F E) (L : IntermediateField F E) :
    separableClosure F E ≤ L ↔ IsPurelyInseparable L E := by
  refine ⟨fun h ↦ ?_, fun _ ↦ separableClosure_le F E L⟩
  haveI := separableClosure.isPurelyInseparable F E halg
  letI := (inclusion h).toAlgebra
  letI : SMul (separableClosure F E) L := Algebra.toSMul
  haveI : IsScalarTower (separableClosure F E) L E := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  exact IsPurelyInseparable.tower_top (separableClosure F E) L E

/-- If an intermediate field of `E / F` is separable over `F`, and `E` is purely inseparable
over it, then it is equal to the separable closure of `F` in `E`. -/
theorem eq_separableClosure (L : IntermediateField F E)
    [IsSeparable F L] [IsPurelyInseparable L E] : L = separableClosure F E :=
  le_antisymm (le_separableClosure F E L) (separableClosure_le F E L)

/-- If `E / F` is algebraic, then an intermediate field of `E / F` is equal to the separable closure
of `F` in `E` if and only if it is separable over `F`, and `E` is purely inseparable
over it. -/
theorem eq_separableClosure_iff (halg : Algebra.IsAlgebraic F E) (L : IntermediateField F E) :
    L = separableClosure F E ↔ IsSeparable F L ∧ IsPurelyInseparable L E :=
  ⟨by rintro rfl; exact ⟨separableClosure.isSeparable F E,
    separableClosure.isPurelyInseparable F E halg⟩, fun ⟨_, _⟩ ↦ eq_separableClosure F E L⟩

-- TODO: prove it
set_option linter.unusedVariables false in
/-- If `L` is an algebraically closed field containing `E`, such that the map
`(E →+* L) → (F →+* L)` induced by `algebraMap F E` is injective, then `E / F` is
purely inseparable. As a corollary, epimorphisms in the category of fields must be
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
  rw [← le_perfectClosure_iff, adjoin_simple_le_iff, mem_perfectClosure_iff_natSepDegree_eq_one]

/-- If `F` is of exponential characteristic `q`, then `F⟮x⟯ / F` is a purely inseparable extension
if and only if `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`. -/
theorem isPurelyInseparable_adjoin_simple_iff_pow_mem (q : ℕ) [hF : ExpChar F q] {x : E} :
    IsPurelyInseparable F F⟮x⟯ ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [← le_perfectClosure_iff, adjoin_simple_le_iff, mem_perfectClosure_iff_pow_mem q]

/-- If `F` is of exponential characteristic `q`, then `F(S) / F` is a purely inseparable extension
if and only if for any `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`. -/
theorem isPurelyInseparable_adjoin_iff_pow_mem (q : ℕ) [hF : ExpChar F q] {S : Set E} :
    IsPurelyInseparable F (adjoin F S) ↔ ∀ x ∈ S, ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  simp_rw [← le_perfectClosure_iff, adjoin_le_iff, ← mem_perfectClosure_iff_pow_mem q]
  rfl

/-- A compositum of two purely inseparable extensions is purely inseparable. -/
instance isPurelyInseparable_sup (L1 L2 : IntermediateField F E)
    [h1 : IsPurelyInseparable F L1] [h2 : IsPurelyInseparable F L2] :
    IsPurelyInseparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_perfectClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/-- A compositum of purely inseparable extensions is purely inseparable. -/
instance isPurelyInseparable_iSup {ι : Type*} {t : ι → IntermediateField F E}
    [h : ∀ i, IsPurelyInseparable F (t i)] :
    IsPurelyInseparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_perfectClosure_iff] at h ⊢
  exact iSup_le h

/-- If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, then
`F(S) = F(S ^ (q ^ n))` for any natural number `n`. -/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E) [IsSeparable F (adjoin F S)]
    (q : ℕ) [ExpChar F q] (n : ℕ) : adjoin F S = adjoin F ((· ^ q ^ n) '' S) := by
  set L := adjoin F S
  set M := adjoin F ((· ^ q ^ n) '' S)
  have hi : M ≤ L := by
    rw [adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact pow_mem (subset_adjoin F S hy) _
  letI := (inclusion hi).toAlgebra
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
    (q : ℕ) [ExpChar F q] (n : ℕ) : adjoin F S = adjoin F ((· ^ q ^ n) '' S) :=
  haveI := isSeparable_tower_bot_of_isSeparable F (adjoin F S) E
  adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q n

-- TODO: prove the converse when `F(S) / F` is finite
/-- If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, then
`F(S) = F(S ^ q)`. -/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable (S : Set E) [IsSeparable F (adjoin F S)]
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q 1

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F(S) = F(S ^ q)` for any subset `S` of `E`. -/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable' [IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E S q 1

end IntermediateField

section

variable (q n : ℕ) [hF : ExpChar F q] {ι : Type*} {v : ι → E} {F E}

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is a family
of elements of `E` which `F`-linearly spans `E`, then `{ u_i ^ (q ^ n) }` also `F`-linearly spans
`E` for any natural number `n`. -/
theorem Field.span_map_pow_expChar_pow_eq_top_of_isSeparable [IsSeparable F E]
    (h : Submodule.span F (Set.range v) = ⊤) :
    Submodule.span F (Set.range (v · ^ q ^ n)) = ⊤ := by
  erw [← Algebra.top_toSubmodule, ← top_toSubalgebra, ← adjoin_univ,
    adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E _ q n,
    adjoin_algebraic_toSubalgebra fun x _ ↦ IsSeparable.isAlgebraic F E x,
    Set.image_univ, Algebra.adjoin_eq_span, (powMonoidHom _).mrange.closure_eq]
  refine (Submodule.span_mono <| Set.range_comp_subset_range _ _).antisymm (Submodule.span_le.2 ?_)
  rw [Set.range_comp, ← Set.image_univ]
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective q
  apply h ▸ Submodule.image_span_subset_span (LinearMap.iterateFrobenius F E q n) _

/-- If `E / F` is a finite separable extension of exponential characteristic `q`, if `{ u_i }` is a
family of elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ n) }` is also
`F`-linearly independent for any natural number `n`. A special case of
`LinearIndependent.map_pow_expChar_pow_of_isSeparable`
and is an intermediate result used to prove it. -/
private theorem LinearIndependent.map_pow_expChar_pow_of_fd_isSeparable
    [FiniteDimensional F E] [IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  have h' := h.coe_range
  let ι' := h'.extend (Set.range v).subset_univ
  let b : Basis ι' F E := Basis.extend h'
  letI : Fintype ι' := fintypeBasisIndex b
  have H := linearIndependent_of_top_le_span_of_card_eq_finrank
    (span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge
    (finrank_eq_card_basis b).symm
  let f (i : ι) : ι' := ⟨v i, h'.subset_extend _ ⟨i, rfl⟩⟩
  convert H.comp f fun _ _ heq ↦ h.injective (by simpa only [Subtype.mk.injEq] using heq)
  simp_rw [Function.comp_apply, Basis.extend_apply_self]

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is a
family of elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ n) }` is also
`F`-linearly independent for any natural number `n`. -/
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable [IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  have halg := IsSeparable.isAlgebraic F E
  rw [linearIndependent_iff_finset_linearIndependent] at h ⊢
  intro s
  let E' := adjoin F (s.image v : Set E)
  haveI : FiniteDimensional F E' := finiteDimensional_adjoin fun x _ ↦ (halg x).isIntegral
  haveI : IsSeparable F E' := isSeparable_tower_bot_of_isSeparable F E' E
  let v' (i : s) : E' := ⟨v i.1, subset_adjoin F _ (Finset.mem_image.2 ⟨i.1, i.2, rfl⟩)⟩
  have h' : LinearIndependent F v' := (h s).of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_fd_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

/-- If `E / F` is a field extension of exponential characteristic `q`, if `{ u_i }` is a
family of separable elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ n) }`
is also `F`-linearly independent for any natural number `n`. -/
theorem LinearIndependent.map_pow_expChar_pow_of_separable
    (hsep : ∀ i : ι, (minpoly F (v i)).Separable)
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  let E' := adjoin F (Set.range v)
  haveI : IsSeparable F E' := (isSeparable_adjoin_iff_separable F _).2 <| by
    rintro _ ⟨y, rfl⟩; exact hsep y
  let v' (i : ι) : E' := ⟨v i, subset_adjoin F _ ⟨i, rfl⟩⟩
  have h' : LinearIndependent F v' := h.of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is an
`F`-basis of `E`, then `{ u_i ^ (q ^ n) }` is also an `F`-basis of `E`
for any natural number `n`. -/
def Basis.mapPowExpCharPowOfIsSeparable [IsSeparable F E]
    (b : Basis ι F E) : Basis ι F E :=
  Basis.mk (b.linearIndependent.map_pow_expChar_pow_of_isSeparable q n)
    (span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge

end

/-- If `E` is an algebraic closure of `F`, then `F` is separably closed if and only if `E / F` is
purely inseparable. -/
theorem isSepClosed_iff_isPurelyInseparable_algebraicClosure [IsAlgClosure F E] :
    IsSepClosed F ↔ IsPurelyInseparable F E :=
  ⟨fun _ ↦ IsAlgClosure.algebraic.isPurelyInseparable_of_isSepClosed, fun H ↦ by
    haveI := IsAlgClosure.alg_closed F (K := E)
    rwa [← separableClosure.eq_bot_iff IsAlgClosure.algebraic,
      IsSepClosed.separableClosure_eq_bot_iff] at H⟩

variable {F E} in
/-- If `E / F` is an algebraic extension, `F` is separably closed,
then `E` is also separably closed. -/
theorem Algebra.IsAlgebraic.isSepClosed (halg : Algebra.IsAlgebraic F E)
    [IsSepClosed F] : IsSepClosed E :=
  haveI := isPurelyInseparable_of_isSepClosed (halg.trans <| AlgebraicClosure.isAlgebraic E)
  (isSepClosed_iff_isPurelyInseparable_algebraicClosure E _).mpr
    (IsPurelyInseparable.tower_top F E <| AlgebraicClosure E)

theorem perfectField_of_perfectClosure_eq_bot [h : PerfectField E] (eq : perfectClosure F E = ⊥) :
    PerfectField F := by
  obtain _ | ⟨p, _, _⟩ := CharP.exists' F
  · exact PerfectField.ofCharZero F
  haveI := charP_of_injective_algebraMap' F E p
  haveI := PerfectField.toPerfectRing E p
  haveI := PerfectRing.ofSurjective F p fun x ↦ by
    obtain ⟨y, h⟩ := surjective_frobenius E p (algebraMap F E x)
    have : y ∈ perfectClosure F E := ⟨1, x, by rw [← h, pow_one, frobenius_def, ringExpChar.eq F p]⟩
    obtain ⟨z, rfl⟩ := eq ▸ this
    refine ⟨z, (algebraMap F E).injective (by erw [RingHom.map_frobenius, h])⟩
  exact PerfectRing.toPerfectField F p

/-- If `E / F` is a separable extension, `E` is perfect, then `F` is also prefect. -/
theorem perfectField_of_isSeparable_of_perfectField_top [IsSeparable F E] [PerfectField E] :
    PerfectField F :=
  perfectField_of_perfectClosure_eq_bot F E (perfectClosure.eq_bot_of_isSeparable F E)

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

/-- The finite separable degree multiply by the finite inseparable degree is equal
to the (finite) field extension degree. -/
theorem finSepDegree_mul_finInsepDegree : finSepDegree F E * finInsepDegree F E = finrank F E := by
  by_cases halg : Algebra.IsAlgebraic F E
  · have := congr_arg Cardinal.toNat (sepDegree_mul_insepDegree F E)
    rwa [Cardinal.toNat_mul, ← finSepDegree_eq F E halg] at this
  rw [finInsepDegree, finrank_of_infinite_dimensional (K := F) (V := E) fun _ ↦
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
  have h := congr_arg lift (adjoin_eq_of_isPurelyInseparable_of_isSeparable F E S)
  rw [lift_top, lift_adjoin] at h
  haveI : IsScalarTower F S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← h, ← map_eq_of_separableClosure_eq_bot F (separableClosure_eq_bot E K)]
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

section TowerLaw

variable [Algebra E K] [IsScalarTower F E K]

variable {F K} in
/-- If `K / E / F` is a field extension tower such that `E / F` is purely inseparable,
if `{ u_i }` is a family of separable elements of `K` which is `F`-linearly independent,
then it is also `E`-linearly independent. -/
theorem LinearIndependent.map_of_isPurelyInseparable_of_separable [IsPurelyInseparable F E]
    {ι : Type*} {v : ι → K} (hsep : ∀ i : ι, (minpoly F (v i)).Separable)
    (h : LinearIndependent F v) : LinearIndependent E v := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  haveI := expChar_of_injective_algebraMap (algebraMap F K).injective q
  refine linearIndependent_iff.mpr fun l hl ↦ Finsupp.ext fun i ↦ ?_
  choose f hf using fun i ↦ (isPurelyInseparable_iff_pow_mem F q).1 ‹_› (l i)
  let n := l.support.sup f
  replace hf (i : ι) : l i ^ q ^ n ∈ (algebraMap F E).range := by
    by_cases hs : i ∈ l.support
    · convert pow_mem (hf i) (q ^ (n - f i)) using 1
      rw [← pow_mul, ← pow_add, Nat.add_sub_of_le (Finset.le_sup hs)]
    exact ⟨0, by rw [map_zero, Finsupp.not_mem_support_iff.1 hs, zero_pow (expChar_pow_pos F q n)]⟩
  choose lF hlF using hf
  let lF₀ := Finsupp.onFinset l.support lF fun i ↦ by
    contrapose!
    refine fun hs ↦ (injective_iff_map_eq_zero _).mp (algebraMap F E).injective _ ?_
    rw [hlF, Finsupp.not_mem_support_iff.1 hs, zero_pow (expChar_pow_pos F q n)]
  replace h := linearIndependent_iff.1 (h.map_pow_expChar_pow_of_separable q n hsep) lF₀ <| by
    replace hl := congr($hl ^ q ^ n)
    rw [Finsupp.total_apply, Finsupp.sum, sum_pow_char_pow, zero_pow (expChar_pow_pos F q n)] at hl
    rw [← hl, Finsupp.total_apply, Finsupp.onFinset_sum _ (fun _ ↦ by exact zero_smul _ _)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp_rw [Algebra.smul_def, mul_pow, IsScalarTower.algebraMap_apply F E K, hlF, map_pow]
  refine pow_eq_zero ((hlF _).symm.trans ?_)
  convert map_zero _
  exact congr($h i)

namespace Field

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable and `K / E`
is separable, then the separable degree of `K / F` is equal to the degree of `K / E`.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
lemma sepDegree_eq_of_isPurelyInseparable_of_isSeparable
    [IsPurelyInseparable F E] [IsSeparable E K] :
    sepDegree F K = Module.rank E K := by
  let S := separableClosure F K
  have h := S.adjoin_rank_le_of_isAlgebraic_right E (IsSeparable.isAlgebraic _ _)
  rw [separableClosure.adjoin_eq_of_isPurelyInseparable_of_isSeparable F E K, rank_top'] at h
  obtain ⟨ι, ⟨b⟩⟩ := Basis.exists_basis F S
  exact h.antisymm' (b.mk_eq_rank'' ▸ (b.linearIndependent.map' S.val.toLinearMap
    (LinearMap.ker_eq_bot_of_injective S.val.injective) |>.map_of_isPurelyInseparable_of_separable E
      (fun i ↦ by simpa only [minpoly_eq] using IsSeparable.separable F (b i)) |>.cardinal_le_rank))

/-- If `K / E / F` is a field extension tower, such that `E / F` is separable,
then $[E:F] [K:E]_s = [K:F]_s$.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
lemma lift_rank_mul_lift_sepDegree_of_isSeparable [IsSeparable F E] :
    Cardinal.lift.{w} (Module.rank F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  rw [sepDegree, sepDegree, separableClosure.eq_restrictScalars_of_isSeparable F E K]
  exact lift_rank_mul_lift_rank F E (separableClosure E K)

/-- The same-universe version of `Field.lift_rank_mul_lift_sepDegree_of_isSeparable`. -/
lemma rank_mul_sepDegree_of_isSeparable (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] [IsSeparable F E] :
    Module.rank F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_rank_mul_lift_sepDegree_of_isSeparable F E K

/-- If `K / E / F` is a field extension tower, such that `E / F` is purely inseparable,
then $[K:F]_s = [K:E]_s$.
It is a special case of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`, and is an
intermediate result used to prove it. -/
lemma sepDegree_eq_of_isPurelyInseparable [IsPurelyInseparable F E] :
    sepDegree F K = sepDegree E K := by
  convert sepDegree_eq_of_isPurelyInseparable_of_isSeparable F E (separableClosure E K)
  haveI : IsScalarTower F (separableClosure E K) K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [sepDegree, ← separableClosure.map_eq_of_separableClosure_eq_bot F
    (separableClosure.separableClosure_eq_bot E K)]
  exact (separableClosure F (separableClosure E K)).equivMap
    (IsScalarTower.toAlgHom F (separableClosure E K) K) |>.symm.toLinearEquiv.rank_eq

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then their
separable degrees satisfy the tower law: $[E:F]_s [K:E]_s = [K:F]_s$. -/
theorem lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic
    (halg : Algebra.IsAlgebraic F E) :
    Cardinal.lift.{w} (sepDegree F E) * Cardinal.lift.{v} (sepDegree E K) =
    Cardinal.lift.{v} (sepDegree F K) := by
  have h := lift_rank_mul_lift_sepDegree_of_isSeparable F (separableClosure F E) K
  haveI := separableClosure.isPurelyInseparable F E halg
  rwa [sepDegree_eq_of_isPurelyInseparable (separableClosure F E) E K] at h

/-- The same-universe version of `Field.lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic`. -/
theorem sepDegree_mul_sepDegree_of_isAlgebraic (K : Type v) [Field K] [Algebra F K]
    [Algebra E K] [IsScalarTower F E K] (halg : Algebra.IsAlgebraic F E) :
    sepDegree F E * sepDegree E K = sepDegree F K := by
  simpa only [Cardinal.lift_id] using lift_sepDegree_mul_lift_sepDegree_of_isAlgebraic F E K halg

end Field

end TowerLaw
