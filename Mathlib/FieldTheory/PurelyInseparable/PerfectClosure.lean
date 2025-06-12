/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!

# Basic results about relative perfect closure

This file contains basic results about relative perfect closures.

## Main definitions

- `perfectClosure`: the relative perfect closure of `F` in `E`, it consists of the elements
  `x` of `E` such that there exists a natural number `n` such that `x ^ (ringExpChar F) ^ n`
  is contained in `F`, where `ringExpChar F` is the exponential characteristic of `F`.
  It is also the maximal purely inseparable subextension of `E / F` (`le_perfectClosure_iff`).

## Main results

- `le_perfectClosure_iff`: an intermediate field of `E / F` is contained in the relative perfect
  closure of `F` in `E` if and only if it is purely inseparable over `F`.

- `perfectClosure.perfectRing`, `perfectClosure.perfectField`: if `E` is a perfect field, then the
  (relative) perfect closure `perfectClosure F E` is perfect.

- `IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem`: if `F` is of exponential
  characteristic `q`, then `F(S) / F` is a purely inseparable extension if and only if for any
  `x ∈ S`, `x ^ (q ^ n)` is contained in `F` for some `n : ℕ`.

## Tags

separable degree, degree, separable closure, purely inseparable

-/

open IntermediateField

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable (K : Type w) [Field K] [Algebra F K]

section perfectClosure

/-- The relative perfect closure of `F` in `E`, consists of the elements `x` of `E` such that there
exists a natural number `n` such that `x ^ (ringExpChar F) ^ n` is contained in `F`, where
`ringExpChar F` is the exponential characteristic of `F`. It is also the maximal purely inseparable
subextension of `E / F` (`le_perfectClosure_iff`). -/
@[stacks 09HH]
def perfectClosure : IntermediateField F E where
  __ := have := expChar_of_injective_algebraMap (algebraMap F E).injective (ringExpChar F)
    Subalgebra.perfectClosure F E (ringExpChar F)
  inv_mem' := by
    rintro x ⟨n, hx⟩
    use n; rw [inv_pow]
    apply inv_mem (id hx : _ ∈ (⊥ : IntermediateField F E))

variable {F E}

theorem mem_perfectClosure_iff {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ (ringExpChar F) ^ n ∈ (algebraMap F E).range := Iff.rfl

theorem mem_perfectClosure_iff_pow_mem (q : ℕ) [ExpChar F q] {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  rw [mem_perfectClosure_iff, ringExpChar.eq F q]

/-- An element is contained in the relative perfect closure if and only if its minimal polynomial
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
instance perfectClosure.isAlgebraic : Algebra.IsAlgebraic F (perfectClosure F E) :=
  IsPurelyInseparable.isAlgebraic F _

/-- If `E / F` is separable, then the perfect closure of `F` in `E` is equal to `F`. Note that
  the converse is not necessarily true (see https://math.stackexchange.com/a/3009197)
  even when `E / F` is algebraic. -/
theorem perfectClosure.eq_bot_of_isSeparable [Algebra.IsSeparable F E] : perfectClosure F E = ⊥ :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (perfectClosure F E) E
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
  refine ⟨fun h ↦ (isPurelyInseparable_iff_pow_mem F (ringExpChar F)).2 fun x ↦ ?_,
    fun _ ↦ le_perfectClosure F E L⟩
  obtain ⟨n, y, hy⟩ := h x.2
  exact ⟨n, y, (algebraMap L E).injective hy⟩

theorem separableClosure_inf_perfectClosure : separableClosure F E ⊓ perfectClosure F E = ⊥ :=
  haveI := (le_separableClosure_iff F E _).mp (inf_le_left (b := perfectClosure F E))
  haveI := (le_perfectClosure_iff F E _).mp (inf_le_right (a := separableClosure F E))
  eq_bot_of_isPurelyInseparable_of_isSeparable _

section map

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

noncomputable
alias AlgEquiv.perfectClosure := perfectClosure.algEquivOfAlgEquiv

end map

/-- If `E` is a perfect field of exponential characteristic `p`, then the (relative) perfect closure
`perfectClosure F E` is perfect. -/
instance perfectClosure.perfectRing (p : ℕ) [ExpChar E p]
    [PerfectRing E p] : PerfectRing (perfectClosure F E) p := .ofSurjective _ p fun x ↦ by
  haveI := RingHom.expChar _ (algebraMap F E).injective p
  obtain ⟨x', hx⟩ := surjective_frobenius E p x.1
  obtain ⟨n, y, hy⟩ := (mem_perfectClosure_iff_pow_mem p).1 x.2
  rw [frobenius_def] at hx
  rw [← hx, ← pow_mul, ← pow_succ'] at hy
  exact ⟨⟨x', (mem_perfectClosure_iff_pow_mem p).2 ⟨n + 1, y, hy⟩⟩, by
    simp_rw [frobenius_def, SubmonoidClass.mk_pow, hx]⟩

/-- If `E` is a perfect field, then the (relative) perfect closure
`perfectClosure F E` is perfect. -/
instance perfectClosure.perfectField [PerfectField E] : PerfectField (perfectClosure F E) :=
  PerfectRing.toPerfectField _ (ringExpChar E)

end perfectClosure

namespace IntermediateField

/-- `F⟮x⟯ / F` is a purely inseparable extension if and only if the minimal polynomial of `x`
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
  simp_rw [← le_perfectClosure_iff, adjoin_le_iff, ← mem_perfectClosure_iff_pow_mem q,
    Set.subset_def, SetLike.mem_coe]

/-- A compositum of two purely inseparable extensions is purely inseparable. -/
instance isPurelyInseparable_sup (L1 L2 : IntermediateField F E)
    [h1 : IsPurelyInseparable F L1] [h2 : IsPurelyInseparable F L2] :
    IsPurelyInseparable F (L1 ⊔ L2 : IntermediateField F E) := by
  rw [← le_perfectClosure_iff] at h1 h2 ⊢
  exact sup_le h1 h2

/-- A compositum of purely inseparable extensions is purely inseparable. -/
instance isPurelyInseparable_iSup {ι : Sort*} {t : ι → IntermediateField F E}
    [h : ∀ i, IsPurelyInseparable F (t i)] :
    IsPurelyInseparable F (⨆ i, t i : IntermediateField F E) := by
  simp_rw [← le_perfectClosure_iff] at h ⊢
  exact iSup_le h

/-- If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, then
`F(S) = F(S ^ (q ^ n))` for any natural number `n`. -/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable (S : Set E)
    [Algebra.IsSeparable F (adjoin F S)] (q : ℕ) [ExpChar F q] (n : ℕ) :
    adjoin F S = adjoin F ((· ^ q ^ n) '' S) := by
  set L := adjoin F S
  set M := adjoin F ((· ^ q ^ n) '' S)
  have hi : M ≤ L := by
    rw [adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact pow_mem (subset_adjoin F S hy) _
  letI := (inclusion hi).toAlgebra
  haveI : Algebra.IsSeparable M (extendScalars hi) :=
    Algebra.isSeparable_tower_top_of_isSeparable F M L
  haveI : IsPurelyInseparable M (extendScalars hi) := by
    haveI := expChar_of_injective_algebraMap (algebraMap F M).injective q
    rw [extendScalars_adjoin hi, isPurelyInseparable_adjoin_iff_pow_mem M _ q]
    exact fun x hx ↦ ⟨n, ⟨x ^ q ^ n, subset_adjoin F _ ⟨x, hx, rfl⟩⟩, rfl⟩
  simpa only [extendScalars_restrictScalars, restrictScalars_bot_eq_self] using congr_arg
    (restrictScalars F) (extendScalars hi).eq_bot_of_isPurelyInseparable_of_isSeparable

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F(S) = F(S ^ (q ^ n))` for any subset `S` of `E` and any natural number `n`. -/
theorem adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] (n : ℕ) : adjoin F S = adjoin F ((· ^ q ^ n) '' S) :=
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F (adjoin F S) E
  adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q n

-- TODO: prove the converse when `F(S) / F` is finite
/-- If `F` is a field of exponential characteristic `q`, `F(S) / F` is separable, then
`F(S) = F(S ^ q)`. -/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable (S : Set E) [Algebra.IsSeparable F (adjoin F S)]
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E S q 1

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F(S) = F(S ^ q)` for any subset `S` of `E`. -/
theorem adjoin_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F E] (S : Set E)
    (q : ℕ) [ExpChar F q] : adjoin F S = adjoin F ((· ^ q) '' S) :=
  pow_one q ▸ adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E S q 1

-- Special cases for simple adjoin

/-- If `F` is a field of exponential characteristic `q`, `a : E` is separable over `F`, then
`F⟮a⟯ = F⟮a ^ q ^ n⟯` for any natural number `n`. -/
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable {a : E} (ha : IsSeparable F a)
    (q : ℕ) [ExpChar F q] (n : ℕ) : F⟮a⟯ = F⟮a ^ q ^ n⟯ := by
  haveI := (isSeparable_adjoin_simple_iff_isSeparable F E).mpr ha
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F⟮a⟯ = F⟮a ^ q ^ n⟯` for any subset `a : E` and any natural number `n`. -/
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (a : E)
    (q : ℕ) [ExpChar F q] (n : ℕ) : F⟮a⟯ = F⟮a ^ q ^ n⟯ := by
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F F⟮a⟯ E
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

/-- If `F` is a field of exponential characteristic `q`, `a : E` is separable over `F`, then
`F⟮a⟯ = F⟮a ^ q⟯`. -/
theorem adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable {a : E} (ha : IsSeparable F a)
    (q : ℕ) [ExpChar F q] : F⟮a⟯ = F⟮a ^ q⟯ :=
  pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E ha q 1

/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F⟮a⟯ = F⟮a ^ q⟯` for any `a : E`. -/
theorem adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable' [Algebra.IsSeparable F E] (a : E)
    (q : ℕ) [ExpChar F q] : F⟮a⟯ = F⟮a ^ q⟯ :=
  pow_one q ▸ adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' F E a q 1

end IntermediateField

section

variable (q n : ℕ) [hF : ExpChar F q] {ι : Type*} {v : ι → E} {F E}

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is a family
of elements of `E` which `F`-linearly spans `E`, then `{ u_i ^ (q ^ n) }` also `F`-linearly spans
`E` for any natural number `n`. -/
theorem Field.span_map_pow_expChar_pow_eq_top_of_isSeparable [Algebra.IsSeparable F E]
    (h : Submodule.span F (Set.range v) = ⊤) :
    Submodule.span F (Set.range (v · ^ q ^ n)) = ⊤ := by
  rw [← Algebra.top_toSubmodule, ← top_toSubalgebra, ← adjoin_univ,
    adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable' F E _ q n,
    adjoin_algebraic_toSubalgebra fun x _ ↦ Algebra.IsAlgebraic.isAlgebraic x,
    Set.image_univ, Algebra.adjoin_eq_span]
  have := (MonoidHom.mrange (powMonoidHom (α := E) (q ^ n))).closure_eq
  simp only [MonoidHom.mrange, powMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Submonoid.coe_copy] at this
  rw [this]
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
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  have h' := h.linearIndepOn_id
  let ι' := h'.extend (Set.range v).subset_univ
  let b : Basis ι' F E := Basis.extend h'
  letI : Fintype ι' := FiniteDimensional.fintypeBasisIndex b
  have H := linearIndependent_of_top_le_span_of_card_eq_finrank
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge
    (Module.finrank_eq_card_basis b).symm
  let f (i : ι) : ι' := ⟨v i, h'.subset_extend _ ⟨i, rfl⟩⟩
  convert H.comp f fun _ _ heq ↦ h.injective (by simpa only [f, Subtype.mk.injEq] using heq)
  simp_rw [Function.comp_apply, b]
  rw [Basis.extend_apply_self]

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is a
family of elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ n) }` is also
`F`-linearly independent for any natural number `n`. -/
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable [Algebra.IsSeparable F E]
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  classical
  have halg := Algebra.IsSeparable.isAlgebraic F E
  rw [linearIndependent_iff_finset_linearIndependent] at h ⊢
  intro s
  let E' := adjoin F (s.image v : Set E)
  haveI : FiniteDimensional F E' := finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x
  haveI : Algebra.IsSeparable F E' := Algebra.isSeparable_tower_bot_of_isSeparable F E' E
  let v' (i : s) : E' := ⟨v i.1, subset_adjoin F _ (Finset.mem_image.2 ⟨i.1, i.2, rfl⟩)⟩
  have h' : LinearIndependent F v' := (h s).of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_fd_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

/-- If `E / F` is a field extension of exponential characteristic `q`, if `{ u_i }` is a
family of separable elements of `E` which is `F`-linearly independent, then `{ u_i ^ (q ^ n) }`
is also `F`-linearly independent for any natural number `n`. -/
theorem LinearIndependent.map_pow_expChar_pow_of_isSeparable'
    (hsep : ∀ i : ι, IsSeparable F (v i))
    (h : LinearIndependent F v) : LinearIndependent F (v · ^ q ^ n) := by
  let E' := adjoin F (Set.range v)
  haveI : Algebra.IsSeparable F E' := (isSeparable_adjoin_iff_isSeparable F _).2 <| by
    rintro _ ⟨y, rfl⟩; exact hsep y
  let v' (i : ι) : E' := ⟨v i, subset_adjoin F _ ⟨i, rfl⟩⟩
  have h' : LinearIndependent F v' := h.of_comp E'.val.toLinearMap
  exact (h'.map_pow_expChar_pow_of_isSeparable q n).map'
    E'.val.toLinearMap (LinearMap.ker_eq_bot_of_injective E'.val.injective)

/-- If `E / F` is a separable extension of exponential characteristic `q`, if `{ u_i }` is an
`F`-basis of `E`, then `{ u_i ^ (q ^ n) }` is also an `F`-basis of `E`
for any natural number `n`. -/
def Basis.mapPowExpCharPowOfIsSeparable [Algebra.IsSeparable F E]
    (b : Basis ι F E) : Basis ι F E :=
  Basis.mk (b.linearIndependent.map_pow_expChar_pow_of_isSeparable q n)
    (Field.span_map_pow_expChar_pow_eq_top_of_isSeparable q n b.span_eq).ge

/-- For an extension `E / F` of exponential characteristic `q` and a separable element `a : E`, the
minimal polynomial of `a ^ q ^ n` equals the minimal polynomial of `a` mapped via `(⬝ ^ q ^ n)`. -/
theorem minpoly.iterateFrobenius_of_isSeparable [ExpChar E q] (n : ℕ) {a : E}
    (hsep : IsSeparable F a) :
    minpoly F (iterateFrobenius E q n a) = (minpoly F a).map (iterateFrobenius F q n) := by
  have hai : IsIntegral F a := hsep.isIntegral
  have hapi : IsIntegral F (iterateFrobenius E q n a) := hai.pow _
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic hapi)
    (minpoly.monic hai |>.map _)
    (minpoly.dvd F (a ^ q ^ n) ?haeval)
    ?hdeg
  · simpa using Eq.symm <|
      (minpoly F a).map_aeval_eq_aeval_map (RingHom.iterateFrobenius_comm _ q n) a
  · rw [(minpoly F a).natDegree_map_eq_of_injective (iterateFrobenius F q n).injective,
      ← IntermediateField.adjoin.finrank hai,
      IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E hsep q n,
      ← IntermediateField.adjoin.finrank hapi, iterateFrobenius_def]

/-- For an extension `E / F` of exponential characteristic `q` and a separable element `a : E`, the
minimal polynomial of `a ^ q` equals the minimal polynomial of `a` mapped via `(⬝ ^ q)`. -/
theorem minpoly.frobenius_of_isSeparable [ExpChar E q] {a : E} (hsep : IsSeparable F a) :
    minpoly F (frobenius E q a) = (minpoly F a).map (frobenius F q) := by
  simpa using minpoly.iterateFrobenius_of_isSeparable q 1 hsep

end

theorem perfectField_of_perfectClosure_eq_bot [h : PerfectField E] (eq : perfectClosure F E = ⊥) :
    PerfectField F := by
  let p := ringExpChar F
  haveI := expChar_of_injective_algebraMap (algebraMap F E).injective p
  haveI := PerfectRing.ofSurjective F p fun x ↦ by
    obtain ⟨y, h⟩ := surjective_frobenius E p (algebraMap F E x)
    have : y ∈ perfectClosure F E := ⟨1, x, by rw [← h, pow_one, frobenius_def, ringExpChar.eq F p]⟩
    obtain ⟨z, rfl⟩ := eq ▸ this
    simp only [Algebra.ofId, AlgHom.coe_ringHom_mk] at h
    exact ⟨z, (algebraMap F E).injective (by rw [RingHom.map_frobenius]; rw [h])⟩
  exact PerfectRing.toPerfectField F p

/-- If `E / F` is a separable extension, `E` is perfect, then `F` is also prefect. -/
theorem perfectField_of_isSeparable_of_perfectField_top [Algebra.IsSeparable F E] [PerfectField E] :
    PerfectField F :=
  perfectField_of_perfectClosure_eq_bot F E (perfectClosure.eq_bot_of_isSeparable F E)

/-- If `E` is an algebraic closure of `F`, then `F` is perfect if and only if `E / F` is
separable. -/
theorem perfectField_iff_isSeparable_algebraicClosure [IsAlgClosure F E] :
    PerfectField F ↔ Algebra.IsSeparable F E :=
  ⟨fun _ ↦ IsSepClosure.separable, fun _ ↦ haveI : IsAlgClosed E := IsAlgClosure.isAlgClosed F
    perfectField_of_isSeparable_of_perfectField_top F E⟩
