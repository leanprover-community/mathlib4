/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module number_theory.cyclotomic.basic
! leanprover-community/mathlib commit 4b05d3f4f0601dca8abf99c4ec99187682ed0bba
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois

/-!
# Cyclotomic extensions

Let `A` and `B` be commutative rings with `Algebra A B`. For `S : Set ℕ+`, we define a class
`IsCyclotomicExtension S A B` expressing the fact that `B` is obtained from `A` by adding `n`-th
primitive roots of unity, for all `n ∈ S`.

## Main definitions

* `IsCyclotomicExtension S A B` : means that `B` is obtained from `A` by adding `n`-th primitive
  roots of unity, for all `n ∈ S`.
* `CyclotomicField`: given `n : ℕ+` and a field `K`, we define `CyclotomicField n K` as the
  splitting field of `cyclotomic n K`. If `n` is nonzero in `K`, it has the instance
  `IsCyclotomicExtension {n} K (CyclotomicField n K)`.
* `CyclotomicRing` : if `A` is a domain with fraction field `K` and `n : ℕ+`, we define
  `CyclotomicRing n A K` as the `A`-subalgebra of `CyclotomicField n K` generated by the roots of
  `X ^ n - 1`. If `n` is nonzero in `A`, it has the instance
  `IsCyclotomicExtension {n} A (CyclotomicRing n A K)`.

## Main results

* `IsCyclotomicExtension.trans` : if `IsCyclotomicExtension S A B` and
  `IsCyclotomicExtension T B C`, then `IsCyclotomicExtension (S ∪ T) A C` if
  `Function.Injective (algebraMap B C)`.
* `IsCyclotomicExtension.union_right` : given `IsCyclotomicExtension (S ∪ T) A B`, then
  `IsCyclotomicExtension T (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }) B`.
* `IsCyclotomicExtension.union_left` : given `IsCyclotomicExtension T A B` and `S ⊆ T`, then
  `IsCyclotomicExtension S A (adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 })`.
* `IsCyclotomicExtension.finite` : if `S` is finite and `IsCyclotomicExtension S A B`, then
  `B` is a finite `A`-algebra.
* `IsCyclotomicExtension.numberField` : a finite cyclotomic extension of a number field is a
  number field.
* `IsCyclotomicExtension.splitting_field_X_pow_sub_one` : if `IsCyclotomicExtension {n} K L`,
  then `L` is the splitting field of `X ^ n - 1`.
* `IsCyclotomicExtension.splitting_field_cyclotomic` : if `IsCyclotomicExtension {n} K L`,
  then `L` is the splitting field of `cyclotomic n K`.

## Implementation details

Our definition of `IsCyclotomicExtension` is very general, to allow rings of any characteristic
and infinite extensions, but it will mainly be used in the case `S = {n}` and for integral domains.
All results are in the `IsCyclotomicExtension` namespace.
Note that some results, for example `IsCyclotomicExtension.trans`,
`IsCyclotomicExtension.finite`, `IsCyclotomicExtension.numberField`,
`IsCyclotomicExtension.finiteDimensional`, `IsCyclotomicExtension.isGalois` and
`CyclotomicField.algebraBase` are lemmas, but they can be made local instances. Some of them are
included in the `cyclotomic` locale.

-/


open Polynomial Algebra FiniteDimensional Set

open scoped BigOperators

universe u v w z

variable (n : ℕ+) (S T : Set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)

variable [CommRing A] [CommRing B] [Algebra A B]

variable [Field K] [Field L] [Algebra K L]

noncomputable section

/-- Given an `A`-algebra `B` and `S : Set ℕ+`, we define `IsCyclotomicExtension S A B` requiring
that there is a `n`-th primitive root of unity in `B` for all `n ∈ S` and that `B` is generated
over `A` by the roots of `X ^ n - 1`. -/

@[mk_iff]
class IsCyclotomicExtension : Prop where
  /-- For all `n ∈ S`, there existe a primitive `n`-th root of unity in `B`. -/
  exists_prim_root {n : ℕ+} (ha : n ∈ S) : ∃ r : B, IsPrimitiveRoot r n
  /-- The `n`-th roots of unity, for `n ∈ S`, generate `B` as an `A`-algebra. -/
  adjoin_roots : ∀ x : B, x ∈ adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}
#align is_cyclotomic_extension IsCyclotomicExtension

namespace IsCyclotomicExtension

section Basic

/-- A reformulation of `IsCyclotomicExtension` that uses `⊤`. -/
theorem iff_adjoin_eq_top :
    IsCyclotomicExtension S A B ↔
      (∀ n : ℕ+, n ∈ S → ∃ r : B, IsPrimitiveRoot r n) ∧
        adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1} = ⊤ :=
  ⟨fun h => ⟨fun _ => h.exists_prim_root, Algebra.eq_top_iff.2 h.adjoin_roots⟩, fun h =>
    ⟨h.1 _, Algebra.eq_top_iff.1 h.2⟩⟩
#align is_cyclotomic_extension.iff_adjoin_eq_top IsCyclotomicExtension.iff_adjoin_eq_top

/-- A reformulation of `IsCyclotomicExtension` in the case `S` is a singleton. -/
theorem iff_singleton :
    IsCyclotomicExtension {n} A B ↔
      (∃ r : B, IsPrimitiveRoot r n) ∧ ∀ x, x ∈ adjoin A {b : B | b ^ (n : ℕ) = 1} :=
  by simp [IsCyclotomicExtension_iff]
#align is_cyclotomic_extension.iff_singleton IsCyclotomicExtension.iff_singleton

/-- If `IsCyclotomicExtension ∅ A B`, then the image of `A` in `B` equals `B`. -/
theorem empty [h : IsCyclotomicExtension ∅ A B] : (⊥ : Subalgebra A B) = ⊤ := by
  simpa [Algebra.eq_top_iff, IsCyclotomicExtension_iff] using h
#align is_cyclotomic_extension.empty IsCyclotomicExtension.empty

/-- If `IsCyclotomicExtension {1} A B`, then the image of `A` in `B` equals `B`. -/
theorem singleton_one [h : IsCyclotomicExtension {1} A B] : (⊥ : Subalgebra A B) = ⊤ :=
  Algebra.eq_top_iff.2 fun x => by
    simpa [adjoin_singleton_one] using ((IsCyclotomicExtension_iff _ _ _).1 h).2 x
#align is_cyclotomic_extension.singleton_one IsCyclotomicExtension.singleton_one

variable {A B}

/-- If `(⊥ : SubAlgebra A B) = ⊤`, then `IsCyclotomicExtension ∅ A B`. -/
theorem singleton_zero_of_bot_eq_top (h : (⊥ : Subalgebra A B) = ⊤) :
    IsCyclotomicExtension ∅ A B := by
-- Porting note: Lean3 is able to infer `A`.
  refine'  (iff_adjoin_eq_top _ A _).2
    ⟨fun s hs => by simp at hs, _root_.eq_top_iff.2 fun x hx => _⟩
  rw [← h] at hx
  simpa using hx
#align is_cyclotomic_extension.singleton_zero_of_bot_eq_top IsCyclotomicExtension.singleton_zero_of_bot_eq_top

variable (A B)

/-- Transitivity of cyclotomic extensions. -/
theorem trans (C : Type w) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [hS : IsCyclotomicExtension S A B] [hT : IsCyclotomicExtension T B C]
    (h : Function.Injective (algebraMap B C)) : IsCyclotomicExtension (S ∪ T) A C := by
  refine' ⟨fun hn => _, fun x => _⟩
  · cases' hn with hn hn
    · obtain ⟨b, hb⟩ := ((IsCyclotomicExtension_iff _ _ _).1 hS).1 hn
      refine' ⟨algebraMap B C b, _⟩
      exact hb.map_of_injective h
    · exact ((IsCyclotomicExtension_iff _ _ _).1 hT).1 hn
  · refine' adjoin_induction (((IsCyclotomicExtension_iff T B _).1 hT).2 x)
      (fun c ⟨n, hn⟩ => subset_adjoin ⟨n, Or.inr hn.1, hn.2⟩) (fun b => _)
      (fun x y hx hy => Subalgebra.add_mem _ hx hy) fun x y hx hy => Subalgebra.mul_mem _ hx hy
    · let f := IsScalarTower.toAlgHom A B C
      have hb : f b ∈ (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}).map f :=
        ⟨b, ((IsCyclotomicExtension_iff _ _ _).1 hS).2 b, rfl⟩
      rw [IsScalarTower.toAlgHom_apply, ← adjoin_image] at hb
      refine' adjoin_mono (fun y hy => _) hb
      obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy
      exact ⟨n, ⟨mem_union_left T hn.1, by rw [← h₁, ← AlgHom.map_pow, hn.2, AlgHom.map_one]⟩⟩
#align is_cyclotomic_extension.trans IsCyclotomicExtension.trans

@[nontriviality]
theorem subsingleton_iff [Subsingleton B] : IsCyclotomicExtension S A B ↔ S = { } ∨ S = {1} := by
  constructor
  · rintro ⟨hprim, -⟩
    rw [← subset_singleton_iff_eq]
    intro t ht
    obtain ⟨ζ, hζ⟩ := hprim ht
    rw [mem_singleton_iff, ← PNat.coe_eq_one_iff]
    exact_mod_cast hζ.unique (IsPrimitiveRoot.of_subsingleton ζ)
  · rintro (rfl | rfl)
-- Porting note: `R := A` was not needed.
    · exact ⟨fun h => h.elim, fun x => by convert (mem_top (R := A) : x ∈ ⊤)⟩
    · rw [iff_singleton]
      exact ⟨⟨0, IsPrimitiveRoot.of_subsingleton 0⟩,
        fun x => by convert (mem_top (R := A) : x ∈ ⊤)⟩
#align is_cyclotomic_extension.subsingleton_iff IsCyclotomicExtension.subsingleton_iff

/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `S ∪ T`, then `B`
is a cyclotomic extension of `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 } ` given by
roots of unity of order in `T`. -/
theorem union_right [h : IsCyclotomicExtension (S ∪ T) A B] :
    IsCyclotomicExtension T (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}) B := by
  have : {b : B | ∃ n : ℕ+, n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1} =
      {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1} ∪
        {b : B | ∃ n : ℕ+, n ∈ T ∧ b ^ (n : ℕ) = 1} := by
    refine' le_antisymm _ _
    · rintro x ⟨n, hn₁ | hn₂, hnpow⟩
      · left; exact ⟨n, hn₁, hnpow⟩
      · right; exact ⟨n, hn₂, hnpow⟩
    · rintro x (⟨n, hn⟩ | ⟨n, hn⟩)
      · exact ⟨n, Or.inl hn.1, hn.2⟩
      · exact ⟨n, Or.inr hn.1, hn.2⟩
  refine' ⟨fun hn => ((IsCyclotomicExtension_iff _ A _).1 h).1 (mem_union_right S hn), fun b => _⟩
  replace h := ((IsCyclotomicExtension_iff _ _ _).1 h).2 b
  rwa [this, adjoin_union_eq_adjoin_adjoin, Subalgebra.mem_restrictScalars] at h
#align is_cyclotomic_extension.union_right IsCyclotomicExtension.union_right

/-- If `B` is a cyclotomic extension of `A` given by roots of unity of order in `T` and `S ⊆ T`,
then `adjoin A { b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1 }` is a cyclotomic extension of `B`
given by roots of unity of order in `S`. -/
theorem union_left [h : IsCyclotomicExtension T A B] (hS : S ⊆ T) :
    IsCyclotomicExtension S A (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}) := by
  refine' ⟨@fun n hn => _, fun b => _⟩
  · obtain ⟨b, hb⟩ := ((IsCyclotomicExtension_iff _ _ _).1 h).1 (hS hn)
    refine' ⟨⟨b, subset_adjoin ⟨n, hn, hb.pow_eq_one⟩⟩, _⟩
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk]
  · convert mem_top (R := A) (x := b)
    rw [← adjoin_adjoin_coe_preimage, preimage_setOf_eq]
    norm_cast
#align is_cyclotomic_extension.union_left IsCyclotomicExtension.union_left

variable {n S}

/-- If `∀ s ∈ S, n ∣ s` and `S` is not empty, then `IsCyclotomicExtension S A B` implies
`IsCyclotomicExtension (S ∪ {n}) A B`. -/
theorem of_union_of_dvd (h : ∀ s ∈ S, n ∣ s) (hS : S.Nonempty) [H : IsCyclotomicExtension S A B] :
    IsCyclotomicExtension (S ∪ {n}) A B := by
  refine' (iff_adjoin_eq_top _ A _).2 ⟨fun s hs => _, _⟩
  · rw [mem_union, mem_singleton_iff] at hs
    obtain hs | rfl := hs
    · exact H.exists_prim_root hs
    · obtain ⟨m, hm⟩ := hS
      obtain ⟨x, rfl⟩ := h m hm
      obtain ⟨ζ, hζ⟩ := H.exists_prim_root hm
      refine' ⟨ζ ^ (x : ℕ), _⟩
      convert hζ.pow_of_dvd x.ne_zero (dvd_mul_left (x : ℕ) s)
      simp only [PNat.mul_coe, Nat.mul_div_left, PNat.pos]
  · refine' _root_.eq_top_iff.2 _
    rw [← ((iff_adjoin_eq_top S A B).1 H).2]
    refine' adjoin_mono fun x hx => _
    simp only [union_singleton, mem_insert_iff, mem_setOf_eq] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, ⟨Or.inr hm.1, hm.2⟩⟩
#align is_cyclotomic_extension.of_union_of_dvd IsCyclotomicExtension.of_union_of_dvd

/-- If `∀ s ∈ S, n ∣ s` and `S` is not empty, then `IsCyclotomicExtension S A B` if and only if
`IsCyclotomicExtension (S ∪ {n}) A B`. -/
theorem iff_union_of_dvd (h : ∀ s ∈ S, n ∣ s) (hS : S.Nonempty) :
    IsCyclotomicExtension S A B ↔ IsCyclotomicExtension (S ∪ {n}) A B := by
  refine'
    ⟨fun H => of_union_of_dvd A B h hS, fun H => (iff_adjoin_eq_top _ A _).2 ⟨fun s hs => _, _⟩⟩
  · exact H.exists_prim_root (subset_union_left _ _ hs)
  · rw [_root_.eq_top_iff, ← ((iff_adjoin_eq_top _ A B).1 H).2]
    refine' adjoin_mono fun x hx => _
    simp only [union_singleton, mem_insert_iff, mem_setOf_eq] at hx ⊢
    obtain ⟨m, rfl | hm, hxpow⟩ := hx
    · obtain ⟨y, hy⟩ := hS
      refine' ⟨y, ⟨hy, _⟩⟩
      obtain ⟨z, rfl⟩ := h y hy
      simp only [PNat.mul_coe, pow_mul, hxpow, one_pow]
    · exact ⟨m, ⟨hm, hxpow⟩⟩
#align is_cyclotomic_extension.iff_union_of_dvd IsCyclotomicExtension.iff_union_of_dvd

variable (n S)

/-- `IsCyclotomicExtension S A B` is equivalent to `IsCyclotomicExtension (S ∪ {1}) A B`. -/
theorem iff_union_singleton_one :
    IsCyclotomicExtension S A B ↔ IsCyclotomicExtension (S ∪ {1}) A B := by
  obtain hS | rfl := S.eq_empty_or_nonempty.symm
  · exact iff_union_of_dvd _ _ (fun s _ => one_dvd _) hS
  rw [empty_union]
  refine' ⟨fun H => _, fun H => _⟩
  · refine' (iff_adjoin_eq_top _ A _).2 ⟨fun s hs => ⟨1, by simp [mem_singleton_iff.1 hs]⟩, _⟩
    simp [adjoin_singleton_one, empty]
  · refine' (iff_adjoin_eq_top _ A _).2 ⟨fun s hs => (not_mem_empty s hs).elim, _⟩
    simp [@singleton_one A B _ _ _ H]
#align is_cyclotomic_extension.iff_union_singleton_one IsCyclotomicExtension.iff_union_singleton_one

variable {A B}

/-- If `(⊥ : SubAlgebra A B) = ⊤`, then `IsCyclotomicExtension {1} A B`. -/
theorem singleton_one_of_bot_eq_top (h : (⊥ : Subalgebra A B) = ⊤) :
    IsCyclotomicExtension {1} A B := by
  convert (iff_union_singleton_one _ A _).1 (singleton_zero_of_bot_eq_top h)
  simp
#align is_cyclotomic_extension.singleton_one_of_bot_eq_top IsCyclotomicExtension.singleton_one_of_bot_eq_top

/-- If `Function.Surjective (algebraMap A B)`, then `IsCyclotomicExtension {1} A B`. -/
theorem singleton_one_of_algebraMap_bijective (h : Function.Surjective (algebraMap A B)) :
    IsCyclotomicExtension {1} A B :=
  singleton_one_of_bot_eq_top (surjective_algebraMap_iff.1 h).symm
#align is_cyclotomic_extension.singleton_one_of_algebra_map_bijective IsCyclotomicExtension.singleton_one_of_algebraMap_bijective

variable (A B)

/-- Given `(f : B ≃ₐ[A] C)`, if `IsCyclotomicExtension S A B` then
`IsCyclotomicExtension S A C`. -/
protected
theorem equiv {C : Type _} [CommRing C] [Algebra A C] [h : IsCyclotomicExtension S A B]
    (f : B ≃ₐ[A] C) : IsCyclotomicExtension S A C := by
  letI : Algebra B C := f.toAlgHom.toRingHom.toAlgebra
  haveI : IsCyclotomicExtension {1} B C := singleton_one_of_algebraMap_bijective f.surjective
  haveI : IsScalarTower A B C := IsScalarTower.of_ring_hom f.toAlgHom
  exact (iff_union_singleton_one _ _ _).2 (trans S {1} A B C f.injective)
#align is_cyclotomic_extension.equiv IsCyclotomicExtension.equiv

protected
theorem neZero [h : IsCyclotomicExtension {n} A B] [IsDomain B] : NeZero ((n : ℕ) : B) := by
  obtain ⟨⟨r, hr⟩, -⟩ := (iff_singleton n A B).1 h
  exact hr.ne_zero'
#align is_cyclotomic_extension.ne_zero IsCyclotomicExtension.neZero

protected
theorem ne_zero' [IsCyclotomicExtension {n} A B] [IsDomain B] : NeZero ((n : ℕ) : A) := by
  haveI := IsCyclotomicExtension.neZero n A B
  exact NeZero.nat_of_neZero (algebraMap A B)
#align is_cyclotomic_extension.ne_zero' IsCyclotomicExtension.ne_zero'

end Basic

section Fintype

theorem finite_of_singleton [IsDomain B] [h : IsCyclotomicExtension {n} A B] :
    Module.Finite A B := by
  classical
  rw [Module.finite_def, ← top_toSubmodule, ← ((iff_adjoin_eq_top _ _ _).1 h).2]
  refine' FG_adjoin_of_finite _ fun b hb => _
  · simp only [mem_singleton_iff, exists_eq_left]
    have : {b : B | b ^ (n : ℕ) = 1} = (nthRoots n (1 : B)).toFinset :=
      Set.ext fun x => ⟨fun h => by simpa using h, fun h => by simpa using h⟩
    rw [this]
    exact (nthRoots (↑n) 1).toFinset.finite_toSet
  · simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq] at hb
    refine' ⟨X ^ (n : ℕ) - 1, ⟨monic_X_pow_sub_C _ n.pos.ne.symm, by simp [hb]⟩⟩
#align is_cyclotomic_extension.finite_of_singleton IsCyclotomicExtension.finite_of_singleton

/-- If `S` is finite and `IsCyclotomicExtension S A B`, then `B` is a finite `A`-algebra. -/
protected
theorem finite [IsDomain B] [h₁ : Finite S] [h₂ : IsCyclotomicExtension S A B] :
    Module.Finite A B := by
  cases' nonempty_fintype S with h
  revert h₂ A B
  refine' Set.Finite.induction_on (Set.Finite.intro h) (fun A B => _) @fun n S _ _ H A B => _
  · intro _ _ _ _ _
    refine' Module.finite_def.2 ⟨({1} : Finset B), _⟩
    simp [← top_toSubmodule, ← empty, toSubmodule_bot]
  · intro _ _ _ _ h
    haveI : IsCyclotomicExtension S A (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) :=
      union_left _ (insert n S) _ _ (subset_insert n S)
    haveI := H A (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1})
    have : Module.Finite (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) B := by
      rw [← union_singleton] at h
      letI := @union_right S {n} A B _ _ _ h
      exact finite_of_singleton n _ _
    exact Module.Finite.trans (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) _
#align is_cyclotomic_extension.finite IsCyclotomicExtension.finite

/-- A cyclotomic finite extension of a number field is a number field. -/
theorem numberField [h : NumberField K] [Finite S] [IsCyclotomicExtension S K L] : NumberField L :=
  { to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
    to_finiteDimensional := by
      haveI := charZero_of_injective_algebraMap (algebraMap K L).injective
      haveI := IsCyclotomicExtension.finite S K L
      exact Module.Finite.trans K _ }
#align is_cyclotomic_extension.number_field IsCyclotomicExtension.numberField

/-- A finite cyclotomic extension of an integral noetherian domain is integral -/
theorem integral [IsDomain B] [IsNoetherianRing A] [Finite S] [IsCyclotomicExtension S A B] :
    Algebra.IsIntegral A B :=
  isIntegral_of_noetherian <| isNoetherian_of_fg_of_noetherian' <|
    (IsCyclotomicExtension.finite S A B).out
#align is_cyclotomic_extension.integral IsCyclotomicExtension.integral

/-- If `S` is finite and `IsCyclotomicExtension S K A`, then `finiteDimensional K A`. -/
theorem finiteDimensional (C : Type z) [Finite S] [CommRing C] [Algebra K C] [IsDomain C]
    [IsCyclotomicExtension S K C] : FiniteDimensional K C :=
  IsCyclotomicExtension.finite S K C
#align is_cyclotomic_extension.finite_dimensional IsCyclotomicExtension.finiteDimensional

end Fintype

section

variable {A B}

theorem adjoin_roots_cyclotomic_eq_adjoin_nth_roots [IsDomain B] {ζ : B} {n : ℕ+}
    (hζ : IsPrimitiveRoot ζ n) :
    adjoin A ((cyclotomic n A).rootSet B) =
      adjoin A {b : B | ∃ a : ℕ+, a ∈ ({n} : Set ℕ+) ∧ b ^ (a : ℕ) = 1} := by
  simp only [mem_singleton_iff, exists_eq_left, map_cyclotomic]
  refine' le_antisymm (adjoin_mono fun x hx => _) (adjoin_le fun x hx => _)
  · rw [mem_rootSet'] at hx
    simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq]
    rw [isRoot_of_unity_iff n.pos]
    refine' ⟨n, Nat.mem_divisors_self n n.ne_zero, _⟩
    rw [IsRoot.def, ← map_cyclotomic n (algebraMap A B), eval_map, ← aeval_def]
    exact hx.2
  · simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq] at hx
    obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos
    refine' SetLike.mem_coe.2 (Subalgebra.pow_mem _ (subset_adjoin _) _)
    rw [mem_rootSet', map_cyclotomic, aeval_def, ← eval_map, map_cyclotomic, ← IsRoot]
    refine' ⟨cyclotomic_ne_zero n B, hζ.isRoot_cyclotomic n.pos⟩
#align is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots

theorem adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic {n : ℕ+} [IsDomain B] {ζ : B}
    (hζ : IsPrimitiveRoot ζ n) : adjoin A ((cyclotomic n A).rootSet B) = adjoin A {ζ} := by
  refine' le_antisymm (adjoin_le fun x hx => _) (adjoin_mono fun x hx => _)
  · suffices hx : x ^ n.1 = 1
    obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx n.pos
    exact SetLike.mem_coe.2 (Subalgebra.pow_mem _ (subset_adjoin <| mem_singleton ζ) _)
    refine' (isRoot_of_unity_iff n.pos B).2 _
    refine' ⟨n, Nat.mem_divisors_self n n.ne_zero, _⟩
    rw [mem_rootSet', aeval_def, ← eval_map, map_cyclotomic, ← IsRoot] at hx
    exact hx.2
  · simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq] at hx
    simpa only [hx, mem_rootSet', map_cyclotomic, aeval_def, ← eval_map, IsRoot] using
      And.intro (cyclotomic_ne_zero n B) (hζ.isRoot_cyclotomic n.pos)
#align is_cyclotomic_extension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic

theorem adjoin_primitive_root_eq_top {n : ℕ+} [IsDomain B] [h : IsCyclotomicExtension {n} A B]
    {ζ : B} (hζ : IsPrimitiveRoot ζ n) : adjoin A ({ζ} : Set B) = ⊤ := by
  classical
  rw [← adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic hζ]
  rw [adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ]
  exact ((iff_adjoin_eq_top {n} A B).mp h).2
#align is_cyclotomic_extension.adjoin_primitive_root_eq_top IsCyclotomicExtension.adjoin_primitive_root_eq_top

variable (A)

theorem _root_.IsPrimitiveRoot.adjoin_isCyclotomicExtension {ζ : B} {n : ℕ+}
    (h : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} A (adjoin A ({ζ} : Set B)) :=
  { exists_prim_root := fun hi => by
      rw [Set.mem_singleton_iff] at hi
      refine' ⟨⟨ζ, subset_adjoin <| Set.mem_singleton ζ⟩, _⟩
      rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk, hi]
    adjoin_roots := fun x => by
      refine
        adjoin_induction'
          (x := x) (fun b hb => ?_) (fun a => ?_) (fun b₁ b₂ hb₁ hb₂ => ?_)
          (fun b₁ b₂ hb₁ hb₂ => ?_)
      · rw [Set.mem_singleton_iff] at hb
        refine' subset_adjoin _
        simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq, hb]
        rw [← Subalgebra.coe_eq_one, Subalgebra.coe_pow, Subtype.coe_mk]
        exact ((IsPrimitiveRoot.iff_def ζ n).1 h).1
      · exact Subalgebra.algebraMap_mem _ _
      · exact Subalgebra.add_mem _ hb₁ hb₂
      · exact Subalgebra.mul_mem _ hb₁ hb₂ }
#align is_primitive_root.adjoin_is_cyclotomic_extension IsPrimitiveRoot.adjoin_isCyclotomicExtension

end

section Field

variable {n S}

/-- A cyclotomic extension splits `X ^ n - 1` if `n ∈ S`.-/
theorem splits_X_pow_sub_one [H : IsCyclotomicExtension S K L] (hS : n ∈ S) :
    Splits (algebraMap K L) (X ^ (n : ℕ) - 1) := by
  rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X]
  obtain ⟨z, hz⟩ := ((IsCyclotomicExtension_iff _ _ _).1 H).1 hS
  exact X_pow_sub_one_splits hz
set_option linter.uppercaseLean3 false in
#align is_cyclotomic_extension.splits_X_pow_sub_one IsCyclotomicExtension.splits_X_pow_sub_one

/-- A cyclotomic extension splits `cyclotomic n K` if `n ∈ S` and `ne_zero (n : K)`.-/
theorem splits_cyclotomic [IsCyclotomicExtension S K L] (hS : n ∈ S) :
    Splits (algebraMap K L) (cyclotomic n K) := by
  refine' splits_of_splits_of_dvd _ (X_pow_sub_C_ne_zero n.pos _) (splits_X_pow_sub_one K L hS) _
  use ∏ i : ℕ in (n : ℕ).properDivisors, Polynomial.cyclotomic i K
  rw [(eq_cyclotomic_iff n.pos _).1 rfl, RingHom.map_one]
#align is_cyclotomic_extension.splits_cyclotomic IsCyclotomicExtension.splits_cyclotomic

variable (n S)

section Singleton

variable [IsCyclotomicExtension {n} K L]

/-- If `IsCyclotomicExtension {n} K L`, then `L` is the splitting field of `X ^ n - 1`. -/
theorem isSplittingField_X_pow_sub_one : IsSplittingField K L (X ^ (n : ℕ) - 1) :=
  { splits' := splits_X_pow_sub_one K L (mem_singleton n)
    adjoin_rootSet' := by
      rw [← ((iff_adjoin_eq_top {n} K L).1 inferInstance).2]
      congr
      refine' Set.ext fun x => _
      simp only [Polynomial.map_pow, mem_singleton_iff, Multiset.mem_toFinset, exists_eq_left,
        mem_setOf_eq, Polynomial.map_X, Polynomial.map_one, Finset.mem_coe, Polynomial.map_sub]
      simp only [mem_rootSet', map_sub, map_pow, aeval_one, aeval_X, sub_eq_zero, map_X,
        and_iff_right_iff_imp, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one]
      exact fun _ => X_pow_sub_C_ne_zero n.pos (1 : L) }
set_option linter.uppercaseLean3 false in
#align is_cyclotomic_extension.splitting_field_X_pow_sub_one
       IsCyclotomicExtension.isSplittingField_X_pow_sub_one

/-- Any two `n`-th cyclotomic extensions are isomorphic. -/
def algEquiv (L' : Type _) [Field L'] [Algebra K L'] [IsCyclotomicExtension {n} K L'] :
    L ≃ₐ[K] L' :=
  let h₁ := isSplittingField_X_pow_sub_one n K L
  let h₂ := isSplittingField_X_pow_sub_one n K L'
  (@IsSplittingField.algEquiv K L _ _ _ (X ^ (n : ℕ) - 1) h₁).trans
    (@IsSplittingField.algEquiv K L' _ _ _ (X ^ (n : ℕ) - 1) h₂).symm
#align is_cyclotomic_extension.alg_equiv IsCyclotomicExtension.algEquiv

scoped[cyclotomic] attribute [instance] IsCyclotomicExtension.isSplittingField_X_pow_sub_one

theorem isGalois : IsGalois K L :=
  letI := isSplittingField_X_pow_sub_one n K L
  IsGalois.of_separable_splitting_field (X_pow_sub_one_separable_iff.2
    (IsCyclotomicExtension.ne_zero' n K L).1)
#align is_cyclotomic_extension.is_galois IsCyclotomicExtension.isGalois

/-- If `IsCyclotomicExtension {n} K L`, then `L` is the splitting field of `cyclotomic n K`. -/
theorem splitting_field_cyclotomic : IsSplittingField K L (cyclotomic n K) :=
  { splits' := splits_cyclotomic K L (mem_singleton n)
    adjoin_rootSet' := by
      rw [← ((iff_adjoin_eq_top {n} K L).1 inferInstance).2]
      letI := Classical.decEq L
      -- todo: make `exists_prim_root` take an explicit `L`
      obtain ⟨ζ : L, hζ⟩ := IsCyclotomicExtension.exists_prim_root K (mem_singleton n)
      exact adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ }
#align is_cyclotomic_extension.splitting_field_cyclotomic IsCyclotomicExtension.splitting_field_cyclotomic

scoped[cyclotomic] attribute [instance] IsCyclotomicExtension.splitting_field_cyclotomic

end Singleton

end Field

end IsCyclotomicExtension

section CyclotomicField

/-- Given `n : ℕ+` and a field `K`, we define `CyclotomicField n K` as the
splitting field of `cyclotomic n K`. If `n` is nonzero in `K`, it has
the instance `IsCyclotomicExtension {n} K (CyclotomicField n K)`. -/
def CyclotomicField : Type w :=
  (cyclotomic n K).SplittingField
#align cyclotomic_field CyclotomicField

namespace CyclotomicField

--Porting note: could not be derived
instance : Field (CyclotomicField n K) := by
  delta CyclotomicField; infer_instance

--Porting note: could not be derived
instance algebra : Algebra K (CyclotomicField n K) := by
  delta CyclotomicField; infer_instance

--Porting note: could not be derived
instance : Inhabited (CyclotomicField n K) := by
  delta CyclotomicField; infer_instance

instance [CharZero K] : CharZero (CyclotomicField n K) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

instance isCyclotomicExtension [NeZero ((n : ℕ) : K)] :
    IsCyclotomicExtension {n} K (CyclotomicField n K) := by
  haveI : NeZero ((n : ℕ) : CyclotomicField n K) :=
    NeZero.nat_of_injective (algebraMap K _).injective
  letI := Classical.decEq (CyclotomicField n K)
  obtain ⟨ζ, hζ⟩ :=
    exists_root_of_splits (algebraMap K (CyclotomicField n K)) (SplittingField.splits _)
      (degree_cyclotomic_pos n K n.pos).ne'
  rw [← eval_map, ← IsRoot.def, map_cyclotomic, isRoot_cyclotomic_iff] at hζ
  refine ⟨?_, ?_⟩
  . simp only [mem_singleton_iff, forall_eq]
    exact ⟨ζ, hζ⟩
  . rw [← Algebra.eq_top_iff, ← SplittingField.adjoin_rootSet, eq_comm]
    exact IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ
#align cyclotomic_field.is_cyclotomic_extension CyclotomicField.isCyclotomicExtension

end CyclotomicField

end CyclotomicField

section IsDomain

variable [Algebra A K] [IsFractionRing A K]

section CyclotomicRing

/-- If `K` is the fraction field of `A`, the `A`-algebra structure on `CyclotomicField n K`.
-/
@[nolint unusedArguments]
instance CyclotomicField.algebraBase : Algebra A (CyclotomicField n K) :=
  SplittingField.algebra' (cyclotomic n K)
#align cyclotomic_field.algebra_base CyclotomicField.algebraBase

/-- Ensure there are no diamonds when `A = ℤ`. -/
example : algebraInt (CyclotomicField n ℚ) = CyclotomicField.algebraBase _ _ _ :=
  rfl

instance CyclotomicField.algebra' {R : Type _} [CommRing R] [Algebra R K] :
    Algebra R (CyclotomicField n K) :=
  SplittingField.algebra' (cyclotomic n K)
#align cyclotomic_field.algebra' CyclotomicField.algebra'

instance {R : Type _} [CommRing R] [Algebra R K] : IsScalarTower R K (CyclotomicField n K) :=
  SplittingField.isScalarTower _

instance CyclotomicField.noZeroSMulDivisors : NoZeroSMulDivisors A (CyclotomicField n K) := by
  refine' NoZeroSMulDivisors.of_algebraMap_injective _
  rw [IsScalarTower.algebraMap_eq A K (CyclotomicField n K)]
  exact
    (Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective K (CyclotomicField n K))
      (IsFractionRing.injective A K) : _)
#align cyclotomic_field.no_zero_smul_divisors CyclotomicField.noZeroSMulDivisors

/-- If `A` is a domain with fraction field `K` and `n : ℕ+`, we define `CyclotomicRing n A K` as
the `A`-subalgebra of `CyclotomicField n K` generated by the roots of `X ^ n - 1`. If `n`
is nonzero in `A`, it has the instance `IsCyclotomicExtension {n} A (CyclotomicRing n A K)`. -/
@[nolint unusedArguments]
def CyclotomicRing : Type w :=
  adjoin A {b : CyclotomicField n K | b ^ (n : ℕ) = 1}
--deriving CommRing, IsDomain, Inhabited
#align cyclotomic_ring CyclotomicRing

namespace CyclotomicRing

--Porting note: could not be derived
instance : CommRing (CyclotomicRing n A K) := by
  delta CyclotomicRing; infer_instance

--Porting note: could not be derived
instance : IsDomain (CyclotomicRing n A K) := by
  delta CyclotomicRing; infer_instance

--Porting note: could not be derived
instance : Inhabited (CyclotomicRing n A K) := by
  delta CyclotomicRing; infer_instance

/-- The `A`-algebra structure on `CyclotomicRing n A K`. -/
instance algebraBase : Algebra A (CyclotomicRing n A K) :=
  (adjoin A _).algebra
#align cyclotomic_ring.algebra_base CyclotomicRing.algebraBase

-- Ensure that there is no diamonds with ℤ.
example {n : ℕ+} : CyclotomicRing.algebraBase n ℤ ℚ = algebraInt _ :=
  rfl

instance : NoZeroSMulDivisors A (CyclotomicRing n A K) :=
  (adjoin A _).noZeroSMulDivisors_bot

theorem algebraBase_injective : Function.Injective <| algebraMap A (CyclotomicRing n A K) :=
  NoZeroSMulDivisors.algebraMap_injective _ _
#align cyclotomic_ring.algebra_base_injective CyclotomicRing.algebraBase_injective

instance : Algebra (CyclotomicRing n A K) (CyclotomicField n K) :=
  (adjoin A _).toAlgebra

theorem adjoin_algebra_injective :
    Function.Injective <| algebraMap (CyclotomicRing n A K) (CyclotomicField n K) :=
  Subtype.val_injective
#align cyclotomic_ring.adjoin_algebra_injective CyclotomicRing.adjoin_algebra_injective

instance : NoZeroSMulDivisors (CyclotomicRing n A K) (CyclotomicField n K) :=
  NoZeroSMulDivisors.of_algebraMap_injective (adjoin_algebra_injective n A K)

instance : IsScalarTower A (CyclotomicRing n A K) (CyclotomicField n K) :=
  IsScalarTower.subalgebra' _ _ _ _

instance isCyclotomicExtension [NeZero ((n : ℕ) : A)] :
    IsCyclotomicExtension {n} A (CyclotomicRing n A K) where
  exists_prim_root := @fun a han => by
    rw [mem_singleton_iff] at han
    subst a
    haveI := NeZero.of_noZeroSMulDivisors A K n
    haveI := NeZero.of_noZeroSMulDivisors A (CyclotomicField n K) n
    obtain ⟨μ, hμ⟩ := (CyclotomicField.isCyclotomicExtension n K).exists_prim_root (mem_singleton n)
    refine' ⟨⟨μ, subset_adjoin _⟩, _⟩
    · apply (isRoot_of_unity_iff n.pos (CyclotomicField n K)).mpr
      refine' ⟨n, Nat.mem_divisors_self _ n.ne_zero, _⟩
      rwa [← isRoot_cyclotomic_iff] at hμ
    · rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk]
  adjoin_roots x := by
    refine'
      adjoin_induction' (fun y hy => _) (fun a => _) (fun y z hy hz => _) (fun y z hy hz => _) x
    · refine' subset_adjoin _
      simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq]
      rwa [← Subalgebra.coe_eq_one, Subalgebra.coe_pow, Subtype.coe_mk]
    · exact Subalgebra.algebraMap_mem _ a
    · exact Subalgebra.add_mem _ hy hz
    · exact Subalgebra.mul_mem _ hy hz
#align cyclotomic_ring.is_cyclotomic_extension CyclotomicRing.isCyclotomicExtension

instance [IsDomain A] [NeZero ((n : ℕ) : A)] :
    IsFractionRing (CyclotomicRing n A K) (CyclotomicField n K) where
  map_units' := fun ⟨x, hx⟩ => by
    rw [isUnit_iff_ne_zero]
    apply map_ne_zero_of_mem_nonZeroDivisors
    apply adjoin_algebra_injective
    exact hx
  surj' x := by
    letI : NeZero ((n : ℕ) : K) := NeZero.nat_of_injective (IsFractionRing.injective A K)
    refine
      Algebra.adjoin_induction
        (((IsCyclotomicExtension.iff_singleton n K (CyclotomicField n K)).1
              (CyclotomicField.isCyclotomicExtension n K)).2
          x)
        (fun y hy => ?_) (fun k => ?_) ?_ ?_
    · refine' ⟨⟨⟨y, subset_adjoin hy⟩, 1⟩, _⟩
      simp only [OneMemClass.coe_one, map_one, mul_one]
      rfl
    · have : IsLocalization (nonZeroDivisors A) K := inferInstance
      replace := this.surj
      obtain ⟨⟨z, w⟩, hw⟩ := this k
      refine' ⟨⟨algebraMap A (CyclotomicRing n A K) z, algebraMap A (CyclotomicRing n A K) w,
        map_mem_nonZeroDivisors _ (algebraBase_injective n A K) w.2⟩, _⟩
      letI : IsScalarTower A K (CyclotomicField n K) :=
        IsScalarTower.of_algebraMap_eq (congr_fun rfl)
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        @IsScalarTower.algebraMap_apply A K _ _ _ _ _ (_root_.CyclotomicField.algebra n K) _ _ w,
        ← RingHom.map_mul, hw, ← IsScalarTower.algebraMap_apply]
    · rintro y z ⟨a, ha⟩ ⟨b, hb⟩
      refine' ⟨⟨a.1 * b.2 + b.1 * a.2, a.2 * b.2, mul_mem_nonZeroDivisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩
      rw [RingHom.map_mul, add_mul, ← mul_assoc, ha,
        mul_comm ((algebraMap (CyclotomicRing n A K) _) ↑a.2), ← mul_assoc, hb]
      simp only [map_add, map_mul]
    · rintro y z ⟨a, ha⟩ ⟨b, hb⟩
      refine' ⟨⟨a.1 * b.1, a.2 * b.2, mul_mem_nonZeroDivisors.2 ⟨a.2.2, b.2.2⟩⟩, _⟩
      rw [RingHom.map_mul, mul_comm ((algebraMap (CyclotomicRing n A K)  _) ↑a.2), mul_assoc, ←
        mul_assoc z, hb, ← mul_comm ((algebraMap (CyclotomicRing n A K)  _) ↑a.2), ← mul_assoc, ha]
      simp only [map_mul]
  eq_iff_exists' := @fun x y =>
    ⟨fun h => ⟨1, by rw [adjoin_algebra_injective n A K h]⟩, fun ⟨c, hc⟩ => by
      rw [mul_left_cancel₀ (nonZeroDivisors.ne_zero c.prop) hc]⟩

theorem eq_adjoin_primitive_root {μ : CyclotomicField n K} (h : IsPrimitiveRoot μ n) :
    CyclotomicRing n A K = adjoin A ({μ} : Set (CyclotomicField n K)) := by
  rw [← IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic h,
    IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots h]
  simp [CyclotomicRing]
#align cyclotomic_ring.eq_adjoin_primitive_root CyclotomicRing.eq_adjoin_primitive_root

end CyclotomicRing

end CyclotomicRing

end IsDomain

section IsAlgClosed

variable [IsAlgClosed K]

/-- Algebraically closed fields are `S`-cyclotomic extensions over themselves if
`NeZero ((a : ℕ) : K))` for all `a ∈ S`. -/
theorem IsAlgClosed.isCyclotomicExtension (h : ∀ a ∈ S, NeZero ((a : ℕ) : K)) :
    IsCyclotomicExtension S K K := by
  refine' ⟨@fun a ha => _, Algebra.eq_top_iff.mp <| Subsingleton.elim _ _⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero K _ (degree_cyclotomic_pos a K a.pos).ne'
  refine' ⟨r, _⟩
  haveI := h a ha
  rwa [coe_aeval_eq_eval, ← IsRoot.def, isRoot_cyclotomic_iff] at hr
#align is_alg_closed.is_cyclotomic_extension IsAlgClosed.isCyclotomicExtension

instance IsAlgClosedOfCharZero.isCyclotomicExtension [CharZero K] :
    ∀ S, IsCyclotomicExtension S K K := fun S =>
  IsAlgClosed.isCyclotomicExtension S K fun _ _ => inferInstance
#align is_alg_closed_of_char_zero.is_cyclotomic_extension IsAlgClosedOfCharZero.isCyclotomicExtension

end IsAlgClosed
