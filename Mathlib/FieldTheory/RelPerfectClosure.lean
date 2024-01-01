/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.FieldTheory.PerfectClosure

/-!

# Maximal purely inseparable subextension

This file contains basics about the maximal purely inseparable subextension
(or called relative perfect closure) of fields.

## Main definitions

- ...

## Main results

- ...

## Tags

separable degree, degree, perfect closure, purely inseparable

-/

open scoped Classical Polynomial

open FiniteDimensional Polynomial IntermediateField Field

noncomputable section

universe u v w

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

variable (K : Type w) [Field K] [Algebra F K]

section IsPerfectClosure

/-- A field is a perfect field (which means that any irreducible polynomial is separable)
if and only if every separable degree one polynomial splits. -/
theorem perfectField_iff_splits_of_natSepDegree_eq_one :
    PerfectField F ↔ ∀ f : F[X], f.natSepDegree = 1 → f.Splits (RingHom.id F) := by
  refine ⟨fun ⟨h⟩ f hf ↦ or_iff_not_imp_left.2 fun hn g hg hd ↦ ?_, fun h ↦ ?_⟩
  · rw [map_id] at hn hd
    have := natSepDegree_le_of_dvd g f hd hn
    rw [hf, (h hg).natSepDegree_eq_natDegree] at this
    exact (degree_eq_iff_natDegree_eq_of_pos one_pos).2 <| this.antisymm <|
      natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hg)
  obtain ⟨p, hchar⟩ := CharP.exists F
  by_cases hp : p = 0
  · haveI := (CharP.charP_zero_iff_charZero F).1 (hp ▸ hchar)
    exact PerfectField.ofCharZero F
  haveI := NeZero.mk hp
  haveI := CharP.char_is_prime_of_pos F p
  haveI := PerfectRing.ofSurjective F p fun x ↦ by
    haveI : ExpChar F p := ExpChar.prime Fact.out
    obtain ⟨y, hy⟩ := exists_root_of_splits _
      (h _ (pow_one p ▸ natSepDegree_X_pow_char_sub_C p 1 x))
      ((degree_X_pow_sub_C (expChar_pos F p) x).symm ▸ Nat.cast_pos.2 (expChar_pos F p)).ne'
    exact ⟨y, by rwa [← eval, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy⟩
  exact PerfectRing.toPerfectField F p

/-- If `E / F` is a field extension, then `E` is a perfect closure of `F` means that `E` is perfect
and `E / F` is purely inseparable. -/
class IsPerfectClosure : Prop where
  [perfectField : PerfectField E]
  [isPurelyInseparable : IsPurelyInseparable F E]

end IsPerfectClosure

section perfectClosure

/-- The (relative) perfect closure of `E / F`, or called maximal purely inseparable subextension
of `E / F`, is defined to be the compositum of all purely inseparable intermediate fields
of `E / F`. -/
irreducible_def perfectClosure : IntermediateField F E :=
  ⨆ L : { L : IntermediateField F E // IsPurelyInseparable F L }, L.1

/-- The (relative) perfect closure of `E / F` is purely inseparable over `F`. -/
instance perfectClosure.isPurelyInseparable : IsPurelyInseparable F (perfectClosure F E) := by
  rw [perfectClosure_def]
  haveI (L : { L : IntermediateField F E // IsPurelyInseparable F L }) :
      IsPurelyInseparable F L.1 := L.2
  exact isPurelyInseparable_iSup F E

/-- The (relative) perfect closure of `E / F` is algebraic over `F`. -/
theorem perfectClosure.isAlgebraic : Algebra.IsAlgebraic F (perfectClosure F E) :=
  IsPurelyInseparable.isAlgebraic F _

/-- An intermediate field of `E / F` is contained in the (relative) perfect closure of `E / F`
if it is purely inseparable over `F`. -/
theorem le_perfectClosure (L : IntermediateField F E) [h : IsPurelyInseparable F L] :
    L ≤ perfectClosure F E := by
  rw [perfectClosure_def]
  exact le_iSup (fun L : { L : IntermediateField F E // IsPurelyInseparable F L } ↦ L.1) ⟨L, h⟩

/-- An intermediate field of `E / F` is contained in the (relative) perfect closure of `E / F`
if and only if it is purely inseparable over `F`. -/
theorem le_perfectClosure_iff (L : IntermediateField F E) :
    L ≤ perfectClosure F E ↔ IsPurelyInseparable F L := by
  refine ⟨fun h ↦ ?_, fun _ ↦ le_perfectClosure F E L⟩
  letI := (inclusion h).toAlgebra
  letI : Module L (perfectClosure F E) := Algebra.toModule
  letI : SMul L (perfectClosure F E) := Algebra.toSMul
  haveI : IsScalarTower F L (perfectClosure F E) := SMul.comp.isScalarTower id
  exact IsPurelyInseparable.tower_bot F L (perfectClosure F E)

/-- If `F` is of exponential characteristic `q`, then an element `x` of `E` is contained in the
(relative) perfect closure of `E / F` if and only if there exists a natural number `n` such that
`x ^ (q ^ n)` is contained in `F`. -/
theorem mem_perfectClosure_iff (q : ℕ) [hF : ExpChar F q] {x : E} :
    x ∈ perfectClosure F E ↔ ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨n, y, h⟩ := (isPurelyInseparable_iff_mem_pow F _ q).1
      (perfectClosure.isPurelyInseparable F E) ⟨x, h⟩
    exact ⟨n, y, congr_arg (algebraMap _ E) h⟩
  haveI := (isPurelyInseparable_adjoin_simple_iff_mem_pow F E q).2 h
  exact le_perfectClosure F E F⟮x⟯ <| mem_adjoin_simple_self F x

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained in
`perfectClosure F K` if and only if `x` is contained in `perfectClosure F E`. -/
theorem map_mem_perfectClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ perfectClosure F K ↔ x ∈ perfectClosure F E := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  simp_rw [mem_perfectClosure_iff F _ q]
  refine ⟨fun ⟨n, y, h⟩ ↦ ⟨n, y, ?_⟩, fun ⟨n, y, h⟩ ↦ ⟨n, y, ?_⟩⟩
  · apply_fun i using i.injective
    rwa [AlgHom.commutes, map_pow]
  simpa only [AlgHom.commutes, map_pow] using congr_arg i h

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `perfectClosure F E` is equal to
the preimage of `perfectClosure F K` under the map `i`. -/
theorem perfectClosure.eq_comap_of_algHom (i : E →ₐ[F] K) :
    perfectClosure F E = (perfectClosure F K).comap i := by
  ext x
  exact (map_mem_perfectClosure_iff F E K i).symm

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `perfectClosure F K` contains
the image of `perfectClosure F E` under the map `i`. -/
theorem perfectClosure.map_le_of_algHom (i : E →ₐ[F] K) :
    (perfectClosure F E).map i ≤ perfectClosure F K := fun x hx ↦ by
  change x ∈ (_ : Set K) at hx
  rw [coe_map, Set.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (map_mem_perfectClosure_iff F E K i).2 hy

/-- If `i` is an `F`-algebra isomorphism of `E` and `K`, then `perfectClosure F K` is equal to
the image of `perfectClosure F E` under the map `i`. -/
theorem perfectClosure.eq_map_of_algEquiv (i : E ≃ₐ[F] K) :
    perfectClosure F K = (perfectClosure F E).map i.toAlgHom := by
  refine le_antisymm (fun x hx ↦ ?_) (map_le_of_algHom F E K i.toAlgHom)
  change x ∈ (_ : Set K)
  rw [coe_map, Set.mem_image]
  exact ⟨i.symm.toAlgHom x,
    (map_mem_perfectClosure_iff F K E i.symm.toAlgHom).2 hx, i.apply_symm_apply x⟩

/-- If `E` and `K` are isomorphic as `F`-algebras, then `perfectClosure F E` and
`perfectClosure F K` are also isomorphic as `F`-algebras. -/
def perfectClosure.algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    perfectClosure F E ≃ₐ[F] perfectClosure F K :=
  ((perfectClosure F E).intermediateFieldMap i).trans
    (equivOfEq (eq_map_of_algEquiv F E K i).symm)

-- TODO: move to suitable location
instance IntermediateField.charZero [CharZero F] (L : IntermediateField F E) :
    CharZero L := charZero_of_injective_algebraMap (algebraMap F _).injective

-- TODO: move to suitable location
instance IntermediateField.charP (p : ℕ) [CharP F p] (L : IntermediateField F E) :
    CharP L p := charP_of_injective_algebraMap (algebraMap F _).injective p

-- TODO: move to suitable location
instance IntermediateField.expChar (p : ℕ) [ExpChar F p] (L : IntermediateField F E) :
    ExpChar L p := expChar_of_injective_algebraMap (algebraMap F _).injective p

/-- If `E` is a perfect field of characteristic `p`, then the (relative) perfect closure
`perfectClosure F E` is perfect. -/
instance perfectClosure.perfectRing (p : ℕ) [Fact p.Prime] [CharP F p] [CharP E p]
    [PerfectRing E p] : PerfectRing (perfectClosure F E) p := .ofSurjective _ p fun x ↦ by
  haveI : ExpChar F p := ExpChar.prime Fact.out
  obtain ⟨x', hx⟩ := surjective_frobenius E p x.1
  obtain ⟨n, y, hy⟩ := (mem_perfectClosure_iff F E p).1 x.2
  rw [frobenius_def] at hx
  rw [← hx, ← pow_mul, ← pow_succ] at hy
  exact ⟨⟨x', (mem_perfectClosure_iff F E p).2 ⟨n + 1, y, hy⟩⟩, by
    simp_rw [frobenius_def, SubmonoidClass.mk_pow, hx]⟩

/-- If `E` is a perfect field, then the (relative) perfect closure
`perfectClosure F E` is a perfect closre of `F`. -/
instance perfectClosure.isPerfectClosure [PerfectField E] :
    IsPerfectClosure F (perfectClosure F E) where
  perfectField := by
    obtain ⟨p, hchar⟩ := CharP.exists F
    by_cases hp : p = 0
    · haveI := (CharP.charP_zero_iff_charZero F).1 (hp ▸ hchar)
      exact PerfectField.ofCharZero _
    haveI := NeZero.mk hp
    haveI := CharP.char_is_prime_of_pos F p
    haveI := charP_of_injective_algebraMap (algebraMap F E).injective p
    exact PerfectRing.toPerfectField _ p
  isPurelyInseparable := perfectClosure.isPurelyInseparable F E

end perfectClosure

section AbsolutePerfectClosure

namespace perfectClosure

variable (p : ℕ) [Fact p.Prime] [CharP F p]

private theorem mapPerfectClosure_aux (x : perfectClosure F E) :
    ∃ y : ℕ × F, (algebraMap F E) y.2 = x.1 ^ p ^ y.1 := by
  haveI : ExpChar F p := ExpChar.prime Fact.out
  obtain ⟨n, y, h⟩ := (mem_perfectClosure_iff F E p).1 x.2
  exact ⟨⟨n, y⟩, h⟩

/-- If `E / F` are fields of characteristic `p`, then there is a map from (relative)
perfect closure `perfectClosure F E` to the (absolute) perfect closure `PerfectClosure F p`. -/
def mapPerfectClosure (x : perfectClosure F E) :=
  PerfectClosure.mk F p <| Classical.choose <| mapPerfectClosure_aux F E p x

/-- If `E / F` are fields of characteristic `p`, `x` is an element of (relative) perfect closure
`perfectClosure F E` such that `x ^ (p ^ n) = y` for some `n : ℕ` and `y : F`, then
`perfectClosure.mapPerfectClosure` maps `x` to `PerfectClosure.mk F p (n, y)` (namely,
`y ^ (p ^ -n)`). -/
theorem mapPerfectClosure_apply
    (x : perfectClosure F E) (n : ℕ) (y : F) (h : (algebraMap F E) y = x.1 ^ p ^ n) :
    mapPerfectClosure F E p x = PerfectClosure.mk F p (n, y) := by
  rw [mapPerfectClosure, PerfectClosure.eq_iff']
  apply_fun (· ^ p ^ (Classical.choose <| mapPerfectClosure_aux F E p x).1) at h
  have h' := Classical.choose_spec <| mapPerfectClosure_aux F E p x
  apply_fun (· ^ p ^ n) at h'
  rw [← pow_mul, ← pow_add, add_comm] at h
  rw [← pow_mul, ← pow_add, ← h, ← map_pow, ← map_pow] at h'
  exact ⟨0, by simp only [add_zero, iterate_frobenius, (algebraMap F E).injective h']⟩

/-- If `E / F` are fields of characteristic `p`, then there is a ring homomorphism from (relative)
perfect closure `perfectClosure F E` to the (absolute) perfect closure `PerfectClosure F p`. -/
def ringHomPerfectClosure : perfectClosure F E →+* PerfectClosure F p where
  toFun := mapPerfectClosure F E p
  map_one' := by
    refine (mapPerfectClosure_apply F E p _ _ _ ?_).trans (PerfectClosure.one_def F p).symm
    simp only [map_one, OneMemClass.coe_one, one_pow]
  map_mul' x1 x2 := by
    haveI : ExpChar F p := ExpChar.prime Fact.out
    obtain ⟨n1, y1, h1⟩ := (mem_perfectClosure_iff F E p).1 x1.2
    obtain ⟨n2, y2, h2⟩ := (mem_perfectClosure_iff F E p).1 x2.2
    simp only [mapPerfectClosure_apply F E p _ _ _ h1, mapPerfectClosure_apply F E p _ _ _ h2,
      PerfectClosure.mk_mul_mk, iterate_frobenius]
    refine mapPerfectClosure_apply F E p _ _ _ ?_
    simp_rw [map_mul, map_pow, h1, h2, ← pow_mul, ← pow_add, add_comm n2 n1]
    exact mul_pow x1.1 x2.1 (p ^ (n1 + n2)) |>.symm
  map_zero' := by
    refine (mapPerfectClosure_apply F E p _ _ _ ?_).trans (PerfectClosure.zero_def F p).symm
    simp only [map_zero, ZeroMemClass.coe_zero, pow_zero, pow_one]
  map_add' x1 x2 := by
    haveI : ExpChar F p := ExpChar.prime Fact.out
    haveI := charP_of_injective_algebraMap' F E p
    obtain ⟨n1, y1, h1⟩ := (mem_perfectClosure_iff F E p).1 x1.2
    obtain ⟨n2, y2, h2⟩ := (mem_perfectClosure_iff F E p).1 x2.2
    simp only [mapPerfectClosure_apply F E p _ _ _ h1, mapPerfectClosure_apply F E p _ _ _ h2,
      PerfectClosure.mk_add_mk, iterate_frobenius]
    refine mapPerfectClosure_apply F E p _ _ _ ?_
    simp_rw [map_add, map_pow, h1, h2, ← pow_mul, ← pow_add, add_comm n2 n1]
    exact add_pow_char_pow E x1.1 x2.1 |>.symm

/-- If `E / F` are fields of characteristic `p`, then there is an `F`-algebra homomorphism from
(relative) perfect closure `perfectClosure F E` to the (absolute) perfect closure
`PerfectClosure F p`. -/
def algHomPerfectClosure :
    letI := (PerfectClosure.of F p).toAlgebra
    perfectClosure F E →ₐ[F] PerfectClosure F p :=
  letI := (PerfectClosure.of F p).toAlgebra
  {
    __ := ringHomPerfectClosure F E p
    commutes' := fun x ↦ mapPerfectClosure_apply F E p _ 0 x (by rw [pow_zero, pow_one]; rfl)
  }

-- TODO: move to suitable location
theorem _root_.PerfectClosure.lift_apply (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (L : Type v) [CommSemiring L] [CharP L p] [PerfectRing L p] (f : K →+* L) (x : ℕ × K) :
    PerfectClosure.lift K p L f (PerfectClosure.mk K p x) =
    (frobeniusEquiv L p).symm^[x.1] (f x.2) := by
  simp only [PerfectClosure.lift, Equiv.coe_fn_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    PerfectClosure.liftOn_mk]

-- TODO: move to suitable location
theorem _root_.iterate_frobeniusEquiv_symm_apply_iterate_frobenius (R : Type*) (p : ℕ)
    [CommSemiring R] [Fact p.Prime] [CharP R p] [PerfectRing R p] (x : R) (n : ℕ) :
    (frobeniusEquiv R p).symm^[n] ((frobenius R p)^[n] x) = x := by
  induction' n with n ih
  · rfl
  rwa [Function.iterate_succ_apply, Function.iterate_succ_apply',
    frobeniusEquiv_symm_apply_frobenius]

-- TODO: move to suitable location
theorem _root_.iterate_frobenius_apply_iterate_frobeniusEquiv_symm (R : Type*) (p : ℕ)
    [CommSemiring R] [Fact p.Prime] [CharP R p] [PerfectRing R p] (x : R) (n : ℕ) :
    (frobenius R p)^[n] ((frobeniusEquiv R p).symm^[n] x) = x := by
  induction' n with n ih
  · rfl
  rwa [Function.iterate_succ_apply, Function.iterate_succ_apply',
    frobenius_apply_frobeniusEquiv_symm]

variable [CharP E p] [PerfectRing E p]

/-- If `E` is a perfect field of characteristic `p`, then the (relative) perfect closure
`perfectClosure F E` is isomorphic to the (absolute) perfect closure `PerfectClosure F p`
as rings. -/
def ringEquivPerfectClosure : perfectClosure F E ≃+* PerfectClosure F p where
  __ := ringHomPerfectClosure F E p
  invFun := PerfectClosure.lift F p (perfectClosure F E) (algebraMap F _)
  left_inv x := by
    haveI : ExpChar F p := ExpChar.prime Fact.out
    obtain ⟨n, y, h⟩ := (mem_perfectClosure_iff F E p).1 x.2
    simp only [ringHomPerfectClosure, RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk,
      OneHom.toFun_eq_coe, OneHom.coe_mk, mapPerfectClosure_apply F E p x n y h,
      PerfectClosure.lift_apply]
    replace h : (algebraMap F (perfectClosure F E)) y = x ^ p ^ n := (algebraMap _ E).injective h
    apply_fun (frobeniusEquiv (perfectClosure F E) p).symm^[n] at h
    rw [h, ← iterate_frobenius, iterate_frobeniusEquiv_symm_apply_iterate_frobenius]
  right_inv x := PerfectClosure.induction_on x fun x ↦ by
    simp only [RingHom.toMonoidHom_eq_coe, PerfectClosure.lift_apply, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    refine mapPerfectClosure_apply F E p _ x.1 x.2 ?_
    have := congr_arg (algebraMap _ E) (iterate_frobenius_apply_iterate_frobeniusEquiv_symm
      (perfectClosure F E) p (algebraMap F (perfectClosure F E) x.2) x.1).symm
    rwa [iterate_frobenius, map_pow] at this

/-- If `E` is a perfect field of characteristic `p`, then the (relative) perfect closure
`perfectClosure F E` is isomorphic to the (absolute) perfect closure `PerfectClosure F p`
as `F`-algebras. -/
def algEquivPerfectClosure :
    letI := (PerfectClosure.of F p).toAlgebra
    perfectClosure F E ≃ₐ[F] PerfectClosure F p :=
  letI := (PerfectClosure.of F p).toAlgebra
  {
    __ := ringEquivPerfectClosure F E p
    commutes' := (algHomPerfectClosure F E p).commutes'
  }

end perfectClosure

end AbsolutePerfectClosure
