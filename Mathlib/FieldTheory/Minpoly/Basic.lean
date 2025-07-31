/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`, and derives some basic properties
such as irreducibility under the assumption `B` is a domain.

-/


open Polynomial Set Function

variable {A B B' : Type*}

section MinPolyDef

variable (A) [CommRing A] [Ring B] [Algebra A B]

open scoped Classical in
/-- Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`IsIntegral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
@[stacks 09GM]
noncomputable def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0

end MinPolyDef

namespace minpoly

section Ring

variable [CommRing A] [Ring B] [Ring B'] [Algebra A B] [Algebra A B']
variable {x : B}

/-- A minimal polynomial is monic. -/
theorem monic (hx : IsIntegral A x) : Monic (minpoly A x) := by
  delta minpoly
  rw [dif_pos hx]
  exact (degree_lt_wf.min_mem _ hx).1

/-- A minimal polynomial is nonzero. -/
theorem ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly A x ≠ 0 :=
  (monic hx).ne_zero

theorem eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0 :=
  dif_neg hx

theorem ne_zero_iff [Nontrivial A] : minpoly A x ≠ 0 ↔ IsIntegral A x :=
  ⟨fun h => of_not_not <| eq_zero.mt h, ne_zero⟩

theorem algHom_eq (f : B →ₐ[A] B') (hf : Function.Injective f) (x : B) :
    minpoly A (f x) = minpoly A x := by
  classical
  simp_rw [minpoly, isIntegral_algHom_iff _ hf, ← Polynomial.aeval_def, aeval_algHom,
    AlgHom.comp_apply, _root_.map_eq_zero_iff f hf]

theorem algebraMap_eq {B} [CommRing B] [Algebra A B] [Algebra B B'] [IsScalarTower A B B']
    (h : Function.Injective (algebraMap B B')) (x : B) :
    minpoly A (algebraMap B B' x) = minpoly A x :=
  algHom_eq (IsScalarTower.toAlgHom A B B') h x

@[simp]
theorem algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f x) = minpoly A x :=
  algHom_eq (f : B →ₐ[A] B') f.injective x

variable (A x)

/-- An element is a root of its minimal polynomial. -/
@[simp]
theorem aeval : aeval x (minpoly A x) = 0 := by
  delta minpoly
  split_ifs with hx
  · exact (degree_lt_wf.min_mem _ hx).2
  · exact aeval_zero _

/-- Given any `f : B →ₐ[A] B'` and any `x : L`, the minimal polynomial of `x` vanishes at `f x`. -/
@[simp]
theorem aeval_algHom (f : B →ₐ[A] B') (x : B) : (Polynomial.aeval (f x)) (minpoly A x) = 0 := by
  rw [Polynomial.aeval_algHom, AlgHom.coe_comp, comp_apply, aeval, map_zero]

/-- A minimal polynomial is not `1`. -/
theorem ne_one [Nontrivial B] : minpoly A x ≠ 1 := by
  intro h
  refine (one_ne_zero : (1 : B) ≠ 0) ?_
  simpa using congr_arg (Polynomial.aeval x) h

theorem map_ne_one [Nontrivial B] {R : Type*} [Semiring R] [Nontrivial R] (f : A →+* R) :
    (minpoly A x).map f ≠ 1 := by
  by_cases hx : IsIntegral A x
  · exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x)
  · rw [eq_zero hx, Polynomial.map_zero]
    exact zero_ne_one

/-- A minimal polynomial is not a unit. -/
theorem not_isUnit [Nontrivial B] : ¬IsUnit (minpoly A x) := by
  haveI : Nontrivial A := (algebraMap A B).domain_nontrivial
  by_cases hx : IsIntegral A x
  · exact mt (monic hx).eq_one_of_isUnit (ne_one A x)
  · rw [eq_zero hx]
    exact not_isUnit_zero

theorem mem_range_of_degree_eq_one (hx : (minpoly A x).degree = 1) :
    x ∈ (algebraMap A B).range := by
  have h : IsIntegral A x := by
    by_contra h
    rw [eq_zero h, degree_zero, ← WithBot.coe_one] at hx
    exact ne_of_lt (show ⊥ < ↑1 from WithBot.bot_lt_coe 1) hx
  have key := minpoly.aeval A x
  rw [eq_X_add_C_of_degree_eq_one hx, (minpoly.monic h).leadingCoeff, C_1, one_mul, aeval_add,
    aeval_C, aeval_X, ← eq_neg_iff_add_eq_zero, ← RingHom.map_neg] at key
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩

/-- The defining property of the minimal polynomial of an element `x`:
it is the monic polynomial with smallest degree that has `x` as its root. -/
theorem min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0) :
    degree (minpoly A x) ≤ degree p := by
  delta minpoly; split_ifs with hx
  · exact le_of_not_gt (degree_lt_wf.not_lt_min _ hx ⟨pmonic, hp⟩)
  · simp only [degree_zero, bot_le]

theorem unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeval x p = 0)
    (hl : ∀ q : A[X], degree q < degree p → q = 0 ∨ Polynomial.aeval x q ≠ 0) :
    p = minpoly A x := by
  nontriviality A
  have hx : IsIntegral A x := ⟨p, hm, hp⟩
  obtain h | h := hl _ ((minpoly A x).degree_modByMonic_lt hm)
  swap
  · exact (h <| (aeval_modByMonic_eq_self_of_root hm hp).trans <| aeval A x).elim
  obtain ⟨r, hr⟩ := (modByMonic_eq_zero_iff_dvd hm).1 h
  rw [hr]
  have hlead := congr_arg leadingCoeff hr
  rw [mul_comm, leadingCoeff_mul_monic hm, (monic hx).leadingCoeff] at hlead
  have : natDegree r ≤ 0 := by
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact ne_zero hx (mul_zero p ▸ hr)
    apply_fun natDegree at hr
    rw [hm.natDegree_mul' hr0] at hr
    apply Nat.le_of_add_le_add_left
    rw [add_zero]
    exact hr.symm.trans_le (natDegree_le_natDegree <| min A x hm hp)
  rw [eq_C_of_natDegree_le_zero this, ← Nat.eq_zero_of_le_zero this, ← leadingCoeff, ← hlead, C_1,
    mul_one]

@[nontriviality]
theorem subsingleton [Subsingleton B] : minpoly A x = 1 := by
  nontriviality A
  have := minpoly.min A x monic_one (Subsingleton.elim _ _)
  rw [degree_one] at this
  rcases le_or_gt (minpoly A x).degree 0 with h | h
  · rwa [(monic ⟨1, monic_one, by simp [eq_iff_true_of_subsingleton]⟩ :
           (minpoly A x).Monic).degree_le_zero_iff_eq_one] at h
  · exact (this.not_gt h).elim

end Ring

section CommRing

variable [CommRing A]

section Ring

variable [Ring B] [Algebra A B]
variable {x : B}

/-- The degree of a minimal polynomial, as a natural number, is positive. -/
theorem natDegree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < natDegree (minpoly A x) := by
  rw [pos_iff_ne_zero]
  intro ndeg_eq_zero
  have eq_one : minpoly A x = 1 := by
    rw [eq_C_of_natDegree_eq_zero ndeg_eq_zero]
    convert C_1 (R := A)
    simpa only [ndeg_eq_zero.symm] using (monic hx).leadingCoeff
  simpa only [eq_one, map_one, one_ne_zero] using aeval A x

/-- The degree of a minimal polynomial is positive. -/
theorem degree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < degree (minpoly A x) :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos hx)

section
variable [Nontrivial B]

open Polynomial in
theorem degree_eq_one_iff : (minpoly A x).degree = 1 ↔ x ∈ (algebraMap A B).range := by
  refine ⟨minpoly.mem_range_of_degree_eq_one _ _, ?_⟩
  rintro ⟨x, rfl⟩
  haveI := Module.nontrivial A B
  exact (degree_X_sub_C x ▸ minpoly.min A (algebraMap A B x) (monic_X_sub_C x) (by simp)).antisymm
    (Nat.WithBot.add_one_le_of_lt <| minpoly.degree_pos isIntegral_algebraMap)

theorem natDegree_eq_one_iff :
    (minpoly A x).natDegree = 1 ↔ x ∈ (algebraMap A B).range := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos zero_lt_one]
  exact degree_eq_one_iff

theorem two_le_natDegree_iff (int : IsIntegral A x) :
    2 ≤ (minpoly A x).natDegree ↔ x ∉ (algebraMap A B).range := by
  rw [iff_not_comm, ← natDegree_eq_one_iff, not_le]
  exact ⟨fun h ↦ h.trans_lt one_lt_two, fun h ↦ by linarith only [minpoly.natDegree_pos int, h]⟩

theorem two_le_natDegree_subalgebra {B} [CommRing B] [Algebra A B] [Nontrivial B]
    {S : Subalgebra A B} {x : B} (int : IsIntegral S x) : 2 ≤ (minpoly S x).natDegree ↔ x ∉ S := by
  rw [two_le_natDegree_iff int, Iff.not]
  apply Set.ext_iff.mp Subtype.range_val_subtype

end

/-- If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebraMap A B a` is `X - C a`. -/
theorem eq_X_sub_C_of_algebraMap_inj (a : A) (hf : Function.Injective (algebraMap A B)) :
    minpoly A (algebraMap A B a) = X - C a := by
  nontriviality A
  refine (unique' A _ (monic_X_sub_C a) ?_ ?_).symm
  · rw [map_sub, aeval_C, aeval_X, sub_self]
  simp_rw [or_iff_not_imp_left]
  intro q hl h0
  rw [← natDegree_lt_natDegree_iff h0, natDegree_X_sub_C, Nat.lt_one_iff] at hl
  rw [eq_C_of_natDegree_eq_zero hl] at h0 ⊢
  rwa [aeval_C, map_ne_zero_iff _ hf, ← C_ne_zero]

end Ring

section IsDomain

variable [Ring B] [Algebra A B]
variable {x : B}

/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
theorem aeval_ne_zero_of_dvdNotUnit_minpoly {a : A[X]} (hx : IsIntegral A x) (hamonic : a.Monic)
    (hdvd : DvdNotUnit a (minpoly A x)) : Polynomial.aeval x a ≠ 0 := by
  refine fun ha => (min A x hamonic ha).not_gt (degree_lt_degree ?_)
  obtain ⟨_, c, hu, he⟩ := hdvd
  have hcm := hamonic.of_mul_monic_left (he.subst <| monic hx)
  rw [he, hamonic.natDegree_mul hcm]
  -- TODO: port Nat.lt_add_of_zero_lt_left from lean3 core
  apply lt_add_of_pos_right
  refine (lt_of_not_ge fun h => hu ?_)
  rw [eq_C_of_natDegree_le_zero h, ← Nat.eq_zero_of_le_zero h, ← leadingCoeff, hcm.leadingCoeff,
    C_1]
  exact isUnit_one

variable [IsDomain A] [IsDomain B]

/-- A minimal polynomial is irreducible. -/
theorem irreducible (hx : IsIntegral A x) : Irreducible (minpoly A x) := by
  refine (irreducible_of_monic (monic hx) <| ne_one A x).2 fun f g hf hg he => ?_
  rw [← hf.isUnit_iff, ← hg.isUnit_iff]
  by_contra! h
  have heval := congr_arg (Polynomial.aeval x) he
  rw [aeval A x, aeval_mul, mul_eq_zero] at heval
  rcases heval with heval | heval
  · exact aeval_ne_zero_of_dvdNotUnit_minpoly hx hf ⟨hf.ne_zero, g, h.2, he.symm⟩ heval
  · refine aeval_ne_zero_of_dvdNotUnit_minpoly hx hg ⟨hg.ne_zero, f, h.1, ?_⟩ heval
    rw [mul_comm, he]

end IsDomain

end CommRing

end minpoly
