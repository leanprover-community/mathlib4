/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.Instances.ZMod

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Homotopy.Lifting

/-!
# Examples of Pontryagin duals

This file constructs explicit isomorphisms for Pontryagin duals of particular topological groups.

## Main definitions and results

* `AddChar.exists_eq_probChar_mulShift`: Every continuous circle-valued character of `ℝ` is a
  multiplicative shift of `Real.probChar`.
* `Circle.exists_eq_zpowGroupHom`: Every continuous endomorphism of `Circle` is of the form
  `z ↦ z ^ n` for some `n : ℤ`.
* `PontryaginDual.zmodEquiv`: A finite cyclic group is isomorphic to its Pontryagin dual.
* `PontryaginDual.intEquiv`: The Pontryagin dual of `ℤ` is isomorphic to `Circle`.
* `PontryaginDual.realEquiv`: The Pontryagin dual of `ℝ` is isomorphic to `ℝ`.
* `PontryaginDual.circleEquiv`: The Pontryagin dual of `Circle` is isomorphic to `ℤ`.

Additive groups are written using `Multiplicative`, as `PontryaginDual` takes a multiplicative
group.
-/

noncomputable section

open Real ContinuousMonoidHom

/-- Every continuous circle-valued character of `ℝ` is a multiplicative shift of
`Real.probChar`. -/
public theorem AddChar.exists_eq_probChar_mulShift (χ : AddChar ℝ Circle) (hχ : Continuous χ) :
    ∃ a : ℝ, χ = Real.probChar.mulShift a := by
  obtain ⟨F, ⟨hF0, hF⟩, _⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts ⟨χ, hχ⟩ 0 0 (by simp)
  have hF' (t : ℝ) : Circle.exp (F t) = χ t := congr_fun hF t
  -- The lift is additive by uniqueness of lifts.
  have hadd (s t : ℝ) : F (s + t) = F s + F t := by
    apply congr_fun _ t
    refine Circle.isCoveringMap_exp.eq_of_comp_eq (by fun_prop) (by fun_prop) ?_ 0 (by simp [hF0])
    ext t
    simp [hF', map_add_eq_mul]
  have eq_aux (t : ℝ) : F t = t * F 1 := by
    simpa using map_real_smul (AddMonoidHom.mk' F hadd) F.continuous t 1
  exact ⟨F 1, AddChar.ext _ _ fun t ↦ by simp [← hF', eq_aux t, mul_comm, probChar_apply']⟩

/-- Every continuous endomorphism of the circle is of the form `z ↦ z ^ n` for some `n : ℤ`. -/
public theorem Circle.exists_eq_zpowGroupHom (χ : Circle →* Circle) (hχ : Continuous χ) :
    ∃ n : ℤ, χ = zpowGroupHom n := by
  obtain ⟨a, ha⟩ := AddChar.exists_eq_probChar_mulShift (χ.compAddChar Real.probChar)
    (hχ.comp Circle.exp.continuous)
  have ha' (t : ℝ) : χ (Circle.exp t) = Circle.exp (a * t) := congr($ha _)
  have : Circle.exp (a * (2 * π)) = 1 := by simp [← ha']
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp this
  rw [mul_left_inj' (by positivity)] at hn
  refine ⟨n, MonoidHom.ext <| Circle.exp_surjective.forall.mpr fun t ↦ ?_⟩
  simpa [hn] using ha' t

namespace PontryaginDual

section ZMod

variable (n : ℕ) [NeZero n]

/-- The character of `ZMod n` indexed by `x`, using the standard finite cyclic pairing. -/
def zmodChar : Multiplicative (ZMod n) →* PontryaginDual (Multiplicative (ZMod n)) where
  toFun x := ⟨(AddChar.zmod n x.toAdd).toMonoidHom, continuous_of_discreteTopology⟩
  map_one' := by ext1 x; exact congr($(AddChar.zmod_zero n) x.toAdd)
  map_mul' x y := by ext1 z; exact congr($(AddChar.zmod_add x.toAdd y.toAdd) z.toAdd)

@[simp]
theorem zmodChar_apply (x y : Multiplicative (ZMod n)) :
    zmodChar n x y = AddChar.zmod n x.toAdd y.toAdd := rfl

theorem zmodChar_bijective : Function.Bijective (zmodChar n) := by
  refine ⟨fun x y h ↦ ?_, fun χ ↦ ?_⟩
  · apply Multiplicative.toAdd.injective
    apply AddChar.zmod_injective
    ext z
    exact congr($h (Multiplicative.ofAdd z))
  · let ψ := AddChar.toMonoidHomEquiv.symm χ.toMonoidHom
    obtain ⟨x, hx⟩ := (AddChar.zmodAddEquiv (n := n)).surjective (AddChar.circleEquivComplex ψ)
    exact ⟨.ofAdd x, ext fun y ↦ congr($(AddChar.circleEquivComplex.injective hx) y.toAdd)⟩

/-- A finite cyclic group is isomorphic to its Pontryagin dual. -/
public def zmodEquiv : Multiplicative (ZMod n) ≃ₜ* PontryaginDual (Multiplicative (ZMod n)) :=
  (MulEquiv.ofBijective (zmodChar n) (zmodChar_bijective n)).toContinuousMulEquiv
    fun _ ↦ by simp [isOpen_discrete]

@[simp]
public theorem zmodEquiv_apply (x y : Multiplicative (ZMod n)) :
    zmodEquiv n x y = AddChar.zmod n x.toAdd y.toAdd := by rfl

public theorem zmodEquiv_apply_intCast (x y : ℤ) :
    zmodEquiv n (.ofAdd (x : ZMod n)) (.ofAdd (y : ZMod n)) =
      Circle.exp (2 * π * (x * y / n)) := by simp

end ZMod

section Int

/-- The Pontryagin dual of `ℤ` is isomorphic to the circle, via `z ↦ (n ↦ z ^ n)`. -/
public def intEquiv : Circle ≃ₜ* PontryaginDual (Multiplicative ℤ) where
  toFun z := ⟨zpowersHom Circle z, continuous_of_discreteTopology⟩
  invFun χ := χ (.ofAdd 1)
  left_inv z := zpow_one z
  right_inv χ := by ext1 n; exact (MonoidHom.apply_mint Circle χ.toMonoidHom n).symm
  map_mul' z w := by ext1 n; exact mul_zpow z w n.toAdd
  continuous_toFun := continuous_of_continuous_uncurry _ <|
    continuous_prod_of_discrete_right.mpr fun n ↦ continuous_zpow n.toAdd
  continuous_invFun := continuous_eval_const _

@[simp]
public theorem intEquiv_apply (z : Circle) (n : Multiplicative ℤ) :
    intEquiv z n = z ^ n.toAdd := by rfl

@[simp]
public theorem intEquiv_symm_apply (χ : PontryaginDual (Multiplicative ℤ)) :
    intEquiv.symm χ = χ (.ofAdd 1) := by rfl

end Int

section Real

/-- The real character with frequency `a`, given by `t ↦ exp (a * t * I)`. -/
def realChar : Multiplicative ℝ →* PontryaginDual (Multiplicative ℝ) where
  toFun a := ⟨(Real.probChar.mulShift a.toAdd).toMonoidHom,
    Circle.exp.continuous.comp (continuous_const.mul continuous_toAdd)⟩
  map_one' := by ext1 t; exact congr($(Real.probChar.mulShift_zero) t.toAdd)
  map_mul' a b := by
    ext1 t
    exact congr($(Real.probChar.mulShift_mul a.toAdd b.toAdd) t.toAdd).symm

@[simp]
theorem realChar_apply (a t : Multiplicative ℝ) :
    realChar a t = Circle.exp (a.toAdd * t.toAdd) := rfl

theorem realChar_bijective : Function.Bijective realChar := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun a ha ↦ ?_, fun χ ↦ ?_⟩
  · by_contra h
    apply Real.probChar_ne_one
    rw [← Real.probChar.mulShift_unit_eq_one_iff (isUnit_iff_ne_zero.mpr h)]
    exact AddChar.ext _ _ fun t ↦ congr($ha (Multiplicative.ofAdd t))
  · obtain ⟨a, ha⟩ :=
      AddChar.exists_eq_probChar_mulShift (AddChar.toMonoidHomEquiv.symm χ.toMonoidHom)
        ((map_continuous χ).comp continuous_ofAdd)
    exact ⟨.ofAdd a, ext fun t ↦ congr($ha t.toAdd).symm⟩

theorem continuous_realChar : Continuous realChar :=
  continuous_of_continuous_uncurry _ <| Circle.exp.continuous.comp <|
    continuous_toAdd.fst'.mul continuous_toAdd.snd'

theorem isOpenMap_realChar : IsOpenMap realChar :=
  realChar.isOpenMap_of_sigmaCompact realChar_bijective.surjective continuous_realChar

/-- The Pontryagin dual of `ℝ` is isomorphic to `ℝ`, via `a ↦ (t ↦ exp (a * t * I))`. -/
public def realEquiv : Multiplicative ℝ ≃ₜ* PontryaginDual (Multiplicative ℝ) :=
  (MulEquiv.ofBijective realChar realChar_bijective).toContinuousMulEquiv fun _ ↦
    ((isOpenMap_realChar).isQuotientMap continuous_realChar
      realChar_bijective.surjective).isOpen_preimage

@[simp]
public theorem realEquiv_apply (a t : Multiplicative ℝ) :
    realEquiv a t = Circle.exp (a.toAdd * t.toAdd) := by rfl

end Real

section Circle

/-- The homomorphism `ℤ → PontryaginDual Circle` sending `n` to the character `z ↦ z ^ n`. -/
def zpowCircle : Multiplicative ℤ →* PontryaginDual Circle where
  toFun n := (⟨zpowGroupHom n.toAdd, continuous_zpow _⟩ : Circle →ₜ* Circle)
  map_one' := by ext1 z; exact zpow_zero z
  map_mul' m n := by ext1 z; exact zpow_add z _ _

@[simp]
theorem zpowCircle_apply (n : Multiplicative ℤ) (z : Circle) :
    zpowCircle n z = z ^ n.toAdd := rfl

theorem zpowCircle_bijective : Function.Bijective zpowCircle := by
  refine ⟨(injective_iff_map_eq_one _).mpr fun n hn ↦ ?_, fun χ ↦ ?_⟩
  · by_contra h
    have hn' : (n.toAdd : ℝ) ≠ 0 := by simpa using h
    apply Circle.exp_pi_ne_one
    simpa [← Circle.exp_intCast_mul, mul_div_cancel₀ _ hn'] using
      congr($hn (Circle.exp (π / n.toAdd)))
  · obtain ⟨n, hn⟩ := Circle.exists_eq_zpowGroupHom χ.toMonoidHom (map_continuous χ)
    exact ⟨.ofAdd n, ext fun z ↦ congr($hn z).symm⟩

/-- The Pontryagin dual of the circle is isomorphic to `ℤ`. -/
public def circleEquiv : Multiplicative ℤ ≃ₜ* PontryaginDual Circle :=
  (MulEquiv.ofBijective zpowCircle zpowCircle_bijective).toContinuousMulEquiv
    fun _ ↦ by simp [isOpen_discrete]

@[simp]
public theorem circleEquiv_apply (n : Multiplicative ℤ) (z : Circle) :
    circleEquiv n z = z ^ n.toAdd := by rfl

end Circle

end PontryaginDual
