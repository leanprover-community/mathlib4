/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.RingTheory.OreLocalization.Basic
/-!

# Algebra instances of Ore Localizations

If `R` is a commutative ring with submonoid `S`, and if `A` is a commutative `R`-algebra,
then this file gives `A[S⁻¹]` the structure of an`R[S⁻¹]`-algebra.

-/

namespace OreLocalization

section CommMagma

variable {R A : Type*} [CommMonoid R] [CommMagma A] [MulAction R A] [IsScalarTower R A A]
  {S : Submonoid R}

@[to_additive]
private def mul' (a₁ : A) (s₁ : S) (a₂ : A) (s₂ : S) : A[S⁻¹] :=
  a₁ * a₂ /ₒ (s₂ * s₁)

@[to_additive]
private def mul''
  (a : A) (s : S) : A[S⁻¹] → A[S⁻¹] :=
  liftExpand (mul' a s) fun a₁ r₁ ⟨s₁, hs₁⟩ hr₁s₁ => by
  unfold OreLocalization.mul'
  simp only at hr₁s₁ ⊢
  rw [oreDiv_eq_iff]
  use ⟨s₁, hs₁⟩, r₁ * s₁
  simp only [Submonoid.mk_smul, Submonoid.coe_mul]
  constructor
  · -- lol this was fun. Do we have a tactic for this?
    rw [← smul_mul_assoc, ← smul_mul_assoc, mul_comm, smul_mul_assoc, smul_mul_assoc, mul_comm,
      smul_mul_assoc, ← mul_smul] --
  · obtain ⟨s₂, hs₂⟩ := s
    simpa only [Submonoid.mk_smul, Submonoid.coe_mul] using mul_left_comm s₁ (r₁ * s₁) s₂

/-- The multiplication on `A[S⁻¹]` induced from the multiplication on `A`.
-/
@[to_additive
  "The addition on `AddOreLocalization S A` induced from the
  addition on `A`."]
protected def mul : A[S⁻¹] → A[S⁻¹] → A[S⁻¹] :=
  liftExpand mul'' fun a₁ r₁ s hs => by
  obtain ⟨s₁, hs₁⟩ := s
  unfold OreLocalization.mul'' OreLocalization.mul'
  ext sa
  induction' sa with a s_temp
  obtain ⟨s, hs⟩ := s_temp
  simp only [liftExpand_of, oreDiv_eq_iff, Submonoid.mk_smul, Submonoid.coe_mul]
  use ⟨s₁, hs₁⟩, r₁ * s₁
  simp only [Submonoid.mk_smul, Submonoid.coe_mul]
  constructor
  · rw [smul_mul_assoc, ← mul_smul, mul_comm]
  · repeat rw [mul_assoc]
    repeat rw [mul_left_comm s₁]
    rw [mul_left_comm s]

instance : Mul (A[S⁻¹]) where
  mul := OreLocalization.mul

protected lemma mul_def (a : A) (s : { x // x ∈ S }) (b : A) (t : { x // x ∈ S }) :
    a /ₒ s * (b /ₒ t) = a * b /ₒ (t * s) := rfl

-- no diamond
example (as bt : R[S⁻¹]) : as * bt = as • bt := rfl

end CommMagma

section One

variable {R A : Type*} [CommMonoid R] [MulAction R A] [One A] {S : Submonoid R}

instance instOne' : One (A[S⁻¹]) where
  one := 1 /ₒ 1

protected theorem one_def' : (1 : A[S⁻¹]) = 1 /ₒ 1 := rfl

end One

section CommMonoid

variable {R A : Type*} [CommMonoid R] [CommMonoid A] [MulAction R A] [IsScalarTower R A A]
  {S : Submonoid R}

instance instCommMonoid' : CommMonoid (A[S⁻¹]) where
  mul_assoc a b c := by
    induction' a with a
    induction' b with b
    induction' c with c
    simp only [OreLocalization.mul_def, mul_assoc]
  one_mul a := by
    induction' a with a
    simp only [OreLocalization.one_def', OreLocalization.mul_def, one_mul, mul_one]
  mul_one a := by
    induction' a with a s
    simp only [OreLocalization.one_def', OreLocalization.mul_def, mul_one, one_mul]
  mul_comm a b := by
    induction' a with a
    induction' b with b
    simp only [OreLocalization.mul_def, mul_comm]

end CommMonoid

section CommSemiring

variable {R A : Type*} [CommMonoid R] [CommSemiring A] [DistribMulAction R A] [IsScalarTower R A A]
  {S : Submonoid R}

theorem left_distrib' (a b c : A[S⁻¹]) :
    a * (b + c) = a * b + a * c := by
  induction' a with a r
  induction' b with b s
  induction' c with c t
  rcases oreDivAddChar' b c s t with ⟨r₁, s₁, h₁, q⟩; rw [q]; clear q
  simp only [OreLocalization.mul_def]
  rcases oreDivAddChar' (a * b) (a * c) (s * r) (t * r) with ⟨r₂, s₂, h₂, q⟩; rw [q]; clear q
  rw [oreDiv_eq_iff]
  obtain ⟨t, ht⟩ := t
  obtain ⟨s₂, hs₂⟩ := s₂
  simp only [Submonoid.mk_smul, Submonoid.coe_mul] at h₁ h₂ ⊢
  rw [h₂, h₁]
  use s₁ * s * r, s₂ * s * r
  obtain ⟨s₁, hs₁⟩ := s₁
  obtain ⟨s, hs⟩ := s
  obtain ⟨r, hr⟩ := r
  simp only [Submonoid.mk_mul_mk, smul_add, Submonoid.mk_smul] at h₁ h₂ ⊢
  constructor
  · rw [mul_add, smul_add]
    congr 1
    · rw [smul_smul, mul_comm a (s₁ • b), show s₁ * s * r * s₂ = (s₂ * s * r) * s₁ by
        rw [mul_comm, mul_assoc, mul_assoc, mul_assoc, mul_comm s₁, mul_assoc]]
      rw [mul_smul]
      congr 1
      rw [mul_comm, smul_mul_assoc]
    · rw [h₁, mul_assoc s₂, h₂, mul_comm r₂, mul_assoc, mul_comm r₁, mul_smul, mul_smul (t * r)]
      congr 1
      rw [smul_smul, mul_comm, mul_smul, mul_comm a, mul_comm a, smul_mul_assoc]
  · rw [mul_assoc s₂, h₂, h₁]
    repeat rw [← mul_assoc]
    congr 2
    rw [mul_right_comm _ r, mul_right_comm _ r]
    congr 1
    rw [mul_comm, mul_assoc, mul_comm r₁]

instance instCommSemiring' : CommSemiring A[S⁻¹] where
  __ := instCommMonoid'
  left_distrib := left_distrib'
  right_distrib a b c := by
    rw [mul_comm, mul_comm a, mul_comm b, left_distrib']
  zero_mul a := by
    induction' a with a s
    rw [OreLocalization.zero_def, OreLocalization.mul_def, zero_mul,
      mul_one, zero_oreDiv, zero_oreDiv]
  mul_zero a := by
    induction' a with a s
    rw [OreLocalization.zero_def, OreLocalization.mul_def, mul_zero,
      one_mul, zero_oreDiv, zero_oreDiv]

end CommSemiring

section Algebra

variable (R A : Type*) [cR : CommSemiring R] [cA : CommSemiring A] [cRA : Algebra R A]
    (S : Submonoid R)

/--
The `R[S⁻¹]`-algebra structure on `A[S⁻¹]` induced by the `R`-algebra
structure on `A`.
-/
def algebra : Algebra (R[S⁻¹]) (A[S⁻¹]) where
  toFun := liftExpand (fun r s ↦ (algebraMap R A r) /ₒ s) fun r₁ r₂ s hs => by
    rw [oreDiv_eq_iff]
    use s, r₂ * s
    rw [smul_eq_mul, map_mul]
    obtain ⟨s, hs⟩ := s
    simp only [Submonoid.mk_smul] at hs ⊢
    refine ⟨?_, mul_comm s (r₂ * s)⟩
    rw [← smul_mul_assoc, Algebra.algebraMap_eq_smul_one r₂, smul_smul, mul_comm s]
    simp only [smul_mul_assoc, one_mul]
  map_one' := by
    simp only [OreLocalization.one_def', liftExpand_of, map_one]
  map_mul' a b := by
    induction' a with a s
    induction' b with b t
    simp only [OreLocalization.mul_def, liftExpand_of, map_mul]
  map_zero' := by
    simp only [OreLocalization.zero_def, liftExpand_of]
    simp only [map_zero, zero_oreDiv]
  map_add' r₁ r₂ := by
    induction' r₁ with r₁ s₁
    induction' r₂ with r₂ s2
    simp only [add_def, smul_eq_mul, liftExpand_of, map_add, algebraMap.coe_smul, map_mul,
      Algebra.smul_def]
  commutes' r₁ r₂ := by
    induction' r₁ with r₁ s₁
    induction' r₂ with r₂ s₂
    simp only [OreLocalization.mul_def, mul_comm]
  smul_def' r a := by
    induction' r with r s
    induction' a with a t
    simp only [smul_eq_mul, id_eq, Submonoid.mk_smul, eq_mpr_eq_cast, cast_eq, OneHom.toFun_eq_coe,
      OneHom.coe_mk, liftExpand_of, RingHom.coe_mk, MonoidHom.coe_mk,
      OreLocalization.smul_def, Algebra.smul_def, OreLocalization.mul_def]

attribute [ext] Algebra

-- If `algebra` were an instance then this would be a diamond:
example : (algebra R R S : Algebra R[S⁻¹] R[S⁻¹]) =
    (inferInstance : Algebra R[S⁻¹] R[S⁻¹]) := by
  apply Algebra.ext
  · rfl
  · ext rs
    unfold OneHom.toFun
    dsimp
    unfold Algebra.toRingHom
    unfold algebra
    unfold inferInstance
    dsimp
    unfold Algebra.id oreDiv
    dsimp
    unfold liftExpand
    dsimp
    cases rs
    rfl

-- how far is this from `rfl`?
example : (algebra R R S : Algebra R[S⁻¹] R[S⁻¹]) =
    (inferInstance : Algebra R[S⁻¹] R[S⁻¹]) := by
  refine Algebra.algebra_ext (algebra R R S) inferInstance fun r ↦ ?_
  refine Quotient.inductionOn r fun rs ↦ ?_
  rfl

end Algebra

end OreLocalization
