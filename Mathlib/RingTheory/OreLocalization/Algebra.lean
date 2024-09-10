import Mathlib.RingTheory.OreLocalization.Ring
--import Mathlib -- just in case, when developing

/-!

# Algebra instances of Ore Localizations

If `R` is a commutative ring with submonoid `S`, and if `A` is a commutative `R`-algebra,
then my guess is that `A[S⁻¹]` is an `R[S⁻¹]`-algebra. Let's see if I'm right and if so,
in what generality.

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
  · rw [← smul_mul_assoc]
    rw [← smul_mul_assoc]
    rw [mul_comm]
    rw [smul_mul_assoc, smul_mul_assoc]
    rw [mul_comm]
    -- it's like a bloody Rubik's cube
    rw [smul_mul_assoc]
    rw [← mul_smul]
  · obtain ⟨s₂, hs₂⟩ := s
    simpa only [Submonoid.mk_smul, Submonoid.coe_mul] using mul_left_comm s₁ (r₁ * s₁) s₂

@[to_additive]
protected def mul : A[S⁻¹] → A[S⁻¹] → A[S⁻¹] :=
  liftExpand mul'' fun a₁ r₁ s hs => by
  obtain ⟨s₁, hs₁⟩ := s
  simp only at hs
  unfold OreLocalization.mul''
  simp
  unfold OreLocalization.mul'
  dsimp
  ext sa
  induction sa
  rename_i a s_temp
  obtain ⟨s, hs⟩ := s_temp
  rw [liftExpand_of]
  rw [liftExpand_of]
  rw [oreDiv_eq_iff]
  simp only [Submonoid.mk_smul, Submonoid.coe_mul]
  use ⟨s₁, hs₁⟩, r₁ * s₁
  simp only [Submonoid.mk_smul, Submonoid.coe_mul]
  constructor
  · rw [smul_mul_assoc]
    rw [← mul_smul]
    rw [mul_comm]
  · repeat rw [mul_assoc]
    repeat rw [mul_left_comm s₁]
    rw [mul_left_comm s]

instance : Mul (A[S⁻¹]) where
  mul := OreLocalization.mul

protected def mul_def (a : A) (s : { x // x ∈ S }) (b : A) (t : { x // x ∈ S }) :
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

instance commMonoid' : CommMonoid (A[S⁻¹]) where
  mul_assoc a b c := by
    induction' a with a
    induction' b with b
    induction' c with c
    change (a * b * c) /ₒ _ = (a * (b * c)) /ₒ _
    simp [mul_assoc]
  one_mul a := by
    induction' a with a
    change (1 * a) /ₒ _ = a /ₒ _
    simp
  mul_one a := by
    induction' a with a s
    simp [OreLocalization.mul_def, OreLocalization.one_def']
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
  obtain ⟨r, hr⟩ := r
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  obtain ⟨s₁, hs₁⟩ := s₁
  obtain ⟨s₂, hs₂⟩ := s₂
  simp only [Submonoid.mk_smul, Submonoid.coe_mul] at h₁ h₂ ⊢
  sorry
  --use ⟨?_, ?_⟩, ?_
  --constructor
  --· simp
  --  sorry
  --· sorry

instance instCommSemiring' : CommSemiring A[S⁻¹] where
  __ := commMonoid'
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

variable {R A : Type} [cR : CommSemiring R] [cA : CommSemiring A] [cRA : Algebra R A]
    {S : Submonoid R}
-- **TODO** `A[S⁻¹]` prettyprints as `OreLocalization S A`

private abbrev to_fun' (r : R) (s : S) : A[S⁻¹] :=
  (algebraMap R A r) /ₒ s

-- simplfication of `oreDiv_add_oreDiv` in the commutative case
theorem add_def {r r' : A} {s s' : S} :
    r /ₒ s + r' /ₒ s' =
      (s' • r + (s : R) • r') /ₒ (s' * s) := by
  with_unfolding_all rfl

-- simplification of oreDiv_smul_oreDiv in comm case
theorem smul_def {r₁ : R} {r₂ : A} {s₁ s₂ : S} :
    (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = r₁ • r₂ /ₒ (s₂ * s₁) := rfl

instance : Algebra (R[S⁻¹]) (A[S⁻¹]) where
  toFun := liftExpand to_fun' fun r₁ r₂ s hs => by
    rw [oreDiv_eq_iff]
    use s, r₂ * s
    rw [smul_eq_mul, map_mul]
    obtain ⟨s, hs⟩ := s
    simp only [Submonoid.mk_smul] at hs ⊢
    refine ⟨?_, mul_comm s (r₂ * s)⟩
    rw [← smul_mul_assoc]
    rw [Algebra.algebraMap_eq_smul_one r₂, smul_smul, mul_comm s]
    simp only [smul_mul_assoc, one_mul]
  map_one' := by
    unfold OreLocalization.to_fun'
    simp [OreLocalization.one_def', liftExpand_of]
  map_mul' a b := by
    induction' a with a s
    induction' b with b t
    simp only [OreLocalization.mul_def, liftExpand_of, OreLocalization.to_fun', map_mul]
  map_zero' := by
    unfold OreLocalization.to_fun'
    simp only [OreLocalization.zero_def, liftExpand_of]
    simp only [map_zero, zero_oreDiv]
  map_add' r₁ r₂ := by
    induction' r₁ with r₁ s₁
    induction' r₂ with r₂ s2
    dsimp
    unfold OreLocalization.to_fun'
    simp [add_def, add_def, liftExpand_of, map_add, algebraMap.coe_smul, Algebra.smul_def]
  commutes' r₁ r₂ := by
    induction' r₁ with r₁ s₁
    induction' r₂ with r₂ s₂
    dsimp
    unfold OreLocalization.to_fun'
    simp only [OreLocalization.mul_def, mul_comm]
  smul_def' r a := by
    induction' r with r s
    induction' a with a t
    dsimp
    unfold OreLocalization.to_fun'
    simp only [OreLocalization.smul_def, Algebra.smul_def, OreLocalization.mul_def]

end Algebra

end OreLocalization
