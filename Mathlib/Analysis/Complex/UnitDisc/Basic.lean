/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.NormedSpace.BallAction

/-!
# Poincaré disc

In this file we define `Complex.UnitDisc` to be the unit disc in the complex plane. We also
introduce some basic operations on this disc.
-/


open Set Function Metric

noncomputable section

local notation "conj'" => starRingEnd ℂ

namespace Complex

/-- The complex unit disc, denoted as `𝔻` withinin the Complex namespace -/
def UnitDisc : Type :=
  ball (0 : ℂ) 1 deriving TopologicalSpace

@[inherit_doc] scoped[UnitDisc] notation "𝔻" => Complex.UnitDisc
open UnitDisc

namespace UnitDisc

/-- Coercion to `ℂ`. -/
@[coe] protected def coe : 𝔻 → ℂ := Subtype.val

instance instCommSemigroup : CommSemigroup UnitDisc := by unfold UnitDisc; infer_instance
instance instSemigroupWithZero : SemigroupWithZero UnitDisc := by unfold UnitDisc; infer_instance
instance instIsCancelMulZero : IsCancelMulZero UnitDisc := by unfold UnitDisc; infer_instance
instance instHasDistribNeg : HasDistribNeg UnitDisc := by unfold UnitDisc; infer_instance
instance instCoe : Coe UnitDisc ℂ := ⟨UnitDisc.coe⟩

@[ext]
theorem coe_injective : Injective ((↑) : 𝔻 → ℂ) :=
  Subtype.coe_injective

@[simp, norm_cast]
theorem coe_inj {z w : 𝔻} : (z : ℂ) = w ↔ z = w := Subtype.val_inj

theorem norm_lt_one (z : 𝔻) : ‖(z : ℂ)‖ < 1 :=
  mem_ball_zero_iff.1 z.2

theorem norm_ne_one (z : 𝔻) : ‖(z : ℂ)‖ ≠ 1 :=
  z.norm_lt_one.ne

@[deprecated (since := "2025-02-16")] alias abs_lt_one := norm_lt_one
@[deprecated (since := "2025-02-16")] alias abs_ne_one := norm_ne_one

theorem normSq_lt_one (z : 𝔻) : normSq z < 1 := by
  convert (Real.sqrt_lt' one_pos).1 z.norm_lt_one
  exact (one_pow 2).symm

theorem coe_ne_one (z : 𝔻) : (z : ℂ) ≠ 1 :=
  ne_of_apply_ne (‖·‖) <| by simp [z.norm_ne_one]

theorem coe_ne_neg_one (z : 𝔻) : (z : ℂ) ≠ -1 :=
  ne_of_apply_ne (‖·‖) <| by simpa [norm_neg] using z.norm_ne_one

theorem one_add_coe_ne_zero (z : 𝔻) : (1 + z : ℂ) ≠ 0 :=
  mt neg_eq_iff_add_eq_zero.2 z.coe_ne_neg_one.symm

@[simp, norm_cast]
theorem coe_mul (z w : 𝔻) : ↑(z * w) = (z * w : ℂ) :=
  rfl

@[simp, norm_cast]
theorem coe_neg (z : 𝔻) : ↑(-z) = (-z : ℂ) := rfl

/-- A constructor that assumes `‖z‖ < 1` instead of `dist z 0 < 1` and returns an element
of `𝔻` instead of `↥Metric.ball (0 : ℂ) 1`. -/
def mk (z : ℂ) (hz : ‖z‖ < 1) : 𝔻 :=
  ⟨z, mem_ball_zero_iff.2 hz⟩

@[simp]
theorem coe_mk (z : ℂ) (hz : ‖z‖ < 1) : (mk z hz : ℂ) = z :=
  rfl

@[simp]
theorem mk_coe (z : 𝔻) (hz : ‖(z : ℂ)‖ < 1 := z.norm_lt_one) : mk z hz = z :=
  Subtype.eta _ _

@[simp]
theorem mk_neg (z : ℂ) (hz : ‖-z‖ < 1) : mk (-z) hz = -mk z (norm_neg z ▸ hz) :=
  rfl

@[simp]
theorem coe_zero : ((0 : 𝔻) : ℂ) = 0 :=
  rfl

@[simp]
theorem coe_eq_zero {z : 𝔻} : (z : ℂ) = 0 ↔ z = 0 :=
  coe_injective.eq_iff' coe_zero

@[simp] theorem mk_zero : mk 0 (by simp) = 0 := rfl
@[simp] theorem mk_eq_zero {z : ℂ} (hz : ‖z‖ < 1) : mk z hz = 0 ↔ z = 0 := by simp [← coe_inj]

instance : Inhabited 𝔻 :=
  ⟨0⟩

instance instMulActionCircle : MulAction Circle 𝔻 :=
  mulActionSphereBall

instance instIsScalarTower_circle_circle : IsScalarTower Circle Circle 𝔻 :=
  isScalarTower_sphere_sphere_ball

instance instIsScalarTower_circle : IsScalarTower Circle 𝔻 𝔻 :=
  isScalarTower_sphere_ball_ball

instance instSMulCommClass_circle_left : SMulCommClass Circle 𝔻 𝔻 :=
  instSMulCommClass_sphere_ball_ball

instance instSMulCommClass_circle_right : SMulCommClass 𝔻 Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_circle_smul (z : Circle) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

@[deprecated (since := "2025-04-21")]
alias Complex.UnitDisc.coe_smul_circle := coe_circle_smul

instance instMulActionClosedBall : MulAction (closedBall (0 : ℂ) 1) 𝔻 :=
  mulActionClosedBallBall

instance instIsScalarTower_closedBall_closedBall :
    IsScalarTower (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) 𝔻 :=
  isScalarTower_closedBall_closedBall_ball

instance instIsScalarTower_closedBall : IsScalarTower (closedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  isScalarTower_closedBall_ball_ball

instance instSMulCommClass_closedBall_left : SMulCommClass (closedBall (0 : ℂ) 1) 𝔻 𝔻 :=
  ⟨fun _ _ _ => Subtype.ext <| mul_left_comm _ _ _⟩

instance instSMulCommClass_closedBall_righ : SMulCommClass 𝔻 (closedBall (0 : ℂ) 1) 𝔻 :=
  SMulCommClass.symm _ _ _

instance instSMulCommClass_circle_closedBall : SMulCommClass Circle (closedBall (0 : ℂ) 1) 𝔻 :=
  instSMulCommClass_sphere_closedBall_ball

instance instSMulCommClass_closedBall_circle : SMulCommClass (closedBall (0 : ℂ) 1) Circle 𝔻 :=
  SMulCommClass.symm _ _ _

@[simp, norm_cast]
theorem coe_closedBall_smul (z : closedBall (0 : ℂ) 1) (w : 𝔻) : ↑(z • w) = (z * w : ℂ) :=
  rfl

@[deprecated (since := "2025-04-21")]
alias Complex.UnitDisc.coe_smul_closedBall := coe_closedBall_smul

/-- Real part of a point of the unit disc. -/
def re (z : 𝔻) : ℝ :=
  Complex.re z

/-- Imaginary part of a point of the unit disc. -/
def im (z : 𝔻) : ℝ :=
  Complex.im z

@[simp, norm_cast]
theorem re_coe (z : 𝔻) : (z : ℂ).re = z.re :=
  rfl

@[simp, norm_cast]
theorem im_coe (z : 𝔻) : (z : ℂ).im = z.im :=
  rfl

@[simp]
theorem re_neg (z : 𝔻) : (-z).re = -z.re :=
  rfl

@[simp]
theorem im_neg (z : 𝔻) : (-z).im = -z.im :=
  rfl

/-- Conjugate point of the unit disc. -/
def conj (z : 𝔻) : 𝔻 :=
  mk (conj' ↑z) <| (norm_conj z).symm ▸ z.norm_lt_one

@[simp]
theorem coe_conj (z : 𝔻) : (z.conj : ℂ) = conj' ↑z :=
  rfl

@[simp]
theorem conj_zero : conj 0 = 0 :=
  coe_injective (map_zero conj')

@[simp]
theorem conj_conj (z : 𝔻) : conj (conj z) = z :=
  coe_injective <| Complex.conj_conj (z : ℂ)

@[simp]
theorem conj_neg (z : 𝔻) : (-z).conj = -z.conj :=
  rfl

@[simp]
theorem re_conj (z : 𝔻) : z.conj.re = z.re :=
  rfl

@[simp]
theorem im_conj (z : 𝔻) : z.conj.im = -z.im :=
  rfl

@[simp]
theorem conj_mul (z w : 𝔻) : (z * w).conj = z.conj * w.conj :=
  Subtype.ext <| map_mul _ _ _

private lemma shift_den_ne_zero {z w : 𝔻} : 1 + conj' z * w ≠ 0 :=
  (conj z * w).one_add_coe_ne_zero

def shiftFun (z w : 𝔻) : 𝔻 :=
  mk ((z + w) / (1 + conj' z * w)) <| by
    -- TODO: add `div_lt_one_of_lt`
    suffices ‖(z + w : ℂ)‖ < ‖1 + conj' z * w‖ by
      rwa [norm_div, div_lt_one]
      exact (norm_nonneg _).trans_lt this
    dsimp only [Complex.norm_def]
    gcongr
    · apply normSq_nonneg -- TODO: add a `positivity` extension
    · rw [← sub_pos]
      convert mul_pos (sub_pos.2 z.normSq_lt_one) (sub_pos.2 w.normSq_lt_one) using 1
      simp [normSq]
      ring

theorem coe_shiftFun (z w : 𝔻) : (shiftFun z w : ℂ) = (z + w) / (1 + conj' z * w) := rfl

theorem shiftFun_eq_iff {z w u : 𝔻} : shiftFun z w = u ↔ z + w = u + u * conj' z * w := by
  rw [← coe_inj, coe_shiftFun, div_eq_iff shift_den_ne_zero]
  ring_nf

theorem shiftFun_neg_apply_shiftFun (z w : 𝔻) : shiftFun (-z) (shiftFun z w) = w := by
  rw [shiftFun_eq_iff]
  field_simp [coe_shiftFun, shift_den_ne_zero]
  ring

def shift (z : 𝔻) : 𝔻 ≃ 𝔻 where
  toFun := shiftFun z
  invFun := shiftFun (-z)
  left_inv := shiftFun_neg_apply_shiftFun _
  right_inv := by simpa using shiftFun_neg_apply_shiftFun (-z)

end UnitDisc

end Complex

#exit

@[simp] lemma coe_foldl_mul (z : 𝔻) (l : list 𝔻) :
  ((l.foldl (*) z : 𝔻) : ℂ) = ((z :: l).map coe).prod :=
list.coe_foldl_mul z l

lemma coe_shift (z w : 𝔻) : (shift z w : ℂ) = (z + w) / (1 + conj' z * w) := rfl

lemma conj_coe_shift (z w : 𝔻) : conj' (shift z w) = shift z.conj w.conj :=
by simp only [coe_shift, ring_hom.map_div, map_add, map_one, map_mul, complex.conj_conj, coe_conj]

lemma conj_shift (z w : 𝔻) : conj (shift z w) = shift z.conj w.conj :=
coe_injective $ conj_coe_shift z w

@[simp] lemma shift_eq_self {z w : 𝔻} : shift z w = w ↔ z = 0 :=
begin
  rw [← subtype.coe_inj, coe_shift, div_eq_iff shift_denom_ne_zero, mul_add, mul_one, add_comm,
    add_right_inj],
  rcases eq_or_ne z 0 with rfl|hz,
  { rw [coe_zero, map_zero, zero_mul, mul_zero, eq_self_iff_true, eq_self_iff_true] },
  { simp only [hz, iff_false],
    refine ne_of_apply_ne abs (ne_of_gt _),
    rw [abs_mul, abs_mul, abs_conj, mul_left_comm, ← sq],
    refine mul_lt_of_lt_one_right (abs_pos.2 $ _) _,
    { rwa [ne.def, coe_eq_zero] },
    { exact pow_lt_one (abs_nonneg _) w.abs_lt_one two_ne_zero } }
end

@[simp] lemma shift_zero : shift 0 = id := funext $ λ z, shift_eq_self.2 rfl

@[simp] lemma shift_apply_zero (z : 𝔻) : shift z 0 = z :=
coe_injective $ by rw [coe_shift, coe_zero, mul_zero, add_zero, add_zero, div_one]

@[simp] lemma shift_apply_neg (z : 𝔻) : shift z (-z) = 0 :=
coe_injective $ by rw [coe_shift, coe_zero, coe_neg_ball, add_neg_self, zero_div]

lemma shift_apply_smul (c : circle) (z w : 𝔻) :
  shift z (c • w) = c • shift (c⁻¹ • z) w :=
begin
  apply coe_injective,
  rw [coe_smul_circle, coe_shift, coe_shift, ← mul_div_assoc,
    div_eq_div_iff shift_denom_ne_zero shift_denom_ne_zero],
  simp only [coe_smul_circle, map_mul, ← coe_inv_circle_eq_conj, coe_inv_circle, conj_inv, inv_inv],
  field_simp [ne_zero_of_mem_circle c],
  ring
end

@[simps coe] def shift_comp_coeff (z₁ z₂ : 𝔻) : circle :=
circle.of_conj_div_self (1 + conj' z₁ * z₂) shift_denom_ne_zero

lemma shift_apply_shift (z₁ z₂ w : 𝔻) :
  shift z₁ (shift z₂ w) = shift_comp_coeff z₁ z₂ • shift (shift z₂ z₁) w :=
have h₀ : ∀ {z w : 𝔻}, (1 + conj' z * w : ℂ) ≠ 0, from λ z w, one_add_coe_ne_zero (z.conj * w),
coe_injective $
calc (shift z₁ (shift z₂ w) : ℂ)
    = (z₁ + z₂ + (1 + z₁ * conj' z₂) * w) / (1 + conj' z₁ * z₂ + (conj' z₁ + conj' z₂) * w) :
  begin
    rw [coe_shift, coe_shift, add_div', ← mul_div_assoc, one_add_div, div_div_div_cancel_right],
    { congr' 1; ring },
    all_goals { exact shift_denom_ne_zero }
  end
... = shift_comp_coeff z₁ z₂ * shift (shift z₂ z₁) w :
  begin
    rw [coe_shift, shift_comp_coeff_coe, div_mul_div_comm, mul_add, conj_coe_shift, coe_shift,
      mul_comm (z₁ : ℂ), mul_div_cancel' _ shift_denom_ne_zero, coe_shift, div_mul_eq_mul_div,
      one_add_div shift_denom_ne_zero, coe_conj, coe_conj, complex.conj_conj, mul_comm (z₂ : ℂ),
      mul_div_cancel' _ shift_denom_ne_zero],
    congr' 1; ring_nf
  end

@[simp] lemma shift_neg_apply_shift (z w : 𝔻) : shift (-z) (shift z w) = w :=
by rw [shift_apply_shift, shift_apply_neg, shift_zero, id.def, ← subtype.coe_inj, coe_smul_circle,
  shift_comp_coeff_coe, coe_neg_ball, neg_mul, ← mul_neg, ← map_neg, mul_comm (z : ℂ),
  ← coe_neg_ball, div_self shift_denom_ne_zero,  one_mul]

@[simp] lemma shift_apply_shift_neg (z w : 𝔻) : shift z (shift (-z) w) = w :=
by simpa only [neg_neg] using shift_neg_apply_shift (-z) w

def shift_equiv (z : 𝔻) : 𝔻 ≃ 𝔻 :=
{ to_fun := shift z,
  inv_fun := shift (-z),
  left_inv := shift_neg_apply_shift z,
  right_inv := shift_apply_shift_neg z }

def is_fin_blaschke_prod (n : ℕ) (f : 𝔻 → 𝔻) : Prop :=
∃ (c : circle) (z : 𝔻) (zs : list 𝔻),
  n = zs.length + 1 ∧ f = c • (zs.map shift).foldl (*) (shift z)

namespace is_fin_blaschke_prod

variables {m n : ℕ} {f g : 𝔻 → 𝔻}

lemma ne_zero (h : is_fin_blaschke_prod n f) : n ≠ 0 :=
begin
  rcases h with ⟨c, z, zs, rfl, -⟩,
  apply nat.succ_ne_zero
end

lemma mk_one (c : circle) (z : 𝔻) : is_fin_blaschke_prod 1 (c • shift z) :=
⟨c, z, [], rfl, rfl⟩

lemma mk_shift (z : 𝔻) : is_fin_blaschke_prod 1 (shift z) :=
one_smul circle (shift z) ▸ mk_one 1 z

protected lemma mul (hf : is_fin_blaschke_prod m f) (hg : is_fin_blaschke_prod n g) :
  is_fin_blaschke_prod (m + n) (f * g) :=
begin
  rcases hf with ⟨cf, zf, zsf, rfl, rfl⟩,
  rcases hg with ⟨cg, zg, zsg, rfl, rfl⟩,
  refine ⟨cf * cg, zf, zg :: (zsf ++ zsg), _, _⟩,
  { rw [list.length_cons, list.length_append, add_add_add_comm] },
  { ext w : 2,
    simp only [pi.mul_apply, pi.smul_apply, coe_mul, coe_smul_circle, pi.list_foldl_mul_apply,
      coe_foldl_mul],
    simp only [list.map_cons, list.map_map, (∘), list.prod_cons, list.map_append, list.prod_append,
      coe_mul_unit_sphere, mul_assoc, mul_comm, mul_left_comm] }
end

lemma mul_shift (hf : is_fin_blaschke_prod n f) (z : 𝔻) :
  is_fin_blaschke_prod (n + 1) (f * shift z) :=
hf.mul (mk_shift z)

lemma foldl_mul {α} {l : list α} (ns : α → ℕ) (fs : α → 𝔻 → 𝔻) (hf : is_fin_blaschke_prod n f)
  (hl : ∀ x ∈ l, is_fin_blaschke_prod (ns x) (fs x)) :
  is_fin_blaschke_prod (n + (l.map ns).sum) ((l.map fs).foldl (*) f) :=
begin
  induction l with a l ihl generalizing n f,
  { exact hf },
  { rw [list.forall_mem_cons] at hl,
    rw [list.map_cons, list.sum_cons, ← add_assoc, list.map_cons, list.foldl_cons],
    exact ihl hl.2 (hf.mul hl.1) }
end

lemma foldl_mul' {α} {l : list α} (ns : α → ℕ) (fs : α → 𝔻 → 𝔻) (hf : is_fin_blaschke_prod n f)
  (hl : ∀ x ∈ l, is_fin_blaschke_prod (ns x) (fs x)) :
  is_fin_blaschke_prod (n + (l.map ns).sum) (λ w, (l.map $ λ x, fs x w).foldl (*) (f w)) :=
begin
  convert hf.foldl_mul ns fs hl,
  ext1 w,
  rw [pi.list_foldl_mul_apply, list.map_map]
end

lemma succ_iff : is_fin_blaschke_prod (n + 2) f ↔
  ∃ g z, is_fin_blaschke_prod (n + 1) g ∧ f = g * shift z :=
begin
  refine ⟨_, λ ⟨g, z, hg, hf⟩, hf.symm ▸ hg.mul_shift z⟩,
  rintro ⟨c, z, zs, hn, rfl⟩,
  rw [bit0, ← add_assoc, add_left_inj] at hn,
  cases zs with z' zs, { exact (nat.succ_ne_zero _ hn).elim },
  rw [list.length_cons, add_left_inj] at hn, subst n,
  refine ⟨_, z, ⟨c, z', zs, rfl, rfl⟩, _⟩,
  haveI : is_scalar_tower ↥circle (𝔻 → 𝔻) (𝔻 → 𝔻) := pi.is_scalar_tower',
  rw [list.map_cons, list.foldl_cons, list.foldl_assoc, mul_comm, smul_mul_assoc],
end

protected lemma smul (hf : is_fin_blaschke_prod n f) (c : circle) :
  is_fin_blaschke_prod n (c • f) :=
begin
  rcases hf with ⟨c', z, zs, rfl, rfl⟩,
  exact ⟨c * c', z, zs, rfl, smul_smul _ _ _⟩
end

lemma comp_shift (hf : is_fin_blaschke_prod n f) (z : 𝔻) :
  is_fin_blaschke_prod n (f ∘ shift z) :=
begin
  rcases hf with ⟨c, z', zs, rfl, rfl⟩,
  simp only [(∘), pi.smul_apply, pi.list_foldl_mul_apply, list.map_map, shift_apply_shift,
    add_comm _ 1],
  convert (foldl_mul' (λ _, 1) (λ z', shift_comp_coeff z' z • shift (shift z z')) (mk_one _ _)
    (λ x hx, mk_one _ _)).smul c,
   rw [list.map_const, list.sum_repeat, smul_eq_mul, mul_one]
end

lemma comp_smul (hf : is_fin_blaschke_prod n f) (c : circle) :
  is_fin_blaschke_prod n (λ x, f (c • x)) :=
begin
  rcases hf with ⟨c', z', zs, rfl, rfl⟩,
  simp only [(∘), pi.smul_apply, pi.list_foldl_mul_apply, list.map_map, shift_apply_smul,
    add_comm _ 1],
  convert (foldl_mul' 1 (λ z', c • shift (c⁻¹ • z')) (mk_one _ _) (λ x hx, mk_one _ _)).smul c',
  rw [pi.one_def, list.map_const, list.sum_repeat, smul_eq_mul, mul_one]
end

end is_fin_blaschke_prod

end unit_disc

end complex
