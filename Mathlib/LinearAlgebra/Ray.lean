/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.LinearAlgebra.LinearIndependent

#align_import linear_algebra.ray from "leanprover-community/mathlib"@"0f6670b8af2dff699de1c0b4b49039b31bc13c46"

/-!
# Rays in modules

This file defines rays in modules.

## Main definitions

* `SameRay`: two vectors belong to the same ray if they are proportional with a nonnegative
  coefficient.

* `Module.Ray` is a type for the equivalence class of nonzero vectors in a module with some
common positive multiple.
-/


noncomputable section

open BigOperators

section StrictOrderedCommSemiring

variable (R : Type*) [StrictOrderedCommSemiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {N : Type*} [AddCommMonoid N] [Module R N]

variable (ι : Type*) [DecidableEq ι]

/-- Two vectors are in the same ray if either one of them is zero or some positive multiples of them
are equal (in the typical case over a field, this means one of them is a nonnegative multiple of
the other). -/
def SameRay (v₁ v₂ : M) : Prop :=
  v₁ = 0 ∨ v₂ = 0 ∨ ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂
#align same_ray SameRay

variable {R}

namespace SameRay

variable {x y z : M}

@[simp]
theorem zero_left (y : M) : SameRay R 0 y :=
  Or.inl rfl
#align same_ray.zero_left SameRay.zero_left

@[simp]
theorem zero_right (x : M) : SameRay R x 0 :=
  Or.inr <| Or.inl rfl
#align same_ray.zero_right SameRay.zero_right

@[nontriviality]
theorem of_subsingleton [Subsingleton M] (x y : M) : SameRay R x y := by
  rw [Subsingleton.elim x 0]
  -- ⊢ SameRay R 0 y
  exact zero_left _
  -- 🎉 no goals
#align same_ray.of_subsingleton SameRay.of_subsingleton

@[nontriviality]
theorem of_subsingleton' [Subsingleton R] (x y : M) : SameRay R x y :=
  haveI := Module.subsingleton R M
  of_subsingleton x y
#align same_ray.of_subsingleton' SameRay.of_subsingleton'

/-- `SameRay` is reflexive. -/
@[refl]
theorem refl (x : M) : SameRay R x x := by
  nontriviality R
  -- ⊢ SameRay R x x
  exact Or.inr (Or.inr <| ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩)
  -- 🎉 no goals
#align same_ray.refl SameRay.refl

protected theorem rfl : SameRay R x x :=
  refl _
#align same_ray.rfl SameRay.rfl

/-- `SameRay` is symmetric. -/
@[symm]
theorem symm (h : SameRay R x y) : SameRay R y x :=
  (or_left_comm.1 h).imp_right <| Or.imp_right fun ⟨r₁, r₂, h₁, h₂, h⟩ => ⟨r₂, r₁, h₂, h₁, h.symm⟩
#align same_ray.symm SameRay.symm

/-- If `x` and `y` are nonzero vectors on the same ray, then there exist positive numbers `r₁ r₂`
such that `r₁ • x = r₂ • y`. -/
theorem exists_pos (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y :=
  (h.resolve_left hx).resolve_left hy
#align same_ray.exists_pos SameRay.exists_pos

theorem sameRay_comm : SameRay R x y ↔ SameRay R y x :=
  ⟨SameRay.symm, SameRay.symm⟩
#align same_ray_comm SameRay.sameRay_comm

/-- `SameRay` is transitive unless the vector in the middle is zero and both other vectors are
nonzero. -/
theorem trans (hxy : SameRay R x y) (hyz : SameRay R y z) (hy : y = 0 → x = 0 ∨ z = 0) :
    SameRay R x z := by
  rcases eq_or_ne x 0 with (rfl | hx); · exact zero_left z
  -- ⊢ SameRay R 0 z
                                         -- 🎉 no goals
  rcases eq_or_ne z 0 with (rfl | hz); · exact zero_right x
  -- ⊢ SameRay R x 0
                                         -- 🎉 no goals
  rcases eq_or_ne y 0 with (rfl | hy);
  -- ⊢ SameRay R x z
  · exact (hy rfl).elim (fun h => (hx h).elim) fun h => (hz h).elim
    -- 🎉 no goals
  rcases hxy.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, h₁⟩
  -- ⊢ SameRay R x z
  rcases hyz.exists_pos hy hz with ⟨r₃, r₄, hr₃, hr₄, h₂⟩
  -- ⊢ SameRay R x z
  refine' Or.inr (Or.inr <| ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, _⟩)
  -- ⊢ (r₃ * r₁) • x = (r₂ * r₄) • z
  rw [mul_smul, mul_smul, h₁, ← h₂, smul_comm]
  -- 🎉 no goals
#align same_ray.trans SameRay.trans

/-- A vector is in the same ray as a nonnegative multiple of itself. -/
theorem sameRay_nonneg_smul_right (v : M) {r : R} (h : 0 ≤ r) : SameRay R v (r • v) :=
  Or.inr <|
    h.eq_or_lt.imp (fun (h : 0 = r) => h ▸ zero_smul R v) fun h =>
      ⟨r, 1, h, by
        nontriviality R
        -- ⊢ 0 < 1
        exact zero_lt_one, (one_smul _ _).symm⟩
        -- 🎉 no goals
#align same_ray_nonneg_smul_right SameRay.sameRay_nonneg_smul_right

/-- A vector is in the same ray as a positive multiple of itself. -/
theorem sameRay_pos_smul_right (v : M) {r : R} (h : 0 < r) : SameRay R v (r • v) :=
  sameRay_nonneg_smul_right v h.le
#align same_ray_pos_smul_right SameRay.sameRay_pos_smul_right

/-- A vector is in the same ray as a nonnegative multiple of one it is in the same ray as. -/
theorem nonneg_smul_right {r : R} (h : SameRay R x y) (hr : 0 ≤ r) : SameRay R x (r • y) :=
  h.trans (sameRay_nonneg_smul_right y hr) fun hy => Or.inr <| by rw [hy, smul_zero]
                                                                  -- 🎉 no goals
#align same_ray.nonneg_smul_right SameRay.nonneg_smul_right

/-- A vector is in the same ray as a positive multiple of one it is in the same ray as. -/
theorem pos_smul_right {r : R} (h : SameRay R x y) (hr : 0 < r) : SameRay R x (r • y) :=
  h.nonneg_smul_right hr.le
#align same_ray.pos_smul_right SameRay.pos_smul_right

/-- A nonnegative multiple of a vector is in the same ray as that vector. -/
theorem sameRay_nonneg_smul_left (v : M) {r : R} (h : 0 ≤ r) : SameRay R (r • v) v :=
  (sameRay_nonneg_smul_right v h).symm
#align same_ray_nonneg_smul_left SameRay.sameRay_nonneg_smul_left

/-- A positive multiple of a vector is in the same ray as that vector. -/
theorem sameRay_pos_smul_left (v : M) {r : R} (h : 0 < r) : SameRay R (r • v) v :=
  sameRay_nonneg_smul_left v h.le
#align same_ray_pos_smul_left SameRay.sameRay_pos_smul_left

/-- A nonnegative multiple of a vector is in the same ray as one it is in the same ray as. -/
theorem nonneg_smul_left {r : R} (h : SameRay R x y) (hr : 0 ≤ r) : SameRay R (r • x) y :=
  (h.symm.nonneg_smul_right hr).symm
#align same_ray.nonneg_smul_left SameRay.nonneg_smul_left

/-- A positive multiple of a vector is in the same ray as one it is in the same ray as. -/
theorem pos_smul_left {r : R} (h : SameRay R x y) (hr : 0 < r) : SameRay R (r • x) y :=
  h.nonneg_smul_left hr.le
#align same_ray.pos_smul_left SameRay.pos_smul_left

/-- If two vectors are on the same ray then they remain so after applying a linear map. -/
theorem map (f : M →ₗ[R] N) (h : SameRay R x y) : SameRay R (f x) (f y) :=
  (h.imp fun hx => by rw [hx, map_zero]) <|
                      -- 🎉 no goals
    Or.imp (fun hy => by rw [hy, map_zero]) fun ⟨r₁, r₂, hr₁, hr₂, h⟩ =>
                         -- 🎉 no goals
      ⟨r₁, r₂, hr₁, hr₂, by rw [← f.map_smul, ← f.map_smul, h]⟩
                            -- 🎉 no goals
#align same_ray.map SameRay.map

/-- The images of two vectors under an injective linear map are on the same ray if and only if the
original vectors are on the same ray. -/
theorem _root_.Function.Injective.sameRay_map_iff {F : Type*} [LinearMapClass F R M N] {f : F}
    (hf : Function.Injective f) : SameRay R (f x) (f y) ↔ SameRay R x y := by
  simp only [SameRay, map_zero, ← hf.eq_iff, map_smul]
  -- 🎉 no goals
#align function.injective.same_ray_map_iff Function.Injective.sameRay_map_iff

/-- The images of two vectors under a linear equivalence are on the same ray if and only if the
original vectors are on the same ray. -/
@[simp]
theorem sameRay_map_iff (e : M ≃ₗ[R] N) : SameRay R (e x) (e y) ↔ SameRay R x y :=
  Function.Injective.sameRay_map_iff (EquivLike.injective e)
#align same_ray_map_iff SameRay.sameRay_map_iff

/-- If two vectors are on the same ray then both scaled by the same action are also on the same
ray. -/
theorem smul {S : Type*} [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]
    (h : SameRay R x y) (s : S) : SameRay R (s • x) (s • y) :=
  h.map (s • (LinearMap.id : M →ₗ[R] M))
#align same_ray.smul SameRay.smul

/-- If `x` and `y` are on the same ray as `z`, then so is `x + y`. -/
theorem add_left (hx : SameRay R x z) (hy : SameRay R y z) : SameRay R (x + y) z := by
  rcases eq_or_ne x 0 with (rfl | hx₀); · rwa [zero_add]
  -- ⊢ SameRay R (0 + y) z
                                          -- 🎉 no goals
  rcases eq_or_ne y 0 with (rfl | hy₀); · rwa [add_zero]
  -- ⊢ SameRay R (x + 0) z
                                          -- 🎉 no goals
  rcases eq_or_ne z 0 with (rfl | hz₀); · apply zero_right
  -- ⊢ SameRay R (x + y) 0
                                          -- 🎉 no goals
  rcases hx.exists_pos hx₀ hz₀ with ⟨rx, rz₁, hrx, hrz₁, Hx⟩
  -- ⊢ SameRay R (x + y) z
  rcases hy.exists_pos hy₀ hz₀ with ⟨ry, rz₂, hry, hrz₂, Hy⟩
  -- ⊢ SameRay R (x + y) z
  refine' Or.inr (Or.inr ⟨rx * ry, ry * rz₁ + rx * rz₂, mul_pos hrx hry, _, _⟩)
  -- ⊢ 0 < ry * rz₁ + rx * rz₂
  · apply_rules [add_pos, mul_pos]
    -- 🎉 no goals
  · simp only [mul_smul, smul_add, add_smul, ← Hx, ← Hy]
    -- ⊢ rx • ry • x + rx • ry • y = ry • rx • x + rx • ry • y
    rw [smul_comm]
    -- 🎉 no goals
#align same_ray.add_left SameRay.add_left

/-- If `y` and `z` are on the same ray as `x`, then so is `y + z`. -/
theorem add_right (hy : SameRay R x y) (hz : SameRay R x z) : SameRay R x (y + z) :=
  (hy.symm.add_left hz.symm).symm
#align same_ray.add_right SameRay.add_right

end SameRay

-- Porting note: removed has_nonempty_instance nolint, no such linter
set_option linter.unusedVariables false in
/-- Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that
`RayVector.Setoid` can be an instance. -/
@[nolint unusedArguments]
def RayVector (R M : Type*) [Zero M] :=
  { v : M // v ≠ 0 }
#align ray_vector RayVector

-- Porting note: Made Coe into CoeOut so it's not dangerous anymore
instance RayVector.coe [Zero M] : CoeOut (RayVector R M) M where
  coe := Subtype.val
#align ray_vector.has_coe RayVector.coe
instance {R M : Type*} [Zero M] [Nontrivial M] : Nonempty (RayVector R M) :=
  let ⟨x, hx⟩ := exists_ne (0 : M)
  ⟨⟨x, hx⟩⟩
variable (R M)

/-- The setoid of the `SameRay` relation for the subtype of nonzero vectors. -/
instance RayVector.Setoid : Setoid (RayVector R M)
    where
  r x y := SameRay R (x : M) y
  iseqv :=
    ⟨fun x => SameRay.refl _, fun h => h.symm, by
      intros x y z hxy hyz
      -- ⊢ SameRay R ↑x ↑z
      exact hxy.trans hyz fun hy => (y.2 hy).elim⟩
      -- 🎉 no goals

/-- A ray (equivalence class of nonzero vectors with common positive multiples) in a module. -/
-- Porting note: removed has_nonempty_instance nolint, no such linter
def Module.Ray :=
  Quotient (RayVector.Setoid R M)
#align module.ray Module.Ray

variable {R M}

/-- Equivalence of nonzero vectors, in terms of `SameRay`. -/
theorem equiv_iff_sameRay {v₁ v₂ : RayVector R M} : v₁ ≈ v₂ ↔ SameRay R (v₁ : M) v₂ :=
  Iff.rfl
#align equiv_iff_same_ray equiv_iff_sameRay

variable (R)

-- Porting note: Removed `protected` here, not in namespace
/-- The ray given by a nonzero vector. -/
def rayOfNeZero (v : M) (h : v ≠ 0) : Module.Ray R M :=
  ⟦⟨v, h⟩⟧
#align ray_of_ne_zero rayOfNeZero

/-- An induction principle for `Module.Ray`, used as `induction x using Module.Ray.ind`. -/
theorem Module.Ray.ind {C : Module.Ray R M → Prop} (h : ∀ (v) (hv : v ≠ 0), C (rayOfNeZero R v hv))
    (x : Module.Ray R M) : C x :=
  Quotient.ind (Subtype.rec <| h) x
#align module.ray.ind Module.Ray.ind

variable {R}

instance [Nontrivial M] : Nonempty (Module.Ray R M) :=
  Nonempty.map Quotient.mk' inferInstance

/-- The rays given by two nonzero vectors are equal if and only if those vectors
satisfy `SameRay`. -/
theorem ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    rayOfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂ :=
  Quotient.eq'
#align ray_eq_iff ray_eq_iff

/-- The ray given by a positive multiple of a nonzero vector. -/
@[simp]
theorem ray_pos_smul {v : M} (h : v ≠ 0) {r : R} (hr : 0 < r) (hrv : r • v ≠ 0) :
    rayOfNeZero R (r • v) hrv = rayOfNeZero R v h :=
  (ray_eq_iff _ _).2 <| SameRay.sameRay_pos_smul_left v hr
#align ray_pos_smul ray_pos_smul

/-- An equivalence between modules implies an equivalence between ray vectors. -/
def RayVector.mapLinearEquiv (e : M ≃ₗ[R] N) : RayVector R M ≃ RayVector R N :=
  Equiv.subtypeEquiv e.toEquiv fun _ => e.map_ne_zero_iff.symm
#align ray_vector.map_linear_equiv RayVector.mapLinearEquiv

/-- An equivalence between modules implies an equivalence between rays. -/
def Module.Ray.map (e : M ≃ₗ[R] N) : Module.Ray R M ≃ Module.Ray R N :=
  Quotient.congr (RayVector.mapLinearEquiv e) fun _ _=> (SameRay.sameRay_map_iff _).symm
#align module.ray.map Module.Ray.map

@[simp]
theorem Module.Ray.map_apply (e : M ≃ₗ[R] N) (v : M) (hv : v ≠ 0) :
    Module.Ray.map e (rayOfNeZero _ v hv) = rayOfNeZero _ (e v) (e.map_ne_zero_iff.2 hv) :=
  rfl
#align module.ray.map_apply Module.Ray.map_apply

@[simp]
theorem Module.Ray.map_refl : (Module.Ray.map <| LinearEquiv.refl R M) = Equiv.refl _ :=
  Equiv.ext <| Module.Ray.ind R fun _ _ => rfl
#align module.ray.map_refl Module.Ray.map_refl

@[simp]
theorem Module.Ray.map_symm (e : M ≃ₗ[R] N) : (Module.Ray.map e).symm = Module.Ray.map e.symm :=
  rfl
#align module.ray.map_symm Module.Ray.map_symm

section Action

variable {G : Type*} [Group G] [DistribMulAction G M]

/-- Any invertible action preserves the non-zeroness of ray vectors. This is primarily of interest
when `G = Rˣ` -/
instance {R : Type*} : MulAction G (RayVector R M)
    where
  smul r := Subtype.map ((· • ·) r) fun _ => (smul_ne_zero_iff_ne _).2
  mul_smul a b _ := Subtype.ext <| mul_smul a b _
  one_smul _ := Subtype.ext <| one_smul _ _

variable [SMulCommClass R G M]

/-- Any invertible action preserves the non-zeroness of rays. This is primarily of interest when
`G = Rˣ` -/
instance : MulAction G (Module.Ray R M)
    where
  smul r := Quotient.map ((· • ·) r) fun _ _ h => h.smul _
  mul_smul a b := Quotient.ind fun _ => congr_arg Quotient.mk' <| mul_smul a b _
  one_smul := Quotient.ind fun _ => congr_arg Quotient.mk' <| one_smul _ _

/-- The action via `LinearEquiv.apply_distribMulAction` corresponds to `Module.Ray.map`. -/
@[simp]
theorem Module.Ray.linearEquiv_smul_eq_map (e : M ≃ₗ[R] M) (v : Module.Ray R M) :
    e • v = Module.Ray.map e v :=
  rfl
#align module.ray.linear_equiv_smul_eq_map Module.Ray.linearEquiv_smul_eq_map

@[simp]
theorem smul_rayOfNeZero (g : G) (v : M) (hv) :
    g • rayOfNeZero R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv) :=
  rfl
#align smul_ray_of_ne_zero smul_rayOfNeZero

end Action

namespace Module.Ray

-- Porting note: `(u.1 : R)` was `(u : R)`, CoeHead from R to Rˣ does not seem to work.
/-- Scaling by a positive unit is a no-op. -/
theorem units_smul_of_pos (u : Rˣ) (hu : 0 < (u.1 : R)) (v : Module.Ray R M) : u • v = v := by
  induction v using Module.Ray.ind
  -- ⊢ u • rayOfNeZero R v✝ hv✝ = rayOfNeZero R v✝ hv✝
  rw [smul_rayOfNeZero, ray_eq_iff]
  -- ⊢ SameRay R (u • v✝) v✝
  exact SameRay.sameRay_pos_smul_left _ hu
  -- 🎉 no goals
#align module.ray.units_smul_of_pos Module.Ray.units_smul_of_pos

/-- An arbitrary `RayVector` giving a ray. -/
def someRayVector (x : Module.Ray R M) : RayVector R M :=
  Quotient.out x
#align module.ray.some_ray_vector Module.Ray.someRayVector

/-- The ray of `someRayVector`. -/
@[simp]
theorem someRayVector_ray (x : Module.Ray R M) : (⟦x.someRayVector⟧ : Module.Ray R M) = x :=
  Quotient.out_eq _
#align module.ray.some_ray_vector_ray Module.Ray.someRayVector_ray

/-- An arbitrary nonzero vector giving a ray. -/
def someVector (x : Module.Ray R M) : M :=
  x.someRayVector
#align module.ray.some_vector Module.Ray.someVector

/-- `someVector` is nonzero. -/
@[simp]
theorem someVector_ne_zero (x : Module.Ray R M) : x.someVector ≠ 0 :=
  x.someRayVector.property
#align module.ray.some_vector_ne_zero Module.Ray.someVector_ne_zero

/-- The ray of `someVector`. -/
@[simp]
theorem someVector_ray (x : Module.Ray R M) : rayOfNeZero R _ x.someVector_ne_zero = x :=
  (congr_arg _ (Subtype.coe_eta _ _) : _).trans x.out_eq
#align module.ray.some_vector_ray Module.Ray.someVector_ray

end Module.Ray

end StrictOrderedCommSemiring

section StrictOrderedCommRing

variable {R : Type*} [StrictOrderedCommRing R]

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] {x y : M}

/-- `SameRay.neg` as an `iff`. -/
@[simp]
theorem sameRay_neg_iff : SameRay R (-x) (-y) ↔ SameRay R x y := by
  simp only [SameRay, neg_eq_zero, smul_neg, neg_inj]
  -- 🎉 no goals
#align same_ray_neg_iff sameRay_neg_iff

alias ⟨SameRay.of_neg, SameRay.neg⟩ := sameRay_neg_iff
#align same_ray.of_neg SameRay.of_neg
#align same_ray.neg SameRay.neg

theorem sameRay_neg_swap : SameRay R (-x) y ↔ SameRay R x (-y) := by rw [← sameRay_neg_iff, neg_neg]
                                                                     -- 🎉 no goals
#align same_ray_neg_swap sameRay_neg_swap

theorem eq_zero_of_sameRay_neg_smul_right [NoZeroSMulDivisors R M] {r : R} (hr : r < 0)
    (h : SameRay R x (r • x)) : x = 0 := by
  rcases h with (rfl | h₀ | ⟨r₁, r₂, hr₁, hr₂, h⟩)
  · rfl
    -- 🎉 no goals
  · simpa [hr.ne] using h₀
    -- 🎉 no goals
  · rw [← sub_eq_zero, smul_smul, ← sub_smul, smul_eq_zero] at h
    -- ⊢ x = 0
    refine' h.resolve_left (ne_of_gt <| sub_pos.2 _)
    -- ⊢ r₂ * r < r₁
    exact (mul_neg_of_pos_of_neg hr₂ hr).trans hr₁
    -- 🎉 no goals
#align eq_zero_of_same_ray_neg_smul_right eq_zero_of_sameRay_neg_smul_right

/-- If a vector is in the same ray as its negation, that vector is zero. -/
theorem eq_zero_of_sameRay_self_neg [NoZeroSMulDivisors R M] (h : SameRay R x (-x)) : x = 0 := by
  nontriviality M; haveI : Nontrivial R := Module.nontrivial R M
  -- ⊢ x = 0
                   -- ⊢ x = 0
  refine' eq_zero_of_sameRay_neg_smul_right (neg_lt_zero.2 (zero_lt_one' R)) _
  -- ⊢ SameRay R x (-1 • x)
  rwa [neg_one_smul]
  -- 🎉 no goals
#align eq_zero_of_same_ray_self_neg eq_zero_of_sameRay_self_neg

namespace RayVector

/-- Negating a nonzero vector. -/
instance {R : Type*} : Neg (RayVector R M) :=
  ⟨fun v => ⟨-v, neg_ne_zero.2 v.prop⟩⟩

/-- Negating a nonzero vector commutes with coercion to the underlying module. -/
@[simp, norm_cast]
theorem coe_neg {R : Type*} (v : RayVector R M) : ↑(-v) = -(v : M) :=
  rfl
#align ray_vector.coe_neg RayVector.coe_neg

/-- Negating a nonzero vector twice produces the original vector. -/
instance {R : Type*} : InvolutiveNeg (RayVector R M)
    where
  neg := Neg.neg
  neg_neg v := by rw [Subtype.ext_iff, coe_neg, coe_neg, neg_neg]
                  -- 🎉 no goals

/-- If two nonzero vectors are equivalent, so are their negations. -/
@[simp]
theorem equiv_neg_iff {v₁ v₂ : RayVector R M} : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂ :=
  sameRay_neg_iff
#align ray_vector.equiv_neg_iff RayVector.equiv_neg_iff

end RayVector

variable (R)

/-- Negating a ray. -/
instance : Neg (Module.Ray R M) :=
  ⟨Quotient.map (fun v => -v) fun _ _ => RayVector.equiv_neg_iff.2⟩

/-- The ray given by the negation of a nonzero vector. -/
@[simp]
theorem neg_rayOfNeZero (v : M) (h : v ≠ 0) :
    -rayOfNeZero R _ h = rayOfNeZero R (-v) (neg_ne_zero.2 h) :=
  rfl
#align neg_ray_of_ne_zero neg_rayOfNeZero

namespace Module.Ray

variable {R}

/-- Negating a ray twice produces the original ray. -/
instance : InvolutiveNeg (Module.Ray R M)
    where
  neg := Neg.neg
  neg_neg x := by apply ind R (by simp) x
                  -- 🎉 no goals
  -- Quotient.ind (fun a => congr_arg Quotient.mk' <| neg_neg _) x

/-- A ray does not equal its own negation. -/
theorem ne_neg_self [NoZeroSMulDivisors R M] (x : Module.Ray R M) : x ≠ -x := by
  induction' x using Module.Ray.ind with x hx
  -- ⊢ rayOfNeZero R x hx ≠ -rayOfNeZero R x hx
  rw [neg_rayOfNeZero, Ne.def, ray_eq_iff]
  -- ⊢ ¬SameRay R x (-x)
  exact mt eq_zero_of_sameRay_self_neg hx
  -- 🎉 no goals
#align module.ray.ne_neg_self Module.Ray.ne_neg_self

theorem neg_units_smul (u : Rˣ) (v : Module.Ray R M) : -u • v = -(u • v) := by
  induction v using Module.Ray.ind
  -- ⊢ -u • rayOfNeZero R v✝ hv✝ = -(u • rayOfNeZero R v✝ hv✝)
  simp only [smul_rayOfNeZero, Units.smul_def, Units.val_neg, neg_smul, neg_rayOfNeZero]
  -- 🎉 no goals
#align module.ray.neg_units_smul Module.Ray.neg_units_smul

-- Porting note: `(u.1 : R)` was `(u : R)`, CoeHead from R to Rˣ does not seem to work.
/-- Scaling by a negative unit is negation. -/
theorem units_smul_of_neg (u : Rˣ) (hu : u.1 < 0) (v : Module.Ray R M) : u • v = -v := by
  rw [← neg_inj, neg_neg, ← neg_units_smul, units_smul_of_pos]
  -- ⊢ 0 < ↑(-u)
  rwa [Units.val_neg, Right.neg_pos_iff]
  -- 🎉 no goals
#align module.ray.units_smul_of_neg Module.Ray.units_smul_of_neg

@[simp]
protected theorem map_neg (f : M ≃ₗ[R] N) (v : Module.Ray R M) : map f (-v) = -map f v := by
  induction' v using Module.Ray.ind with g hg
  -- ⊢ ↑(map f) (-rayOfNeZero R g hg) = -↑(map f) (rayOfNeZero R g hg)
  simp
  -- 🎉 no goals
#align module.ray.map_neg Module.Ray.map_neg

end Module.Ray

end StrictOrderedCommRing

section LinearOrderedCommRing

variable {R : Type*} [LinearOrderedCommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

-- Porting note: Needed to add coercion ↥ below
/-- `SameRay` follows from membership of `MulAction.orbit` for the `Units.posSubgroup`. -/
theorem sameRay_of_mem_orbit {v₁ v₂ : M} (h : v₁ ∈ MulAction.orbit (↥Units.posSubgroup R) v₂) :
    SameRay R v₁ v₂ := by
  rcases h with ⟨⟨r, hr : 0 < r.1⟩, rfl : r • v₂ = v₁⟩
  -- ⊢ SameRay R (r • v₂) v₂
  exact SameRay.sameRay_pos_smul_left _ hr
  -- 🎉 no goals
#align same_ray_of_mem_orbit sameRay_of_mem_orbit

/-- Scaling by an inverse unit is the same as scaling by itself. -/
@[simp]
theorem units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v = u • v :=
  have := mul_self_pos.2 u.ne_zero
  calc
    u⁻¹ • v = (u * u) • u⁻¹ • v := Eq.symm <| (u⁻¹ • v).units_smul_of_pos _ (by exact this)
                                                                                -- 🎉 no goals
    _ = u • v := by rw [mul_smul, smul_inv_smul]
                    -- 🎉 no goals
#align units_inv_smul units_inv_smul

section

variable [NoZeroSMulDivisors R M]

@[simp]
theorem sameRay_smul_right_iff {v : M} {r : R} : SameRay R v (r • v) ↔ 0 ≤ r ∨ v = 0 :=
  ⟨fun hrv => or_iff_not_imp_left.2 fun hr => eq_zero_of_sameRay_neg_smul_right (not_le.1 hr) hrv,
    or_imp.2 ⟨SameRay.sameRay_nonneg_smul_right v, fun h => h.symm ▸ SameRay.zero_left _⟩⟩
#align same_ray_smul_right_iff sameRay_smul_right_iff

/-- A nonzero vector is in the same ray as a multiple of itself if and only if that multiple
is positive. -/
theorem sameRay_smul_right_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) :
    SameRay R v (r • v) ↔ 0 < r := by
  simp only [sameRay_smul_right_iff, hv, or_false_iff, hr.symm.le_iff_lt]
  -- 🎉 no goals
#align same_ray_smul_right_iff_of_ne sameRay_smul_right_iff_of_ne

@[simp]
theorem sameRay_smul_left_iff {v : M} {r : R} : SameRay R (r • v) v ↔ 0 ≤ r ∨ v = 0 :=
  SameRay.sameRay_comm.trans sameRay_smul_right_iff
#align same_ray_smul_left_iff sameRay_smul_left_iff

/-- A multiple of a nonzero vector is in the same ray as that vector if and only if that multiple
is positive. -/
theorem sameRay_smul_left_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) :
    SameRay R (r • v) v ↔ 0 < r :=
  SameRay.sameRay_comm.trans (sameRay_smul_right_iff_of_ne hv hr)
#align same_ray_smul_left_iff_of_ne sameRay_smul_left_iff_of_ne

@[simp]
theorem sameRay_neg_smul_right_iff {v : M} {r : R} : SameRay R (-v) (r • v) ↔ r ≤ 0 ∨ v = 0 := by
  rw [← sameRay_neg_iff, neg_neg, ← neg_smul, sameRay_smul_right_iff, neg_nonneg]
  -- 🎉 no goals
#align same_ray_neg_smul_right_iff sameRay_neg_smul_right_iff

theorem sameRay_neg_smul_right_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) :
    SameRay R (-v) (r • v) ↔ r < 0 := by
  simp only [sameRay_neg_smul_right_iff, hv, or_false_iff, hr.le_iff_lt]
  -- 🎉 no goals
#align same_ray_neg_smul_right_iff_of_ne sameRay_neg_smul_right_iff_of_ne

@[simp]
theorem sameRay_neg_smul_left_iff {v : M} {r : R} : SameRay R (r • v) (-v) ↔ r ≤ 0 ∨ v = 0 :=
  SameRay.sameRay_comm.trans sameRay_neg_smul_right_iff
#align same_ray_neg_smul_left_iff sameRay_neg_smul_left_iff

theorem sameRay_neg_smul_left_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) :
    SameRay R (r • v) (-v) ↔ r < 0 :=
  SameRay.sameRay_comm.trans <| sameRay_neg_smul_right_iff_of_ne hv hr
#align same_ray_neg_smul_left_iff_of_ne sameRay_neg_smul_left_iff_of_ne

-- Porting note: `(u.1 : R)` was `(u : R)`, CoeHead from R to Rˣ does not seem to work.
@[simp]
theorem units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray R M} : u • v = v ↔ 0 < u.1 := by
  induction' v using Module.Ray.ind with v hv
  -- ⊢ u • rayOfNeZero R v hv = rayOfNeZero R v hv ↔ 0 < ↑u
  simp only [smul_rayOfNeZero, ray_eq_iff, Units.smul_def, sameRay_smul_left_iff_of_ne hv u.ne_zero]
  -- 🎉 no goals
#align units_smul_eq_self_iff units_smul_eq_self_iff

@[simp]
theorem units_smul_eq_neg_iff {u : Rˣ} {v : Module.Ray R M} : u • v = -v ↔ u.1 < 0 := by
  rw [← neg_inj, neg_neg, ← Module.Ray.neg_units_smul, units_smul_eq_self_iff, Units.val_neg,
    neg_pos]
#align units_smul_eq_neg_iff units_smul_eq_neg_iff

/-- Two vectors are in the same ray, or the first is in the same ray as the negation of the
second, if and only if they are not linearly independent. -/
theorem sameRay_or_sameRay_neg_iff_not_linearIndependent {x y : M} :
    SameRay R x y ∨ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y] := by
  by_cases hx : x = 0; · simpa [hx] using fun h : LinearIndependent R ![0, y] => h.ne_zero 0 rfl
  -- ⊢ SameRay R x y ∨ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y]
                         -- 🎉 no goals
  by_cases hy : y = 0; · simpa [hy] using fun h : LinearIndependent R ![x, 0] => h.ne_zero 1 rfl
  -- ⊢ SameRay R x y ∨ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y]
                         -- 🎉 no goals
  simp_rw [Fintype.not_linearIndependent_iff]
  -- ⊢ SameRay R x y ∨ SameRay R x (-y) ↔ ∃ g, ∑ i : Fin (Nat.succ (Nat.succ 0)), g …
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ ∃ g, ∑ i : Fin (Nat.succ (Nat.succ 0)), g i • Matrix.vecCons x ![y] i = 0 ∧  …
  · rcases h with ((hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩) | (hx0 | hy0 | ⟨r₁, r₂, hr₁, _, h⟩))
    · exact False.elim (hx hx0)
      -- 🎉 no goals
    · exact False.elim (hy hy0)
      -- 🎉 no goals
    · refine' ⟨![r₁, -r₂], _⟩
      -- ⊢ ∑ i : Fin (Nat.succ (Nat.succ 0)), Matrix.vecCons r₁ ![-r₂] i • Matrix.vecCo …
      rw [Fin.sum_univ_two, Fin.exists_fin_two]
      -- ⊢ Matrix.vecCons r₁ ![-r₂] 0 • Matrix.vecCons x ![y] 0 + Matrix.vecCons r₁ ![- …
      simp [h, hr₁.ne.symm]
      -- 🎉 no goals
    · exact False.elim (hx hx0)
      -- 🎉 no goals
    · exact False.elim (hy (neg_eq_zero.1 hy0))
      -- 🎉 no goals
    · refine' ⟨![r₁, r₂], _⟩
      -- ⊢ ∑ i : Fin (Nat.succ (Nat.succ 0)), Matrix.vecCons r₁ ![r₂] i • Matrix.vecCon …
      rw [Fin.sum_univ_two, Fin.exists_fin_two]
      -- ⊢ Matrix.vecCons r₁ ![r₂] 0 • Matrix.vecCons x ![y] 0 + Matrix.vecCons r₁ ![r₂ …
      simp [h, hr₁.ne.symm]
      -- 🎉 no goals
  · rcases h with ⟨m, hm, hmne⟩
    -- ⊢ SameRay R x y ∨ SameRay R x (-y)
    rw [Fin.sum_univ_two, add_eq_zero_iff_eq_neg, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] at hm
    rcases lt_trichotomy (m 0) 0 with (hm0 | hm0 | hm0) <;>
      rcases lt_trichotomy (m 1) 0 with (hm1 | hm1 | hm1)
    · refine'
        Or.inr (Or.inr (Or.inr ⟨-m 0, -m 1, Left.neg_pos_iff.2 hm0, Left.neg_pos_iff.2 hm1, _⟩))
      rw [neg_smul_neg, neg_smul, hm, neg_neg]
      -- 🎉 no goals
    · exfalso
      -- ⊢ False
      simp [hm1, hx, hm0.ne] at hm
      -- 🎉 no goals
    · refine' Or.inl (Or.inr (Or.inr ⟨-m 0, m 1, Left.neg_pos_iff.2 hm0, hm1, _⟩))
      -- ⊢ -m 0 • x = m 1 • y
      rw [neg_smul, hm, neg_neg]
      -- 🎉 no goals
    · exfalso
      -- ⊢ False
      simp [hm0, hy, hm1.ne] at hm
      -- 🎉 no goals
    · rw [Fin.exists_fin_two] at hmne
      -- ⊢ SameRay R x y ∨ SameRay R x (-y)
      exact False.elim (not_and_or.2 hmne ⟨hm0, hm1⟩)
      -- 🎉 no goals
    · exfalso
      -- ⊢ False
      simp [hm0, hy, hm1.ne.symm] at hm
      -- 🎉 no goals
    · refine' Or.inl (Or.inr (Or.inr ⟨m 0, -m 1, hm0, Left.neg_pos_iff.2 hm1, _⟩))
      -- ⊢ m 0 • x = -m 1 • y
      rwa [neg_smul]
      -- 🎉 no goals
    · exfalso
      -- ⊢ False
      simp [hm1, hx, hm0.ne.symm] at hm
      -- 🎉 no goals
    · refine' Or.inr (Or.inr (Or.inr ⟨m 0, m 1, hm0, hm1, _⟩))
      -- ⊢ m 0 • x = m 1 • -y
      rwa [smul_neg]
      -- 🎉 no goals
#align same_ray_or_same_ray_neg_iff_not_linear_independent sameRay_or_sameRay_neg_iff_not_linearIndependent

/-- Two vectors are in the same ray, or they are nonzero and the first is in the same ray as the
negation of the second, if and only if they are not linearly independent. -/
theorem sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent {x y : M} :
    SameRay R x y ∨ x ≠ 0 ∧ y ≠ 0 ∧ SameRay R x (-y) ↔ ¬LinearIndependent R ![x, y] := by
  rw [← sameRay_or_sameRay_neg_iff_not_linearIndependent]
  -- ⊢ SameRay R x y ∨ x ≠ 0 ∧ y ≠ 0 ∧ SameRay R x (-y) ↔ SameRay R x y ∨ SameRay R …
  by_cases hx : x = 0; · simp [hx]
  -- ⊢ SameRay R x y ∨ x ≠ 0 ∧ y ≠ 0 ∧ SameRay R x (-y) ↔ SameRay R x y ∨ SameRay R …
                         -- 🎉 no goals
  by_cases hy : y = 0 <;> simp [hx, hy]
  -- ⊢ SameRay R x y ∨ x ≠ 0 ∧ y ≠ 0 ∧ SameRay R x (-y) ↔ SameRay R x y ∨ SameRay R …
                          -- 🎉 no goals
                          -- 🎉 no goals
#align same_ray_or_ne_zero_and_same_ray_neg_iff_not_linear_independent sameRay_or_ne_zero_and_sameRay_neg_iff_not_linearIndependent

end

end LinearOrderedCommRing

namespace SameRay

variable {R : Type*} [LinearOrderedField R]

variable {M : Type*} [AddCommGroup M] [Module R M] {x y v₁ v₂ : M}

theorem exists_pos_left (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : R, 0 < r ∧ r • x = y :=
  let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h.exists_pos hx hy
  ⟨r₂⁻¹ * r₁, mul_pos (inv_pos.2 hr₂) hr₁, by rw [mul_smul, h, inv_smul_smul₀ hr₂.ne']⟩
                                              -- 🎉 no goals
#align same_ray.exists_pos_left SameRay.exists_pos_left

theorem exists_pos_right (h : SameRay R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ r : R, 0 < r ∧ x = r • y :=
  (h.symm.exists_pos_left hy hx).imp fun _ => And.imp_right Eq.symm
#align same_ray.exists_pos_right SameRay.exists_pos_right

/-- If a vector `v₂` is on the same ray as a nonzero vector `v₁`, then it is equal to `c • v₁` for
some nonnegative `c`. -/
theorem exists_nonneg_left (h : SameRay R x y) (hx : x ≠ 0) : ∃ r : R, 0 ≤ r ∧ r • x = y := by
  obtain rfl | hy := eq_or_ne y 0
  -- ⊢ ∃ r, 0 ≤ r ∧ r • x = 0
  · exact ⟨0, le_rfl, zero_smul _ _⟩
    -- 🎉 no goals
  · exact (h.exists_pos_left hx hy).imp fun _ => And.imp_left le_of_lt
    -- 🎉 no goals
#align same_ray.exists_nonneg_left SameRay.exists_nonneg_left

/-- If a vector `v₁` is on the same ray as a nonzero vector `v₂`, then it is equal to `c • v₂` for
some nonnegative `c`. -/
theorem exists_nonneg_right (h : SameRay R x y) (hy : y ≠ 0) : ∃ r : R, 0 ≤ r ∧ x = r • y :=
  (h.symm.exists_nonneg_left hy).imp fun _ => And.imp_right Eq.symm
#align same_ray.exists_nonneg_right SameRay.exists_nonneg_right

/-- If vectors `v₁` and `v₂` are on the same ray, then for some nonnegative `a b`, `a + b = 1`, we
have `v₁ = a • (v₁ + v₂)` and `v₂ = b • (v₁ + v₂)`. -/
theorem exists_eq_smul_add (h : SameRay R v₁ v₂) :
    ∃ a b : R, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ + v₂) := by
  rcases h with (rfl | rfl | ⟨r₁, r₂, h₁, h₂, H⟩)
  · use 0, 1
    -- ⊢ 0 ≤ 0 ∧ 0 ≤ 1 ∧ 0 + 1 = 1 ∧ 0 = 0 • (0 + v₂) ∧ v₂ = 1 • (0 + v₂)
    simp
    -- 🎉 no goals
  · use 1, 0
    -- ⊢ 0 ≤ 1 ∧ 0 ≤ 0 ∧ 1 + 0 = 1 ∧ v₁ = 1 • (v₁ + 0) ∧ 0 = 0 • (v₁ + 0)
    simp
    -- 🎉 no goals
  · have h₁₂ : 0 < r₁ + r₂ := add_pos h₁ h₂
    -- ⊢ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ + v₂)
    refine'
      ⟨r₂ / (r₁ + r₂), r₁ / (r₁ + r₂), div_nonneg h₂.le h₁₂.le, div_nonneg h₁.le h₁₂.le, _, _, _⟩
    · rw [← add_div, add_comm, div_self h₁₂.ne']
      -- 🎉 no goals
    · rw [div_eq_inv_mul, mul_smul, smul_add, ← H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']
      -- 🎉 no goals
    · rw [div_eq_inv_mul, mul_smul, smul_add, H, ← add_smul, add_comm r₂, inv_smul_smul₀ h₁₂.ne']
      -- 🎉 no goals
#align same_ray.exists_eq_smul_add SameRay.exists_eq_smul_add

/-- If vectors `v₁` and `v₂` are on the same ray, then they are nonnegative multiples of the same
vector. Actually, this vector can be assumed to be `v₁ + v₂`, see `SameRay.exists_eq_smul_add`. -/
theorem exists_eq_smul (h : SameRay R v₁ v₂) :
    ∃ (u : M) (a b : R), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u :=
  ⟨v₁ + v₂, h.exists_eq_smul_add⟩
#align same_ray.exists_eq_smul SameRay.exists_eq_smul

end SameRay

section LinearOrderedField

variable {R : Type*} [LinearOrderedField R]

variable {M : Type*} [AddCommGroup M] [Module R M] {x y : M}

theorem exists_pos_left_iff_sameRay (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y := by
  refine' ⟨fun h => _, fun h => h.exists_pos_left hx hy⟩
  -- ⊢ SameRay R x y
  rcases h with ⟨r, hr, rfl⟩
  -- ⊢ SameRay R x (r • x)
  exact SameRay.sameRay_pos_smul_right x hr
  -- 🎉 no goals
#align exists_pos_left_iff_same_ray exists_pos_left_iff_sameRay

theorem exists_pos_left_iff_sameRay_and_ne_zero (hx : x ≠ 0) :
    (∃ r : R, 0 < r ∧ r • x = y) ↔ SameRay R x y ∧ y ≠ 0 := by
  constructor
  -- ⊢ (∃ r, 0 < r ∧ r • x = y) → SameRay R x y ∧ y ≠ 0
  · rintro ⟨r, hr, rfl⟩
    -- ⊢ SameRay R x (r • x) ∧ r • x ≠ 0
    simp [hx, hr.le, hr.ne']
    -- 🎉 no goals
  · rintro ⟨hxy, hy⟩
    -- ⊢ ∃ r, 0 < r ∧ r • x = y
    exact (exists_pos_left_iff_sameRay hx hy).2 hxy
    -- 🎉 no goals
#align exists_pos_left_iff_same_ray_and_ne_zero exists_pos_left_iff_sameRay_and_ne_zero

theorem exists_nonneg_left_iff_sameRay (hx : x ≠ 0) :
    (∃ r : R, 0 ≤ r ∧ r • x = y) ↔ SameRay R x y := by
  refine' ⟨fun h => _, fun h => h.exists_nonneg_left hx⟩
  -- ⊢ SameRay R x y
  rcases h with ⟨r, hr, rfl⟩
  -- ⊢ SameRay R x (r • x)
  exact SameRay.sameRay_nonneg_smul_right x hr
  -- 🎉 no goals
#align exists_nonneg_left_iff_same_ray exists_nonneg_left_iff_sameRay

theorem exists_pos_right_iff_sameRay (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ x = r • y) ↔ SameRay R x y := by
  rw [SameRay.sameRay_comm]
  -- ⊢ (∃ r, 0 < r ∧ x = r • y) ↔ SameRay R y x
  simp_rw [eq_comm (a := x)]
  -- ⊢ (∃ r, 0 < r ∧ r • y = x) ↔ SameRay R y x
  exact exists_pos_left_iff_sameRay hy hx
  -- 🎉 no goals
#align exists_pos_right_iff_same_ray exists_pos_right_iff_sameRay

theorem exists_pos_right_iff_sameRay_and_ne_zero (hy : y ≠ 0) :
    (∃ r : R, 0 < r ∧ x = r • y) ↔ SameRay R x y ∧ x ≠ 0 := by
  rw [SameRay.sameRay_comm]
  -- ⊢ (∃ r, 0 < r ∧ x = r • y) ↔ SameRay R y x ∧ x ≠ 0
  simp_rw [eq_comm (a := x)]
  -- ⊢ (∃ r, 0 < r ∧ r • y = x) ↔ SameRay R y x ∧ x ≠ 0
  exact exists_pos_left_iff_sameRay_and_ne_zero hy
  -- 🎉 no goals
#align exists_pos_right_iff_same_ray_and_ne_zero exists_pos_right_iff_sameRay_and_ne_zero

theorem exists_nonneg_right_iff_sameRay (hy : y ≠ 0) :
    (∃ r : R, 0 ≤ r ∧ x = r • y) ↔ SameRay R x y := by
  rw [SameRay.sameRay_comm]
  -- ⊢ (∃ r, 0 ≤ r ∧ x = r • y) ↔ SameRay R y x
  simp_rw [eq_comm (a := x)]
  -- ⊢ (∃ r, 0 ≤ r ∧ r • y = x) ↔ SameRay R y x
  exact exists_nonneg_left_iff_sameRay (R := R) hy
  -- 🎉 no goals
#align exists_nonneg_right_iff_same_ray exists_nonneg_right_iff_sameRay

end LinearOrderedField
