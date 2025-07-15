/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Algebra.Ring.Submonoid.Pointwise
import Mathlib.Data.Set.Semiring
import Mathlib.GroupTheory.GroupAction.SubMulAction.Pointwise

/-!
# Multiplication and division of submodules of an algebra.

An interface for multiplication and division of sub-R-modules of an R-algebra A is developed.

## Main definitions

Let `R` be a commutative ring (or semiring) and let `A` be an `R`-algebra.

* `1 : Submodule R A`   : the R-submodule R of the R-algebra A
* `Mul (Submodule R A)` : multiplication of two sub-R-modules M and N of A is defined to be
                              the smallest submodule containing all the products `m * n`.
* `Div (Submodule R A)` : `I / J` is defined to be the submodule consisting of all `a : A` such
                              that `a • J ⊆ I`

It is proved that `Submodule R A` is a semiring, and also an algebra over `Set A`.

Additionally, in the `Pointwise` locale we promote `Submodule.pointwiseDistribMulAction` to a
`MulSemiringAction` as `Submodule.pointwiseMulSemiringAction`.

When `R` is not necessarily commutative, and `A` is merely a `R`-module with a ring structure
such that `IsScalarTower R A A` holds (equivalent to the data of a ring homomorphism `R →+* A`
by `ringHomEquivModuleIsScalarTower`), we can still define `1 : Submodule R A` and
`Mul (Submodule R A)`, but `1` is only a left identity, not necessarily a right one.

## Tags

multiplication of submodules, division of submodules, submodule semiring
-/


universe uι u v

open Algebra Set MulOpposite

open Pointwise

namespace SubMulAction

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

theorem algebraMap_mem (r : R) : algebraMap R A r ∈ (1 : SubMulAction R A) :=
  ⟨r, (algebraMap_eq_smul_one r).symm⟩

theorem mem_one' {x : A} : x ∈ (1 : SubMulAction R A) ↔ ∃ y, algebraMap R A y = x :=
  exists_congr fun r => by rw [algebraMap_eq_smul_one]

end SubMulAction

namespace Submodule

section Module

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

-- TODO: Why is this in a file about `Algebra`?
-- TODO: potentially change this back to `LinearMap.range (Algebra.linearMap R A)`
-- once a version of `Algebra` without the `commutes'` field is introduced.
-- See issue https://github.com/leanprover-community/mathlib4/issues/18110.
/-- `1 : Submodule R A` is the submodule `R ∙ 1` of `A`.
-/
instance one : One (Submodule R A) :=
  ⟨LinearMap.range (LinearMap.toSpanSingleton R A 1)⟩

theorem one_eq_span : (1 : Submodule R A) = R ∙ 1 :=
  (LinearMap.span_singleton_eq_range _ _ _).symm

theorem le_one_toAddSubmonoid : 1 ≤ (1 : Submodule R A).toAddSubmonoid := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, show (n : R) • (1 : A) = n by rw [Nat.cast_smul_eq_nsmul, nsmul_one]⟩

@[simp]
theorem toSubMulAction_one : (1 : Submodule R A).toSubMulAction = 1 :=
  SetLike.ext fun _ ↦ by rw [one_eq_span, SubMulAction.mem_one]; exact mem_span_singleton

theorem one_eq_span_one_set : (1 : Submodule R A) = span R 1 :=
  one_eq_span

@[simp]
theorem one_le {P : Submodule R A} : (1 : Submodule R A) ≤ P ↔ (1 : A) ∈ P := by
  simp [one_eq_span]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

instance : SMul (Submodule R A) (Submodule R M) where
  smul A' M' :=
  { __ := A'.toAddSubmonoid • M'.toAddSubmonoid
    smul_mem' := fun r m hm ↦ AddSubmonoid.smul_induction_on hm
      (fun a ha m hm ↦ by rw [← smul_assoc]; exact AddSubmonoid.smul_mem_smul (A'.smul_mem r ha) hm)
      fun m₁ m₂ h₁ h₂ ↦ by rw [smul_add]; exact (A'.1 • M'.1).add_mem h₁ h₂ }

section

variable {I J : Submodule R A} {N P : Submodule R M}

theorem smul_toAddSubmonoid : (I • N).toAddSubmonoid = I.toAddSubmonoid • N.toAddSubmonoid := rfl

theorem smul_mem_smul {r} {n} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N :=
  AddSubmonoid.smul_mem_smul hr hn

theorem smul_le : I • N ≤ P ↔ ∀ r ∈ I, ∀ n ∈ N, r • n ∈ P :=
  AddSubmonoid.smul_le

@[simp, norm_cast]
lemma coe_set_smul : (I : Set A) • N = I • N :=
  set_smul_eq_of_le _ _ _
    (fun _ _ hr hx ↦ smul_mem_smul hr hx)
    (smul_le.mpr fun _ hr _ hx ↦ mem_set_smul_of_mem_mem hr hx)

@[elab_as_elim]
theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N) (smul : ∀ r ∈ I, ∀ n ∈ N, p (r • n))
    (add : ∀ x y, p x → p y → p (x + y)) : p x :=
  AddSubmonoid.smul_induction_on H smul add

/-- Dependent version of `Submodule.smul_induction_on`. -/
@[elab_as_elim]
theorem smul_induction_on' {x : M} (hx : x ∈ I • N) {p : ∀ x, x ∈ I • N → Prop}
    (smul : ∀ (r : A) (hr : r ∈ I) (n : M) (hn : n ∈ N), p (r • n) (smul_mem_smul hr hn))
    (add : ∀ x hx y hy, p x hx → p y hy → p (x + y) (add_mem ‹_› ‹_›)) : p x hx := by
  refine Exists.elim ?_ fun (h : x ∈ I • N) (H : p x h) ↦ H
  exact smul_induction_on hx (fun a ha x hx ↦ ⟨_, smul _ ha _ hx⟩)
    fun x y ⟨_, hx⟩ ⟨_, hy⟩ ↦ ⟨_, add _ _ _ _ hx hy⟩

theorem smul_mono (hij : I ≤ J) (hnp : N ≤ P) : I • N ≤ J • P :=
  AddSubmonoid.smul_le_smul hij hnp

theorem smul_mono_left (h : I ≤ J) : I • N ≤ J • N :=
  smul_mono h le_rfl

instance : CovariantClass (Submodule R A) (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => smul_mono le_rfl⟩

variable (I J N P)

@[simp]
theorem smul_bot : I • (⊥ : Submodule R M) = ⊥ :=
  toAddSubmonoid_injective <| AddSubmonoid.addSubmonoid_smul_bot _

@[simp]
theorem bot_smul : (⊥ : Submodule R A) • N = ⊥ :=
  le_bot_iff.mp <| smul_le.mpr <| by rintro _ rfl _ _; rw [zero_smul]; exact zero_mem _

theorem smul_sup : I • (N ⊔ P) = I • N ⊔ I • P :=
  toAddSubmonoid_injective <| by
    simp only [smul_toAddSubmonoid, sup_toAddSubmonoid, AddSubmonoid.addSubmonoid_smul_sup]

theorem sup_smul : (I ⊔ J) • N = I • N ⊔ J • N :=
  le_antisymm (smul_le.mpr fun mn hmn p hp ↦ by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_sup.mp hmn
    rw [add_smul]; exact add_mem_sup (smul_mem_smul hm hp) <| smul_mem_smul hn hp)
    (sup_le (smul_mono_left le_sup_left) <| smul_mono_left le_sup_right)

protected theorem smul_assoc {B} [Semiring B] [Module R B] [Module A B] [Module B M]
    [IsScalarTower R A B] [IsScalarTower R B M] [IsScalarTower A B M]
    (I : Submodule R A) (J : Submodule R B) (N : Submodule R M) :
    (I • J) • N = I • J • N :=
  le_antisymm
    (smul_le.2 fun _ hrsij t htn ↦ smul_induction_on hrsij
      (fun r hr s hs ↦ smul_assoc r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
      fun x y ↦ (add_smul x y t).symm ▸ add_mem)
    (smul_le.2 fun r hr _ hsn ↦ smul_induction_on hsn
      (fun j hj n hn ↦ (smul_assoc r j n).symm ▸ smul_mem_smul (smul_mem_smul hr hj) hn)
      fun m₁ m₂ ↦ (smul_add r m₁ m₂) ▸ add_mem)

theorem smul_iSup {ι : Sort*} {I : Submodule R A} {t : ι → Submodule R M} :
    I • (⨆ i, t i)= ⨆ i, I • t i :=
  toAddSubmonoid_injective <| by
    simp only [smul_toAddSubmonoid, iSup_toAddSubmonoid, AddSubmonoid.smul_iSup]

theorem iSup_smul {ι : Sort*} {t : ι → Submodule R A} {N : Submodule R M} :
    (⨆ i, t i) • N = ⨆ i, t i • N :=
  le_antisymm (smul_le.mpr fun t ht s hs ↦ iSup_induction _ (motive := (· • s ∈ _)) ht
    (fun i t ht ↦ mem_iSup_of_mem i <| smul_mem_smul ht hs)
    (by simp_rw [zero_smul]; apply zero_mem) fun x y ↦ by simp_rw [add_smul]; apply add_mem)
    (iSup_le fun i ↦ Submodule.smul_mono_left <| le_iSup _ i)

protected theorem one_smul : (1 : Submodule R A) • N = N := by
  refine le_antisymm (smul_le.mpr fun r hr m hm ↦ ?_) fun m hm ↦ ?_
  · obtain ⟨r, rfl⟩ := hr
    rw [LinearMap.toSpanSingleton_apply, smul_one_smul]; exact N.smul_mem r hm
  · rw [← one_smul A m]; exact smul_mem_smul (one_le.mp le_rfl) hm

theorem smul_subset_smul : (↑I : Set A) • (↑N : Set M) ⊆ (↑(I • N) : Set M) :=
  AddSubmonoid.smul_subset_smul

end

variable [IsScalarTower R A A]

/-- Multiplication of sub-R-modules of an R-module A that is also a semiring. The submodule `M * N`
consists of finite sums of elements `m * n` for `m ∈ M` and `n ∈ N`. -/
instance mul : Mul (Submodule R A) where
  mul := (· • ·)

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem mul_mem_mul (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
  smul_mem_smul hm hn

theorem mul_le : M * N ≤ P ↔ ∀ m ∈ M, ∀ n ∈ N, m * n ∈ P :=
  smul_le

theorem mul_toAddSubmonoid (M N : Submodule R A) :
    (M * N).toAddSubmonoid = M.toAddSubmonoid * N.toAddSubmonoid := rfl

@[elab_as_elim]
protected theorem mul_induction_on {C : A → Prop} {r : A} (hr : r ∈ M * N)
    (hm : ∀ m ∈ M, ∀ n ∈ N, C (m * n)) (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
  smul_induction_on hr hm ha

/-- A dependent version of `mul_induction_on`. -/
@[elab_as_elim]
protected theorem mul_induction_on' {C : ∀ r, r ∈ M * N → Prop}
    (mem_mul_mem : ∀ m (hm : m ∈ M) n (hn : n ∈ N), C (m * n) (mul_mem_mul hm hn))
    (add : ∀ x hx y hy, C x hx → C y hy → C (x + y) (add_mem hx hy)) {r : A} (hr : r ∈ M * N) :
    C r hr :=
  smul_induction_on' hr mem_mul_mem add

variable (M)

@[simp]
theorem mul_bot : M * ⊥ = ⊥ :=
  smul_bot _

@[simp]
theorem bot_mul : ⊥ * M = ⊥ :=
  bot_smul _

protected theorem one_mul : (1 : Submodule R A) * M = M :=
  Submodule.one_smul _

variable {M}

@[mono]
theorem mul_le_mul (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q :=
  smul_mono hmp hnq

theorem mul_le_mul_left (h : M ≤ N) : M * P ≤ N * P :=
  smul_mono_left h

theorem mul_le_mul_right (h : N ≤ P) : M * N ≤ M * P :=
  smul_mono_right _ h

theorem mul_comm_of_commute (h : ∀ m ∈ M, ∀ n ∈ N, Commute m n) : M * N = N * M :=
  toAddSubmonoid_injective <| AddSubmonoid.mul_comm_of_commute h

variable (M N P)

theorem mul_sup : M * (N ⊔ P) = M * N ⊔ M * P :=
  smul_sup _ _ _

theorem sup_mul : (M ⊔ N) * P = M * P ⊔ N * P :=
  sup_smul _ _ _

theorem mul_subset_mul : (↑M : Set A) * (↑N : Set A) ⊆ (↑(M * N) : Set A) :=
  smul_subset_smul _ _

lemma restrictScalars_mul {A B C} [Semiring A] [Semiring B] [Semiring C]
    [SMul A B] [Module A C] [Module B C] [IsScalarTower A C C] [IsScalarTower B C C]
    [IsScalarTower A B C] {I J : Submodule B C} :
    (I * J).restrictScalars A = I.restrictScalars A * J.restrictScalars A :=
  rfl

variable {ι : Sort uι}

theorem iSup_mul (s : ι → Submodule R A) (t : Submodule R A) : (⨆ i, s i) * t = ⨆ i, s i * t :=
  iSup_smul

theorem mul_iSup (t : Submodule R A) (s : ι → Submodule R A) : (t * ⨆ i, s i) = ⨆ i, t * s i :=
  smul_iSup

/-- Sub-`R`-modules of an `R`-module form an idempotent semiring. -/
instance : NonUnitalSemiring (Submodule R A) where
  __ := toAddSubmonoid_injective.semigroup _ mul_toAddSubmonoid
  zero_mul := bot_mul
  mul_zero := mul_bot
  left_distrib := mul_sup
  right_distrib := sup_mul

instance : Pow (Submodule R A) ℕ where
  pow s n := npowRec n s

theorem pow_eq_npowRec {n : ℕ} : M ^ n = npowRec n M := rfl

protected theorem pow_zero : M ^ 0 = 1 := rfl

protected theorem pow_succ {n : ℕ} : M ^ (n + 1) = M ^ n * M := rfl

protected theorem pow_add {m n : ℕ} (h : n ≠ 0) : M ^ (m + n) = M ^ m * M ^ n :=
  npowRec_add m n h _ M.one_mul

protected theorem pow_one : M ^ 1 = M := by
  rw [Submodule.pow_succ, Submodule.pow_zero, Submodule.one_mul]

/-- `Submodule.pow_succ` with the right hand side commuted. -/
protected theorem pow_succ' {n : ℕ} (h : n ≠ 0) : M ^ (n + 1) = M * M ^ n := by
  rw [add_comm, M.pow_add h, Submodule.pow_one]

theorem pow_toAddSubmonoid {n : ℕ} (h : n ≠ 0) : (M ^ n).toAddSubmonoid = M.toAddSubmonoid ^ n := by
  induction n with
  | zero => exact (h rfl).elim
  | succ n ih =>
    rw [Submodule.pow_succ, pow_succ, mul_toAddSubmonoid]
    cases n with
    | zero => rw [Submodule.pow_zero, pow_zero, one_mul, ← mul_toAddSubmonoid, Submodule.one_mul]
    | succ n => rw [ih n.succ_ne_zero]

theorem le_pow_toAddSubmonoid {n : ℕ} : M.toAddSubmonoid ^ n ≤ (M ^ n).toAddSubmonoid := by
  obtain rfl | hn := Decidable.eq_or_ne n 0
  · rw [Submodule.pow_zero, pow_zero]
    exact le_one_toAddSubmonoid
  · exact (pow_toAddSubmonoid M hn).ge

theorem pow_subset_pow {n : ℕ} : (↑M : Set A) ^ n ⊆ ↑(M ^ n : Submodule R A) :=
  trans AddSubmonoid.pow_subset_pow (le_pow_toAddSubmonoid M)

theorem pow_mem_pow {x : A} (hx : x ∈ M) (n : ℕ) : x ^ n ∈ M ^ n :=
  pow_subset_pow _ <| Set.pow_mem_pow hx

lemma restrictScalars_pow {A B C : Type*} [Semiring A] [Semiring B]
    [Semiring C] [SMul A B] [Module A C] [Module B C]
    [IsScalarTower A C C] [IsScalarTower B C C] [IsScalarTower A B C]
    {I : Submodule B C} :
    ∀ {n : ℕ}, (hn : n ≠ 0) → (I ^ n).restrictScalars A = I.restrictScalars A ^ n
  | 1, _ => by simp [Submodule.pow_one]
  | n + 2, _ => by
    simp [Submodule.pow_succ (n := n + 1), restrictScalars_mul, restrictScalars_pow n.succ_ne_zero]

end Module

variable {ι : Sort uι}
variable {R : Type u} [CommSemiring R]

section AlgebraSemiring

variable {A : Type v} [Semiring A] [Algebra R A]
variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

theorem one_eq_range : (1 : Submodule R A) = LinearMap.range (Algebra.linearMap R A) := by
  rw [one_eq_span, LinearMap.span_singleton_eq_range,
    LinearMap.toSpanSingleton_eq_algebra_linearMap]

theorem algebraMap_mem (r : R) : algebraMap R A r ∈ (1 : Submodule R A) := by
  simp [one_eq_range]

@[simp]
theorem mem_one {x : A} : x ∈ (1 : Submodule R A) ↔ ∃ y, algebraMap R A y = x := by
  simp [one_eq_range]

protected theorem map_one {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') :
    map f.toLinearMap (1 : Submodule R A) = 1 := by
  ext
  simp

@[simp]
theorem map_op_one :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (1 : Submodule R A) = 1 := by
  ext x
  induction x
  simp

@[simp]
theorem comap_op_one :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (1 : Submodule R Aᵐᵒᵖ) = 1 := by
  ext
  simp

@[simp]
theorem map_unop_one :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (1 : Submodule R Aᵐᵒᵖ) = 1 := by
  rw [← comap_equiv_eq_map_symm, comap_op_one]

@[simp]
theorem comap_unop_one :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (1 : Submodule R A) = 1 := by
  rw [← map_equiv_eq_comap_symm, map_op_one]

theorem mul_eq_map₂ : M * N = map₂ (LinearMap.mul R A) M N :=
  le_antisymm (mul_le.mpr fun _m hm _n ↦ apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n ↦ mul_mem_mul hm)

variable (R M N)

theorem span_mul_span : span R S * span R T = span R (S * T) := by
  rw [mul_eq_map₂]; apply map₂_span_span

lemma mul_def : M * N = span R (M * N : Set A) := by simp [← span_mul_span]

variable {R} (P Q)

protected theorem mul_one : M * 1 = M := by
  conv_lhs => rw [one_eq_span, ← span_eq M]
  rw [span_mul_span]
  simp

protected theorem map_mul {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') :
    map f.toLinearMap (M * N) = map f.toLinearMap M * map f.toLinearMap N :=
  calc
    map f.toLinearMap (M * N) = ⨆ i : M, (N.map (LinearMap.mul R A i)).map f.toLinearMap := by
      rw [mul_eq_map₂]; apply map_iSup
    _ = map f.toLinearMap M * map f.toLinearMap N := by
      rw [mul_eq_map₂]
      apply congr_arg sSup
      ext S
      constructor <;> rintro ⟨y, hy⟩
      · use ⟨f y, mem_map.mpr ⟨y.1, y.2, rfl⟩⟩
        refine Eq.trans ?_ hy
        ext
        simp
      · obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2
        use ⟨y', hy'⟩
        refine Eq.trans ?_ hy
        rw [f.toLinearMap_apply] at fy_eq
        ext
        simp [fy_eq]

theorem map_op_mul :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M * N) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) N *
        map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M := by
  apply le_antisymm
  · simp_rw [map_le_iff_le_comap]
    refine mul_le.2 fun m hm n hn => ?_
    rw [mem_comap, map_equiv_eq_comap_symm, map_equiv_eq_comap_symm]
    show op n * op m ∈ _
    exact mul_mem_mul hn hm
  · refine mul_le.2 (MulOpposite.rec' fun m hm => MulOpposite.rec' fun n hn => ?_)
    rw [Submodule.mem_map_equiv] at hm hn ⊢
    exact mul_mem_mul hn hm

theorem comap_unop_mul :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M * N) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) N *
        comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M := by
  simp_rw [← map_equiv_eq_comap_symm, map_op_mul]

theorem map_unop_mul (M N : Submodule R Aᵐᵒᵖ) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M * N) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) N *
        map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M :=
  have : Function.Injective (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) :=
    LinearEquiv.injective _
  map_injective_of_injective this <| by
    rw [← map_comp, map_op_mul, ← map_comp, ← map_comp, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, map_id, map_id, map_id]

theorem comap_op_mul (M N : Submodule R Aᵐᵒᵖ) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M * N) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) N *
        comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M := by
  simp_rw [comap_equiv_eq_map_symm, map_unop_mul]

section
variable {α : Type*} [Monoid α] [DistribMulAction α A] [SMulCommClass α R A]

instance [IsScalarTower α A A] : IsScalarTower α (Submodule R A) (Submodule R A) where
  smul_assoc a S T := by
    rw [← S.span_eq, ← T.span_eq, smul_span, smul_eq_mul, smul_eq_mul, span_mul_span, span_mul_span,
      smul_span, smul_mul_assoc]

instance [SMulCommClass α A A] : SMulCommClass α (Submodule R A) (Submodule R A) where
  smul_comm a S T := by
    rw [← S.span_eq, ← T.span_eq, smul_span, smul_eq_mul, smul_eq_mul, span_mul_span, span_mul_span,
      smul_span, mul_smul_comm]

instance [SMulCommClass A α A] : SMulCommClass (Submodule R A) α (Submodule R A) :=
  have := SMulCommClass.symm A α A; .symm ..

end

section

open Pointwise

/-- `Submodule.pointwiseNeg` distributes over multiplication.

This is available as an instance in the `Pointwise` locale. -/
protected def hasDistribPointwiseNeg {A} [Ring A] [Algebra R A] : HasDistribNeg (Submodule R A) :=
  toAddSubmonoid_injective.hasDistribNeg _ neg_toAddSubmonoid mul_toAddSubmonoid

scoped[Pointwise] attribute [instance] Submodule.hasDistribPointwiseNeg

end

section DecidableEq

theorem mem_span_mul_finite_of_mem_span_mul {R A} [Semiring R] [AddCommMonoid A] [Mul A]
    [Module R A] {S : Set A} {S' : Set A} {x : A} (hx : x ∈ span R (S * S')) :
    ∃ T T' : Finset A, ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ x ∈ span R (T * T' : Set A) := by
  classical
  obtain ⟨U, h, hU⟩ := mem_span_finite_of_mem_span hx
  obtain ⟨T, T', hS, hS', h⟩ := Finset.subset_mul h
  use T, T', hS, hS'
  have h' : (U : Set A) ⊆ T * T' := by assumption_mod_cast
  have h'' := span_mono h' hU
  assumption

end DecidableEq

theorem mul_eq_span_mul_set (s t : Submodule R A) : s * t = span R ((s : Set A) * (t : Set A)) := by
  rw [mul_eq_map₂]; exact map₂_eq_span_image2 _ s t

theorem mem_span_mul_finite_of_mem_mul {P Q : Submodule R A} {x : A} (hx : x ∈ P * Q) :
    ∃ T T' : Finset A, (T : Set A) ⊆ P ∧ (T' : Set A) ⊆ Q ∧ x ∈ span R (T * T' : Set A) :=
  Submodule.mem_span_mul_finite_of_mem_span_mul
    (by rwa [← Submodule.span_eq P, ← Submodule.span_eq Q, Submodule.span_mul_span] at hx)

variable {M N P}

theorem mem_span_singleton_mul {x y : A} : x ∈ span R {y} * P ↔ ∃ z ∈ P, y * z = x := by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map, mem_map, LinearMap.mul_apply_apply]

theorem mem_mul_span_singleton {x y : A} : x ∈ P * span R {y} ↔ ∃ z ∈ P, z * y = x := by
  simp_rw [mul_eq_map₂, map₂_span_singleton_eq_map_flip, mem_map, LinearMap.flip_apply,
    LinearMap.mul_apply_apply]

lemma span_singleton_mul {x : A} {p : Submodule R A} :
    Submodule.span R {x} * p = x • p := ext fun _ ↦ mem_span_singleton_mul

lemma mem_smul_iff_inv_mul_mem {S} [DivisionSemiring S] [Algebra R S] {x : S} {p : Submodule R S}
    {y : S} (hx : x ≠ 0) : y ∈ x • p ↔ x⁻¹ * y ∈ p := by
  constructor
  · rintro ⟨a, ha : a ∈ p, rfl⟩; simpa [inv_mul_cancel_left₀ hx]
  · exact fun h ↦ ⟨_, h, by simp [mul_inv_cancel_left₀ hx]⟩

lemma mul_mem_smul_iff {S} [CommRing S] [Algebra R S] {x : S} {p : Submodule R S} {y : S}
    (hx : x ∈ nonZeroDivisors S) :
    x * y ∈ x • p ↔ y ∈ p := by
  simp [mem_smul_pointwise_iff_exists, mul_cancel_left_mem_nonZeroDivisors hx]

variable (M N) in
theorem mul_smul_mul_eq_smul_mul_smul (x y : R) : (x * y) • (M * N) = (x • M) * (y • N) := by
  ext
  refine ⟨?_, fun hx ↦ Submodule.mul_induction_on hx ?_ fun _ _ hx hy ↦ Submodule.add_mem _ hx hy⟩
  · rintro ⟨_, hx, rfl⟩
    rw [DistribMulAction.toLinearMap_apply]
    refine Submodule.mul_induction_on hx (fun m hm n hn ↦ ?_) (fun _ _ hn hm ↦ ?_)
    · rw [mul_smul_mul_comm]
      exact mul_mem_mul (smul_mem_pointwise_smul m x M hm) (smul_mem_pointwise_smul n y N hn)
    · rw [smul_add]
      exact Submodule.add_mem _ hn hm
  · rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩
    simp_rw [DistribMulAction.toLinearMap_apply, smul_mul_smul_comm]
    exact smul_mem_pointwise_smul _ _ _ (mul_mem_mul hm hn)

/-- Sub-R-modules of an R-algebra form an idempotent semiring. -/
instance idemSemiring : IdemSemiring (Submodule R A) where
  __ := instNonUnitalSemiring
  one_mul := Submodule.one_mul
  mul_one := Submodule.mul_one
  bot_le _ := bot_le

instance : IsOrderedRing (Submodule R A) where
  mul_le_mul_of_nonneg_left _ _ _ h _ := mul_le_mul_left' h _
  mul_le_mul_of_nonneg_right _ _ _ h _ := mul_le_mul_right' h _

variable (M)

theorem span_pow (s : Set A) : ∀ n : ℕ, span R s ^ n = span R (s ^ n)
  | 0 => by rw [pow_zero, pow_zero, one_eq_span_one_set]
  | n + 1 => by rw [pow_succ, pow_succ, span_pow s n, span_mul_span]

theorem pow_eq_span_pow_set (n : ℕ) : M ^ n = span R ((M : Set A) ^ n) := by
  rw [← span_pow, span_eq]

/-- Dependent version of `Submodule.pow_induction_on_left`. -/
@[elab_as_elim]
protected theorem pow_induction_on_left' {C : ∀ (n : ℕ) (x), x ∈ M ^ n → Prop}
    (algebraMap : ∀ r : R, C 0 (algebraMap _ _ r) (algebraMap_mem r))
    (add : ∀ x y i hx hy, C i x hx → C i y hy → C i (x + y) (add_mem ‹_› ‹_›))
    (mem_mul : ∀ m (hm : m ∈ M), ∀ (i x hx), C i x hx → C i.succ (m * x)
      ((pow_succ' M i).symm ▸ (mul_mem_mul hm hx)))
    {n : ℕ} {x : A}
    (hx : x ∈ M ^ n) : C n x hx := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ']
    exact fun hx ↦ Submodule.mul_induction_on' (fun m hm x ih => mem_mul _ hm _ _ _ (n_ih ih))
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

/-- Dependent version of `Submodule.pow_induction_on_right`. -/
@[elab_as_elim]
protected theorem pow_induction_on_right' {C : ∀ (n : ℕ) (x), x ∈ M ^ n → Prop}
    (algebraMap : ∀ r : R, C 0 (algebraMap _ _ r) (algebraMap_mem r))
    (add : ∀ x y i hx hy, C i x hx → C i y hy → C i (x + y) (add_mem ‹_› ‹_›))
    (mul_mem :
      ∀ i x hx, C i x hx →
        ∀ m (hm : m ∈ M), C i.succ (x * m) (mul_mem_mul hx hm))
    {n : ℕ} {x : A} (hx : x ∈ M ^ n) : C n x hx := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := mem_one.mp hx
    exact algebraMap r
  | succ n n_ih =>
    revert hx
    simp_rw [pow_succ]
    exact fun hx ↦ Submodule.mul_induction_on' (fun m hm x ih => mul_mem _ _ hm (n_ih _) _ ih)
      (fun x hx y hy Cx Cy => add _ _ _ _ _ Cx Cy) hx

/-- To show a property on elements of `M ^ n` holds, it suffices to show that it holds for scalars,
is closed under addition, and holds for `m * x` where `m ∈ M` and it holds for `x` -/
@[elab_as_elim]
protected theorem pow_induction_on_left {C : A → Prop} (hr : ∀ r : R, C (algebraMap _ _ r))
    (hadd : ∀ x y, C x → C y → C (x + y)) (hmul : ∀ m ∈ M, ∀ (x), C x → C (m * x)) {x : A} {n : ℕ}
    (hx : x ∈ M ^ n) : C x :=
  Submodule.pow_induction_on_left' M (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _m hm _i _x _hx => hmul _ hm _) hx

/-- To show a property on elements of `M ^ n` holds, it suffices to show that it holds for scalars,
is closed under addition, and holds for `x * m` where `m ∈ M` and it holds for `x` -/
@[elab_as_elim]
protected theorem pow_induction_on_right {C : A → Prop} (hr : ∀ r : R, C (algebraMap _ _ r))
    (hadd : ∀ x y, C x → C y → C (x + y)) (hmul : ∀ x, C x → ∀ m ∈ M, C (x * m)) {x : A} {n : ℕ}
    (hx : x ∈ M ^ n) : C x :=
  Submodule.pow_induction_on_right' (M := M) (C := fun _ a _ => C a) hr
    (fun x y _i _hx _hy => hadd x y)
    (fun _i _x _hx => hmul _) hx

/-- `Submonoid.map` as a `RingHom`, when applied to an `AlgHom`. -/
@[simps]
def mapHom {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') :
    Submodule R A →+* Submodule R A' where
  toFun := map f.toLinearMap
  map_zero' := Submodule.map_bot _
  map_add' := (Submodule.map_sup · · _)
  map_one' := Submodule.map_one _
  map_mul' := (Submodule.map_mul · · _)

theorem mapHom_id : mapHom (.id R A) = .id _ := RingHom.ext map_id

/-- The ring of submodules of the opposite algebra is isomorphic to the opposite ring of
submodules. -/
@[simps apply symm_apply]
def equivOpposite : Submodule R Aᵐᵒᵖ ≃+* (Submodule R A)ᵐᵒᵖ where
  toFun p := op <| p.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ)
  invFun p := p.unop.comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A)
  left_inv _ := SetLike.coe_injective <| rfl
  right_inv _ := unop_injective <| SetLike.coe_injective rfl
  map_add' p q := by simp [comap_equiv_eq_map_symm, ← op_add]
  map_mul' _ _ := congr_arg op <| comap_op_mul _ _

protected theorem map_pow {A'} [Semiring A'] [Algebra R A'] (f : A →ₐ[R] A') (n : ℕ) :
    map f.toLinearMap (M ^ n) = map f.toLinearMap M ^ n :=
  map_pow (mapHom f) M n

theorem comap_unop_pow (n : ℕ) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M ^ n) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M ^ n :=
  (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).symm.map_pow (op M) n

theorem comap_op_pow (n : ℕ) (M : Submodule R Aᵐᵒᵖ) :
    comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M ^ n) =
      comap (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M ^ n :=
  op_injective <| (equivOpposite : Submodule R Aᵐᵒᵖ ≃+* _).map_pow M n

theorem map_op_pow (n : ℕ) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M ^ n) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M ^ n := by
  rw [map_equiv_eq_comap_symm, map_equiv_eq_comap_symm, comap_unop_pow]

theorem map_unop_pow (n : ℕ) (M : Submodule R Aᵐᵒᵖ) :
    map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M ^ n) =
      map (↑(opLinearEquiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M ^ n := by
  rw [← comap_equiv_eq_map_symm, ← comap_equiv_eq_map_symm, comap_op_pow]

/-- `span` is a semiring homomorphism (recall multiplication is pointwise multiplication of subsets
on either side). -/
@[simps]
noncomputable def span.ringHom : SetSemiring A →+* Submodule R A where
  toFun s := Submodule.span R (SetSemiring.down s)
  map_zero' := span_empty
  map_one' := one_eq_span.symm
  map_add' := span_union
  map_mul' s t := by simp_rw [SetSemiring.down_mul, span_mul_span]

section

variable {α : Type*} [Monoid α] [MulSemiringAction α A] [SMulCommClass α R A]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`. -/
protected def pointwiseMulSemiringAction : MulSemiringAction α (Submodule R A) where
  __ := Submodule.pointwiseDistribMulAction
  smul_mul r x y := Submodule.map_mul x y <| MulSemiringAction.toAlgHom R A r
  smul_one r := Submodule.map_one <| MulSemiringAction.toAlgHom R A r

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulSemiringAction

end

end AlgebraSemiring

section AlgebraCommSemiring

variable {A : Type v} [CommSemiring A] [Algebra R A]
variable {M N : Submodule R A} {m n : A}

theorem mul_mem_mul_rev (hm : m ∈ M) (hn : n ∈ N) : n * m ∈ M * N :=
  mul_comm m n ▸ mul_mem_mul hm hn

variable (M N)

protected theorem mul_comm : M * N = N * M :=
  le_antisymm (mul_le.2 fun _r hrm _s hsn => mul_mem_mul_rev hsn hrm)
    (mul_le.2 fun _r hrn _s hsm => mul_mem_mul_rev hsm hrn)

/-- Sub-R-modules of an R-algebra A form a semiring. -/
instance : IdemCommSemiring (Submodule R A) :=
  { Submodule.idemSemiring with mul_comm := Submodule.mul_comm }

theorem prod_span {ι : Type*} (s : Finset ι) (M : ι → Set A) :
    (∏ i ∈ s, Submodule.span R (M i)) = Submodule.span R (∏ i ∈ s, M i) := by
  letI := Classical.decEq ι
  refine Finset.induction_on s ?_ ?_
  · simp [one_eq_span, Set.singleton_one]
  · intro _ _ H ih
    rw [Finset.prod_insert H, Finset.prod_insert H, ih, span_mul_span]

theorem prod_span_singleton {ι : Type*} (s : Finset ι) (x : ι → A) :
    (∏ i ∈ s, span R ({x i} : Set A)) = span R {∏ i ∈ s, x i} := by
  rw [prod_span, Set.finset_prod_singleton]

variable (R A)

/-- R-submodules of the R-algebra A are a module over `Set A`. -/
noncomputable instance moduleSet : Module (SetSemiring A) (Submodule R A) where
  smul s P := span R (SetSemiring.down s) * P
  smul_add _ _ _ := mul_add _ _ _
  add_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_add, span_union, sup_mul, add_eq_sup]
  mul_smul s t P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_mul, ← mul_assoc, span_mul_span]
  one_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_one, ← one_eq_span_one_set, one_mul]
  zero_smul P := by
    simp_rw [HSMul.hSMul, SetSemiring.down_zero, span_empty, bot_mul, bot_eq_zero]
  smul_zero _ := mul_bot _

variable {R A}

theorem setSemiring_smul_def (s : SetSemiring A) (P : Submodule R A) :
    s • P = span R (SetSemiring.down (α := A) s) * P :=
  rfl

theorem smul_le_smul {s t : SetSemiring A} {M N : Submodule R A}
    (h₁ : SetSemiring.down (α := A) s ⊆ SetSemiring.down (α := A) t)
    (h₂ : M ≤ N) : s • M ≤ t • N :=
  mul_le_mul (span_mono h₁) h₂

theorem singleton_smul (a : A) (M : Submodule R A) :
    Set.up ({a} : Set A) • M = M.map (LinearMap.mulLeft R a) := by
  conv_lhs => rw [← span_eq M]
  rw [setSemiring_smul_def, SetSemiring.down_up, span_mul_span, singleton_mul]
  exact (map (LinearMap.mulLeft R a) M).span_eq

section Quotient

/-- The elements of `I / J` are the `x` such that `x • J ⊆ I`.

In fact, we define `x ∈ I / J` to be `∀ y ∈ J, x * y ∈ I` (see `mem_div_iff_forall_mul_mem`),
which is equivalent to `x • J ⊆ I` (see `mem_div_iff_smul_subset`), but nicer to use in proofs.

This is the general form of the ideal quotient, traditionally written $I : J$.
-/
instance : Div (Submodule R A) :=
  ⟨fun I J =>
    { carrier := { x | ∀ y ∈ J, x * y ∈ I }
      zero_mem' := fun y _ => by
        rw [zero_mul]
        apply Submodule.zero_mem
      add_mem' := fun ha hb y hy => by
        rw [add_mul]
        exact Submodule.add_mem _ (ha _ hy) (hb _ hy)
      smul_mem' := fun r x hx y hy => by
        rw [Algebra.smul_mul_assoc]
        exact Submodule.smul_mem _ _ (hx _ hy) }⟩

theorem mem_div_iff_forall_mul_mem {x : A} {I J : Submodule R A} : x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I :=
  Iff.refl _

theorem mem_div_iff_smul_subset {x : A} {I J : Submodule R A} : x ∈ I / J ↔ x • (J : Set A) ⊆ I :=
  ⟨fun h y ⟨y', hy', xy'_eq_y⟩ => by rw [← xy'_eq_y]; exact h _ hy',
    fun h _ hy => h (Set.smul_mem_smul_set hy)⟩

theorem le_div_iff {I J K : Submodule R A} : I ≤ J / K ↔ ∀ x ∈ I, ∀ z ∈ K, x * z ∈ J :=
  Iff.refl _

theorem le_div_iff_mul_le {I J K : Submodule R A} : I ≤ J / K ↔ I * K ≤ J := by
  rw [le_div_iff, mul_le]

theorem one_le_one_div {I : Submodule R A} : 1 ≤ 1 / I ↔ I ≤ 1 := by
  rw [le_div_iff_mul_le, one_mul]

@[simp]
theorem one_mem_div {I J : Submodule R A} : 1 ∈ I / J ↔ J ≤ I := by
  rw [← one_le, le_div_iff_mul_le, one_mul]

theorem le_self_mul_one_div {I : Submodule R A} (hI : I ≤ 1) : I ≤ I * (1 / I) := by
  refine (mul_one I).symm.trans_le ?_
  apply mul_le_mul_right (one_le_one_div.mpr hI)

theorem mul_one_div_le_one {I : Submodule R A} : I * (1 / I) ≤ 1 := by
  rw [Submodule.mul_le]
  intro m hm n hn
  rw [Submodule.mem_div_iff_forall_mul_mem] at hn
  rw [mul_comm]
  exact hn m hm

@[simp]
protected theorem map_div {B : Type*} [CommSemiring B] [Algebra R B] (I J : Submodule R A)
    (h : A ≃ₐ[R] B) : (I / J).map h.toLinearMap = I.map h.toLinearMap / J.map h.toLinearMap := by
  ext x
  simp only [mem_map, mem_div_iff_forall_mul_mem, AlgEquiv.toLinearMap_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hx _ hy, map_mul h x y⟩
  · rintro hx
    refine ⟨h.symm x, fun z hz => ?_, h.apply_symm_apply x⟩
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩
    convert xz_mem
    apply h.injective
    rw [map_mul, h.apply_symm_apply, hxz]

end Quotient

end AlgebraCommSemiring

end Submodule
