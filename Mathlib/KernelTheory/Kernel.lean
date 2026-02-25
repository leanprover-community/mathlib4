/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Normed.Operator.Compact
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Real.CompleteField
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Reproducing kernels

This file develops the basic theory of reproducing kernels, which underlies the reproducing kernel
Hilbert spaces. It shows that the kernels form an ordered semiring and common ways of constructing
kernels from other kernels.

## Tags

Kernels

## TODO

* Change from real-valued to complex-valued / vector-valuad kernels.
* Mercer's theorem
-/

@[expose] public section

open Real

variable {X : Type*}

/-- Standard defintion of a real-valued kernel in the context of reproducing kernel Hilbert spaces:
 A symmetric function `K: X×X→ℝ` that is positive semi-definite.
-/
structure Kernel X where
  /-- The kernel function `K : X → X → ℝ`. -/
  kernel : X → X → ℝ
  /-- Symmetry: `K(x₁,x₂) = K(x₂,x₁)` for all `x₁,x₂∈X`. -/
  symmetric : ∀ x y : X, kernel x y = kernel y x
  /-- Positive semi-definite: ∑_{x₁∈ support(c)}∑_{x₂∈ support(c)} c(x₁)*c(x₂)*K(x₁,x₂)≥0.
   Atypical but equivalent and more convenient way of writing it. Typical way is part of theorem
  `posSemiDefₙ`. -/
  posSemiDef : ∀ (c : X →₀ ℝ), ∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * kernel x y ≥ 0

namespace Kernel

/-- The kernel function of a kernel is encoded in the field `.kernel`. -/
instance : CoeFun (Kernel X) (fun _ => X → X → ℝ) := ⟨Kernel.kernel⟩


/-- All kernels are nonnegative on the diagonal. -/
theorem nonneg (K : Kernel X) : ∀ x : X, K x x ≥ 0 := by
  intro x
  have h := K.posSemiDef (Finsupp.single x 1)
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finset.sum_singleton, Finsupp.single_eq_same] at h
  rw [one_mul, one_mul] at h
  exact h

/-- Reformulation of `Kernel.posSemiDef` which takes an explicit subset of X as input, instead of
  using the implicit set subset of X given by the support of `c:X→₀ℝ`. -/
theorem posSemiDefₓ (K : Kernel X) : ∀ (s : Finset X) (c : X →₀ ℝ),
  ∑ x ∈ s, ∑ y ∈ s, c x * c y * K x y ≥ 0 := by
  classical
  intro s c
  let c' : X →₀ ℝ := c.filter (fun x => x ∈ s ∩ c.support)
  have hc : c'.support ⊆ s := by
    intro x hx
    rw [Finsupp.support_filter, Finset.mem_filter, Finset.mem_inter] at hx
    exact hx.2.1
  have : ∑ x ∈ s, ∑ y ∈ s, c x * c y * K x y = ∑ x ∈ s, ∑ y ∈ s, c' x * c' y * K x y := by
    apply Finset.sum_congr
    · exact rfl
    rintro x hx
    apply Finset.sum_congr
    · exact rfl
    rintro y hy
    simp only [mul_eq_mul_right_iff]
    left
    have hzc : ∀ (z : X) (hz : z ∈ s), c z = c' z := by
      intro z hz
      by_cases hc : z ∈ c.support
      · simp [c', Finsupp.filter_apply, hz]
      · simp [c', Finsupp.notMem_support_iff.1 hc]
    rw [hzc x hx]
    rw [hzc y hy]
  rw [this]
  let f := fun x => ∑ y ∈ s, c' x * c' y * K x y
  let f' := fun x => ∑ y ∈ c'.support, c' x * c' y * K x y
  have h0 : ∀ x ∈ s, x ∉ c'.support → f x = 0 := by
    intro x hx hnc
    subst f
    simp_rw [mul_assoc, <-Finset.mul_sum, mul_eq_zero]
    left
    exact Finsupp.notMem_support_iff.mp hnc
  rw [<-Finset.sum_subset (s₁ := c'.support) (s₂ := s) (f := f) hc h0]
  have : ∑ x ∈ c'.support, f x = ∑ x ∈ c'.support, f' x := by
    apply Finset.sum_congr
    · exact rfl
    rintro x hx
    subst f f'
    simp only
    let g := fun y => c' x * c' y * K x y
    have : ∀ y ∈ s, y ∉ c'.support → g y = 0 := by
      intro y hy hnc
      subst g
      simp_rw [mul_assoc, mul_eq_zero]
      right; left -- get the middle condition
      exact Finsupp.notMem_support_iff.mp hnc
    exact Eq.symm (Finset.sum_subset hc this)
  rw [this]
  subst f'
  simp only [ge_iff_le]
  exact K.posSemiDef c'

/-- Standard way of writing `Kernel.posSemiDef` on paper, but this way is less convenient for use
 in lean. Given a sequence `{x₁, ... , xₙ}` and coefficients `{c₁, ... , cₙ}`,
 $∑_{n=1}^∞ ∑_{m=1}^∞ c_n * c_m * K(x_n,x_m) ≥ 0$. -/
theorem posSemiDefₙ (K : Kernel X) (N : Nat) (xs : Fin N → X) (c : Fin N → ℝ)
  (hinj : Function.Injective xs) : ∑ i ∈ Finset.univ, ∑ j ∈ Finset.univ, c i * K (xs i) (xs j)
                                                                                    * c j ≥ 0 := by
  classical
  let c' : X →₀ ℝ :=
    { support := (c.support.image xs).toFinset
      toFun := fun x => if h : ∃ n, xs n = x then c (Classical.choose h) else 0
      mem_support_toFun := by
        intro x
        have h1 : x ∈ (c.support.image xs).toFinset ↔ ∃ n ∈ Function.support c, xs n = x := by
          rw [Set.mem_toFinset]
          rfl
        rw [h1]
        simp only [Function.mem_support, ne_eq, dite_eq_right_iff, forall_exists_index, not_forall]
        constructor
        · rintro hl
          let hn := Classical.choose_spec hl
          set n := Classical.choose hl
          use n
          use hn.2
          set hp := (Exists.intro n hn.right : ∃ x_1, xs x_1 = x)
          have hm := Classical.choose_spec hp
          set m := Classical.choose hp
          have : n = m := by
            apply hinj
            exact cast (congrArg (Eq (xs n)) (id (Eq.symm hm))) hn.right
          rw [<-this]
          exact hn.left
        · intro hr
          have hn := Classical.choose_spec hr
          set n := Classical.choose hr
          have h_spec := Classical.choose_spec hn
          set h := Classical.choose hn
          use n
          rw [and_iff_left h]
          set hp := (Exists.intro n h : ∃ m, xs m = x)
          have hm := Classical.choose_spec hp
          set m := Classical.choose hp
          have : n = m := by
            apply hinj
            exact cast (congrArg (Eq (xs n)) (id (Eq.symm hm))) h
          rw [this]
          exact h_spec
    }
  have h_xs_inj: Set.InjOn xs c.support.toFinset := by exact Function.Injective.injOn hinj
  have c'_support_spec : c'.support = Finset.image xs c.support.toFinset := by
    have : c'.support = (c.support.image xs).toFinset := by rfl
    rw [this]
    exact Set.toFinset_image xs (Function.support c)
  have c'_spec (n : Fin N) (hn : n ∈ c.support.toFinset) : c n = c' (xs n) := by
    set x := xs n
    have h : ∃ m, xs m = x := by exact exists_apply_eq_apply xs n
    unfold c'
    simp only [Set.toFinset_image, Finsupp.coe_mk]
    simp_rw [h]
    simp only [↓reduceDIte]
    let m_spec := Classical.choose_spec h
    set m := Classical.choose h
    have : n = m := hinj (id (Eq.symm m_spec))
    rw [this]
  calc
    ∑ i, ∑ j, c i * K (xs i) (xs j) * c j = ∑ i, ∑ j ∈ c.support, c i * K (xs i) (xs j) * c j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Eq.symm
      refine Finset.sum_subset (Finset.subset_univ c.support.toFinset) ?_
      rintro j hj hjnc
      simp only [Set.mem_toFinset, Function.mem_support, ne_eq, Decidable.not_not] at hjnc
      rw [hjnc]
      simp
    _ = ∑ i ∈ c.support, ∑ j ∈ c.support, c i * K (xs i) (xs j) * c j := by
      apply Eq.symm
      refine Finset.sum_subset (Finset.subset_univ c.support.toFinset) ?_
      rintro i hi hinc
      simp only [Set.mem_toFinset, Function.mem_support, ne_eq, Decidable.not_not] at hinc
      apply Finset.sum_eq_zero
      intro j hj
      rw [hinc]
      simp
    _ = ∑ i ∈ c.support, ∑ y ∈ c'.support, c i * K (xs i) y * c' y := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [c'_support_spec]
      apply Eq.symm
      rw [Finset.sum_image h_xs_inj (f:= fun y => c i * K (xs i) y * c' y)]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [mul_eq_mul_left_iff, mul_eq_zero]
      left
      exact Eq.symm (c'_spec j hj)
    _ = ∑ x ∈ c'.support, ∑ y ∈ c'.support, (c' x) * (K x y) * (c' y) := by
      apply Eq.symm
      nth_rewrite 1 [c'_support_spec]
      rw [Finset.sum_image h_xs_inj (f:=fun x => ∑ y ∈ c'.support, (c' x) * (K x y) * (c' y))]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro y hy
      simp only [mul_eq_mul_right_iff]
      left; left
      exact Eq.symm (c'_spec i hi)
    _ = ∑ x ∈ c'.support, ∑ y ∈ c'.support, (c' x) * (c' y) * (K x y) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [mul_assoc, mul_comm (K x y), <-mul_assoc]
  exact posSemiDefₓ K c'.support c'

/-- Kernels are equal when they agree pointwise. -/
@[ext]
theorem ext {k1 k2 : Kernel X} (h : ∀ x y, k1.kernel x y = k2.kernel x y) : k1 = k2 := by
  cases k1; cases k2; simp only [mk.injEq]; ext x y; exact h x y

/-- The zero kernel is the map `(x,y) ↦ 0`. -/
def zeroKernel : Kernel X := {
  kernel := fun x y => 0
  symmetric := by intro x y; exact rfl
  posSemiDef := by intro c; simp
}

/-- The zero kernel is the map `(x,y) ↦ 0`. -/
instance : Zero (Kernel X) where
  zero := zeroKernel

@[simp]
theorem zero_kernel_apply (x y : X) : (0 : Kernel X) x y = 0 := rfl

/-- The one kernel is the map `(x,y) ↦ 1`. -/
def oneKernel : Kernel X := {
  kernel := fun x y => 1
  symmetric := by intro x y; exact rfl
  posSemiDef := by
    intro c
    have (x: X) : ∑ y ∈ c.support, c x * c y * 1 = c x * ∑ y ∈ c.support, c y := by
      simp only [mul_one]
      simp_rw [Finset.mul_sum]
    simp_rw [this, mul_comm (b := ∑ x ∈ c.support, c x), <-Finset.mul_sum]
    exact mul_self_nonneg (∑ y ∈ c.support, c y)
}

/-- The one kernel is the map `(x,y) ↦ 1`. -/
instance : One (Kernel X) where
  one := oneKernel

@[simp]
theorem one_kernel_apply (x y : X) : (1 : Kernel X) x y = 1 := rfl

@[simp]
theorem one_ne_zero [Nonempty X] : (1 : Kernel X) ≠ (0 : Kernel X) := by
  intro h
  rw [Kernel.ext_iff] at h
  simp at h

/-- Addition of two kernels `K₁` and `K₂` yields the kernel `(x,y) ↦ K₁(x,y)+K₂(x,y)`. -/
def addKernel (K₁ K₂ : Kernel X) : Kernel X := {
  kernel := fun x y => K₁.kernel x y + K₂.kernel x y
  symmetric := by intro x y; simp_rw [K₁.symmetric, K₂.symmetric]
  posSemiDef := by
    intro c
    simp_rw [mul_add, Finset.sum_add_distrib]
    have h1 := K₁.posSemiDef c
    have h2 := K₂.posSemiDef c
    simp [add_nonneg h1 h2]
}

/-- Addition of two kernels `K₁` and `K₂` yields the kernel `(x,y) ↦ K₁(x,y)+K₂(x,y)`. -/
instance : Add (Kernel X) where
  add := addKernel

@[simp]
theorem add_kernel_apply (K₁ K₂ : Kernel X) (x y : X) :
    (K₁ + K₂).kernel x y = K₁.kernel x y + K₂.kernel x y :=
  rfl

/-- A kernel `K` multiplied by a nonnegative real number `c` yields the kernel
  `(x,y) ↦ c * K(x,y)`. -/
def smulPosKernel (r : ℝ) (hr : r ≥ 0) (K : Kernel X) : Kernel X := {
  kernel := fun x y => r * K x y
  symmetric := by intro x y; simp_rw [K.symmetric]
  posSemiDef := by
    intro c
    have (x : X) : ∑ y ∈ c.support, c x * c y * (r * K x y)
      = r * ∑ y ∈ c.support, c x * c y * K x y := by
      simp_rw [mul_assoc, mul_comm, Finset.mul_sum, <-mul_assoc, mul_comm]
    simp_rw [this, <-Finset.mul_sum]
    have h := K.posSemiDef c
    simp [mul_nonneg hr h]
}

@[simp]
theorem smulPoseKernel_apply (r : ℝ) (hr : r ≥ 0) (K : Kernel X) (x y : X) :
    (smulPosKernel r hr K).kernel x y = r * K x y :=
  rfl

/-- A kernel `K` multiplied by a natural number `n` yields the kernel `(x,y) ↦ n * K(x,y)`. -/
def nsmulKernel (n : ℕ) (K : Kernel X) : Kernel X := smulPosKernel (n:ℝ) (Nat.cast_nonneg' n) K

/-- The kernels inherit the `AddCommMonoid` structure as submodule of the function `X×X→ℝ`. -/
instance : AddCommMonoid (Kernel X) where
  add_assoc := by
    intro K₁ K₂ K₃
    ext x y
    simp only [add_kernel_apply]
    rw [add_assoc]
  zero_add := by
    intro K
    ext x y
    simp
  add_comm := by
    intro K₁ K₂
    ext x y
    rw [add_kernel_apply, add_kernel_apply, AddCommMagma.add_comm]
  add_zero := by
    intro K
    ext x y
    simp
  nsmul := nsmulRec

/-- A kernel `K` with its domain mapped through a function `f:X→Y` yields the kernel
  `(x₁,x₂) ↦ K(f(x₁),f(x₂))`. -/
def pullbackKernel {Y : Type*} [DecidableEq Y] (f : X → Y) (K : Kernel Y) : Kernel X := {
  kernel := fun x₁ x₂ => K (f x₁) (f x₂)
  symmetric := by intro x y; simp_rw [K.symmetric]
  posSemiDef := by
    intro c
    let d := c.mapDomain f
    let a := fun y => ((c.support.filter fun x => f x = y).card : ℝ)
    have ha_spec (y : Y) : a y = ((c.support.filter fun x => f x = y).card : ℝ) := by rfl
    let D : Finset Y := Finset.image f c.support
    have hdsD : d.support ⊆ D := Finsupp.mapDomain_support
    have hd (y : Y) : d y = ∑ x ∈ c.support, if f x = y then c x else 0 := by
      rw [show d = ∑ x ∈ c.support, (fun x ↦ Finsupp.single (f x)) x (c x) from rfl]
      simp_all only [Finsupp.coe_finset_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finsupp.single_apply]
    have hd' (y : Y) : d y = ∑ x ∈ c.support, c x * (if f x = y then 1 else 0) := by
      rw [hd y]
      simp_all
    calc
      ∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * K (f x) (f y)
      =
      ∑ x ∈ c.support, ∑ y ∈ c.support, ∑ u ∈ D, ∑ v ∈ D,
          c x * c y *
          (if f x = u then 1 else 0) *
          (if f y = v then 1 else 0) *
          K u v := by
        apply Finset.sum_congr rfl
        intro x₁ hx₁
        apply Finset.sum_congr rfl
        intro x₂ hx₂
        have hx₁D : f x₁ ∈ D := by
          unfold D
          exact Finset.mem_image_of_mem f hx₁
        have hx₂D : f x₂ ∈ D := by
          unfold D
          exact Finset.mem_image_of_mem f hx₂
        simp [hx₁D, hx₂D]
    _ = ∑ x ∈ c.support, ∑ u ∈ D, ∑ v ∈ D, ∑ y ∈ c.support,
          c x * c y *
          (if f x = u then 1 else 0) *
          (if f y = v then 1 else 0) *
          K u v := by
          apply Finset.sum_congr rfl
          intro x₁ hx₁
          exact Eq.symm Finset.sum_comm_cycle
    _ = ∑ u ∈ D, ∑ v ∈ D, ∑ x ∈ c.support, ∑ y ∈ c.support,
          c x * c y *
          (if f x = u then 1 else 0) *
          (if f y = v then 1 else 0) *
          K u v := by
          exact Eq.symm Finset.sum_comm_cycle
    _ = ∑ u ∈ D, ∑ v ∈ D,
        (∑ x ∈ c.support, c x * (if f x = u then 1 else 0)) *
        (∑ y ∈ c.support, c y * (if f y = v then 1 else 0)) *
          K u v := by
          apply Finset.sum_congr rfl
          intro y₁ hy₁
          apply Finset.sum_congr rfl
          intro y₂ hy₂
          rw [mul_comm (∑ x ∈ c.support, c x * if f x = y₁ then 1 else 0)]
          rw [Finset.mul_sum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x₁ hx₁
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x₂ hx₂
          rw [mul_comm (c x₁), mul_assoc (c x₂), mul_comm (c x₂), mul_assoc _ (c x₂),
            mul_comm (c x₁ * if f x₁ = y₁ then 1 else 0)]
    _ = ∑ u ∈ D, ∑ v ∈ D, d u * d v * K u v := by
      apply Finset.sum_congr rfl
      intro y₁ hy₁
      apply Finset.sum_congr rfl
      intro y₂ hy₂
      rw [hd' y₁]
      rw [hd' y₂]
    _ = ∑ u ∈ d.support, ∑ v ∈ d.support, d u * d v * K u v := by
      rw [Finset.sum_subset (s₁:=d.support) (s₂:=D) (M:=ℝ)]
      · apply Finset.sum_congr rfl
        intro y₁ hy₁
        rw [Finset.sum_subset (s₁:=d.support) (s₂:=D) (M:=ℝ)]
        · exact hdsD
        rintro y₂ hy₂ hy₂nd
        simp_all
      · exact hdsD
      rintro y₁ hy₁ hy₁nd
      simp_all
    _ ≥ 0 := by
      exact K.posSemiDef d
  }

/-- A kernel `K` with its domain restricted from `X` to a subset of `X` is still a kernel. -/
def restrictKernel [DecidableEq X] (S : Set X) (K : Kernel X) : Kernel S :=
  pullbackKernel (Subtype.val : S → X) K

open Matrix
open scoped MatrixOrder

/-- Any kernel `K` can be turned into a matrix given a list `[x₁,...,xₙ]` (so overlap allowed,
  atypical though) by defining the matrix $K_{n,m}=K(x_n,x_m)$. -/
def toMatrix (K : Kernel X) (L : List X) : Matrix (Fin L.length) (Fin L.length) ℝ :=
  Matrix.of fun i j => K (L.get i) (L.get j)

/-- A kernel is positive semi-definite, which mean that the formed kernel matrix is PSD. -/
theorem toMatrix_posSemiDef (K : Kernel X) (L : List X) : Matrix.PosSemidef (K.toMatrix L) := by
  classical
  let N := L.length
  set Kₘ := K.toMatrix L
  constructor
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    rw [show star (Kₘ j i) = K (L.get j) (L.get i) from rfl]
    rw [show Kₘ i j = K (L.get i) (L.get j) from rfl]
    exact K.symmetric (L.get j) (L.get i)
  · intro c_pre
    let K' := pullbackKernel L.get K
    calc
      (c_pre.sum fun i xi ↦ c_pre.sum fun j xj ↦ star xi * Kₘ i j * xj)
        = ∑ i ∈ c_pre.support, ∑ j ∈ c_pre.support, star (c_pre i) * Kₘ i j * c_pre j := by
        rfl
      _ = ∑ i ∈ c_pre.support, ∑ j ∈ c_pre.support, c_pre i * c_pre j * K'.kernel i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [star_trivial, mul_assoc, mul_comm (Kₘ i j), <-mul_assoc]
        simp_all
        rfl
      _ ≥ 0 := by
        exact K'.posSemiDef c_pre

/-- Schur's product: The hadamard product of two PSD matrices is PSD. Should perhaps be part of
  `Matrix.PosDef` or mabye `Matrix.Hadamard`. -/
theorem hadamard_mul {m : Type*} [Finite m] {A : Matrix m m ℝ} {B : Matrix m m ℝ}
  (hA : A.PosSemidef) (hB : B.PosSemidef) : (A.hadamard B).PosSemidef := by
    have := Fintype.ofFinite m
    classical
    constructor
    · apply Matrix.IsHermitian.ext
      intro n₁ n₂
      simp only [hadamard_apply, star_trivial]
      rw [<-Matrix.IsHermitian.apply hA.1 n₁ n₂]
      rw [<-Matrix.IsHermitian.apply hB.1 n₁ n₂]
      simp
    · intro c
      simp only [star_trivial, hadamard_apply]
      set A' := CFC.sqrt A
      have hA := CFC.sqrt_nonneg A
      have hA₁ : A'.IsHermitian := by simpa using hA.1
      set AB' := A' * B * A'.conjTranspose
      calc
        (c.sum fun i xi ↦ c.sum fun j xj ↦ xi * (A i j * B i j) * xj)
          = ∑ i ∈ c.support, ∑ j ∈ c.support, c i * (A i j * B i j) * c j := by rfl
        _ = ∑ i ∈ c.support, ∑ j ∈ c.support, ∑ k, (c i * A' i k) * B i j * (c j * A' j k) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [<-CFC.sqrt_mul_sqrt_self A]
          rw [Matrix.mul_apply (M:=A') (N:=A')]
          simp only [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [
            <-Matrix.IsHermitian.apply hA₁ j k,
            mul_assoc (A' i k), mul_comm (A' k j) (B i j),
            <-mul_assoc, mul_comm (c j) (star (A' k j))
          ]
          simp_rw [mul_assoc, star_trivial]
        _ = ∑ i ∈ c.support, ∑ k, ∑ j ∈ c.support, (c i * A' i k) * B i j * (c j * A' j k) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_comm
        _ = ∑ k, ∑ i ∈ c.support, ∑ j ∈ c.support, (c i * A' i k) * B i j * (c j * A' j k) := by
          exact Finset.sum_comm
        _ ≥ 0 := by
          apply Finset.sum_nonneg
          intro k hk
          let v_k : m →₀ ℝ :=
            { support := c.support.filter fun i => A' i k ≠ 0
              toFun := fun i => c i * A' i k
              mem_support_toFun := by
                intro i
                simp [Finset.mem_filter]
            }
          have h_inner : ∑ i ∈ c.support, ∑ j ∈ c.support, (c i * A' i k) * B i j * (c j * A' j k)
            = ∑ i ∈ v_k.support, ∑ j ∈ v_k.support, star (v_k i) * B i j * v_k j := by
            simp only [star_trivial, v_k, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hki : A' i k = 0
            · simp_rw [hki]
              simp
            simp only [ne_eq, Finsupp.coe_mk, ite_not]
            simp_rw [hki]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hkj : A' j k = 0
            · simp_rw [hkj]
              simp
            simp_rw [hkj]
            simp
          rw [h_inner]
          exact hB.2 v_k

/-- The product of two kernel `K₁` and `K₂` yields the kernel `(x₁,x₂)↦K₁(x₁,x₂)*K₂(x₁,x₂)`. -/
def mulKernel (K₁ K₂ : Kernel X) : Kernel X := {
  kernel := fun x y => K₁.kernel x y * K₂.kernel x y
  symmetric := by intro x y; simp_rw [K₁.symmetric, K₂.symmetric]
  posSemiDef := by
    intro c
    let L := c.support.toList
    set N := L.length
    -- Create relevant matrices
    let A := toMatrix K₁ L
    let B := toMatrix K₂ L
    let AB := A.hadamard B
    -- Show that the relevant matrices are PSD
    have hA : Matrix.PosSemidef A := toMatrix_posSemiDef K₁ L
    have hB : Matrix.PosSemidef B := toMatrix_posSemiDef K₂ L
    have hAB : Matrix.PosSemidef AB := hadamard_mul hA hB
    have hLn (n : Fin N) : L.get n ∈ c.support := Finset.mem_toList.mp (List.get_mem L n)
    let v : Fin N →₀ ℝ := {
      toFun := fun n => c (L.get n)
      support := Finset.univ
      mem_support_toFun := by
        intro n
        simp only [Finset.mem_univ, true_iff]
        exact Finsupp.mem_support_iff.mp (hLn n)
    }
    let e : v.support → c.support := fun n => ⟨L.get n, hLn n⟩
    have hL (n : v.support) : L.get (n : Fin N) = e n := by rfl
    have hC (n : v.support) : c (e n) = v n := by rfl
    have he : Function.Bijective e := by
      constructor
      · intro n₁ n₂ h
        have hnodup : L.Nodup := by simpa [L] using (Finset.nodup_toList c.support)
        have hLget_inj:= List.Nodup.injective_get hnodup
        have h2 : L.get (n₁ : Fin N) = L.get (n₂ : Fin N) := by
          rw [hL, hL]
          apply Subtype.ext_iff.mp h
        exact SetLike.coe_eq_coe.mp (hLget_inj h2)
      · intro x
        have hxL : x.val ∈ L := by
          simp [L]
        have hmem (n : Fin N): n ∈ v.support ↔ L.get n ∈ c.support := by
          rw [v.mem_support_toFun n]
          exact Iff.symm Finsupp.mem_support_iff
        obtain ⟨n, hn⟩ := List.get_of_mem hxL
        refine ⟨⟨⟨n, ?_⟩, ?_⟩, ?_⟩
        · exact n.isLt
        · apply (hmem n).mpr
          exact Finset.mem_def.mpr (hLn n)
        · ext
          simp [e, <-hn]
    calc
      ∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * (K₁ x y * K₂ x y)
          = ∑ x ∈ c.support, ∑ y : c.support, c x * c y * (K₁ x y * K₂ x y) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_subtype]
        intro y
        rfl
      _  = ∑ x : c.support, ∑ y : c.support, c x * c y * (K₁ x y * K₂ x y) := by
        rw [Finset.sum_subtype]
        intro y
        rfl
      _ = ∑ x : c.support, ∑ m : v.support, c x * c (e m) * (K₁ x (e m) * K₂ x (e m)) := by
        apply Fintype.sum_congr
        intro x
        rw [Fintype.sum_bijective e he]
        intro m
        simp
      _ = ∑ n : v.support, ∑ m : v.support, c (e n) * c (e m)
          * (K₁ (e n) (e m) * K₂ (e n) (e m)) := by
        rw [Fintype.sum_bijective e he]
        intro n
        simp
      _ = ∑ n : v.support, ∑ m : v.support, c (e n) * c (e m)
          * (K₁ (L.get n) (L.get m) * K₂ (L.get n) (L.get m)) := by
        apply Fintype.sum_congr
        intro n
        apply Fintype.sum_congr
        intro m
        simp only [List.get_eq_getElem, mul_eq_mul_left_iff, mul_eq_zero]
        left
        rw [←List.get_eq_getElem, <-List.get_eq_getElem]
      _ = ∑ n : v.support, ∑ m : v.support, (v n) * (v m)
          * (K₁ (L.get n) (L.get m) * K₂ (L.get n) (L.get m)) := by
        simp_rw [hC]
      _ = ∑ n : v.support, ∑ m ∈ v.support, (v n) * (v m)
          * (K₁ (L.get n) (L.get m) * K₂ (L.get n) (L.get m)) := by
        apply Fintype.sum_congr
        intro n
        rw [Finset.sum_subtype v.support]
        intro x
        rfl
      _ = ∑ n ∈ v.support, ∑ m ∈ v.support, (v n) * (v m)
          * (K₁ (L.get n) (L.get m) * K₂ (L.get n) (L.get m)) := by
        rw [Finset.sum_subtype v.support]
        intro x
        rfl
      _ = ∑ n ∈ v.support, ∑ m ∈ v.support, star (v n) * (AB n m) * (v m) := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro m hm
        rw [star_trivial, mul_assoc _ (AB n m) _, mul_comm (AB n m) (v m), <-mul_assoc _ _ (AB n m)]
        simp only [List.get_eq_getElem, mul_eq_mul_left_iff, mul_eq_zero]
        left
        rfl
      _ = v.sum fun i xi ↦ v.sum fun j xj ↦ star xi * AB i j * xj := by rfl
      _ ≥ 0 := hAB.2 v
}

/-- The product of two kernel `K₁` and `K₂` yields the kernel `(x₁,x₂)↦K₁(x₁,x₂)*K₂(x₁,x₂)`. -/
instance : Mul (Kernel X) where
  mul := mulKernel

@[simp]
theorem mul_kernel_apply (K₁ K₂ : Kernel X) (x y : X) :
    (K₁ * K₂).kernel x y = K₁.kernel x y * K₂ x y :=
  rfl

/-- The powers of kernels follows by repeated multiplication. -/
def natPowKernel (K : Kernel X) : ℕ → Kernel X
  | 0     => oneKernel
  | n+1   => mulKernel (natPowKernel K n) K

@[simp]
lemma powKernel_zero (K : Kernel X) :
  natPowKernel K 0 = oneKernel := rfl

@[simp]
lemma powKernel_succ (K : Kernel X) (n : ℕ) :
  natPowKernel K (n+1) = (natPowKernel K n) * K := rfl

@[simp]
lemma natPowKernel_apply (K : Kernel X) (N : ℕ) (x y : X) : (natPowKernel K N) x y = (K x y)^N := by
  induction N with
  | zero => rfl
  | succ n h =>
    rw [powKernel_succ]
    rw [mul_kernel_apply]
    rw [h]
    exact Eq.symm (pow_succ _ n)

/-- The powers of kernels follows by repeated multiplication. -/
instance : NatPow (Kernel X) where
  pow := natPowKernel

/-- Any map `φ` mapping `X` to a pre-Hilbert space `F` can define a kernel through the map
  `(x₁,x₂)↦⟪φ(x₁),φ(x₂)`. Essential part of the 'Kernel trick'. -/
def featureKernel {α : Type*} [NormedAddCommGroup α] [InnerProductSpace ℝ α] (φ : X → α) : Kernel X
                                                                                                := {
  kernel := fun x y => inner ℝ (φ x) (φ y)
  symmetric := by intro x y; exact real_inner_comm (φ y) (φ x)
  posSemiDef := by
    intro c
    have : ∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * inner ℝ (φ x) (φ y)
      = inner ℝ (∑ x ∈ c.support, c x • (φ x)) (∑ y ∈ c.support, c y • (φ y)) := by
      simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    rw [this]
    exact real_inner_self_nonneg
}

@[simp]
theorem featureKernel_apply {α : Type*} [NormedAddCommGroup α] [InnerProductSpace ℝ α]
                            (φ : X → α) (x y : X) :
    (featureKernel φ).kernel x y = inner ℝ (φ x) (φ y) :=
  rfl

/-- A kernel `K` scaled on both sides with a function `f:X→ℝ` yields the kernel
  `(x₁,x₂) ↦ f(x₁)k(x₁,x₂)f(x₁)`. -/
noncomputable def scaledKernel (f : X → ℝ) (K : Kernel X) : Kernel X := by
  let K' := featureKernel f
  exact mulKernel K K'

/-- Any polynomial $x↦∑_{n=1}^∞ f_n x^n$ with at most finitely many non-zero coefficients, all
  positive, yields the kernel $(x₁,x₂)↦∑_{n=1}^∞ f_n K(x₁,x₂)^n`. -/
def polyOfKernel (f : ℕ →₀ ℝ) (hf : ∀ (n : ℕ), f n ≥ 0) (K : Kernel X) : Kernel X := {
  kernel := fun x y => ∑ n ∈ f.support, f n * (natPowKernel K n).kernel x y
  symmetric := by
    intro x y
    apply Finset.sum_congr rfl
    intro z hz
    simp [K.symmetric]
  posSemiDef := by
    intro c
    calc
      _ = ∑ x ∈ c.support, ∑ y ∈ c.support, ∑ n ∈ f.support, c x * c y * f n *
                                                                        (K.natPowKernel n) x y := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [mul_assoc (c x * c y)]
      _ = ∑ x ∈ c.support, ∑ n ∈ f.support, ∑ y ∈ c.support, c x * c y * f n *
                                                                        (K.natPowKernel n) x y := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
      _ = ∑ n ∈ f.support, ∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * f n *
                                                                        (K.natPowKernel n) x y := by
        rw [Finset.sum_comm]
      _ ≥ 0 := by
        apply Finset.sum_nonneg
        rintro n hn
        simp_rw [mul_comm (c _ * c _) (f n)]
        have : ∑ x ∈ c.support, ∑ x_1 ∈ c.support, f n * (c x * c x_1) * (K.natPowKernel n) x x_1
          = ∑ x ∈ c.support, f n * ∑ x_1 ∈ c.support, (c x * c x_1) * (K.natPowKernel n) x x_1 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          simp [mul_assoc]
        rw [this]
        have : ∑ x ∈ c.support, f n * ∑ x_1 ∈ c.support, (c x * c x_1) * (K.natPowKernel n) x x_1
          = f n * ∑ x ∈ c.support, ∑ x_1 ∈ c.support, (c x * c x_1) * (K.natPowKernel n) x x_1 := by
          rw [Finset.mul_sum]
        rw [this]
        exact mul_nonneg (hf n) ((K.natPowKernel n).posSemiDef c)
}

@[simp]
theorem polyOfKernel_apply (f : ℕ →₀ ℝ) (hf : ∀ (n : ℕ), f n ≥ 0) (K : Kernel X) (x y : X) :
    (polyOfKernel f hf K) x y = ∑ n ∈ f.support, f n * (natPowKernel K n) x y :=
  rfl

/-- Any kernel `K` satisfies the Cauchy-Schwartz type inequality
  `K(x₁,x₂)^2 ≤ K(x₁,x₁) * K(x₂,x₂)`. -/
theorem sq_le_ker_mul_ker (K : Kernel X) (x y : X) : (K x y)^2 ≤ K x x * K y y := by
  classical
  have hΓ := toMatrix_posSemiDef K [x, y]
  have h_nonneg := Matrix.PosSemidef.det_nonneg hΓ
  set A : Matrix (Fin 2) (Fin 2) ℝ := K.toMatrix [x, y]
  rw [Matrix.det_fin_two] at h_nonneg
  rw [pow_two]
  nth_rw 2 [K.symmetric]
  rw [sub_nonneg] at h_nonneg
  exact h_nonneg

/-- If a kernel `K` satisfies `K(x,x)=0` for some `x∈X`, then `K(x,y)=0` for all `y∈X`. -/
theorem zero_row_iff_zero_diag (K : Kernel X) (x : X) : K x x = 0 → ∀ y, K x y = 0 := by
  classical
  rintro hk y
  have h := sq_le_ker_mul_ker K x y
  rw [hk] at h
  simp only [zero_mul, sq_nonpos_iff] at h
  exact h

/-- For two nonnegative reals `a,b` the inequality `√(a*b) ≤ max(a,b)` holds. Should maybe be part
  of `NNReal`. -/
lemma sqrt_mul_le_max (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : √ (a*b) ≤ max a b := by
  rw [le_max_iff]
  by_cases hab : a ≥ b
  · left
    rw [sqrt_le_left ha]
    rw [pow_two]
    exact PosMulMono.mul_le_mul_of_nonneg_left ha hab
  · right
    rw [sqrt_le_left hb]
    rw [pow_two]
    simp only [ge_iff_le, not_le] at hab
    rw [le_iff_eq_or_lt]
    by_cases hb0 : b=0
    · left
      simp only [mul_eq_mul_right_iff]
      right
      exact hb0
    · right
      have : b>0 := by exact Std.lt_of_le_of_lt ha hab
      exact mul_lt_mul_of_pos_right hab this

/-- For any kernel `K` the estimate `|K(x,y)≤ max(K(x₁,x₁),K(x₂,x₂))` holds for all `x₁,x₂∈ X`. -/
theorem abs_le_max (K : Kernel X) (x y : X) : |K x y| ≤ max (K x x) (K y y) := by
  classical
  apply le_trans
  · exact abs_le_sqrt (sq_le_ker_mul_ker K x y)
  · exact sqrt_mul_le_max (K x x) (K y y) (K.nonneg x) (K.nonneg y)

/-- For any kernel `K` the estimate `2*K(x,y)≤ K(x₁,x₁)+K(x₂,x₂)` holds for all `x₁,x₂∈ X`. -/
theorem le_add (K : Kernel X) (x y : X) : 2 * K x y  ≤ (K x x) + (K y y) := by
  classical
  by_cases hxy : x=y
  · rw [hxy]
    rw [← two_mul (K y y)]
  · let c : X→₀ℝ := Finsupp.single x 1 + Finsupp.single y (-1)
    let hc' := c.support
    have hc : c.support = {x, y} := by
      unfold c
      rw [Finsupp.support_single_add_single hxy (one_ne_zero' ℝ) ?_]
      simp
    have hk := K.posSemiDef c
    rw [hc] at hk
    unfold c at hk
    simp_all only [Finsupp.single_neg, Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply,
      Finset.mem_singleton, not_false_eq_true, Finset.sum_insert, Finsupp.single_eq_same, ne_eq,
      Finsupp.single_eq_of_ne, neg_zero, add_zero, mul_one, Finset.sum_singleton,
      Finsupp.single_eq_of_ne', zero_add, mul_neg, neg_add_rev, neg_neg, one_mul, neg_mul,
      ge_iff_le]
    nth_rw 3 [K.symmetric] at hk
    have : K x x + -K x y + (-K x y + K y y) = K x x + K y y - 2*K x y := by ring
    rw [this] at hk
    nth_rw 1 [← sub_nonneg]
    exact hk

/-- For any kernel `K` the estimate `K(x₁,x₂) ≤ (K(x₁,x₁) + K(x₂,x₂)) / 2` holds for all
  `x₁,x₂∈ X`. -/
theorem le_average (K : Kernel X) (x y : X) : K x y  ≤ ((K x x) + (K y y))/2 := by
  rw [le_div_iff₀' two_pos]
  exact le_add K x y

/-- The only way that for a kernel `K` its negative `-K` is also a kernel is when the kernel is the
  zero kernel. -/
lemma kernel_neg_eq_zero (D E : Kernel X) (h : E.kernel = -D.kernel) : E = 0 := by
  classical
  ext x y
  let δx : X →₀ ℝ := Finsupp.single x 1
  have hDx := D.posSemiDef δx
  have hEx := E.posSemiDef δx
  rw [Finsupp.support_single_ne_zero x (one_ne_zero' ℝ)] at hDx
  rw [Finsupp.support_single_ne_zero x (one_ne_zero' ℝ)] at hEx
  simp only [Finset.sum_singleton, ge_iff_le] at hDx
  simp only [Finset.sum_singleton, ge_iff_le] at hEx
  rw [Finsupp.single_eq_same] at hDx
  rw [Finsupp.single_eq_same, h] at hEx
  simp only [mul_one, one_mul] at hDx
  simp only [mul_one, Pi.neg_apply, mul_neg, one_mul, Left.nonneg_neg_iff] at hEx
  have hDx0 : D.kernel x x = 0 := by
    exact le_antisymm hEx hDx
  have hEx0 : E.kernel x x = 0 := by
    simp_all
  let δy : X →₀ ℝ := Finsupp.single y 1
  have hDy := D.posSemiDef δy
  have hEy := E.posSemiDef δy
  rw [Finsupp.support_single_ne_zero y (one_ne_zero' ℝ)] at hDy
  rw [Finsupp.support_single_ne_zero y (one_ne_zero' ℝ)] at hEy
  simp only [Finset.sum_singleton, ge_iff_le] at hDy
  simp only [Finset.sum_singleton, ge_iff_le] at hEy
  rw [Finsupp.single_eq_same] at hDy
  rw [Finsupp.single_eq_same, h] at hEy
  simp only [mul_one, one_mul] at hDy
  simp only [mul_one, Pi.neg_apply, mul_neg, one_mul, Left.nonneg_neg_iff] at hEy
  have hDy0 : D.kernel y y = 0 := by
    exact le_antisymm hEy hDy
  have hEy0 : E.kernel y y = 0 := by
    simp_all
  rw [show kernel 0 x y = 0 from rfl]
  apply le_antisymm
  · have hExy_bound : (E.kernel x y)^2 ≤ E.kernel x x * E.kernel y y := by
      exact sq_le_ker_mul_ker E x y
    rw [hEx0, hEy0] at hExy_bound
    simp_all
  · rw [h]
    simp only [Pi.neg_apply, Left.nonneg_neg_iff]
    have hDxy_bound : (D.kernel x y)^2 ≤ D.kernel x x * D.kernel y y := by
      exact sq_le_ker_mul_ker D x y
    rw [hDx0, hDy0] at hDxy_bound
    simp_all

/-- A kernels have a partial order when `K₁ ≤ K₂` holds when `K₂-K₁` exists as a kernel, where
  `K:=K₂-K₁` refers to the function such that `K₂=K₁+K`. -/
instance : PartialOrder (Kernel X) where
  le := fun K₁ K₂ => ∃ (K : Kernel X), K₂ = K₁ + K
  le_refl := by
    intro K
    use 0
    simp
  le_trans := by
    rintro K₁ K₂ K₃ hD₁₂ hD₂₃
    let hK₁₂ := Classical.choose_spec hD₁₂
    let hK₂₃ := Classical.choose_spec hD₂₃
    set K₁₂ := Classical.choose hD₁₂
    set K₂₃ := Classical.choose hD₂₃
    use K₁₂ + K₂₃
    rw [hK₂₃, hK₁₂, add_assoc]
  le_antisymm := by
    rintro K₁ K₂ hD₁₂ hD₂₁
    let hK₁₂ := Classical.choose_spec hD₁₂
    let hK₂₁ := Classical.choose_spec hD₂₁
    set K₁₂ := Classical.choose hD₁₂
    set K₂₁ := Classical.choose hD₂₁
    rw [hK₂₁] at hK₁₂
    rw [Kernel.ext_iff] at hK₁₂
    have : K₂₁.kernel = - K₁₂.kernel := by
      ext x y
      rw [show (-K₁₂.kernel) x y = -K₁₂.kernel x y from rfl]
      rw [eq_neg_iff_add_eq_zero]
      rw [<-sub_self (K₂ x y)]
      rw [eq_sub_iff_add_eq]
      rw [add_comm, <-add_assoc]
      exact Eq.symm (hK₁₂ x y)
    have : K₂₁ = 0 := by exact kernel_neg_eq_zero K₁₂ K₂₁ this
    rw [this] at hK₂₁
    simp only [add_zero] at hK₂₁
    exact hK₂₁

/-- The kernels inherit the `Semiring` structure as submodule of the function `X×X→ℝ`. -/
instance : Semiring (Kernel X) where
  left_distrib := by
    intro K₁ K₂ K₃
    ext x y
    simp only [mul_kernel_apply, add_kernel_apply]
    rw [left_distrib]
  right_distrib := by
    intro K₁ K₂ K₃
    ext x y
    simp only [mul_kernel_apply, add_kernel_apply]
    rw [right_distrib]
  zero_mul := by
    intro K
    ext x y
    simp
  mul_zero := by
    intro K
    ext x y
    simp
  mul_assoc := by
    intro K₁ K₂ K₃
    ext x y
    simp only [mul_kernel_apply]
    rw [mul_assoc]
  one_mul := by
    intro K
    ext x y
    simp
  mul_one := by
    intro K
    ext x y
    simp

/-- The kernels have an `IsOrderedRing` structure since it has a as `Semiring` and `PartialOrder`
  structure, and the remaining requirements carry over from being a submodule of the functions
  `X×X→ℝ`. -/
instance : IsOrderedRing (Kernel X) where
  add_le_add_left := by
    rintro K₁ K₂ hK K₃
    have hKdiff := Classical.choose_spec hK
    set Kdiff := Classical.choose hK
    use Kdiff
    rw [hKdiff]
    exact add_right_comm K₁ Kdiff K₃
  zero_le_one := by
    use oneKernel
    simp
    rfl
  mul_le_mul_of_nonneg_left := by
    rintro K₁ hK₁ K₂ K₃ hK₂₃
    have hKdiff := Classical.choose_spec hK₂₃
    set Kdiff := Classical.choose hK₂₃
    use K₁*Kdiff
    rw [hKdiff]
    rw [left_distrib]
  mul_le_mul_of_nonneg_right := by
    rintro K₁ hK₁ K₂ K₃ hK₂₃
    have hKdiff := Classical.choose_spec hK₂₃
    set Kdiff := Classical.choose hK₂₃
    use Kdiff*K₁
    rw [hKdiff]
    rw [right_distrib]

theorem zero_le (K : Kernel X) : 0 ≤ K := ⟨K, by simp⟩

/-- Any pointwise limit of kernels is again a kernel. -/
def pointwiseLimitKernel (Kseq : ℕ → Kernel X) (K : X → X → ℝ) (h_conv : ∀ x y, Filter.Tendsto
                                (fun n => (Kseq n) x y) Filter.atTop (nhds (K x y))) : Kernel X := {
    kernel := K
    symmetric := by
      intro x y
      have L := h_conv x y
      have R := h_conv y x
      have hsym : (fun n => (Kseq n) x y) = (fun n => (Kseq n) y x) := by
        funext n
        exact (Kseq n).symmetric x y
      rw [hsym] at L
      exact tendsto_nhds_unique L R
    posSemiDef := by
      intro c
      let S : ℕ → ℝ := fun n => ∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * (Kseq n) x y
      have h_nonneg : ∀ n, 0 ≤ S n := by
        intro n
        exact (Kseq n).posSemiDef c
      have h_tendsto : Filter.Tendsto S Filter.atTop
                                  (nhds (∑ x ∈ c.support, ∑ y ∈ c.support, c x * c y * K x y)) := by
        apply tendsto_finset_sum c.support
        intro x hx
        apply tendsto_finset_sum c.support
        intro y hy
        exact Filter.Tendsto.const_mul ((c x) * (c y)) (h_conv x y)
      exact ge_of_tendsto h_tendsto (Filter.Eventually.of_forall h_nonneg)
  }

/-- Any finite sum of kernels is again a kernel. -/
def finsetSumKernel {α : Type*} (s : Finset α) (K : α → Kernel X) : Kernel X := ∑ i ∈ s, K i

@[simp]
theorem finsetSumKernel_apply {α : Type*} (s : Finset α) (K : α → Kernel X) (x y : X) :
    (finsetSumKernel s K) x y = ∑ i ∈ s, (K i) x y := by
  classical
  rw [show finsetSumKernel s K = ∑ i ∈ s, K i from rfl]
  induction s using Finset.induction with
    | empty => simp [zero_kernel_apply]
    | insert i s hi ih =>
      rw [← Finset.union_singleton i s]
      rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr hi)]
      rw [Finset.sum_union (Finset.disjoint_singleton_right.mpr hi)]
      rw [add_kernel_apply]
      rw [ih]
      simp

/-- Any power series $x↦∑_{n=1}^∞ f_n x^n$ with nonnegative coefficients yields the kernel
  $(x₁,x₂)↦∑_{n=1}^∞ f_n K(x₁,x₂)^n`. -/
noncomputable def posPowerSeriesKernel (p : PowerSeries ℝ) (hp₁ : ∀ n, 0 ≤ PowerSeries.coeff n p)
    (hp₂ : ∀ x : ℝ, Summable (fun n => PowerSeries.coeff n p * x ^ n)) (K : Kernel X) : Kernel X :=
  let Kseq : ℕ → Kernel X := fun N => finsetSumKernel (Finset.range N)
    (fun n => smulPosKernel (PowerSeries.coeff n p) (hp₁ n) (natPowKernel K n))
  let Klim (x y : X) : ℝ := ∑' n, (PowerSeries.coeff n p) * (K x y) ^ n
  pointwiseLimitKernel Kseq Klim (by
    intro x y
    unfold Kseq Klim
    simp only [finsetSumKernel_apply, smulPoseKernel_apply, natPowKernel_apply]
    apply HasSum.tendsto_sum_nat
    exact (hp₂ (K x y)).hasSum
  )

@[simp]
theorem posPowerSeriesKernel_apply (p : PowerSeries ℝ) (hp₁ : ∀ n, 0 ≤ PowerSeries.coeff n p)
  (hp₂ : ∀ x : ℝ, Summable (fun n => PowerSeries.coeff n p * x ^ n)) (K : Kernel X) (x y : X) :
  (posPowerSeriesKernel p hp₁ hp₂ K) x y = ∑' n, (PowerSeries.coeff n p) * (K x y) ^ n := rfl

/-- The exponent of a kernel is again a kernel. Follows `exp` having a power series with nonnegative
  coefficients. -/
noncomputable def expKernel (K : Kernel X) : Kernel X :=
  posPowerSeriesKernel (PowerSeries.exp ℝ)
    (fun n => by
      rw [PowerSeries.coeff_exp]
      rw [eq_ratCast]
      rw [Rat.cast_nonneg]
      exact Nat.one_div_cast_nonneg n.factorial
    )
    (fun x => by
      simp_rw [PowerSeries.coeff_exp]
      let hExp_sum := NormedSpace.expSeries_div_hasSum_exp (𝔸:=ℝ) x
      nth_rw
        1 [show
          (Summable fun n ↦ (algebraMap ℚ ℝ) (1 / ↑n.factorial) * x ^ n) =
            ∃ a, HasSum (fun n ↦ (algebraMap ℚ ℝ) (1 / ↑n.factorial) * x ^ n) a
          from rfl]
      simp_rw [eq_ratCast, Rat.cast_div, Rat.cast_one, Rat.cast_natCast, mul_comm]
      simp only [one_div]
      let L := NormedSpace.exp (𝔸:=ℝ) x
      use L
      exact hExp_sum
    )
    K

/-- Definition of the univariate Gaussian kernel `(x₁,x₂)↦exp(-γ*‖x₁-x₂‖^2)`. Proven using the
  decomposition `exp(-γ*‖x-y ‖^2)=exp(-γ‖x‖^2) exp(2γ⟪x,y⟫) exp(-γ‖y‖^2)`, where `exp(2γ⟪x,y⟫)`
  is shown to be a kernel using a pointwise limit. -/
noncomputable def gaussianKernel [NormedAddCommGroup X] [InnerProductSpace ℝ X] (γ : ℝ) (hγ : γ > 0)
                                                                                       : Kernel X :=
  let φ : X→X := fun x => x
  let ψ : X→ ℝ := fun x => exp (-γ * ‖x‖^2)
  let Kseq : ℕ → Kernel X := fun N =>
    let f: ℕ →₀ ℝ := {
      toFun := fun n => if n < N then (2*γ) ^ n / Nat.factorial n else 0
      support := Finset.range N
      mem_support_toFun := by
        intro n
        rw [ite_ne_right_iff]
        rw [div_ne_zero_iff]
        rw [Finset.mem_range]
        rw [iff_self_and]
        rintro hn
        constructor
        · ring_nf
          rw [mul_ne_zero_iff_left ?_]
          · exact Ne.symm (NeZero.ne' (2 ^ n))
          exact Ne.symm (ne_of_lt (pow_pos hγ n))
        · rw [← abs_pos]
          rw [Nat.abs_cast n.factorial]
          rw [Nat.cast_pos]
          exact Nat.factorial_pos n
    }
    have hf : ∀ n, f n ≥ 0 := by
      intro n
      rw [show f n = if n < N then (2*γ) ^ n / ↑n.factorial else 0 from rfl]
      by_cases hn : n<N
      · rw [if_pos hn]
        rw [show ((2*γ) ^ n / ↑n.factorial ≥ 0) = (0 ≤ (2*γ) ^ n / ↑n.factorial) from rfl]
        rw [le_div_iff₀' ?_]
        · ring_nf
          simp only [Nat.ofNat_pos, pow_pos, mul_nonneg_iff_of_pos_right]
          exact Std.le_of_lt (pow_pos hγ n)
        rw [Nat.cast_pos]
        exact Nat.factorial_pos n
      · rw [if_neg hn]
    polyOfKernel f hf (featureKernel φ)
  let Klim : X → X → ℝ := fun x y => exp (2*γ * inner ℝ x y)
  scaledKernel ψ (pointwiseLimitKernel Kseq Klim (by
    intro x y
    unfold Klim
    let hExp_sum := NormedSpace.expSeries_div_hasSum_exp (𝔸:=ℝ) (2 * γ * inner ℝ x y)
    rw [<-Real.exp_eq_exp_ℝ] at hExp_sum
    have hKseq_spec : ∀ N, (Kseq N) x y = ∑ n ∈ Finset.range N, (2 * γ * inner ℝ x y) ^ n
                                                                                / ↑n.factorial := by
      intro N
      rw [show
          (Kseq N) x y = ∑ n ∈ Finset.range N, (fun n ↦ if n < N then (2*γ) ^ n / ↑n.factorial else
                                                      0) n * ((featureKernel φ).natPowKernel n) x y
          from rfl]
      apply Finset.sum_congr rfl
      intro n hn
      simp_all only [Finset.mem_range, ↓reduceIte, natPowKernel_apply]
      unfold φ
      rw [show (featureKernel fun x ↦ x) x y = inner ℝ ((fun x ↦ x) x) ((fun x ↦ x) y) from
          rfl]
      simp only
      ring
    let hExp_tendsto := HasSum.tendsto_sum_nat hExp_sum
    simp_all
  ))

@[simp]
theorem gaussianKernel_apply [NormedAddCommGroup X] [InnerProductSpace ℝ X] (γ : ℝ) (hγ : γ > 0)
                             (x y : X) : (gaussianKernel γ hγ) x y = exp (-γ * ‖x-y‖^2 ) := by
  rw [show (gaussianKernel γ hγ).kernel =
    fun x y ↦ rexp (2 * γ * inner ℝ x y) * (featureKernel fun x ↦ rexp (-γ * ‖x‖ ^ 2)) x y from rfl]
  simp only [neg_mul, featureKernel_apply, RCLike.inner_apply, ringHom_apply]
  rw [<- exp_add, <-exp_add]
  simp only [exp_eq_exp]
  rw [norm_sub_sq_real x y]
  ring_nf

end Kernel
