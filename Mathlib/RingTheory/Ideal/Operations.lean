/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fintype.Lattice
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic

/-!
# More operations on modules and ideals
-/

assert_not_exists Module.Basis -- See `RingTheory.Ideal.Basis`
  Submodule.hasQuotient -- See `RingTheory.Ideal.Quotient.Operations`

universe u v w x

open Pointwise

namespace Submodule

lemma coe_span_smul {R' M' : Type*} [CommSemiring R'] [AddCommMonoid M'] [Module R' M']
    (s : Set R') (N : Submodule R' M') :
    (Ideal.span s : Set R') • N = s • N :=
  set_smul_eq_of_le _ _ _
    (by rintro r n hr hn
        induction hr using Submodule.span_induction with
        | mem _ h => exact mem_set_smul_of_mem_mem h hn
        | zero => rw [zero_smul]; exact Submodule.zero_mem _
        | add _ _ _ _ ihr ihs => rw [add_smul]; exact Submodule.add_mem _ ihr ihs
        | smul _ _ hr =>
          rw [mem_span_set] at hr
          obtain ⟨c, hc, rfl⟩ := hr
          rw [Finsupp.sum, Finset.smul_sum, Finset.sum_smul]
          refine Submodule.sum_mem _ fun i hi => ?_
          rw [← mul_smul, smul_eq_mul, mul_comm, mul_smul]
          exact mem_set_smul_of_mem_mem (hc hi) <| Submodule.smul_mem _ _ hn) <|
    set_smul_mono_left _ Submodule.subset_span

lemma span_singleton_toAddSubgroup_eq_zmultiples (a : ℤ) :
    (span ℤ {a}).toAddSubgroup = AddSubgroup.zmultiples a := by
  ext i
  simp [Ideal.mem_span_singleton', AddSubgroup.mem_zmultiples_iff]

@[simp] lemma _root_.Ideal.span_singleton_toAddSubgroup_eq_zmultiples (a : ℤ) :
    (Ideal.span {a}).toAddSubgroup = AddSubgroup.zmultiples a :=
  Submodule.span_singleton_toAddSubgroup_eq_zmultiples _

variable {R : Type u} {M : Type v} {M' F G : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- This duplicates the global `smul_eq_mul`, but doesn't have to unfold anywhere near as much to
apply. -/
protected theorem _root_.Ideal.smul_eq_mul (I J : Ideal R) : I • J = I * J :=
  rfl

variable {I J : Ideal R} {N : Submodule R M}

theorem smul_le_right : I • N ≤ N :=
  smul_le.2 fun r _ _ ↦ N.smul_mem r

theorem map_le_smul_top (I : Ideal R) (f : R →ₗ[R] M) :
    Submodule.map f I ≤ I • (⊤ : Submodule R M) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← mul_one y, ← smul_eq_mul, f.map_smul]
  exact smul_mem_smul hy mem_top

variable (I J N)

@[simp]
theorem top_smul : (⊤ : Ideal R) • N = N :=
  le_antisymm smul_le_right fun r hri => one_smul R r ▸ smul_mem_smul mem_top hri

protected theorem mul_smul : (I * J) • N = I • J • N :=
  Submodule.smul_assoc _ _ _

theorem mem_of_span_top_of_smul_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M)
    (H : ∀ r : s, (r : R) • x ∈ M') : x ∈ M' := by
  suffices LinearMap.range (LinearMap.toSpanSingleton R M x) ≤ M' by
    rw [← LinearMap.toSpanSingleton_one R M x]
    exact this (LinearMap.mem_range_self _ 1)
  rw [LinearMap.range_eq_map, ← hs, map_le_iff_le_comap, Ideal.span, span_le]
  exact fun r hr ↦ H ⟨r, hr⟩

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

@[simp]
theorem map_smul'' (f : M →ₗ[R] M') : (I • N).map f = I • N.map f :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      smul_le.2 fun r hr n hn =>
        show f (r • n) ∈ I • N.map f from
          (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) <|
    smul_le.2 fun r hr _ hn =>
      let ⟨p, hp, hfp⟩ := mem_map.1 hn
      hfp ▸ f.map_smul r p ▸ mem_map_of_mem (smul_mem_smul hr hp)

theorem mem_smul_top_iff (N : Submodule R M) (x : N) :
    x ∈ I • (⊤ : Submodule R N) ↔ (x : M) ∈ I • N := by
  have : Submodule.map N.subtype (I • ⊤) = I • N := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  simp [← this, -map_smul'']

@[simp]
theorem smul_comap_le_comap_smul (f : M →ₗ[R] M') (S : Submodule R M') (I : Ideal R) :
    I • S.comap f ≤ (I • S).comap f := by
  refine Submodule.smul_le.mpr fun r hr x hx => ?_
  rw [Submodule.mem_comap] at hx ⊢
  rw [f.map_smul]
  exact Submodule.smul_mem_smul hr hx

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

open Pointwise

theorem mem_smul_span_singleton {I : Ideal R} {m : M} {x : M} :
    x ∈ I • span R ({m} : Set M) ↔ ∃ y ∈ I, y • m = x :=
  ⟨fun hx =>
    smul_induction_on hx
      (fun r hri _ hnm =>
        let ⟨s, hs⟩ := mem_span_singleton.1 hnm
        ⟨r * s, I.mul_mem_right _ hri, hs ▸ mul_smul r s m⟩)
      fun m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩ =>
      ⟨y1 + y2, I.add_mem hyi1 hyi2, by rw [add_smul, hy1, hy2]⟩,
    fun ⟨_, hyi, hy⟩ => hy ▸ smul_mem_smul hyi (subset_span <| Set.mem_singleton m)⟩

variable {I J : Ideal R} {N P : Submodule R M}
variable (S : Set R) (T : Set M)

theorem smul_eq_map₂ : I • N = Submodule.map₂ (LinearMap.lsmul R M) I N :=
  le_antisymm (smul_le.mpr fun _m hm _n ↦ Submodule.apply_mem_map₂ _ hm)
    (map₂_le.mpr fun _m hm _n ↦ smul_mem_smul hm)

theorem span_smul_span : Ideal.span S • span R T = span R (⋃ (s ∈ S) (t ∈ T), {s • t}) := by
  rw [smul_eq_map₂]
  exact (map₂_span_span _ _ _ _).trans <| congr_arg _ <| Set.image2_eq_iUnion _ _ _

theorem ideal_span_singleton_smul (r : R) (N : Submodule R M) :
    (Ideal.span {r} : Ideal R) • N = r • N := by
  have : span R (⋃ (t : M) (_ : t ∈ N), {r • t}) = r • N := by
    convert span_eq (r • N)
    exact (Set.image_eq_iUnion _ (N : Set M)).symm
  conv_lhs => rw [← span_eq N, span_smul_span]
  simpa

/-- Given `s`, a generating set of `R`, to check that an `x : M` falls in a
submodule `M'` of `x`, we only need to show that `r ^ n • x ∈ M'` for some `n` for each `r : s`. -/
theorem mem_of_span_eq_top_of_smul_pow_mem (M' : Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤)
    (x : M) (H : ∀ r : s, ∃ n : ℕ, ((r : R) ^ n : R) • x ∈ M') : x ∈ M' := by
  choose f hf using H
  apply M'.mem_of_span_top_of_smul_mem _ (Ideal.span_range_pow_eq_top s hs f)
  rintro ⟨_, r, hr, rfl⟩
  exact hf r

open Pointwise in
@[simp]
theorem map_pointwise_smul (r : R) (N : Submodule R M) (f : M →ₗ[R] M') :
    (r • N).map f = r • N.map f := by
  simp_rw [← ideal_span_singleton_smul, map_smul'']

theorem mem_smul_span {s : Set M} {x : M} :
    x ∈ I • Submodule.span R s ↔ x ∈ Submodule.span R (⋃ (a ∈ I) (b ∈ s), ({a • b} : Set M)) := by
  rw [← I.span_eq, Submodule.span_smul_span, I.span_eq]
  simp

variable (I)

/-- If `x` is an `I`-multiple of the submodule spanned by `f '' s`,
then we can write `x` as an `I`-linear combination of the elements of `f '' s`. -/
theorem mem_ideal_smul_span_iff_exists_sum {ι : Type*} (f : ι → M) (x : M) :
    x ∈ I • span R (Set.range f) ↔
      ∃ (a : ι →₀ R) (_ : ∀ i, a i ∈ I), (a.sum fun i c => c • f i) = x := by
  constructor; swap
  · rintro ⟨a, ha, rfl⟩
    exact Submodule.sum_mem _ fun c _ => smul_mem_smul (ha c) <| subset_span <| Set.mem_range_self _
  refine fun hx => span_induction ?_ ?_ ?_ ?_ (mem_smul_span.mp hx)
  · simp only [Set.mem_iUnion, Set.mem_range, Set.mem_singleton_iff]
    rintro x ⟨y, hy, x, ⟨i, rfl⟩, rfl⟩
    refine ⟨Finsupp.single i y, fun j => ?_, ?_⟩
    · letI := Classical.decEq ι
      rw [Finsupp.single_apply]
      split_ifs
      · assumption
      · exact I.zero_mem
    refine @Finsupp.sum_single_index ι R M _ _ i _ (fun i y => y • f i) ?_
    simp
  · exact ⟨0, fun _ => I.zero_mem, Finsupp.sum_zero_index⟩
  · rintro x y - - ⟨ax, hax, rfl⟩ ⟨ay, hay, rfl⟩
    refine ⟨ax + ay, fun i => I.add_mem (hax i) (hay i), Finsupp.sum_add_index' ?_ ?_⟩ <;>
      intros <;> simp only [zero_smul, add_smul]
  · rintro c x - ⟨a, ha, rfl⟩
    refine ⟨c • a, fun i => I.mul_mem_left c (ha i), ?_⟩
    rw [Finsupp.sum_smul_index, Finsupp.smul_sum] <;> intros <;> simp only [zero_smul, mul_smul]

theorem mem_ideal_smul_span_iff_exists_sum' {ι : Type*} (s : Set ι) (f : ι → M) (x : M) :
    x ∈ I • span R (f '' s) ↔
    ∃ (a : s →₀ R) (_ : ∀ i, a i ∈ I), (a.sum fun i c => c • f i) = x := by
  rw [← Submodule.mem_ideal_smul_span_iff_exists_sum, ← Set.image_eq_range]

end CommSemiring

end Submodule

namespace Ideal

section Add

variable {R : Type u} [Semiring R]

@[simp]
theorem add_eq_sup {I J : Ideal R} : I + J = I ⊔ J :=
  rfl

@[simp]
theorem zero_eq_bot : (0 : Ideal R) = ⊥ :=
  rfl

@[simp]
theorem sum_eq_sup {ι : Type*} (s : Finset ι) (f : ι → Ideal R) : s.sum f = s.sup f :=
  rfl

end Add

section Semiring

variable {R : Type u} [Semiring R] {I J K L : Ideal R}

@[simp, grind =]
theorem one_eq_top : (1 : Ideal R) = ⊤ := by
  rw [Submodule.one_eq_span, ← Ideal.span, Ideal.span_singleton_one]

theorem add_eq_one_iff : I + J = 1 ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = 1 := by
  rw [one_eq_top, eq_top_iff_one, add_eq_sup, Submodule.mem_sup]

theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=
  Submodule.smul_mem_smul hr hs

theorem bot_pow {n : ℕ} (hn : n ≠ 0) :
    (⊥ : Ideal R) ^ n = ⊥ := Submodule.bot_pow hn

theorem pow_mem_pow {x : R} (hx : x ∈ I) (n : ℕ) : x ^ n ∈ I ^ n :=
  Submodule.pow_mem_pow _ hx _

theorem mul_le : I * J ≤ K ↔ ∀ r ∈ I, ∀ s ∈ J, r * s ∈ K :=
  Submodule.smul_le

theorem mul_le_left : I * J ≤ J :=
  mul_le.2 fun _ _ _ => J.mul_mem_left _

@[simp]
theorem sup_mul_left_self : I ⊔ J * I = I :=
  sup_eq_left.2 mul_le_left

@[simp]
theorem mul_left_self_sup : J * I ⊔ I = I :=
  sup_eq_right.2 mul_le_left

theorem mul_le_right [I.IsTwoSided] : I * J ≤ I :=
  mul_le.2 fun _ hr _ _ ↦ I.mul_mem_right _ hr

@[simp]
theorem sup_mul_right_self [I.IsTwoSided] : I ⊔ I * J = I :=
  sup_eq_left.2 mul_le_right

@[simp]
theorem mul_right_self_sup [I.IsTwoSided] : I * J ⊔ I = I :=
  sup_eq_right.2 mul_le_right

protected theorem mul_assoc : I * J * K = I * (J * K) :=
  Submodule.smul_assoc I J K

variable (I)

theorem mul_bot : I * ⊥ = ⊥ := by simp

theorem bot_mul : ⊥ * I = ⊥ := by simp

@[simp]
theorem top_mul : ⊤ * I = I :=
  Submodule.top_smul I

variable {I}

theorem mul_mono (hik : I ≤ K) (hjl : J ≤ L) : I * J ≤ K * L :=
  Submodule.smul_mono hik hjl

theorem mul_mono_left (h : I ≤ J) : I * K ≤ J * K :=
  Submodule.smul_mono_left h

theorem mul_mono_right (h : J ≤ K) : I * J ≤ I * K :=
  smul_mono_right I h

variable (I J K)

theorem mul_sup : I * (J ⊔ K) = I * J ⊔ I * K :=
  Submodule.smul_sup I J K

theorem sup_mul : (I ⊔ J) * K = I * K ⊔ J * K :=
  Submodule.sup_smul I J K

theorem mul_iSup {ι : Sort*} (J : ι → Ideal R) :
    I * (⨆ i, J i) = ⨆ i, I * J i :=
  Submodule.smul_iSup

theorem iSup_mul {ι : Sort*} (J : ι → Ideal R) (I : Ideal R) :
    (⨆ i, J i) * I = ⨆ i, J i * I :=
  Submodule.iSup_smul

variable {I J K}

theorem pow_le_pow_right {m n : ℕ} (h : m ≤ n) : I ^ n ≤ I ^ m := by
  obtain _ | m := m
  · rw [Submodule.pow_zero, one_eq_top]; exact le_top
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, Submodule.pow_add _ m.add_one_ne_zero]
  exact mul_le_left

theorem pow_le_self {n : ℕ} (hn : n ≠ 0) : I ^ n ≤ I :=
  calc
    I ^ n ≤ I ^ 1 := pow_le_pow_right (Nat.pos_of_ne_zero hn)
    _ = I := Submodule.pow_one _

theorem pow_right_mono (e : I ≤ J) (n : ℕ) : I ^ n ≤ J ^ n := by
  induction n with
  | zero => rw [Submodule.pow_zero, Submodule.pow_zero]
  | succ _ hn =>
    rw [Submodule.pow_succ, Submodule.pow_succ]
    exact Ideal.mul_mono hn e

namespace IsTwoSided

instance (priority := low) [J.IsTwoSided] : (I * J).IsTwoSided :=
  ⟨fun b ha ↦ Submodule.mul_induction_on ha
    (fun i hi j hj ↦ by rw [mul_assoc]; exact mul_mem_mul hi (mul_mem_right _ _ hj))
    fun x y hx hy ↦ by rw [right_distrib]; exact add_mem hx hy⟩

variable [I.IsTwoSided] (m n : ℕ)

instance (priority := low) : (I ^ n).IsTwoSided :=
  n.rec
    (by rw [Submodule.pow_zero, one_eq_top]; infer_instance)
    (fun _ _ ↦ by rw [Submodule.pow_succ]; infer_instance)

protected theorem mul_one : I * 1 = I :=
  mul_le_right.antisymm
    fun i hi ↦ mul_one i ▸ mul_mem_mul hi (one_eq_top (R := R) ▸ Submodule.mem_top)

protected theorem pow_add : I ^ (m + n) = I ^ m * I ^ n := by
  obtain rfl | h := eq_or_ne n 0
  · rw [add_zero, Submodule.pow_zero, IsTwoSided.mul_one]
  · exact Submodule.pow_add _ h

protected theorem pow_succ : I ^ (n + 1) = I * I ^ n := by
  rw [add_comm, IsTwoSided.pow_add, Submodule.pow_one]

end IsTwoSided

@[simp]
theorem mul_eq_bot [NoZeroDivisors R] : I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ :=
  ⟨fun hij =>
    or_iff_not_imp_left.mpr fun I_ne_bot =>
      J.eq_bot_iff.mpr fun j hj =>
        let ⟨i, hi, ne0⟩ := I.ne_bot_iff.mp I_ne_bot
        Or.resolve_left (mul_eq_zero.mp ((I * J).eq_bot_iff.mp hij _ (mul_mem_mul hi hj))) ne0,
    fun h => by obtain rfl | rfl := h; exacts [bot_mul _, mul_bot _]⟩

instance [NoZeroDivisors R] : NoZeroDivisors (Ideal R) where
  eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_bot.1

instance {S A : Type*} [Semiring S] [SMul R S] [AddCommMonoid A] [Module R A] [Module S A]
    [IsScalarTower R S A] [NoZeroSMulDivisors R A] {I : Submodule S A} : NoZeroSMulDivisors R I :=
  Submodule.noZeroSMulDivisors (Submodule.restrictScalars R I)

theorem pow_eq_zero_of_mem {I : Ideal R} {n m : ℕ} (hnI : I ^ n = 0) (hmn : n ≤ m) {x : R}
    (hx : x ∈ I) : x ^ m = 0 := by
  simpa [hnI] using pow_le_pow_right hmn <| pow_mem_pow hx m

end Semiring

section MulAndRadical

variable {R : Type u} {ι : Type*} [CommSemiring R]
variable {I J K L : Ideal R}

theorem mul_mem_mul_rev {r s} (hr : r ∈ I) (hs : s ∈ J) : s * r ∈ I * J :=
  mul_comm r s ▸ mul_mem_mul hr hs

theorem prod_mem_prod {ι : Type*} {s : Finset ι} {I : ι → Ideal R} {x : ι → R} :
    (∀ i ∈ s, x i ∈ I i) → (∏ i ∈ s, x i) ∈ ∏ i ∈ s, I i := by
  classical
    refine Finset.induction_on s ?_ ?_
    · grind [Submodule.mem_top]
    · grind [mul_mem_mul]

lemma sup_pow_add_le_pow_sup_pow {n m : ℕ} : (I ⊔ J) ^ (n + m) ≤ I ^ n ⊔ J ^ m := by
  rw [← Ideal.add_eq_sup, ← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n ≤ i
  · exact (Ideal.mul_le_right.trans (Ideal.mul_le_right.trans
      ((Ideal.pow_le_pow_right hn).trans le_sup_left)))
  · refine (Ideal.mul_le_right.trans (Ideal.mul_le_left.trans
      ((Ideal.pow_le_pow_right ?_).trans le_sup_right)))
    cutsat

variable (I J K)

protected theorem mul_comm : I * J = J * I :=
  le_antisymm (mul_le.2 fun _ hrI _ hsJ => mul_mem_mul_rev hsJ hrI)
    (mul_le.2 fun _ hrJ _ hsI => mul_mem_mul_rev hsI hrJ)

theorem span_mul_span (S T : Set R) : span S * span T = span (⋃ (s ∈ S) (t ∈ T), {s * t}) :=
  Submodule.span_smul_span S T

variable {I J K}

theorem span_mul_span' (S T : Set R) : span S * span T = span (S * T) := by
  unfold span
  rw [Submodule.span_mul_span]

theorem span_singleton_mul_span_singleton (r s : R) :
    span {r} * span {s} = (span {r * s} : Ideal R) := by
  unfold span
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem span_singleton_pow (s : R) (n : ℕ) : span {s} ^ n = (span {s ^ n} : Ideal R) := by
  induction n with
  | zero => simp [Set.singleton_one]
  | succ n ih => simp only [pow_succ, ih, span_singleton_mul_span_singleton]

theorem mem_mul_span_singleton {x y : R} {I : Ideal R} : x ∈ I * span {y} ↔ ∃ z ∈ I, z * y = x :=
  Submodule.mem_smul_span_singleton

theorem mem_span_singleton_mul {x y : R} {I : Ideal R} : x ∈ span {y} * I ↔ ∃ z ∈ I, y * z = x := by
  simp only [mul_comm, mem_mul_span_singleton]

@[simp]
lemma range_mul (A : Type*) [CommSemiring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] (a : A) : LinearMap.range (LinearMap.mul R A a) =
    (Ideal.span {a}).restrictScalars R := by
  aesop (add simp Ideal.mem_span_singleton) (add simp dvd_def)

lemma range_mul' (a : R) : LinearMap.range (LinearMap.mul R R a) = Ideal.span {a} := range_mul ..

theorem le_span_singleton_mul_iff {x : R} {I J : Ideal R} :
    I ≤ span {x} * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
  show (∀ {zI} (_ : zI ∈ I), zI ∈ span {x} * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI by
    simp only [mem_span_singleton_mul]

theorem span_singleton_mul_le_iff {x : R} {I J : Ideal R} :
    span {x} * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J := by
  simp only [mul_le, mem_span_singleton]
  constructor
  · intro h zI hzI
    exact h x (dvd_refl x) zI hzI
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [mul_comm x z, mul_assoc]
    exact J.mul_mem_left _ (h zI hzI)

theorem span_singleton_mul_le_span_singleton_mul {x y : R} {I J : Ideal R} :
    span {x} * I ≤ span {y} * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ := by
  simp only [span_singleton_mul_le_iff, mem_span_singleton_mul, eq_comm]

theorem span_singleton_mul_right_mono [IsDomain R] {x : R} (hx : x ≠ 0) :
    span {x} * I ≤ span {x} * J ↔ I ≤ J := by
  simp_rw [span_singleton_mul_le_span_singleton_mul, mul_right_inj' hx,
    exists_eq_right', SetLike.le_def]

theorem span_singleton_mul_left_mono [IsDomain R] {x : R} (hx : x ≠ 0) :
    I * span {x} ≤ J * span {x} ↔ I ≤ J := by
  simpa only [mul_comm I, mul_comm J] using span_singleton_mul_right_mono hx

theorem span_singleton_mul_right_inj [IsDomain R] {x : R} (hx : x ≠ 0) :
    span {x} * I = span {x} * J ↔ I = J := by
  simp only [le_antisymm_iff, span_singleton_mul_right_mono hx]

theorem span_singleton_mul_left_inj [IsDomain R] {x : R} (hx : x ≠ 0) :
    I * span {x} = J * span {x} ↔ I = J := by
  simp only [le_antisymm_iff, span_singleton_mul_left_mono hx]

theorem span_singleton_mul_right_injective [IsDomain R] {x : R} (hx : x ≠ 0) :
    Function.Injective ((span {x} : Ideal R) * ·) := fun _ _ =>
  (span_singleton_mul_right_inj hx).mp

theorem span_singleton_mul_left_injective [IsDomain R] {x : R} (hx : x ≠ 0) :
    Function.Injective fun I : Ideal R => I * span {x} := fun _ _ =>
  (span_singleton_mul_left_inj hx).mp

theorem eq_span_singleton_mul {x : R} (I J : Ideal R) :
    I = span {x} * J ↔ (∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀ z ∈ J, x * z ∈ I := by
  simp only [le_antisymm_iff, le_span_singleton_mul_iff, span_singleton_mul_le_iff]

theorem span_singleton_mul_eq_span_singleton_mul {x y : R} (I J : Ideal R) :
    span {x} * I = span {y} * J ↔
      (∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ) ∧ ∀ zJ ∈ J, ∃ zI ∈ I, x * zI = y * zJ := by
  simp only [le_antisymm_iff, span_singleton_mul_le_span_singleton_mul, eq_comm]

theorem prod_span {ι : Type*} (s : Finset ι) (I : ι → Set R) :
    (∏ i ∈ s, Ideal.span (I i)) = Ideal.span (∏ i ∈ s, I i) :=
  Submodule.prod_span s I

theorem prod_span_singleton {ι : Type*} (s : Finset ι) (I : ι → R) :
    (∏ i ∈ s, Ideal.span ({I i} : Set R)) = Ideal.span {∏ i ∈ s, I i} :=
  Submodule.prod_span_singleton s I

@[simp]
theorem multiset_prod_span_singleton (m : Multiset R) :
    (m.map fun x => Ideal.span {x}).prod = Ideal.span ({Multiset.prod m} : Set R) :=
  Multiset.induction_on m (by simp) fun a m ih => by
    simp only [Multiset.map_cons, Multiset.prod_cons, ih, ← Ideal.span_singleton_mul_span_singleton]

open scoped Function in -- required for scoped `on` notation
theorem finset_inf_span_singleton {ι : Type*} (s : Finset ι) (I : ι → R)
    (hI : Set.Pairwise (↑s) (IsCoprime on I)) :
    (s.inf fun i => Ideal.span ({I i} : Set R)) = Ideal.span {∏ i ∈ s, I i} := by
  ext x
  simp only [Submodule.mem_finsetInf, Ideal.mem_span_singleton]
  exact ⟨Finset.prod_dvd_of_coprime hI, fun h i hi => (Finset.dvd_prod_of_mem _ hi).trans h⟩

theorem iInf_span_singleton {ι : Type*} [Fintype ι] {I : ι → R}
    (hI : ∀ (i j) (_ : i ≠ j), IsCoprime (I i) (I j)) :
    ⨅ i, span ({I i} : Set R) = span {∏ i, I i} := by
  rw [← Finset.inf_univ_eq_iInf, finset_inf_span_singleton]
  rwa [Finset.coe_univ, Set.pairwise_univ]

theorem iInf_span_singleton_natCast {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {I : ι → ℕ} (hI : Pairwise fun i j => (I i).Coprime (I j)) :
    ⨅ (i : ι), span {(I i : R)} = span {((∏ i : ι, I i : ℕ) : R)} := by
  rw [iInf_span_singleton, Nat.cast_prod]
  exact fun i j h ↦ (hI h).cast

theorem sup_eq_top_iff_isCoprime {R : Type*} [CommSemiring R] (x y : R) :
    span ({x} : Set R) ⊔ span {y} = ⊤ ↔ IsCoprime x y := by
  rw [eq_top_iff_one, Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, h1⟩
    rw [mem_span_singleton'] at hu hv
    rw [← hu.choose_spec, ← hv.choose_spec] at h1
    exact ⟨_, _, h1⟩
  · exact fun ⟨u, v, h1⟩ =>
      ⟨_, mem_span_singleton'.mpr ⟨_, rfl⟩, _, mem_span_singleton'.mpr ⟨_, rfl⟩, h1⟩

theorem mul_le_inf : I * J ≤ I ⊓ J :=
  mul_le.2 fun r hri s hsj => ⟨I.mul_mem_right s hri, J.mul_mem_left r hsj⟩

theorem multiset_prod_le_inf {s : Multiset (Ideal R)} : s.prod ≤ s.inf := by
  classical
    refine s.induction_on ?_ ?_
    · rw [Multiset.inf_zero]
      exact le_top
    intro a s ih
    rw [Multiset.prod_cons, Multiset.inf_cons]
    exact le_trans mul_le_inf (inf_le_inf le_rfl ih)

theorem prod_le_inf {s : Finset ι} {f : ι → Ideal R} : s.prod f ≤ s.inf f :=
  multiset_prod_le_inf

theorem mul_eq_inf_of_coprime (h : I ⊔ J = ⊤) : I * J = I ⊓ J :=
  le_antisymm mul_le_inf fun r ⟨hri, hrj⟩ =>
    let ⟨s, hsi, t, htj, hst⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
    mul_one r ▸
      hst ▸
        (mul_add r s t).symm ▸ Ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj) (mul_mem_mul hri htj)

theorem sup_mul_eq_of_coprime_left (h : I ⊔ J = ⊤) : I ⊔ J * K = I ⊔ K :=
  le_antisymm (sup_le_sup_left mul_le_left _) fun i hi => by
    rw [eq_top_iff_one] at h; rw [Submodule.mem_sup] at h hi ⊢
    obtain ⟨i1, hi1, j, hj, h⟩ := h; obtain ⟨i', hi', k, hk, hi⟩ := hi
    refine ⟨_, add_mem hi' (mul_mem_right k _ hi1), _, mul_mem_mul hj hk, ?_⟩
    rw [add_assoc, ← add_mul, h, one_mul, hi]

theorem sup_mul_eq_of_coprime_right (h : I ⊔ K = ⊤) : I ⊔ J * K = I ⊔ J := by
  rw [mul_comm]
  exact sup_mul_eq_of_coprime_left h

theorem mul_sup_eq_of_coprime_left (h : I ⊔ J = ⊤) : I * K ⊔ J = K ⊔ J := by
  rw [sup_comm] at h
  rw [sup_comm, sup_mul_eq_of_coprime_left h, sup_comm]

theorem mul_sup_eq_of_coprime_right (h : K ⊔ J = ⊤) : I * K ⊔ J = I ⊔ J := by
  rw [sup_comm] at h
  rw [sup_comm, sup_mul_eq_of_coprime_right h, sup_comm]

theorem sup_prod_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → I ⊔ J i = ⊤) :
    (I ⊔ ∏ i ∈ s, J i) = ⊤ :=
  Finset.prod_induction _ (fun J => I ⊔ J = ⊤)
    (fun _ _ hJ hK => (sup_mul_eq_of_coprime_left hJ).trans hK)
    (by simp_rw [one_eq_top, sup_top_eq]) h

theorem sup_multiset_prod_eq_top {s : Multiset (Ideal R)} (h : ∀ p ∈ s, I ⊔ p = ⊤) :
    I ⊔ Multiset.prod s = ⊤ :=
  Multiset.prod_induction (I ⊔ · = ⊤) s (fun _ _ hp hq ↦ (sup_mul_eq_of_coprime_left hp).trans hq)
    (by simp only [one_eq_top, le_top, sup_of_le_right]) h

theorem sup_iInf_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → I ⊔ J i = ⊤) :
    (I ⊔ ⨅ i ∈ s, J i) = ⊤ := by
  rw [eq_top_iff, ← sup_prod_eq_top h, ← Finset.inf_eq_iInf]
  grw [prod_le_inf]

theorem prod_sup_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → J i ⊔ I = ⊤) :
    (∏ i ∈ s, J i) ⊔ I = ⊤ := by rw [sup_comm, sup_prod_eq_top]; intro i hi; rw [sup_comm, h i hi]

theorem iInf_sup_eq_top {s : Finset ι} {J : ι → Ideal R} (h : ∀ i, i ∈ s → J i ⊔ I = ⊤) :
    (⨅ i ∈ s, J i) ⊔ I = ⊤ := by rw [sup_comm, sup_iInf_eq_top]; intro i hi; rw [sup_comm, h i hi]

theorem sup_pow_eq_top {n : ℕ} (h : I ⊔ J = ⊤) : I ⊔ J ^ n = ⊤ := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact sup_prod_eq_top fun _ _ => h

theorem pow_sup_eq_top {n : ℕ} (h : I ⊔ J = ⊤) : I ^ n ⊔ J = ⊤ := by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact prod_sup_eq_top fun _ _ => h

theorem pow_sup_pow_eq_top {m n : ℕ} (h : I ⊔ J = ⊤) : I ^ m ⊔ J ^ n = ⊤ :=
  sup_pow_eq_top (pow_sup_eq_top h)

variable (I) in
@[simp]
theorem mul_top : I * ⊤ = I :=
  Ideal.mul_comm ⊤ I ▸ Submodule.top_smul I

/-- A product of ideals in an integral domain is zero if and only if one of the terms is zero. -/
@[simp]
lemma multiset_prod_eq_bot {R : Type*} [CommSemiring R] [IsDomain R] {s : Multiset (Ideal R)} :
    s.prod = ⊥ ↔ ⊥ ∈ s :=
  Multiset.prod_eq_zero_iff

theorem span_pair_mul_span_pair (w x y z : R) :
    (span {w, x} : Ideal R) * span {y, z} = span {w * y, w * z, x * y, x * z} := by
  simp_rw [span_insert, sup_mul, mul_sup, span_singleton_mul_span_singleton, sup_assoc]

theorem isCoprime_iff_codisjoint : IsCoprime I J ↔ Codisjoint I J := by
  rw [IsCoprime, codisjoint_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [eq_top_iff_one]
    apply (show x * I + y * J ≤ I ⊔ J from
      sup_le (mul_le_left.trans le_sup_left) (mul_le_left.trans le_sup_right))
    rw [hxy]
    simp only [one_eq_top, Submodule.mem_top]
  · intro h
    refine ⟨1, 1, ?_⟩
    simpa only [one_eq_top, top_mul, Submodule.add_eq_sup]

theorem isCoprime_of_isMaximal [I.IsMaximal] [J.IsMaximal] (ne : I ≠ J) : IsCoprime I J := by
  rw [isCoprime_iff_codisjoint, isMaximal_def] at *
  exact IsCoatom.codisjoint_of_ne ‹_› ‹_› ne

theorem isCoprime_iff_add : IsCoprime I J ↔ I + J = 1 := by
  rw [isCoprime_iff_codisjoint, codisjoint_iff, add_eq_sup, one_eq_top]

theorem isCoprime_iff_exists : IsCoprime I J ↔ ∃ i ∈ I, ∃ j ∈ J, i + j = 1 := by
  rw [← add_eq_one_iff, isCoprime_iff_add]

theorem isCoprime_iff_sup_eq : IsCoprime I J ↔ I ⊔ J = ⊤ := by
  rw [isCoprime_iff_codisjoint, codisjoint_iff]

theorem coprime_of_no_prime_ge {I J : Ideal R} (h : ∀ P, I ≤ P → J ≤ P → ¬IsPrime P) :
    IsCoprime I J := by
  rw [isCoprime_iff_sup_eq]
  by_contra hIJ
  obtain ⟨P, hP, hIJ⟩ := Ideal.exists_le_maximal _ hIJ
  exact h P (le_trans le_sup_left hIJ) (le_trans le_sup_right hIJ) hP.isPrime

open List in
theorem isCoprime_tfae : TFAE [IsCoprime I J, Codisjoint I J, I + J = 1,
    ∃ i ∈ I, ∃ j ∈ J, i + j = 1, I ⊔ J = ⊤] := by
  rw [← isCoprime_iff_codisjoint, ← isCoprime_iff_add, ← isCoprime_iff_exists,
      ← isCoprime_iff_sup_eq]
  simp

theorem _root_.IsCoprime.codisjoint (h : IsCoprime I J) : Codisjoint I J :=
  isCoprime_iff_codisjoint.mp h

theorem _root_.IsCoprime.add_eq (h : IsCoprime I J) : I + J = 1 := isCoprime_iff_add.mp h

theorem _root_.IsCoprime.exists (h : IsCoprime I J) : ∃ i ∈ I, ∃ j ∈ J, i + j = 1 :=
  isCoprime_iff_exists.mp h

theorem _root_.IsCoprime.sup_eq (h : IsCoprime I J) : I ⊔ J = ⊤ := isCoprime_iff_sup_eq.mp h

theorem inf_eq_mul_of_isCoprime (coprime : IsCoprime I J) : I ⊓ J = I * J :=
  (Ideal.mul_eq_inf_of_coprime coprime.sup_eq).symm

theorem isCoprime_span_singleton_iff (x y : R) :
    IsCoprime (span <| singleton x) (span <| singleton y) ↔ IsCoprime x y := by
  simp_rw [isCoprime_iff_codisjoint, codisjoint_iff, eq_top_iff_one, mem_span_singleton_sup,
    mem_span_singleton]
  constructor
  · rintro ⟨a, _, ⟨b, rfl⟩, e⟩; exact ⟨a, b, mul_comm b y ▸ e⟩
  · rintro ⟨a, b, e⟩; exact ⟨a, _, ⟨b, rfl⟩, mul_comm y b ▸ e⟩

theorem isCoprime_biInf {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
        1 = I + K            := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
        _ = I + K*(I + J i)  := by rw [hf i (Finset.mem_insert_self i s), mul_one]
        _ = (1+K)*I + K*J i  := by ring
        _ ≤ I + K ⊓ J i      := add_le_add mul_le_left mul_le_inf

/-- The radical of an ideal `I` consists of the elements `r` such that `r ^ n ∈ I` for some `n`. -/
def radical (I : Ideal R) : Ideal R where
  carrier := { r | ∃ n : ℕ, r ^ n ∈ I }
  zero_mem' := ⟨1, (pow_one (0 : R)).symm ▸ I.zero_mem⟩
  add_mem' := fun {_ _} ⟨m, hxmi⟩ ⟨n, hyni⟩ =>
    ⟨m + n - 1, add_pow_add_pred_mem_of_pow_mem I hxmi hyni⟩
  smul_mem' {r s} := fun ⟨n, h⟩ ↦ ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r ^ n) h⟩

theorem mem_radical_iff {r : R} : r ∈ I.radical ↔ ∃ n : ℕ, r ^ n ∈ I := Iff.rfl

/-- An ideal is radical if it contains its radical. -/
def IsRadical (I : Ideal R) : Prop :=
  I.radical ≤ I

theorem le_radical : I ≤ radical I := fun r hri => ⟨1, (pow_one r).symm ▸ hri⟩

/-- An ideal is radical iff it is equal to its radical. -/
theorem radical_eq_iff : I.radical = I ↔ I.IsRadical := by
  rw [le_antisymm_iff, and_iff_left le_radical, IsRadical]

alias ⟨_, IsRadical.radical⟩ := radical_eq_iff

theorem isRadical_iff_pow_one_lt (k : ℕ) (hk : 1 < k) : I.IsRadical ↔ ∀ r, r ^ k ∈ I → r ∈ I :=
  ⟨fun h _r hr ↦ h ⟨k, hr⟩, fun h x ⟨n, hx⟩ ↦
    k.pow_imp_self_of_one_lt hk _ (fun _ _ ↦ .inr ∘ I.smul_mem _) h n x hx⟩

variable (R) in
theorem radical_top : (radical ⊤ : Ideal R) = ⊤ :=
  (eq_top_iff_one _).2 ⟨0, Submodule.mem_top⟩

theorem radical_mono (H : I ≤ J) : radical I ≤ radical J := fun _ ⟨n, hrni⟩ => ⟨n, H hrni⟩

variable (I)

theorem radical_isRadical : (radical I).IsRadical := fun r ⟨n, k, hrnki⟩ =>
  ⟨n * k, (pow_mul r n k).symm ▸ hrnki⟩

@[simp]
theorem radical_idem : radical (radical I) = radical I :=
  (radical_isRadical I).radical

variable {I}

theorem IsRadical.radical_le_iff (hJ : J.IsRadical) : I.radical ≤ J ↔ I ≤ J :=
  ⟨le_trans le_radical, fun h => hJ.radical ▸ radical_mono h⟩

theorem radical_le_radical_iff : radical I ≤ radical J ↔ I ≤ radical J :=
  (radical_isRadical J).radical_le_iff

theorem radical_eq_top : radical I = ⊤ ↔ I = ⊤ :=
  ⟨fun h =>
    (eq_top_iff_one _).2 <|
      let ⟨n, hn⟩ := (eq_top_iff_one _).1 h
      @one_pow R _ n ▸ hn,
    fun h => h.symm ▸ radical_top R⟩

theorem IsPrime.isRadical (H : IsPrime I) : I.IsRadical := fun _ ⟨n, hrni⟩ =>
  H.mem_of_pow_mem n hrni

theorem IsPrime.radical (H : IsPrime I) : radical I = I :=
  IsRadical.radical H.isRadical

theorem mem_radical_of_pow_mem {I : Ideal R} {x : R} {m : ℕ} (hx : x ^ m ∈ radical I) :
    x ∈ radical I :=
  radical_idem I ▸ ⟨m, hx⟩

theorem disjoint_powers_iff_notMem (y : R) (hI : I.IsRadical) :
    Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ I.1 := by
  refine ⟨fun h => Set.disjoint_left.1 h (Submonoid.mem_powers _),
      fun h => disjoint_iff.mpr (eq_bot_iff.mpr ?_)⟩
  rintro x ⟨⟨n, rfl⟩, hx'⟩
  exact h (hI <| mem_radical_of_pow_mem <| le_radical hx')

@[deprecated (since := "2025-05-23")]
alias disjoint_powers_iff_not_mem := disjoint_powers_iff_notMem

variable (I J)

theorem radical_sup : radical (I ⊔ J) = radical (radical I ⊔ radical J) :=
  le_antisymm (radical_mono <| sup_le_sup le_radical le_radical) <|
    radical_le_radical_iff.2 <| sup_le (radical_mono le_sup_left) (radical_mono le_sup_right)

theorem radical_inf : radical (I ⊓ J) = radical I ⊓ radical J :=
  le_antisymm (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right))
    fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ I.mul_mem_right _ hrm,
      (pow_add r m n).symm ▸ J.mul_mem_left _ hrn⟩

variable {I J} in
theorem IsRadical.inf (hI : IsRadical I) (hJ : IsRadical J) : IsRadical (I ⊓ J) := by
  rw [IsRadical, radical_inf]; exact inf_le_inf hI hJ

lemma isRadical_bot_iff :
    (⊥ : Ideal R).IsRadical ↔ IsReduced R := by
  simp only [IsRadical, SetLike.le_def, Ideal.mem_radical_iff, Ideal.mem_bot,
    forall_exists_index, isReduced_iff, IsNilpotent]

lemma isRadical_bot [IsReduced R] : (⊥ : Ideal R).IsRadical := by rwa [Ideal.isRadical_bot_iff]

/-- `Ideal.radical` as an `InfTopHom`, bundling in that it distributes over `inf`. -/
def radicalInfTopHom : InfTopHom (Ideal R) (Ideal R) where
  toFun := radical
  map_inf' := radical_inf
  map_top' := radical_top _

@[simp]
lemma radicalInfTopHom_apply (I : Ideal R) : radicalInfTopHom I = radical I := rfl

open Finset in
lemma radical_finset_inf {ι} {s : Finset ι} {f : ι → Ideal R} {i : ι} (hi : i ∈ s)
    (hs : ∀ ⦃y⦄, y ∈ s → (f y).radical = (f i).radical) :
    (s.inf f).radical = (f i).radical := by
  rw [← radicalInfTopHom_apply, map_finset_inf, ← Finset.inf'_eq_inf ⟨_, hi⟩]
  exact Finset.inf'_eq_of_forall _ _ hs

/-- The reverse inclusion does not hold for e.g. `I := fun n : ℕ ↦ Ideal.span {(2 ^ n : ℤ)}`. -/
theorem radical_iInf_le {ι} (I : ι → Ideal R) : radical (⨅ i, I i) ≤ ⨅ i, radical (I i) :=
  le_iInf fun _ ↦ radical_mono (iInf_le _ _)

theorem isRadical_iInf {ι} (I : ι → Ideal R) (hI : ∀ i, IsRadical (I i)) : IsRadical (⨅ i, I i) :=
  (radical_iInf_le I).trans (iInf_mono hI)

theorem radical_mul : radical (I * J) = radical I ⊓ radical J := by
  refine le_antisymm ?_ fun r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩ =>
    ⟨m + n, (pow_add r m n).symm ▸ mul_mem_mul hrm hrn⟩
  have := radical_mono <| @mul_le_inf _ _ I J
  simp_rw [radical_inf I J] at this
  assumption

variable {I J}

theorem IsPrime.radical_le_iff (hJ : IsPrime J) : I.radical ≤ J ↔ I ≤ J :=
  IsRadical.radical_le_iff hJ.isRadical

theorem radical_eq_sInf (I : Ideal R) : radical I = sInf { J : Ideal R | I ≤ J ∧ IsPrime J } :=
  le_antisymm (le_sInf fun _ hJ ↦ hJ.2.radical_le_iff.2 hJ.1) fun r hr ↦
    by_contradiction fun hri ↦
      let ⟨m, hIm, hm⟩ :=
        zorn_le_nonempty₀ { K : Ideal R | r ∉ radical K }
          (fun c hc hcc y hyc =>
            ⟨sSup c, fun ⟨n, hrnc⟩ =>
              let ⟨_, hyc, hrny⟩ := (Submodule.mem_sSup_of_directed ⟨y, hyc⟩ hcc.directedOn).1 hrnc
              hc hyc ⟨n, hrny⟩,
              fun _ => le_sSup⟩)
          I hri
      have hrm : r ∉ radical m := hm.prop
      have : ∀ x ∉ m, r ∈ radical (m ⊔ span {x}) := fun x hxm =>
        by_contradiction fun hrmx => hxm <| by
          rw [hm.eq_of_le hrmx le_sup_left]
          exact Submodule.mem_sup_right <| mem_span_singleton_self x
      have : IsPrime m :=
        ⟨by rintro rfl; rw [radical_top] at hrm; exact hrm trivial, fun {x y} hxym =>
          or_iff_not_imp_left.2 fun hxm =>
            by_contradiction fun hym =>
              let ⟨n, hrn⟩ := this _ hxm
              let ⟨p, hpm, q, hq, hpqrn⟩ := Submodule.mem_sup.1 hrn
              let ⟨c, hcxq⟩ := mem_span_singleton'.1 hq
              let ⟨k, hrk⟩ := this _ hym
              let ⟨f, hfm, g, hg, hfgrk⟩ := Submodule.mem_sup.1 hrk
              let ⟨d, hdyg⟩ := mem_span_singleton'.1 hg
              hrm
                ⟨n + k, by
                  rw [pow_add, ← hpqrn, ← hcxq, ← hfgrk, ← hdyg, add_mul, mul_add (c * x),
                      mul_assoc c x (d * y), mul_left_comm x, ← mul_assoc]
                  refine
                    m.add_mem (m.mul_mem_right _ hpm)
                    (m.add_mem (m.mul_mem_left _ hfm) (m.mul_mem_left _ hxym))⟩⟩
    hrm <|
      this.radical.symm ▸ (sInf_le ⟨hIm, this⟩ : sInf { J : Ideal R | I ≤ J ∧ IsPrime J } ≤ m) hr

theorem isRadical_bot_of_noZeroDivisors {R} [CommSemiring R] [NoZeroDivisors R] :
    (⊥ : Ideal R).IsRadical := fun _ hx => hx.recOn fun _ hn => eq_zero_of_pow_eq_zero hn

@[simp]
theorem radical_bot_of_noZeroDivisors {R : Type u} [CommSemiring R] [NoZeroDivisors R] :
    radical (⊥ : Ideal R) = ⊥ :=
  eq_bot_iff.2 isRadical_bot_of_noZeroDivisors

instance : IdemCommSemiring (Ideal R) :=
  inferInstance

variable (R) in
theorem top_pow (n : ℕ) : (⊤ ^ n : Ideal R) = ⊤ :=
  Nat.recOn n one_eq_top fun n ih => by rw [pow_succ, ih, top_mul]

@[simp]
theorem pow_eq_top_iff {n : ℕ} :
    I ^ n = ⊤ ↔ I = ⊤ ∨ n = 0 := by
  refine ⟨fun h ↦ or_iff_not_imp_right.mpr
      fun hn ↦ (eq_top_iff_one _).mpr <| pow_le_self hn <| (eq_top_iff_one _).mp h, ?_⟩
  rintro (h | h)
  · rw [h, top_pow]
  · rw [h, pow_zero, one_eq_top]

theorem natCast_eq_top {n : ℕ} (hn : n ≠ 0) : (n : Ideal R) = ⊤ :=
  natCast_eq_one hn |>.trans one_eq_top

/-- `3 : Ideal R` is *not* the ideal generated by 3 (which would be spelt
    `Ideal.span {3}`), it is simply `1 + 1 + 1 = ⊤`. -/
theorem ofNat_eq_top {n : ℕ} [n.AtLeastTwo] : (ofNat(n) : Ideal R) = ⊤ :=
  ofNat_eq_one.trans one_eq_top

variable (I)

lemma radical_pow : ∀ {n}, n ≠ 0 → radical (I ^ n) = radical I
  | 1, _ => by simp
  | n + 2, _ => by rw [pow_succ, radical_mul, radical_pow n.succ_ne_zero, inf_idem]

theorem IsPrime.mul_le {I J P : Ideal R} (hp : IsPrime P) : I * J ≤ P ↔ I ≤ P ∨ J ≤ P := by
  rw [or_comm, Ideal.mul_le]
  simp_rw [hp.mul_mem_iff_mem_or_mem, SetLike.le_def, ← forall_or_left, or_comm, forall_or_left]

theorem IsPrime.inf_le {I J P : Ideal R} (hp : IsPrime P) : I ⊓ J ≤ P ↔ I ≤ P ∨ J ≤ P :=
  ⟨fun h ↦ hp.mul_le.1 <| mul_le_inf.trans h, fun h ↦ h.elim inf_le_left.trans inf_le_right.trans⟩

theorem IsPrime.multiset_prod_le {s : Multiset (Ideal R)} {P : Ideal R} (hp : IsPrime P) :
    s.prod ≤ P ↔ ∃ I ∈ s, I ≤ P :=
  s.induction_on (by simp [hp.ne_top]) fun I s ih ↦ by simp [hp.mul_le, ih]

theorem IsPrime.multiset_prod_map_le {s : Multiset ι} (f : ι → Ideal R) {P : Ideal R}
    (hp : IsPrime P) : (s.map f).prod ≤ P ↔ ∃ i ∈ s, f i ≤ P := by
  simp_rw [hp.multiset_prod_le, Multiset.mem_map, exists_exists_and_eq_and]

theorem IsPrime.multiset_prod_mem_iff_exists_mem {I : Ideal R} (hI : I.IsPrime) (s : Multiset R) :
    s.prod ∈ I ↔ ∃ p ∈ s, p ∈ I := by
  simpa [span_singleton_le_iff_mem] using (hI.multiset_prod_map_le (span {·}))

theorem IsPrime.pow_le_iff {I P : Ideal R} [hP : P.IsPrime] {n : ℕ} (hn : n ≠ 0) :
    I ^ n ≤ P ↔ I ≤ P := by
  have h : (Multiset.replicate n I).prod ≤ P ↔ _ := hP.multiset_prod_le
  simp_rw [Multiset.prod_replicate, Multiset.mem_replicate, ne_eq, hn, not_false_eq_true,
    true_and, exists_eq_left] at h
  exact h

theorem IsPrime.le_of_pow_le {I P : Ideal R} [hP : P.IsPrime] {n : ℕ} (h : I ^ n ≤ P) :
    I ≤ P := by
  by_cases hn : n = 0
  · rw [hn, pow_zero, one_eq_top] at h
    exact fun ⦃_⦄ _ ↦ h Submodule.mem_top
  · exact (pow_le_iff hn).mp h

theorem IsPrime.prod_le {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} (hp : IsPrime P) :
    s.prod f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
  hp.multiset_prod_map_le f

/-- The product of a finite number of elements in the commutative semiring `R` lies in the
  prime ideal `p` if and only if at least one of those elements is in `p`. -/
theorem IsPrime.prod_mem_iff {s : Finset ι} {x : ι → R} {p : Ideal R} [hp : p.IsPrime] :
    ∏ i ∈ s, x i ∈ p ↔ ∃ i ∈ s, x i ∈ p := by
  simp_rw [← span_singleton_le_iff_mem, ← prod_span_singleton]
  exact hp.prod_le

theorem IsPrime.prod_mem_iff_exists_mem {I : Ideal R} (hI : I.IsPrime) (s : Finset R) :
    s.prod (fun x ↦ x) ∈ I ↔ ∃ p ∈ s, p ∈ I := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
  exact hI.multiset_prod_mem_iff_exists_mem s.val

theorem IsPrime.inf_le' {s : Finset ι} {f : ι → Ideal R} {P : Ideal R} (hp : IsPrime P) :
    s.inf f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
  ⟨fun h ↦ hp.prod_le.1 <| prod_le_inf.trans h, fun ⟨_, his, hip⟩ ↦ (Finset.inf_le his).trans hip⟩

theorem subset_union {R : Type u} [Ring R] {I J K : Ideal R} :
    (I : Set R) ⊆ J ∪ K ↔ I ≤ J ∨ I ≤ K :=
  AddSubgroupClass.subset_union

theorem subset_union_prime' {R : Type u} [CommRing R] {s : Finset ι} {f : ι → Ideal R} {a b : ι}
    (hp : ∀ i ∈ s, IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) ⊆ f a ∪ f b ∪ ⋃ i ∈ (↑s : Set ι), f i) ↔ I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i := by
  suffices
    ((I : Set R) ⊆ f a ∪ f b ∪ ⋃ i ∈ (↑s : Set ι), f i) → I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i from
    ⟨this, fun h =>
      Or.casesOn h
        (fun h =>
          Set.Subset.trans h <|
            Set.Subset.trans Set.subset_union_left Set.subset_union_left)
        fun h =>
        Or.casesOn h
          (fun h =>
            Set.Subset.trans h <|
              Set.Subset.trans Set.subset_union_right Set.subset_union_left)
          fun ⟨i, his, hi⟩ => by
          refine Set.Subset.trans hi <| Set.Subset.trans ?_ Set.subset_union_right
          exact Set.subset_biUnion_of_mem (u := fun x ↦ (f x : Set R)) (Finset.mem_coe.2 his)⟩
  generalize hn : s.card = n; intro h
  induction n generalizing a b s with
  | zero =>
    clear hp
    rw [Finset.card_eq_zero] at hn
    subst hn
    rw [Finset.coe_empty, Set.biUnion_empty, Set.union_empty, subset_union] at h
    simpa only [exists_prop, Finset.notMem_empty, false_and, exists_false, or_false]
  | succ n ih =>
    classical
    replace hn : ∃ (i : ι) (t : Finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n :=
      Finset.card_eq_succ.1 hn
    rcases hn with ⟨i, t, hit, rfl, hn⟩
    replace hp : IsPrime (f i) ∧ ∀ x ∈ t, IsPrime (f x) := (t.forall_mem_insert _ _).1 hp
    by_cases Ht : ∃ j ∈ t, f j ≤ f i
    · obtain ⟨j, hjt, hfji⟩ : ∃ j ∈ t, f j ≤ f i := Ht
      obtain ⟨u, hju, rfl⟩ : ∃ u, j ∉ u ∧ insert j u = t :=
        ⟨t.erase j, t.notMem_erase j, Finset.insert_erase hjt⟩
      have hp' : ∀ k ∈ insert i u, IsPrime (f k) := by
        rw [Finset.forall_mem_insert] at hp ⊢
        exact ⟨hp.1, hp.2.2⟩
      have hiu : i ∉ u := mt Finset.mem_insert_of_mem hit
      have hn' : (insert i u).card = n := by
        rwa [Finset.card_insert_of_notMem] at hn ⊢
        exacts [hiu, hju]
      have h' : (I : Set R) ⊆ f a ∪ f b ∪ ⋃ k ∈ (↑(insert i u) : Set ι), f k := by
        rw [Finset.coe_insert] at h ⊢
        rw [Finset.coe_insert] at h
        simp only [Set.biUnion_insert] at h ⊢
        rw [← Set.union_assoc (f i : Set R),
            Set.union_eq_self_of_subset_right hfji] at h
        exact h
      specialize ih hp' hn' h'
      refine ih.imp id (Or.imp id (Exists.imp fun k => ?_))
      exact And.imp (fun hk => Finset.insert_subset_insert i (Finset.subset_insert j u) hk) id
    by_cases Ha : f a ≤ f i
    · have h' : (I : Set R) ⊆ f i ∪ f b ∪ ⋃ j ∈ (↑t : Set ι), f j := by
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_assoc,
          Set.union_right_comm (f a : Set R),
          Set.union_eq_self_of_subset_left Ha] at h
        exact h
      specialize ih hp.2 hn h'
      right
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · exact Or.inr ⟨i, Finset.mem_insert_self i t, ih⟩
      · exact Or.inl ih
      · exact Or.inr ⟨k, Finset.mem_insert_of_mem hkt, ih⟩
    by_cases Hb : f b ≤ f i
    · have h' : (I : Set R) ⊆ f a ∪ f i ∪ ⋃ j ∈ (↑t : Set ι), f j := by
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_assoc,
          Set.union_assoc (f a : Set R),
          Set.union_eq_self_of_subset_left Hb] at h
        exact h
      specialize ih hp.2 hn h'
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · exact Or.inl ih
      · exact Or.inr (Or.inr ⟨i, Finset.mem_insert_self i t, ih⟩)
      · exact Or.inr (Or.inr ⟨k, Finset.mem_insert_of_mem hkt, ih⟩)
    by_cases Hi : I ≤ f i
    · exact Or.inr (Or.inr ⟨i, Finset.mem_insert_self i t, Hi⟩)
    have : ¬I ⊓ f a ⊓ f b ⊓ t.inf f ≤ f i := by
      simp only [hp.1.inf_le, hp.1.inf_le', not_or]
      exact ⟨⟨⟨Hi, Ha⟩, Hb⟩, Ht⟩
    rcases Set.not_subset.1 this with ⟨r, ⟨⟨⟨hrI, hra⟩, hrb⟩, hr⟩, hri⟩
    by_cases HI : (I : Set R) ⊆ f a ∪ f b ∪ ⋃ j ∈ (↑t : Set ι), f j
    · specialize ih hp.2 hn HI
      rcases ih with (ih | ih | ⟨k, hkt, ih⟩)
      · left
        exact ih
      · right
        left
        exact ih
      · right
        right
        exact ⟨k, Finset.mem_insert_of_mem hkt, ih⟩
    exfalso
    rcases Set.not_subset.1 HI with ⟨s, hsI, hs⟩
    rw [Finset.coe_insert, Set.biUnion_insert] at h
    have hsi : s ∈ f i := ((h hsI).resolve_left (mt Or.inl hs)).resolve_right (mt Or.inr hs)
    rcases h (I.add_mem hrI hsI) with (⟨ha | hb⟩ | hi | ht)
    · exact hs (Or.inl <| Or.inl <| add_sub_cancel_left r s ▸ (f a).sub_mem ha hra)
    · exact hs (Or.inl <| Or.inr <| add_sub_cancel_left r s ▸ (f b).sub_mem hb hrb)
    · exact hri (add_sub_cancel_right r s ▸ (f i).sub_mem hi hsi)
    · rw [Set.mem_iUnion₂] at ht
      rcases ht with ⟨j, hjt, hj⟩
      simp only [Finset.inf_eq_iInf, SetLike.mem_coe, Submodule.mem_iInf] at hr
      exact hs <| Or.inr <| Set.mem_biUnion hjt <|
        add_sub_cancel_left r s ▸ (f j).sub_mem hj <| hr j hjt

/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Matsumura Ex.1.6. -/
@[stacks 00DS]
theorem subset_union_prime {R : Type u} [CommRing R] {s : Finset ι} {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i) ↔ ∃ i ∈ s, I ≤ f i :=
  suffices ((I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i) → ∃ i, i ∈ s ∧ I ≤ f i by
    have aux := fun h => (bex_def.2 <| this h)
    simp_rw [exists_prop] at aux
    refine ⟨aux, fun ⟨i, his, hi⟩ ↦ Set.Subset.trans hi ?_⟩
    apply Set.subset_biUnion_of_mem (show i ∈ (↑s : Set ι) from his)
  fun h : (I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i => by
  classical
    by_cases has : a ∈ s
    · obtain ⟨t, hat, rfl⟩ : ∃ t, a ∉ t ∧ insert a t = s :=
        ⟨s.erase a, Finset.notMem_erase a s, Finset.insert_erase has⟩
      by_cases hbt : b ∈ t
      · obtain ⟨u, hbu, rfl⟩ : ∃ u, b ∉ u ∧ insert b u = t :=
          ⟨t.erase b, Finset.notMem_erase b t, Finset.insert_erase hbt⟩
        have hp' : ∀ i ∈ u, IsPrime (f i) := by
          intro i hiu
          refine hp i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hiu)) ?_ ?_ <;>
              rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Finset.coe_insert, Set.biUnion_insert, Set.biUnion_insert, ←
          Set.union_assoc, subset_union_prime' hp'] at h
        rwa [Finset.exists_mem_insert, Finset.exists_mem_insert]
      · have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_self (f a : Set R),
          subset_union_prime' hp', ← or_assoc, or_self_iff] at h
        rwa [Finset.exists_mem_insert]
    · by_cases hbs : b ∈ s
      · obtain ⟨t, hbt, rfl⟩ : ∃ t, b ∉ t ∧ insert b t = s :=
          ⟨s.erase b, Finset.notMem_erase b s, Finset.insert_erase hbs⟩
        have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_self (f b : Set R),
          subset_union_prime' hp', ← or_assoc, or_self_iff] at h
        rwa [Finset.exists_mem_insert]
      rcases s.eq_empty_or_nonempty with hse | hsne
      · subst hse
        rw [Finset.coe_empty, Set.biUnion_empty, Set.subset_empty_iff] at h
        have : (I : Set R) ≠ ∅ := Set.Nonempty.ne_empty (Set.nonempty_of_mem I.zero_mem)
        exact absurd h this
      · obtain ⟨i, his⟩ := hsne
        obtain ⟨t, _, rfl⟩ : ∃ t, i ∉ t ∧ insert i t = s :=
          ⟨s.erase i, Finset.notMem_erase i s, Finset.insert_erase his⟩
        have hp' : ∀ j ∈ t, IsPrime (f j) := by
          intro j hj
          refine hp j (Finset.mem_insert_of_mem hj) ?_ ?_ <;> rintro rfl <;>
            solve_by_elim only [Finset.mem_insert_of_mem, *]
        rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_self (f i : Set R),
          subset_union_prime' hp', ← or_assoc, or_self_iff] at h
        rwa [Finset.exists_mem_insert]

/-- Another version of prime avoidance using `Set.Finite` instead of `Finset`. -/
lemma subset_union_prime_finite {R ι : Type*} [CommRing R] {s : Set ι}
    (hs : s.Finite) {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → (f i).IsPrime) {I : Ideal R} :
    ((I : Set R) ⊆ ⋃ i ∈ s, f i) ↔ ∃ i ∈ s, I ≤ f i := by
  rcases Set.Finite.exists_finset hs with ⟨t, ht⟩
  have heq : ⋃ i ∈ s, f i = ⋃ i ∈ t, (f i : Set R) := by
    ext
    simpa using exists_congr (fun i ↦ (and_congr_left fun a ↦ ht i).symm)
  have hmem_union : ((I : Set R) ⊆ ⋃ i ∈ s, f i) ↔ ((I : Set R) ⊆ ⋃ i ∈ (t : Set ι), f i) :=
    (congrArg _ heq).to_iff
  rw [hmem_union, Ideal.subset_union_prime a b (fun i hin ↦ hp i ((ht i).mp hin))]
  exact exists_congr (fun i ↦ and_congr_left fun _ ↦ ht i)

section Dvd

/-- If `I` divides `J`, then `I` contains `J`.

In a Dedekind domain, to divide and contain are equivalent, see `Ideal.dvd_iff_le`.
-/
theorem le_of_dvd {I J : Ideal R} : I ∣ J → J ≤ I
  | ⟨_, h⟩ => h.symm ▸ le_trans mul_le_inf inf_le_left

@[simp]
theorem dvd_bot {I : Ideal R} : I ∣ ⊥ :=
  dvd_zero I

/-- See also `isUnit_iff_eq_one`. -/
@[simp high]
theorem isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤ :=
  isUnit_iff_dvd_one.trans
    ((@one_eq_top R _).symm ▸
      ⟨fun h => eq_top_iff.mpr (Ideal.le_of_dvd h), fun h => ⟨⊤, by rw [mul_top, h]⟩⟩)

instance uniqueUnits : Unique (Ideal R)ˣ where
  default := 1
  uniq u := Units.ext (show (u : Ideal R) = 1 by rw [isUnit_iff.mp u.isUnit, one_eq_top])

end Dvd

end MulAndRadical



section Total

variable (ι : Type*)
variable (M : Type*) [AddCommGroup M] {R : Type*} [CommRing R] [Module R M] (I : Ideal R)
variable (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤)

/-- A variant of `Finsupp.linearCombination` that takes in vectors valued in `I`. -/
noncomputable def finsuppTotal : (ι →₀ I) →ₗ[R] M :=
  (Finsupp.linearCombination R v).comp (Finsupp.mapRange.linearMap I.subtype)

variable {ι M v}

theorem finsuppTotal_apply (f : ι →₀ I) :
    finsuppTotal ι M I v f = f.sum fun i x => (x : R) • v i := by
  dsimp [finsuppTotal]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index]
  exact fun _ => zero_smul _ _

theorem finsuppTotal_apply_eq_of_fintype [Fintype ι] (f : ι →₀ I) :
    finsuppTotal ι M I v f = ∑ i, (f i : R) • v i := by
  rw [finsuppTotal_apply, Finsupp.sum_fintype]
  exact fun _ => zero_smul _ _

theorem range_finsuppTotal :
    LinearMap.range (finsuppTotal ι M I v) = I • Submodule.span R (Set.range v) := by
  ext
  rw [Submodule.mem_ideal_smul_span_iff_exists_sum]
  refine ⟨fun ⟨f, h⟩ => ⟨Finsupp.mapRange.linearMap I.subtype f, fun i => (f i).2, h⟩, ?_⟩
  rintro ⟨a, ha, rfl⟩
  classical
    refine ⟨a.mapRange (fun r => if h : r ∈ I then ⟨r, h⟩ else 0)
      (by simp only [Submodule.zero_mem, ↓reduceDIte]; rfl), ?_⟩
    rw [finsuppTotal_apply, Finsupp.sum_mapRange_index]
    · apply Finsupp.sum_congr
      intro i _
      rw [dif_pos (ha i)]
    · exact fun _ => zero_smul _ _

end Total

end Ideal

section span_range
variable {α R : Type*} [Semiring R]

theorem Finsupp.mem_ideal_span_range_iff_exists_finsupp {x : R} {v : α → R} :
    x ∈ Ideal.span (Set.range v) ↔ ∃ c : α →₀ R, (c.sum fun i a => a * v i) = x :=
  Finsupp.mem_span_range_iff_exists_finsupp

/-- An element `x` lies in the span of `v` iff it can be written as sum `∑ cᵢ • vᵢ = x`.
-/
theorem Ideal.mem_span_range_iff_exists_fun [Fintype α] {x : R} {v : α → R} :
    x ∈ Ideal.span (Set.range v) ↔ ∃ c : α → R, ∑ i, c i * v i = x :=
  Submodule.mem_span_range_iff_exists_fun _

end span_range

theorem Associates.mk_ne_zero' {R : Type*} [CommSemiring R] {r : R} :
    Associates.mk (Ideal.span {r} : Ideal R) ≠ 0 ↔ r ≠ 0 := by
  rw [Associates.mk_ne_zero, Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]

open scoped nonZeroDivisors in
theorem Ideal.span_singleton_nonZeroDivisors {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    {r : R} : span {r} ∈ (Ideal R)⁰ ↔ r ∈ R⁰ := by
  cases subsingleton_or_nontrivial R
  · simp_rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    exact ⟨fun _ _ _ ↦ Subsingleton.eq_zero _, fun _ _ _ ↦ Subsingleton.eq_zero _⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero, mem_nonZeroDivisors_iff_ne_zero, ne_eq, zero_eq_bot,
      span_singleton_eq_bot]

theorem Ideal.primeCompl_le_nonZeroDivisors {R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (P : Ideal R) [P.IsPrime] : P.primeCompl ≤ nonZeroDivisors R :=
  le_nonZeroDivisors_of_noZeroDivisors <| not_not_intro P.zero_mem

namespace Submodule

variable {R : Type u} {M : Type v}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

instance moduleSubmodule : Module (Ideal R) (Submodule R M) where
  smul_add := smul_sup
  add_smul := sup_smul
  mul_smul := Submodule.mul_smul
  one_smul := by simp
  zero_smul := bot_smul
  smul_zero := smul_bot

lemma span_smul_eq
    (s : Set R) (N : Submodule R M) :
    Ideal.span s • N = s • N := by
  rw [← coe_set_smul, coe_span_smul]

@[simp]
theorem set_smul_top_eq_span (s : Set R) :
    s • ⊤ = Ideal.span s :=
  (span_smul_eq s ⊤).symm.trans (Ideal.span s).mul_top

lemma smul_le_span (s : Set R) (I : Ideal R) : s • I ≤ Ideal.span s := by
  simp [← Submodule.set_smul_top_eq_span, smul_le_smul_left]

variable {A B} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

open Submodule

instance algebraIdeal : Algebra (Ideal R) (Submodule R A) where
  __ := moduleSubmodule
  algebraMap :=
  { toFun := map (Algebra.linearMap R A)
    map_one' := by
      rw [one_eq_span, map_span, Set.image_singleton, Algebra.linearMap_apply, map_one, one_eq_span]
    map_mul' := (Submodule.map_mul · · <| Algebra.ofId R A)
    map_zero' := map_bot _
    map_add' := (map_sup · · _) }
  commutes' I M := mul_comm_of_commute <| by rintro _ ⟨r, _, rfl⟩ a _; apply Algebra.commutes
  smul_def' I M := le_antisymm (smul_le.mpr fun r hr a ha ↦ by
    rw [Algebra.smul_def]; exact Submodule.mul_mem_mul ⟨r, hr, rfl⟩ ha) (Submodule.mul_le.mpr <| by
    rintro _ ⟨r, hr, rfl⟩ a ha; rw [Algebra.linearMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr ha)

/-- `Submonoid.map` as an `AlgHom`, when applied to an `AlgHom`. -/
@[simps!] def mapAlgHom (f : A →ₐ[R] B) : Submodule R A →ₐ[Ideal R] Submodule R B where
  __ := mapHom f
  commutes' I := (map_comp _ _ I).symm.trans (congr_arg (map · I) <| LinearMap.ext f.commutes)

/-- `Submonoid.map` as an `AlgEquiv`, when applied to an `AlgEquiv`. -/
-- TODO: when A, B noncommutative, still has `MulEquiv`.
@[simps!] def mapAlgEquiv (f : A ≃ₐ[R] B) : Submodule R A ≃ₐ[Ideal R] Submodule R B where
  __ := mapAlgHom f
  invFun := mapAlgHom f.symm
  left_inv I := (map_comp _ _ I).symm.trans <|
    (congr_arg (map · I) <| LinearMap.ext (f.left_inv ·)).trans (map_id I)
  right_inv I := (map_comp _ _ I).symm.trans <|
    (congr_arg (map · I) <| LinearMap.ext (f.right_inv ·)).trans (map_id I)

end Submodule

instance {R} [Semiring R] : NonUnitalSubsemiringClass (Ideal R) R where
  mul_mem _ hb := Ideal.mul_mem_left _ _ hb
instance {R} [Ring R] : NonUnitalSubringClass (Ideal R) R where

lemma Ideal.exists_subset_radical_span_sup_of_subset_radical_sup {R : Type*} [CommSemiring R]
    (s : Set R) (I J : Ideal R) (hs : s ⊆ (I ⊔ J).radical) :
    ∃ (t : s → R), Set.range t ⊆ I ∧ s ⊆ (span (Set.range t) ⊔ J).radical := by
  replace hs : ∀ z : s, ∃ (m : ℕ) (a b : R) (ha : a ∈ I) (hb : b ∈ J), a + b = z ^ m := by
    rintro ⟨z, hzs⟩
    simp only [Ideal.radical, Submodule.mem_sup] at hs
    obtain ⟨m, y, hyq, b, hb, hy⟩ := hs hzs
    exact ⟨m, y, b, hyq, hb, hy⟩
  choose m a b ha hb heq using hs
  refine ⟨a, by rwa [Set.range_subset_iff], fun z hz ↦ ⟨m ⟨z, hz⟩, heq ⟨z, hz⟩ ▸ ?_⟩⟩
  exact Ideal.add_mem _ (mem_sup_left (subset_span ⟨⟨z, hz⟩, rfl⟩)) (mem_sup_right <| hb _)

@[deprecated (since := "2025-05-13")]
alias Ideal.exists_subset_radical_span_sup_span_of_subset_radical_sup :=
  Ideal.exists_subset_radical_span_sup_of_subset_radical_sup
