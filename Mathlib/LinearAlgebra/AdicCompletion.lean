/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.GeomSum
import Mathlib.LinearAlgebra.SModEq
import Mathlib.RingTheory.JacobsonIdeal

#align_import linear_algebra.adic_completion from "leanprover-community/mathlib"@"2bbc7e3884ba234309d2a43b19144105a753292e"

/-!
# Completion of a module with respect to an ideal.

In this file we define the notions of Hausdorff, precomplete, and complete for an `R`-module `M`
with respect to an ideal `I`:

## Main definitions

- `IsHausdorff I M`: this says that the intersection of `I^n M` is `0`.
- `IsPrecomplete I M`: this says that every Cauchy sequence converges.
- `IsAdicComplete I M`: this says that `M` is Hausdorff and precomplete.
- `Hausdorffification I M`: this is the universal Hausdorff module with a map from `M`.
- `adicCompletion I M`: if `I` is finitely generated, then this is the universal complete module
  (TODO) with a map from `M`. This map is injective iff `M` is Hausdorff and surjective iff `M` is
  precomplete.

-/


open Submodule

variable {R : Type*} [CommRing R] (I : Ideal R)

variable (M : Type*) [AddCommGroup M] [Module R M]

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
class IsHausdorff : Prop where
  haus' : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0
#align is_Hausdorff IsHausdorff

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
class IsPrecomplete : Prop where
  prec' : ∀ f : ℕ → M, (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
    ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]
#align is_precomplete IsPrecomplete

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
class IsAdicComplete extends IsHausdorff I M, IsPrecomplete I M : Prop
#align is_adic_complete IsAdicComplete

variable {I M}

theorem IsHausdorff.haus (_ : IsHausdorff I M) :
    ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  IsHausdorff.haus'
#align is_Hausdorff.haus IsHausdorff.haus

theorem isHausdorff_iff :
    IsHausdorff I M ↔ ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩
#align is_Hausdorff_iff isHausdorff_iff

theorem IsPrecomplete.prec (_ : IsPrecomplete I M) {f : ℕ → M} :
    (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
      ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec' _
#align is_precomplete.prec IsPrecomplete.prec

theorem isPrecomplete_iff :
    IsPrecomplete I M ↔
      ∀ f : ℕ → M,
        (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
          ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align is_precomplete_iff isPrecomplete_iff

variable (I M)

/-- The Hausdorffification of a module with respect to an ideal. -/
@[reducible]
def Hausdorffification : Type _ :=
  M ⧸ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M)
#align Hausdorffification Hausdorffification

set_option maxHeartbeats 700000 in
/-- The completion of a module with respect to an ideal. This is not necessarily Hausdorff.
In fact, this is only complete if the ideal is finitely generated. -/
def adicCompletion : Submodule R (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  carrier := { f | ∀ {m n} (h : m ≤ n), liftQ _ (mkQ _) (by
      rw [ker_mkQ]
      -- ⊢ I ^ n • ⊤ ≤ I ^ m • ⊤
      exact smul_mono (Ideal.pow_le_pow h) le_rfl)
      -- 🎉 no goals
    (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, LinearMap.map_zero]
                      -- 🎉 no goals
  add_mem' hf hg m n hmn := by
    -- 🎉 no goals
    rw [Pi.add_apply, Pi.add_apply, LinearMap.map_add, hf hmn, hg hmn]
  smul_mem' c f hf m n hmn := by rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hf hmn]
                                 -- 🎉 no goals
#align adic_completion adicCompletion

namespace IsHausdorff

instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, SModEq.bot] using hx 1⟩
                  -- 🎉 no goals
#align is_Hausdorff.bot IsHausdorff.bot

variable {M}

protected theorem subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
  ⟨fun x y => eq_of_sub_eq_zero <| h.haus (x - y) fun n => by
    rw [Ideal.top_pow, top_smul]
    -- ⊢ x - y ≡ 0 [SMOD ⊤]
    exact SModEq.top⟩
    -- 🎉 no goals
#align is_Hausdorff.subsingleton IsHausdorff.subsingleton

variable (M)

instance (priority := 100) of_subsingleton [Subsingleton M] : IsHausdorff I M :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩
#align is_Hausdorff.of_subsingleton IsHausdorff.of_subsingleton

variable {I M}

theorem iInf_pow_smul (h : IsHausdorff I M) : (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.2 fun x hx =>
    (mem_bot _).2 <| h.haus x fun n => SModEq.zero.2 <| (mem_iInf fun n : ℕ => I ^ n • ⊤).1 hx n
#align is_Hausdorff.infi_pow_smul IsHausdorff.iInf_pow_smul

end IsHausdorff

namespace Hausdorffification

/-- The canonical linear map to the Hausdorffification. -/
def of : M →ₗ[R] Hausdorffification I M :=
  mkQ _
#align Hausdorffification.of Hausdorffification.of

variable {I M}

@[elab_as_elim]
theorem induction_on {C : Hausdorffification I M → Prop} (x : Hausdorffification I M)
    (ih : ∀ x, C (of I M x)) : C x :=
  Quotient.inductionOn' x ih
#align Hausdorffification.induction_on Hausdorffification.induction_on

variable (I M)

instance : IsHausdorff I (Hausdorffification I M) :=
  ⟨fun x => Quotient.inductionOn' x fun x hx =>
    (Quotient.mk_eq_zero _).2 <| (mem_iInf _).2 fun n => by
      have := comap_map_mkQ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
      -- ⊢ x ∈ I ^ n • ⊤
      simp only [sup_of_le_right (iInf_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
      -- ⊢ x ∈ I ^ n • ⊤
      rw [← this, map_smul'', mem_comap, Submodule.map_top, range_mkQ, ← SModEq.zero]
      -- ⊢ ↑(mkQ (⨅ (n : ℕ), I ^ n • ⊤)) x ≡ 0 [SMOD I ^ n • ⊤]
      exact hx n⟩
      -- 🎉 no goals

variable {M} [h : IsHausdorff I N]

/-- Universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
  liftQ _ f <| map_le_iff_le_comap.1 <| h.iInf_pow_smul ▸ le_iInf fun n =>
    le_trans (map_mono <| iInf_le _ n) <| by
      rw [map_smul'']
      -- ⊢ I ^ n • map f ⊤ ≤ I ^ n • ⊤
      exact smul_mono le_rfl le_top
      -- 🎉 no goals
#align Hausdorffification.lift Hausdorffification.lift

theorem lift_of (f : M →ₗ[R] N) (x : M) : lift I f (of I M x) = f x :=
  rfl
#align Hausdorffification.lift_of Hausdorffification.lift_of

theorem lift_comp_of (f : M →ₗ[R] N) : (lift I f).comp (of I M) = f :=
  LinearMap.ext fun _ => rfl
#align Hausdorffification.lift_comp_of Hausdorffification.lift_comp_of

/-- Uniqueness of lift. -/
theorem lift_eq (f : M →ₗ[R] N) (g : Hausdorffification I M →ₗ[R] N) (hg : g.comp (of I M) = f) :
    g = lift I f :=
  LinearMap.ext fun x => induction_on x fun x => by rw [lift_of, ← hg, LinearMap.comp_apply]
                                                    -- 🎉 no goals
#align Hausdorffification.lift_eq Hausdorffification.lift_eq

end Hausdorffification

namespace IsPrecomplete

instance bot : IsPrecomplete (⊥ : Ideal R) M := by
  refine' ⟨fun f hf => ⟨f 1, fun n => _⟩⟩
  -- ⊢ f n ≡ f 1 [SMOD ⊥ ^ n • ⊤]
  cases' n with n
  -- ⊢ f Nat.zero ≡ f 1 [SMOD ⊥ ^ Nat.zero • ⊤]
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    -- ⊢ f Nat.zero ≡ f 1 [SMOD ⊤]
    exact SModEq.top
    -- 🎉 no goals
  specialize hf (Nat.le_add_left 1 n)
  -- ⊢ f (Nat.succ n) ≡ f 1 [SMOD ⊥ ^ Nat.succ n • ⊤]
  rw [pow_one, bot_smul, SModEq.bot] at hf; rw [hf]
  -- ⊢ f (Nat.succ n) ≡ f 1 [SMOD ⊥ ^ Nat.succ n • ⊤]
                                            -- 🎉 no goals
#align is_precomplete.bot IsPrecomplete.bot

instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f _ =>
    ⟨0, fun n => by
      rw [Ideal.top_pow, top_smul]
      -- ⊢ f n ≡ 0 [SMOD ⊤]
      exact SModEq.top⟩⟩
      -- 🎉 no goals
#align is_precomplete.top IsPrecomplete.top

instance (priority := 100) of_subsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f _ => ⟨0, fun n => by rw [Subsingleton.elim (f n) 0]⟩⟩
                              -- 🎉 no goals
#align is_precomplete.of_subsingleton IsPrecomplete.of_subsingleton

end IsPrecomplete

namespace adicCompletion

/-- The canonical linear map to the completion. -/
def of : M →ₗ[R] adicCompletion I M where
  toFun x := ⟨fun _ => mkQ _ x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align adic_completion.of adicCompletion.of

set_option maxHeartbeats 700000 in
@[simp]
theorem of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkQ _ x :=
  rfl
#align adic_completion.of_apply adicCompletion.of_apply

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval (n : ℕ) : adicCompletion I M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) where
  toFun f := f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align adic_completion.eval adicCompletion.eval

@[simp]
theorem coe_eval (n : ℕ) :
    (eval I M n : adicCompletion I M → M ⧸ (I ^ n • ⊤ : Submodule R M)) = fun f => f.1 n :=
  rfl
#align adic_completion.coe_eval adicCompletion.coe_eval

theorem eval_apply (n : ℕ) (f : adicCompletion I M) : eval I M n f = f.1 n :=
  rfl
#align adic_completion.eval_apply adicCompletion.eval_apply

set_option maxHeartbeats 700000 in
theorem eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkQ _ x :=
  rfl
#align adic_completion.eval_of adicCompletion.eval_of

@[simp]
theorem eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkQ _ :=
  rfl
#align adic_completion.eval_comp_of adicCompletion.eval_comp_of

@[simp]
theorem range_eval (n : ℕ) : LinearMap.range (eval I M n) = ⊤ :=
  LinearMap.range_eq_top.2 fun x => Quotient.inductionOn' x fun x => ⟨of I M x, rfl⟩
#align adic_completion.range_eval adicCompletion.range_eval

variable {I M}

@[ext]
theorem ext {x y : adicCompletion I M} (h : ∀ n, eval I M n x = eval I M n y) : x = y :=
  Subtype.eq <| funext h
#align adic_completion.ext adicCompletion.ext

variable (I M)

instance : IsHausdorff I (adicCompletion I M) :=
  ⟨fun x hx => ext fun n => smul_induction_on (SModEq.zero.1 <| hx n) (fun r hr x _ =>
    ((eval I M n).map_smul r x).symm ▸
      Quotient.inductionOn' (eval I M n x) fun x => SModEq.zero.2 <| smul_mem_smul hr mem_top)
    fun _ _ ih1 ih2 => by rw [LinearMap.map_add, ih1, ih2, LinearMap.map_zero, add_zero]⟩
                          -- 🎉 no goals

end adicCompletion

namespace IsAdicComplete

instance bot : IsAdicComplete (⊥ : Ideal R) M where
#align is_adic_complete.bot IsAdicComplete.bot

protected theorem subsingleton (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M :=
  h.1.subsingleton
#align is_adic_complete.subsingleton IsAdicComplete.subsingleton

instance (priority := 100) of_subsingleton [Subsingleton M] : IsAdicComplete I M where
#align is_adic_complete.of_subsingleton IsAdicComplete.of_subsingleton

open BigOperators

open Finset

theorem le_jacobson_bot [IsAdicComplete I R] : I ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  -- ⊢ x ∈ Ideal.jacobson ⊥
  rw [← Ideal.neg_mem_iff, Ideal.mem_jacobson_bot]
  -- ⊢ ∀ (y : R), IsUnit (-x * y + 1)
  intro y
  -- ⊢ IsUnit (-x * y + 1)
  rw [add_comm]
  -- ⊢ IsUnit (1 + -x * y)
  let f : ℕ → R := fun n => ∑ i in range n, (x * y) ^ i
  -- ⊢ IsUnit (1 + -x * y)
  have hf : ∀ m n, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n h
    simp only [Algebra.id.smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← add_tsub_cancel_of_le h, Finset.sum_range_add, ← sub_sub, sub_self, zero_sub,
      @neg_mem_iff]
    apply Submodule.sum_mem
    intro n _
    rw [mul_pow, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ (I ^ m) (Ideal.pow_mem_pow hx m)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec toIsPrecomplete @hf
  -- ⊢ IsUnit (1 + -x * y)
  · rw [isUnit_iff_exists_inv]
    -- ⊢ ∃ b, (1 + -x * y) * b = 1
    use L
    -- ⊢ (1 + -x * y) * L = 1
    rw [← sub_eq_zero, neg_mul]
    -- ⊢ (1 + -(x * y)) * L - 1 = 0
    apply IsHausdorff.haus (toIsHausdorff : IsHausdorff I R)
    -- ⊢ ∀ (n : ℕ), (1 + -(x * y)) * L - 1 ≡ 0 [SMOD I ^ n • ⊤]
    intro n
    -- ⊢ (1 + -(x * y)) * L - 1 ≡ 0 [SMOD I ^ n • ⊤]
    specialize hL n
    -- ⊢ (1 + -(x * y)) * L - 1 ≡ 0 [SMOD I ^ n • ⊤]
    rw [SModEq.sub_mem, Algebra.id.smul_eq_mul, Ideal.mul_top] at hL ⊢
    -- ⊢ (1 + -(x * y)) * L - 1 - 0 ∈ I ^ n
    rw [sub_zero]
    -- ⊢ (1 + -(x * y)) * L - 1 ∈ I ^ n
    suffices (1 - x * y) * f n - 1 ∈ I ^ n by
      convert Ideal.sub_mem _ this (Ideal.mul_mem_left _ (1 + -(x * y)) hL) using 1
      ring
    cases n
    -- ⊢ (1 - x * y) * f Nat.zero - 1 ∈ I ^ Nat.zero
    · simp only [Ideal.one_eq_top, pow_zero, Nat.zero_eq, mem_top]
      -- 🎉 no goals
    · rw [← neg_sub _ (1 : R), neg_mul, mul_geom_sum, neg_sub, sub_sub, add_comm, ← sub_sub,
        sub_self, zero_sub, @neg_mem_iff, mul_pow]
      exact Ideal.mul_mem_right _ (I ^ _) (Ideal.pow_mem_pow hx _)
      -- 🎉 no goals
#align is_adic_complete.le_jacobson_bot IsAdicComplete.le_jacobson_bot

end IsAdicComplete
