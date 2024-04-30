/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Judith Ludwig, Christian Merten
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
- `AdicCompletion I M`: if `I` is finitely generated, then this is the universal complete module
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

/-- The canonical linear map `M ⧸ (I ^ n • ⊤) →ₗ[R] M ⧸ (I ^ m • ⊤)` for `m ≤ n` used
to define `AdicCompletion`. -/
def AdicCompletion.transitionMap {m n : ℕ} (hmn : m ≤ n) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ m • ⊤ : Submodule R M) :=
  liftQ (I ^ n • ⊤ : Submodule R M) (mkQ (I ^ m • ⊤ : Submodule R M)) (by
    rw [ker_mkQ]
    exact smul_mono (Ideal.pow_le_pow_right hmn) le_rfl)

/-- Auxiliary definition for `AdicCompletion`. -/
private def adicCompletion : Submodule R (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  carrier := { f | ∀ {m n} (hmn : m ≤ n), AdicCompletion.transitionMap I M hmn (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, LinearMap.map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply, Pi.add_apply, LinearMap.map_add, hf hmn, hg hmn]
  smul_mem' c f hf m n hmn := by rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hf hmn]

/-- The completion of a module with respect to an ideal. This is not necessarily Hausdorff.
In fact, this is only complete if the ideal is finitely generated. -/
def AdicCompletion : Type _ :=
  adicCompletion I M
#align adic_completion AdicCompletion

namespace IsHausdorff

instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, SModEq.bot] using hx 1⟩
#align is_Hausdorff.bot IsHausdorff.bot

variable {M}

protected theorem subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
  ⟨fun x y => eq_of_sub_eq_zero <| h.haus (x - y) fun n => by
    rw [Ideal.top_pow, top_smul]
    exact SModEq.top⟩
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
      simp only [sup_of_le_right (iInf_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
      rw [← this, map_smul'', mem_comap, Submodule.map_top, range_mkQ, ← SModEq.zero]
      exact hx n⟩

variable {M} [h : IsHausdorff I N]

/-- Universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
  liftQ _ f <| map_le_iff_le_comap.1 <| h.iInf_pow_smul ▸ le_iInf fun n =>
    le_trans (map_mono <| iInf_le _ n) <| by
      rw [map_smul'']
      exact smul_mono le_rfl le_top
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
#align Hausdorffification.lift_eq Hausdorffification.lift_eq

end Hausdorffification

namespace IsPrecomplete

instance bot : IsPrecomplete (⊥ : Ideal R) M := by
  refine' ⟨fun f hf => ⟨f 1, fun n => _⟩⟩
  cases' n with n
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    exact SModEq.top
  specialize hf (Nat.le_add_left 1 n)
  rw [pow_one, bot_smul, SModEq.bot] at hf; rw [hf]
#align is_precomplete.bot IsPrecomplete.bot

instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f _ =>
    ⟨0, fun n => by
      rw [Ideal.top_pow, top_smul]
      exact SModEq.top⟩⟩
#align is_precomplete.top IsPrecomplete.top

instance (priority := 100) of_subsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f _ => ⟨0, fun n => by rw [Subsingleton.elim (f n) 0]⟩⟩
#align is_precomplete.of_subsingleton IsPrecomplete.of_subsingleton

end IsPrecomplete

namespace AdicCompletion

instance : AddCommGroup (AdicCompletion I M) :=
  inferInstanceAs <| AddCommGroup (adicCompletion I M)

instance : Module R (AdicCompletion I M) :=
  inferInstanceAs <| Module R (adicCompletion I M)

/-- The canonical linear map to the completion. -/
def of : M →ₗ[R] AdicCompletion I M where
  toFun x := ⟨fun n => mkQ (I ^ n • ⊤ : Submodule R M) x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align adic_completion.of AdicCompletion.of

@[simp]
theorem of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl
#align adic_completion.of_apply AdicCompletion.of_apply

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval (n : ℕ) : AdicCompletion I M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) where
  toFun f := f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align adic_completion.eval AdicCompletion.eval

@[simp]
theorem coe_eval (n : ℕ) :
    (eval I M n : AdicCompletion I M → M ⧸ (I ^ n • ⊤ : Submodule R M)) = fun f => f.1 n :=
  rfl
#align adic_completion.coe_eval AdicCompletion.coe_eval

theorem eval_apply (n : ℕ) (f : AdicCompletion I M) : eval I M n f = f.1 n :=
  rfl
#align adic_completion.eval_apply AdicCompletion.eval_apply

theorem eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl
#align adic_completion.eval_of AdicCompletion.eval_of

@[simp]
theorem eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkQ _ :=
  rfl
#align adic_completion.eval_comp_of AdicCompletion.eval_comp_of

@[simp]
theorem range_eval (n : ℕ) : LinearMap.range (eval I M n) = ⊤ :=
  LinearMap.range_eq_top.2 fun x => Quotient.inductionOn' x fun x => ⟨of I M x, rfl⟩
#align adic_completion.range_eval AdicCompletion.range_eval

variable {I M}

@[ext]
theorem ext {x y : AdicCompletion I M} (h : ∀ n, eval I M n x = eval I M n y) : x = y :=
  Subtype.eq <| funext h
#align adic_completion.ext AdicCompletion.ext

variable (I M)

instance : IsHausdorff I (AdicCompletion I M) :=
  ⟨fun x hx => ext fun n => smul_induction_on (SModEq.zero.1 <| hx n) (fun r hr x _ =>
    ((eval I M n).map_smul r x).symm ▸
      Quotient.inductionOn' (eval I M n x) fun x => SModEq.zero.2 <| smul_mem_smul hr mem_top)
    fun _ _ ih1 ih2 => by rw [LinearMap.map_add, ih1, ih2, LinearMap.map_zero, add_zero]⟩

@[simp]
theorem transitionMap_mk {m n : ℕ} (hmn : m ≤ n) (x : M) :
    transitionMap I M hmn
      (Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) x) =
      Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) x := by
  simp [transitionMap]

@[simp]
theorem transitionMap_eq (n : ℕ) : transitionMap I M (Nat.le_refl n) = LinearMap.id := by
  ext
  simp

@[simp]
theorem transitionMap_comp {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
    transitionMap I M hmn ∘ₗ transitionMap I M hnk = transitionMap I M (hmn.trans hnk) := by
  ext
  simp

@[simp]
theorem transitionMap_comp_apply {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : M ⧸ (I ^ k • ⊤ : Submodule R M)) :
    transitionMap I M hmn (transitionMap I M hnk x) = transitionMap I M (hmn.trans hnk) x := by
  change (transitionMap I M hmn ∘ₗ transitionMap I M hnk) x = transitionMap I M (hmn.trans hnk) x
  simp

@[simp]
theorem transitionMap_comp_eval {m n : ℕ} (hmn : m ≤ n) :
    transitionMap I M hmn ∘ₗ eval I M n = eval I M m := by
  ext x
  simp [x.property]

@[simp]
theorem transitionMap_comp_eval_apply {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I M) :
    transitionMap I M hmn (eval I M n x) = eval I M m x := by
  simp [x.property]

/-- The module of `I`-adic cauchy sequences as a submodule of the product `ℕ → M`. -/
def adicCauchySequence : Submodule R (ℕ → M) where
  carrier := { f | ∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)] }
  add_mem' := by
    intro f g hf hg m n hmn
    exact SModEq.add (hf hmn) (hg hmn)
  zero_mem' := by
    intro _ _ _
    rfl
  smul_mem' := by
    intro r f hf m n hmn
    exact SModEq.smul (hf hmn) r

/-- The module of `I`-adic cauchy sequences as a submodule of the product `ℕ → M`. -/
def AdicCauchySequence : Type _ :=
  adicCauchySequence I M

instance : AddCommGroup (AdicCauchySequence I M) :=
  inferInstanceAs <| AddCommGroup (adicCauchySequence I M)

instance : Module R (AdicCauchySequence I M) :=
  inferInstanceAs <| Module R (adicCauchySequence I M)

/-- The `I`-adic cauchy condition can be checked on successive `n`.-/
theorem isAdicCauchy_iff (f : ℕ → M) :
    f ∈ adicCauchySequence I M ↔ ∀ n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  constructor
  · intro h n
    exact h (Nat.le_succ n)
  · intro h m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
        trans
        · exact ih
        · refine SModEq.mono (smul_mono (Ideal.pow_le_pow_right hmn) (by rfl)) (h n)

/-- Construct `I`-adic cauchy sequence from sequence satisfying the successive cauchy condition. -/
def AdicCauchySequence.mk (f : ℕ → M)
    (h : ∀ n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)]) : AdicCauchySequence I M where
  val := f
  property := by
    rw [isAdicCauchy_iff]
    exact h

/-- The canonical linear map from cauchy sequences to the completion. -/
@[simps]
def mk : AdicCauchySequence I M →ₗ[R] AdicCompletion I M where
  toFun f := ⟨fun n ↦ Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (f.val n), by
    intro m n hmn
    simp only [mkQ_apply, transitionMap_mk]
    exact (f.property hmn).symm
    ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every element in the adic completion is represented by a Cauchy sequence. -/
theorem mk_surjective : Function.Surjective (mk I M) := by
  intro x
  have h (n : ℕ) :
      ∃ (a : M), Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R M)) a = x.val n :=
    Quotient.exists_rep (x.val n)
  choose a ha using h
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro m n hmn
    rw [SModEq.def, ha m, ← transitionMap_mk I M hmn, ha n, x.property hmn]
  · ext n
    simp [ha n]

/-- To show a statement about an element of `adicCompletion I M`, it suffices to check it
on Cauchy sequences. -/
theorem inductionOn {p : AdicCompletion I M → Prop} (x : AdicCompletion I M)
    (h : ∀ (f : AdicCauchySequence I M), p (mk I M f)) : p x := by
  obtain ⟨f, rfl⟩ := mk_surjective I M x
  exact h f

variable {M}

/-- Lift a compatible family of linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)` to
the `I`-adic completion of `M`. -/
def lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m) :
    M →ₗ[R] AdicCompletion I N where
  toFun := fun x ↦ ⟨fun n ↦ f n x, by
    intro k l hkl
    change ((transitionMap I N hkl) ∘ₗ (f l)) x = _
    rw [h hkl]⟩
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' r x := by
    simp only [LinearMapClass.map_smul, RingHom.id_apply]
    rfl

@[simp]
lemma lift_eval (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m)
    (n : ℕ) : eval I N n ∘ₗ lift I f h = f n :=
  rfl

@[simp]
lemma lift_eval_apply (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m)
    (n : ℕ) (x : M) : (lift I f h x).val n = f n x :=
  rfl

end AdicCompletion

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
  rw [← Ideal.neg_mem_iff, Ideal.mem_jacobson_bot]
  intro y
  rw [add_comm]
  let f : ℕ → R := fun n => ∑ i in range n, (x * y) ^ i
  have hf : ∀ m n, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n h
    simp only [f, Algebra.id.smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← add_tsub_cancel_of_le h, Finset.sum_range_add, ← sub_sub, sub_self, zero_sub,
      @neg_mem_iff]
    apply Submodule.sum_mem
    intro n _
    rw [mul_pow, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ (I ^ m) (Ideal.pow_mem_pow hx m)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec toIsPrecomplete @hf
  · rw [isUnit_iff_exists_inv]
    use L
    rw [← sub_eq_zero, neg_mul]
    apply IsHausdorff.haus (toIsHausdorff : IsHausdorff I R)
    intro n
    specialize hL n
    rw [SModEq.sub_mem, Algebra.id.smul_eq_mul, Ideal.mul_top] at hL ⊢
    rw [sub_zero]
    suffices (1 - x * y) * f n - 1 ∈ I ^ n by
      convert Ideal.sub_mem _ this (Ideal.mul_mem_left _ (1 + -(x * y)) hL) using 1
      ring
    cases n
    · simp only [Ideal.one_eq_top, pow_zero, Nat.zero_eq, mem_top]
    · rw [← neg_sub _ (1 : R), neg_mul, mul_geom_sum, neg_sub, sub_sub, add_comm, ← sub_sub,
        sub_self, zero_sub, @neg_mem_iff, mul_pow]
      exact Ideal.mul_mem_right _ (I ^ _) (Ideal.pow_mem_pow hx _)
#align is_adic_complete.le_jacobson_bot IsAdicComplete.le_jacobson_bot

end IsAdicComplete
