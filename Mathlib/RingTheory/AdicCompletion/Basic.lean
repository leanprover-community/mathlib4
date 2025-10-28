/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Judith Ludwig, Christian Merten, Jiedong Jiang
-/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.SModEq
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Jacobson.Ideal

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
  with a linear map `AdicCompletion.coeHom` from `M`. This map is injective iff `M` is Hausdorff
  and surjective iff `M` is precomplete.
- `IsAdicComplete.lift`: if `N` is `I`-adically complete, then a compatible family of
  linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤)` can be lifted to a unique linear map `M →ₗ[R] N`.
  Together with `mk_lift_apply` and `eq_lift`, it gives the universal property of being
  `I`-adically complete.
-/

suppress_compilation

open Submodule Ideal Quotient

variable {R S T : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
class IsHausdorff : Prop where
  haus' : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
class IsPrecomplete : Prop where
  prec' : ∀ f : ℕ → M, (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
    ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
@[stacks 0317 "The equivalence between our definition and Stacks Project is established later at
`IsAdicComplete.bijective_iff`"]
class IsAdicComplete : Prop extends IsHausdorff I M, IsPrecomplete I M

variable {I M}

namespace IsHausdorff

theorem haus (_ : IsHausdorff I M) :
    ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  IsHausdorff.haus'

theorem _root_.isHausdorff_iff :
    IsHausdorff I M ↔ ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩

variable [IsHausdorff I M]

theorem eq_iff_smodEq {x y : M} :
    x = y ↔ ∀ n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  refine ⟨fun h _ ↦ h ▸ rfl, fun h ↦ ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I) (x - y)
  simpa [SModEq.sub_mem] using h

alias ⟨_, eq_of_smodEq⟩ := eq_iff_smodEq

section StrictMono
variable {a : ℕ → ℕ} (ha : StrictMono a)
include ha

/--
Given an strictly increasing sequence `a : ℕ → ℕ` and two elements `x y` in a module `M`
Hausdorff with respect to an ideal `I`, `x = y` if and only if `x ≡ y [SMOD (I ^ a n • ⊤)]`
for all `n`.
-/
theorem eq_iff_smodEq_of_strictMono {x y : M} :
    x = y ↔ ∀ n, x ≡ y [SMOD (I ^ a n • ⊤ : Submodule R M)] := by
  refine ⟨fun h _ ↦ h ▸ rfl, fun h ↦ ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I) (x - y)
  intro n
  simpa [SModEq.sub_mem] using SModEq.mono (pow_smul_top_le I M (ha.id_le n)) (h n)

/--
If `F : N → M` is the
limit function of `f n : N → M ⧸ (I ^ a n • ⊤)`, and each
`f n` is additive, then `F` is additive.
-/
protected theorem map_add {N : Type*} [Add N] {f : (n : ℕ) → N → M ⧸ (I ^ (a n) • ⊤)}
    (hf : ∀ (n x y), f n (x + y) = f n x + f n y) {F : N → M}
    (hF : ∀ (n x), f n x = mkQ (I ^ (a n) • ⊤ : Submodule R M) (F x)) (x y : N) :
    F (x + y) = F x + F y := by
  refine (eq_iff_smodEq_of_strictMono (I := I) ha).mpr (fun n ↦ ?_)
  simp only [mkQ_apply] at hF
  simp only [SModEq, ← hF, mk_add]
  exact hf _ _ _

/--
The `M = R` variant of `IsHausdorff.map_add`. It helps to solve the problem
that `I ^ a n` is not defeq to `(I ^ a n) • ⊤`.
-/
protected theorem map_add' [IsHausdorff I R] {N : Type*} [Add N]
    {f : (n : ℕ) → N → R ⧸ (I ^ a n)} (hf : ∀ (n x y), f n (x + y) = f n x + f n y)
    {F : N → R} (hF : ∀ (n x), f n x = Ideal.Quotient.mk (I ^ a n) (F x)) (x y : N) :
    F (x + y) = F x + F y := by
  refine (eq_iff_smodEq_of_strictMono (I := I) ha).mpr (fun n ↦ ?_)
  simp only [smul_eq_mul, mul_top]
  simp only [SModEq, mk_eq_mk, ← hF, _root_.map_add]
  exact hf n _ _

/--
If `F : N → M` is the limit function of `f n : N → M ⧸ (I ^ a n • ⊤)`, and each
`f n` preserves scalar multiplication, then `F` preserves scalar multiplication.
-/
protected theorem map_smul {N : Type*} [HSMul R N N]
    {f : (n : ℕ) → N → M ⧸ (I ^ a n • ⊤)} (hf : ∀ (n : ℕ) (r : R) (x : N), f n (r • x) = r • f n x)
    {F : N → M} (hF : ∀ (n x), f n x = mkQ (I ^ a n • ⊤ : Submodule R M) (F x)) (r : R) (x : N) :
    F (r • x) = r • F x := by
  refine (eq_iff_smodEq_of_strictMono (I := I) ha).mpr (fun n ↦ ?_)
  simp only [mkQ_apply] at hF
  simp only [SModEq, ← hF, mk_smul]
  exact hf _ _ _

/--
If `F : S → R` is the limit function of `f n : S → R ⧸ (I ^ a n)`, and each
`f n` preserves multiplication, then `F` preserves multiplication.
-/
protected theorem map_mul {S : Type*} [IsHausdorff I R] [Mul S]
    {f : (n : ℕ) → S → R ⧸ I ^ a n} (hf : ∀ (n x y), f n (x * y) = f n x * f n y)
    {F : S → R} (hF : ∀ (n x), f n x = Ideal.Quotient.mk (I ^ a n) (F x)) (x y : S) :
    F (x * y) = F x * F y := by
  refine (eq_iff_smodEq_of_strictMono (I := I) ha).mpr (fun n ↦ ?_)
  simp only [smul_eq_mul, mul_top]
  simp only [SModEq, mk_eq_mk, ← hF, _root_.map_mul]
  exact hf n _ _

/--
The limit of `1 : R ⧸ I ^ a n` is `1 : R`.
-/
protected theorem eq_one [IsHausdorff I R] {L : R} (hL : ∀ n, Ideal.Quotient.mk (I ^ a n) L = 1) :
    L = 1 := by
  refine (eq_iff_smodEq_of_strictMono (I := I) ha).mpr (fun n ↦ ?_)
  simp only [smul_eq_mul, mul_top]
  simpa [SModEq, mk_zero] using hL n

/--
The limit of `0 : M ⧸ I ^ (a n) • ⊤` is `0 : M`.
-/
protected theorem eq_zero {L : M} (hL : ∀ n, mkQ (I ^ a n • ⊤ : Submodule R M) L = 0) :
    L = 0 := by
  refine (eq_iff_smodEq_of_strictMono (I := I) ha).mpr (fun n ↦ ?_)
  simpa [SModEq, mk_zero] using hL n

/--
The `M = R` variant of `IsHausdorff.eq_zero`. The limit of `0 : R ⧸ I ^ a n` is `0 : R`.
-/
protected theorem eq_zero' [IsHausdorff I R] {L : R} (hL : ∀ n, Ideal.Quotient.mk (I ^ a n) L = 0) :
    L = 0 := by
  refine (eq_iff_smodEq_of_strictMono (I := I) ha).mpr (fun n ↦ ?_)
  simp only [smul_eq_mul, mul_top]
  simpa [SModEq, mk_zero] using hL n

end StrictMono

end IsHausdorff

namespace IsPrecomplete

theorem prec (_ : IsPrecomplete I M) {f : ℕ → M} :
    (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
      ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec' _

theorem _root_.isPrecomplete_iff :
    IsPrecomplete I M ↔
      ∀ f : ℕ → M,
        (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
          ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem exists_pow_dvd {r : R} (_ : IsPrecomplete (Ideal.span {r}) R)
    {f : ℕ → R} (hf : ∀ {m n}, m ≤ n → r ^ m ∣ f m - f n) :
    ∃ L : R, ∀ n, r ^ n ∣ f n - L := by
  suffices ∃ L, ∀ n, f n ≡ L [SMOD Ideal.span {r} ^ n • (⊤ : Ideal R)] by
    simpa [Ideal.span_singleton_pow, SModEq.sub_mem,
      Ideal.mem_span_singleton] using this
  refine IsPrecomplete.prec' f (fun {m n} h ↦ ?_)
  simpa [Ideal.span_singleton_pow, SModEq.sub_mem,
      Ideal.mem_span_singleton] using hf h

variable [IsPrecomplete I M]
/--
A variant of `IsPrecomplete.prec'`. Instead of checking the `SModEq` condition for
all `n ≥ m`, it suffices to check the condition for `n = m + 1` only.
-/
theorem of_SModEq_succ {f : ℕ → M}
    (hf : ∀ {m}, f m ≡ f (m + 1) [SMOD (I ^ m • ⊤ : Submodule R M)]) :
    ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  refine IsPrecomplete.prec' _ ?_
  intro m n h
  simp only [SModEq]
  rw [← mkQ_apply _ (f n), ← Submodule.factor_mk (pow_smul_top_le I M h), mkQ_apply]
  apply Submodule.eq_factor_of_eq_factor_succ
      (p := fun n => I ^ n • ⊤) (x := fun m ↦ Submodule.Quotient.mk (f m))
  intro m
  simpa using hf

/--
A variant of `IsPrecomplete.of_SModEq_succ`. Instead of starting with a compatible sequence
`f n` in `M`, we start with a compatible sequence `f n` in `M ⧸ I ^ n`.
-/
theorem of_eq_factorPowSucc {f : (n : ℕ) → M ⧸ (I ^ n • ⊤)}
    (hf : ∀ {m}, f m = factorPowSucc I M m (f (m + 1))) :
    ∃ L : M, ∀ n, f n = mkQ _ L := by
  choose g hmk using fun n ↦ Submodule.Quotient.mk_surjective _ (f n)
  have hg : ∀ {m}, g m ≡ g (m + 1) [SMOD (I ^ m • ⊤ : Submodule R M)] := by
    intro m
    simp only [SModEq]
    calc
      _ = f m := (hmk m)
      _ = factorPowSucc I M m (f (m + 1)) := hf
      _ = _ := by simp [← (hmk (m + 1))]
  choose L hL using of_SModEq_succ hg
  refine ⟨L, fun n ↦ (hmk n).symm.trans ?_⟩
  simpa using hL n

/--
The `M = R` variant of `IsPrecomplete.of_eq_factorPowSucc`.
It helps to solve the problem that `I ^ n` is not defeq to `I ^ n • ⊤`.
-/
theorem of_eq_factorPowSucc' [IsPrecomplete I R] {f : (n : ℕ) → R ⧸ I ^ n}
    (hf : ∀ {m}, f m = factorPowSucc I m (f (m + 1))) :
    ∃ L : R, ∀ n, f n = Ideal.Quotient.mk _ L := by
  let i := fun n ↦ (I ^ n).quotEquivOfEq (J := I ^ n • ⊤) (mul_top _).symm
  let f' := fun n => i n (f n)
  suffices ∃ L : R, ∀ n, f' n = Submodule.mkQ (I ^ n • ⊤ : Ideal R) L by
    obtain ⟨L, hL⟩ := this
    refine ⟨L, fun n ↦ ?_⟩
    have := hL n
    apply_fun (i n).symm at this
    -- `simpa only` is needed to avoid loops.
    simpa only [RingEquiv.symm_apply_apply, mkQ_apply, mk_eq_mk, quotientEquiv_symm_mk,
      RingEquiv.symm_refl, RingEquiv.refl_apply, i, f'] using this
  apply IsPrecomplete.of_eq_factorPowSucc
  intro m
  have := hf (m := m)
  apply_fun i m at this
  simpa [f', i, Submodule.factorPowSucc, Submodule.factorPow,
      Ideal.quotEquivOfEq_eq_factor] using this

section StrictMono
variable {a : ℕ → ℕ} (ha : StrictMono a)
include ha

/--
Given an strictly increasing sequence `a : ℕ → ℕ`, a
sequence `f n` in `M ⧸ I ^ a n • ⊤`
compatible in the sense that the image of `f (m + 1)` in `M ⧸ I ^ a m • ⊤`
is `f m`, there exist a limit `L` in `M` such that `f n` the image of `L` in `M ⧸ I ^ a n • ⊤`.
-/
theorem of_eq_factorPow {f : (n : ℕ) → M ⧸ (I ^ (a n) • ⊤)}
    (hf : ∀ {m}, f m = factorPow I M (ha.monotone m.le_succ) (f (m + 1))) :
    ∃ L : M, ∀ n, f n = mkQ _ L := by
  let f' : (n : ℕ) → M ⧸ (I ^ n • ⊤) :=
    fun n => Submodule.factor (pow_smul_top_le _ _ <| ha.id_le n) (f n)
  have : ∀ {m}, f' m = factorPowSucc I M m (f' (m + 1)) := by
    intro m
    simp [f', hf (m := m)]
  choose L hL using of_eq_factorPowSucc this
  refine ⟨L, fun n ↦ ((hL (a n)).symm.trans ?_).symm⟩
  suffices hf' : ∀ {m n}, (h : m ≤ n) → f m = factorPow I M (ha.monotone h) (f n) by
    simpa [f'] using (hf' (ha.id_le n)).symm
  intro m n h
  exact Submodule.eq_factor_of_eq_factor_succ
      (fun _ _ h ↦ pow_smul_top_le I M (ha.monotone h)) f (fun m ↦ hf) m n h

/--
The `M = R` variant of `IsPrecomplete.of_eq_factorPow`.
-/
theorem of_eq_factorPow' [IsPrecomplete I R] {f : (n : ℕ) → R ⧸ I ^ (a n)}
    (hf : ∀ {m}, f m = factorPow I (ha.monotone m.le_succ) (f (m + 1))) :
    ∃ L : R, ∀ n, f n = Ideal.Quotient.mk _ L := by
  let f' : (n : ℕ) → R ⧸ I ^ n :=
    fun n => Ideal.Quotient.factor (I.pow_le_pow_right (ha.id_le n)) (f n)
  have : ∀ {m}, f' m = factorPowSucc I m (f' (m + 1)) := by
    intro m
    simp [f', hf (m := m)]
  choose L hL using of_eq_factorPowSucc' this
  refine ⟨L, fun n ↦ ((hL (a n)).symm.trans ?_).symm⟩
  suffices hf' : ∀ {m n}, (h : m ≤ n) → f m = factorPow I (ha.monotone h) (f n) by
    simpa [f'] using (hf' (ha.id_le n)).symm
  intro m n h
  exact Submodule.eq_factor_of_eq_factor_succ
      (fun _ _ h ↦ I.pow_le_pow_right (ha.monotone h)) f (fun m ↦ hf) m n h

/--
The function variant of `IsPrecomplete.of_eq_factorPow`. Instead of construct a single
element from a compatible sequence of elements in `M ⧸ (I ^ a n • ⊤)`, we construct a function
from a compatible sequence of functions.
-/
theorem function_of_eq_factorPow {α : Type*} {f : (n : ℕ) → α → M ⧸ (I ^ (a n) • ⊤)}
    (hf : ∀ {m s}, f m s = Submodule.factorPow I M (ha.monotone m.le_succ) (f (m + 1) s)) :
    ∃ F : α → M, ∀ n s, f n s = mkQ (I ^ (a n) • ⊤) (F s) :=
    ⟨fun s ↦ Classical.choose <| IsPrecomplete.of_eq_factorPow ha (hf (s := s)),
    fun n s => (Classical.choose_spec <| IsPrecomplete.of_eq_factorPow ha (hf (s := s))) n⟩

/--
The function variant of `IsPrecomplete.of_eq_factorPow`, the `M = R` variant of
`IsPrecomplete.function_of_eq_factorPow`.
-/
theorem function_of_eq_factorPow' [IsPrecomplete I R] {α : Type*} {f : (n : ℕ) → α → R ⧸ I ^ (a n)}
    (hf : ∀ {m s}, f m s = Ideal.Quotient.factorPow I (ha.monotone m.le_succ) (f (m + 1) s)) :
    ∃ F : α → R, ∀ n s, f n s = Ideal.Quotient.mk (I ^ (a n)) (F s) :=
  ⟨fun s ↦ Classical.choose <| IsPrecomplete.of_eq_factorPow' ha (hf (s := s)),
    fun n s => (Classical.choose_spec <| IsPrecomplete.of_eq_factorPow' ha (hf (s := s))) n⟩

end StrictMono

end IsPrecomplete

variable (I M)

/-- The Hausdorffification of a module with respect to an ideal. -/
abbrev Hausdorffification : Type _ :=
  M ⧸ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M)

/-- The canonical linear map `M ⧸ (I ^ n • ⊤) →ₗ[R] M ⧸ (I ^ m • ⊤)` for `m ≤ n` used
to define `AdicCompletion`. -/
abbrev AdicCompletion.transitionMap {m n : ℕ} (hmn : m ≤ n) := factorPow I M hmn

/-- The completion of a module with respect to an ideal.

This is Hausdorff but not necessarily complete: a classical sufficient condition for
completeness is that `M` be finitely generated [Stacks, 0G1Q]. -/
def AdicCompletion : Type _ :=
  { f : ∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M) //
    ∀ {m n} (hmn : m ≤ n), AdicCompletion.transitionMap I M hmn (f n) = f m }

namespace IsHausdorff

instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, SModEq.bot] using hx 1⟩

variable {M} in
protected theorem subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
  ⟨fun x y => eq_of_sub_eq_zero <| h.haus (x - y) fun n => by
    rw [Ideal.top_pow, top_smul]
    exact SModEq.top⟩

instance (priority := 100) of_subsingleton [Subsingleton M] : IsHausdorff I M :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩

variable {I M}

theorem iInf_pow_smul (h : IsHausdorff I M) : (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.2 fun x hx =>
    (mem_bot _).2 <| h.haus x fun n => SModEq.zero.2 <| (mem_iInf fun n : ℕ => I ^ n • ⊤).1 hx n

end IsHausdorff

namespace Hausdorffification

/-- The canonical linear map to the Hausdorffification. -/
def of : M →ₗ[R] Hausdorffification I M :=
  mkQ _

variable {I M}

@[elab_as_elim]
theorem induction_on {C : Hausdorffification I M → Prop} (x : Hausdorffification I M)
    (ih : ∀ x, C (of I M x)) : C x :=
  Quotient.inductionOn' x ih

variable (I M)

instance : IsHausdorff I (Hausdorffification I M) :=
  ⟨fun x => Quotient.inductionOn' x fun x hx =>
    (Quotient.mk_eq_zero _).2 <| (mem_iInf _).2 fun n => by
      have := comap_map_mkQ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
      simp only [sup_of_le_right (iInf_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
      rw [← this, map_smul'', Submodule.mem_comap, Submodule.map_top, range_mkQ, ← SModEq.zero]
      exact hx n⟩

variable {M} [h : IsHausdorff I N]

/-- Universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
  liftQ _ f <| map_le_iff_le_comap.1 <| h.iInf_pow_smul ▸ le_iInf fun n =>
    le_trans (map_mono <| iInf_le _ n) <| by
      rw [map_smul'']
      exact smul_mono le_rfl le_top

theorem lift_of (f : M →ₗ[R] N) (x : M) : lift I f (of I M x) = f x :=
  rfl

theorem lift_comp_of (f : M →ₗ[R] N) : (lift I f).comp (of I M) = f :=
  LinearMap.ext fun _ => rfl

/-- Uniqueness of lift. -/
theorem lift_eq (f : M →ₗ[R] N) (g : Hausdorffification I M →ₗ[R] N) (hg : g.comp (of I M) = f) :
    g = lift I f :=
  LinearMap.ext fun x => induction_on x fun x => by rw [lift_of, ← hg, LinearMap.comp_apply]

end Hausdorffification

namespace IsPrecomplete

instance bot : IsPrecomplete (⊥ : Ideal R) M := by
  refine ⟨fun f hf => ⟨f 1, fun n => ?_⟩⟩
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    exact SModEq.top
  specialize hf (Nat.le_add_left 1 n)
  rw [pow_one, bot_smul, SModEq.bot] at hf; rw [hf]

instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f _ =>
    ⟨0, fun n => by
      rw [Ideal.top_pow, top_smul]
      exact SModEq.top⟩⟩

instance (priority := 100) of_subsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f _ => ⟨0, fun n => by rw [Subsingleton.elim (f n) 0]⟩⟩

end IsPrecomplete

namespace AdicCompletion

/-- `AdicCompletion` is the submodule of compatible families in
`∀ n : ℕ, M ⧸ (I ^ n • ⊤)`. -/
def submodule : Submodule R (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  carrier := { f | ∀ {m n} (hmn : m ≤ n), AdicCompletion.transitionMap I M hmn (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, LinearMap.map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply, Pi.add_apply, LinearMap.map_add, hf hmn, hg hmn]
  smul_mem' c f hf m n hmn := by rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, hf hmn]

instance : Zero (AdicCompletion I M) where
  zero := ⟨0, by simp⟩

instance : Add (AdicCompletion I M) where
  add x y := ⟨x.val + y.val, by simp [x.property, y.property]⟩

instance : Neg (AdicCompletion I M) where
  neg x := ⟨- x.val, by simp [x.property]⟩

instance : Sub (AdicCompletion I M) where
  sub x y := ⟨x.val - y.val, by simp [x.property, y.property]⟩

instance instSMul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S (AdicCompletion I M) where
  smul r x := ⟨r • x.val, by simp [x.property]⟩

@[simp, norm_cast] lemma val_zero : (0 : AdicCompletion I M).val = 0 := rfl

lemma val_zero_apply (n : ℕ) : (0 : AdicCompletion I M).val n = 0 := rfl

variable {I M}

@[simp, norm_cast] lemma val_add (f g : AdicCompletion I M) : (f + g).val = f.val + g.val := rfl
@[simp, norm_cast] lemma val_sub (f g : AdicCompletion I M) : (f - g).val = f.val - g.val := rfl
@[simp, norm_cast] lemma val_neg (f : AdicCompletion I M) : (-f).val = -f.val := rfl

lemma val_add_apply (f g : AdicCompletion I M) (n : ℕ) : (f + g).val n = f.val n + g.val n := rfl
lemma val_sub_apply (f g : AdicCompletion I M) (n : ℕ) : (f - g).val n = f.val n - g.val n := rfl
lemma val_neg_apply (f : AdicCompletion I M) (n : ℕ) : (-f).val n = -f.val n := rfl

/- No `simp` attribute, since it causes `simp` unification timeouts when considering
the `Module (AdicCompletion I R) (AdicCompletion I M)` instance (see `AdicCompletion/Algebra`). -/
@[norm_cast]
lemma val_smul [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M) :
    (s • f).val = s • f.val := rfl

lemma val_smul_apply [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M)
    (n : ℕ) : (s • f).val n = s • f.val n := rfl

@[ext]
lemma ext {x y : AdicCompletion I M} (h : ∀ n, x.val n = y.val n) : x = y := Subtype.eq <| funext h

variable (I M)

instance : AddCommGroup (AdicCompletion I M) :=
  let f : AdicCompletion I M → ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M) := Subtype.val
  Subtype.val_injective.addCommGroup f rfl val_add val_neg val_sub (fun _ _ ↦ val_smul ..)
    (fun _ _ ↦ val_smul ..)

instance [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S (AdicCompletion I M) :=
  let f : AdicCompletion I M →+ ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  Subtype.val_injective.module S f val_smul

instance instIsScalarTower [SMul S T] [SMul S R] [SMul T R] [SMul S M] [SMul T M]
    [IsScalarTower S R M] [IsScalarTower T R M] [IsScalarTower S T M] :
    IsScalarTower S T (AdicCompletion I M) where
  smul_assoc s t f := by ext; simp [val_smul]

instance instSMulCommClass [SMul S R] [SMul T R] [SMul S M] [SMul T M]
    [IsScalarTower S R M] [IsScalarTower T R M] [SMulCommClass S T M] :
    SMulCommClass S T (AdicCompletion I M) where
  smul_comm s t f := by ext; simp [val_smul, smul_comm]

instance instIsCentralScalar [SMul S R] [SMul Sᵐᵒᵖ R] [SMul S M] [SMul Sᵐᵒᵖ M]
    [IsScalarTower S R M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S (AdicCompletion I M) where
  op_smul_eq_smul s f := by ext; simp [val_smul, op_smul_eq_smul]

/-- The canonical inclusion from the completion to the product. -/
@[simps]
def incl : AdicCompletion I M →ₗ[R] (∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {I M}

@[simp, norm_cast]
lemma val_sum {ι : Type*} (s : Finset ι) (f : ι → AdicCompletion I M) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val := by
  simp_rw [← funext (incl_apply _ _ _), map_sum]

lemma val_sum_apply {ι : Type*} (s : Finset ι) (f : ι → AdicCompletion I M) (n : ℕ) :
    (∑ i ∈ s, f i).val n = ∑ i ∈ s, (f i).val n := by simp

variable (I M)

/-- The canonical linear map to the completion. -/
def of : M →ₗ[R] AdicCompletion I M where
  toFun x := ⟨fun n => mkQ (I ^ n • ⊤ : Submodule R M) x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval (n : ℕ) : AdicCompletion I M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) where
  toFun f := f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_eval (n : ℕ) :
    (eval I M n : AdicCompletion I M → M ⧸ (I ^ n • ⊤ : Submodule R M)) = fun f => f.1 n :=
  rfl

theorem eval_apply (n : ℕ) (f : AdicCompletion I M) : eval I M n f = f.1 n :=
  rfl

theorem eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl

@[simp]
theorem eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkQ _ :=
  rfl

theorem eval_surjective (n : ℕ) : Function.Surjective (eval I M n) := fun x ↦
  Quotient.inductionOn' x fun x ↦ ⟨of I M x, rfl⟩

@[simp]
theorem range_eval (n : ℕ) : LinearMap.range (eval I M n) = ⊤ :=
  LinearMap.range_eq_top.2 (eval_surjective I M n)

variable {I M}

variable (I M)

instance : IsHausdorff I (AdicCompletion I M) where
  haus' x h := ext fun n ↦ by
    refine smul_induction_on (SModEq.zero.1 <| h n) (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp only [val_smul_apply, val_zero]
      exact Quotient.inductionOn' (x.val n)
        (fun a ↦ SModEq.zero.2 <| smul_mem_smul hr mem_top)
    · simp only [val_add_apply, hx, val_zero_apply, hy, add_zero]

@[simp]
theorem transitionMap_comp_eval_apply {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I M) :
    transitionMap I M hmn (x.val n) = x.val m :=
  x.property hmn

@[simp]
theorem transitionMap_comp_eval {m n : ℕ} (hmn : m ≤ n) :
    transitionMap I M hmn ∘ₗ eval I M n = eval I M m := by
  ext x
  simp

/-- A sequence `ℕ → M` is an `I`-adic Cauchy sequence if for every `m ≤ n`,
`f m ≡ f n` modulo `I ^ m • ⊤`. -/
def IsAdicCauchy (f : ℕ → M) : Prop :=
  ∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]

/-- The type of `I`-adic Cauchy sequences. -/
def AdicCauchySequence : Type _ := { f : ℕ → M // IsAdicCauchy I M f }

namespace AdicCauchySequence

/-- The type of `I`-adic Cauchy sequences is a submodule of the product `ℕ → M`. -/
def submodule : Submodule R (ℕ → M) where
  carrier := { f | IsAdicCauchy I M f }
  add_mem' := by
    intro f g hf hg m n hmn
    exact SModEq.add (hf hmn) (hg hmn)
  zero_mem' := by
    intro _ _ _
    rfl
  smul_mem' := by
    intro r f hf m n hmn
    exact SModEq.smul (hf hmn) r

instance : Zero (AdicCauchySequence I M) where
  zero := ⟨0, fun _ ↦ rfl⟩

instance : Add (AdicCauchySequence I M) where
  add x y := ⟨x.val + y.val, fun hmn ↦ SModEq.add (x.property hmn) (y.property hmn)⟩

instance : Neg (AdicCauchySequence I M) where
  neg x := ⟨- x.val, fun hmn ↦ SModEq.neg (x.property hmn)⟩

instance : Sub (AdicCauchySequence I M) where
  sub x y := ⟨x.val - y.val, fun hmn ↦ SModEq.sub (x.property hmn) (y.property hmn)⟩

instance : SMul ℕ (AdicCauchySequence I M) where
  smul n x := ⟨n • x.val, fun hmn ↦ SModEq.nsmul (x.property hmn) n⟩

instance : SMul ℤ (AdicCauchySequence I M) where
  smul n x := ⟨n • x.val, fun hmn ↦ SModEq.zsmul (x.property hmn) n⟩

instance : AddCommGroup (AdicCauchySequence I M) := by
  let f : AdicCauchySequence I M → (ℕ → M) := Subtype.val
  apply Subtype.val_injective.addCommGroup f rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance : SMul R (AdicCauchySequence I M) where
  smul r x := ⟨r • x.val, fun hmn ↦ SModEq.smul (x.property hmn) r⟩

instance : Module R (AdicCauchySequence I M) :=
  let f : AdicCauchySequence I M →+ (ℕ → M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  Subtype.val_injective.module R f (fun _ _ ↦ rfl)

instance : CoeFun (AdicCauchySequence I M) (fun _ ↦ ℕ → M) where
  coe f := f.val

@[simp]
theorem zero_apply (n : ℕ) : (0 : AdicCauchySequence I M) n = 0 :=
  rfl

variable {I M}

@[simp]
theorem add_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f + g) n = f n + g n :=
  rfl

@[simp]
theorem sub_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f - g) n = f n - g n :=
  rfl

@[simp]
theorem smul_apply (n : ℕ) (r : R) (f : AdicCauchySequence I M) : (r • f) n = r • f n :=
  rfl

@[ext]
theorem ext {x y : AdicCauchySequence I M} (h : ∀ n, x n = y n) : x = y :=
  Subtype.eq <| funext h

/-- The defining property of an adic Cauchy sequence unwrapped. -/
theorem mk_eq_mk {m n : ℕ} (hmn : m ≤ n) (f : AdicCauchySequence I M) :
    Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (f n) =
      Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (f m) :=
  (f.property hmn).symm

end AdicCauchySequence

/-- The `I`-adic Cauchy condition can be checked on successive `n`. -/
theorem isAdicCauchy_iff (f : ℕ → M) :
    IsAdicCauchy I M f ↔ ∀ n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] := by
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

/-- Construct `I`-adic Cauchy sequence from sequence satisfying the successive Cauchy condition. -/
@[simps]
def AdicCauchySequence.mk (f : ℕ → M)
    (h : ∀ n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)]) : AdicCauchySequence I M where
  val := f
  property := by rwa [isAdicCauchy_iff]

/-- The canonical linear map from Cauchy sequences to the completion. -/
@[simps]
def mk : AdicCauchySequence I M →ₗ[R] AdicCompletion I M where
  toFun f := ⟨fun n ↦ Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (f n), by
    intro m n hmn
    simp only [mkQ_apply]
    exact (f.property hmn).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Criterion for checking that an adic Cauchy sequence is mapped to zero in the adic completion. -/
theorem mk_zero_of (f : AdicCauchySequence I M)
    (h : ∃ k : ℕ, ∀ n ≥ k, ∃ m ≥ n, ∃ l ≥ n, f m ∈ (I ^ l • ⊤ : Submodule R M)) :
    AdicCompletion.mk I M f = 0 := by
  obtain ⟨k, h⟩ := h
  ext n
  obtain ⟨m, hnm, l, hnl, hl⟩ := h (n + k) (by omega)
  rw [mk_apply_coe, Submodule.mkQ_apply, val_zero,
    ← AdicCauchySequence.mk_eq_mk (show n ≤ m by omega)]
  simpa using (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))) hl

/-- Every element in the adic completion is represented by a Cauchy sequence. -/
theorem mk_surjective : Function.Surjective (mk I M) := by
  intro x
  choose a ha using fun n ↦ Submodule.Quotient.mk_surjective _ (x.val n)
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro m n hmn
    rw [SModEq.def, ha m, ← mkQ_apply,
      ← factor_mk (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)) (a n),
      mkQ_apply, ha n, x.property hmn]
  · ext n
    simp [ha n]

/-- To show a statement about an element of `adicCompletion I M`, it suffices to check it
on Cauchy sequences. -/
theorem induction_on {p : AdicCompletion I M → Prop} (x : AdicCompletion I M)
    (h : ∀ (f : AdicCauchySequence I M), p (mk I M f)) : p x := by
  obtain ⟨f, rfl⟩ := mk_surjective I M x
  exact h f

variable {M}

/-- Lift a compatible family of linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)` to
the `I`-adic completion of `M`. -/
def lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m) :
    M →ₗ[R] AdicCompletion I N where
  toFun := fun x ↦ ⟨fun n ↦ f n x, fun hkl ↦ LinearMap.congr_fun (h hkl) x⟩
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' r x := by
    simp only [LinearMapClass.map_smul, RingHom.id_apply]
    rfl

@[simp]
lemma eval_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m)
    (n : ℕ) : eval I N n ∘ₗ lift I f h = f n :=
  rfl

@[simp]
lemma eval_lift_apply (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m)
    (n : ℕ) (x : M) : (lift I f h x).val n = f n x :=
  rfl

section Bijective

variable {I}

theorem injective_of_iff : Function.Injective (of I M) ↔ IsHausdorff I M := by
  constructor
  · refine fun h ↦ ⟨fun x hx ↦ h ?_⟩
    ext n
    simpa [of, SModEq.zero] using hx n
  · intro h
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    refine ⟨fun hx ↦ h.haus x fun n ↦ ?_, fun hx ↦ by simp [hx]⟩
    rw [Subtype.ext_iff] at hx
    simpa [SModEq.zero] using congrFun hx n

variable (I M) in
theorem injective_of [IsHausdorff I M] : Function.Injective (of I M) :=
  injective_of_iff.mpr ‹_›

theorem surjective_of_iff : Function.Surjective (of I M) ↔ IsPrecomplete I M := by
  constructor
  · refine fun h ↦ ⟨fun f hmn ↦ ?_⟩
    let u : AdicCompletion I M := ⟨fun n ↦ Submodule.Quotient.mk (f n), fun c ↦ (hmn c).symm⟩
    obtain ⟨x, hx⟩ := h u
    refine ⟨x, fun n ↦ ?_⟩
    simp only [SModEq]
    rw [← mkQ_apply _ x, ← eval_of, hx]
    simp [u]
  · intro h u
    choose x hx using (fun n ↦ Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R M) (u.1 n))
    obtain ⟨a, ha⟩ := h.prec (f := x) (fun hmn ↦ by rw [SModEq, hx, ← u.2 hmn, ← hx]; simp)
    use a
    ext n
    simpa [SModEq, ← eval_of, ha, ← hx] using (ha n).symm

variable (I M) in
theorem surjective_of [IsPrecomplete I M] : Function.Surjective (of I M) :=
  surjective_of_iff.mpr ‹_›

theorem bijective_of_iff : Function.Bijective (of I M) ↔ IsAdicComplete I M :=
  ⟨fun h ↦
    { toIsHausdorff := injective_of_iff.mp h.1,
      toIsPrecomplete := surjective_of_iff.mp h.2 },
   fun h ↦ ⟨injective_of_iff.mpr h.1, surjective_of_iff.mpr h.2⟩⟩

variable (I M) in
theorem bijective_of [IsAdicComplete I M] : Function.Bijective (of I M) :=
  bijective_of_iff.mpr ‹_›

variable (I M) in
/--
When `M` is `I`-adic complete, the canonical map from `M` to its `I`-adic completion is a linear
equivalence.
-/
def ofLinearEquiv [IsAdicComplete I M] : M ≃ₗ[R] AdicCompletion I M :=
  LinearEquiv.ofBijective (of I M) (bijective_of I M)

@[simp]
theorem ofLinearEquiv_apply [IsAdicComplete I M] (x : M) :
    ofLinearEquiv I M x = of I M x :=
  rfl

end Bijective

end AdicCompletion

namespace IsAdicComplete

open AdicCompletion

section lift

variable [IsAdicComplete I N]

variable {M}

/--
Universal property of `IsAdicComplete`.
The lift linear map `lift I f h : M →ₗ[R] N` of a sequence of compatible
linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
def lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) :
    M →ₗ[R] N := (ofLinearEquiv I N).symm ∘ₗ AdicCompletion.lift I f h

@[simp]
theorem of_lift_apply (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (x : M) :
    of I N (lift I f h x) = AdicCompletion.lift I f h x := by
  simp [lift, ofLinearEquiv]

@[simp]
theorem of_comp_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) :
    (of I N) ∘ₗ (lift I f h) = AdicCompletion.lift I f h := by
  ext1 x
  exact of_lift_apply I f h x

/--
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `M →ₗ[R] N ⧸ (I ^ n • ⊤)` is `f n` .
-/
@[simp]
theorem mk_lift_apply {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (n : ℕ) (x : M) :
    (Submodule.Quotient.mk (lift I f h x)) = f n x := by
  simp only [lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← mkQ_apply, ← eval_of]
  simp


@[simp]
theorem mkQ_comp_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (n : ℕ) :
    (mkQ (I ^ n • ⊤ : Submodule R N)) ∘ₗ (lift I f h) = f n := by
  ext
  exact mk_lift_apply I h n _

/--
Uniqueness of the lift.
Given a compatible family of linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
If `F : M →ₗ[R] N` makes the following diagram commutes
```
  N
  | \
 F|  \ f n
  |   \
  v    v
  M --> M ⧸ (I ^ a n • ⊤)
```
Then it is the map `IsAdicComplete.lift`.
-/
theorem eq_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) {F : M →ₗ[R] N}
    (hF : ∀ {m s}, Submodule.Quotient.mk (F s) = f m s) : F = lift I f h := by
  ext s
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simp [SModEq, hF, mk_lift_apply]

end lift

namespace StrictMono

variable {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ (a n) • ⊤ : Submodule R N))

variable {I M}
/--
Instead of providing all `M →ₗ[R] N ⧸ (I ^ n • ⊤)`, one can just provide
`M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)` for a strictly increasing sequence `a n` to recover all
`M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
def extend (n : ℕ) :
    M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  (factorPow I N (ha.id_le n)) ∘ₗ f n

variable (hf : ∀ {m}, factorPow I N (ha.monotone m.le_succ) ∘ₗ (f (m + 1)) = f m)

include hf in
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq
    {m n : ℕ} (hle : m ≤ n) : factorPow I N (ha.monotone hle) ∘ₗ f n = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n ↦ f n x) ?_ m n hle
  · exact fun _ _ le ↦ smul_mono_left (Ideal.pow_le_pow_right (ha.monotone le))
  · intro s
    simp only [LinearMap.ext_iff] at hf
    simpa using (hf x).symm

include hf in
theorem extend_eq (n : ℕ) : extend ha f (a n) = f n :=
  factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf (ha.id_le n)

include hf in
theorem factorPow_comp_extend {m n : ℕ} (hle : m ≤ n) :
    factorPow I N hle ∘ₗ extend ha f n = extend ha f m := by
  ext
  simp [extend, ← factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf hle]

variable [IsAdicComplete I N]

variable (I)
/--
A variant of `IsAdicComplete.lift`. Only takes `f n : M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)`
from a strictly increasing sequence `a n`.
-/
def lift : M →ₗ[R] N :=
  IsAdicComplete.lift I (extend ha f) (factorPow_comp_extend ha f hf)

theorem of_lift_apply (x : M) :
    of I N (lift I ha f hf x) =
    AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) x :=
  IsAdicComplete.of_lift_apply I (extend ha f) (factorPow_comp_extend ha f hf) x

theorem of_comp_lift :
    (of I N) ∘ₗ (lift I ha f hf) =
      AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) :=
  IsAdicComplete.of_comp_lift I (extend ha f) (factorPow_comp_extend ha f hf)

@[simp]
theorem mk_lift_apply {n : ℕ} (x : M) :
    (Submodule.Quotient.mk (lift I ha f hf x)) = f n x := by
  simp only [lift, IsAdicComplete.lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← mkQ_apply, ← eval_of]
  simp [extend_eq ha f hf]

@[simp]
theorem mkQ_comp_lift {n : ℕ} :
    mkQ (I ^ (a n) • ⊤ : Submodule R N) ∘ₗ (lift I ha f hf) = f n := by
  ext
  exact mk_lift_apply I ha f hf _

theorem eq_lift {F : M →ₗ[R] N}
    (hF : ∀ {m s}, Submodule.Quotient.mk (F s) = f m s) : F = lift I ha f hf := by
  ext s
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (smul_mono_left (Ideal.pow_le_pow_right (ha.id_le n)))
  simp [SModEq, hF, mk_lift_apply I ha f hf]

end StrictMono

instance bot : IsAdicComplete (⊥ : Ideal R) M where

protected theorem subsingleton (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M :=
  h.1.subsingleton

instance (priority := 100) of_subsingleton [Subsingleton M] : IsAdicComplete I M where

open Finset

theorem le_jacobson_bot [IsAdicComplete I R] : I ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  rw [← Ideal.neg_mem_iff, Ideal.mem_jacobson_bot]
  intro y
  rw [add_comm]
  let f : ℕ → R := fun n => ∑ i ∈ range n, (x * y) ^ i
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
  rw [isUnit_iff_exists_inv]
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
  · simp only [Ideal.one_eq_top, pow_zero, mem_top]
  · rw [← neg_sub _ (1 : R), neg_mul, mul_geom_sum, neg_sub, sub_sub, add_comm (_ ^ _), ← sub_sub,
      sub_self, zero_sub, @neg_mem_iff, mul_pow]
    exact Ideal.mul_mem_right _ (I ^ _) (Ideal.pow_mem_pow hx _)

end IsAdicComplete
