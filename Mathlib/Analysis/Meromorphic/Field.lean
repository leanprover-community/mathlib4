/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.RingTheory.Derivation.Basic

/-!
# The field of a meromorphic functions

This file defines `MeromorphicFun`, the field of (equivalent classes of) functions `𝕜 → E`
meromorphic on `U`, denoted as `𝕜 →ℳ[U] E` (or `𝕜 →ℳ E` when `U = Set.univ`).
Meromorphic functions with pointwise equality is too large to be a field, so we construct the field
on the quotient by `=ᶠ[codiscreteWithin U]` instead.

A `MeromorphicFun` itself can also apply as a function, which acts as the normal form of the
equivalent class: on accumulation points in `U`, this is exactly the `toMeromorphicNFOn f U` of any
member `f` in the class. However, its value is not specified outside of `U` or at isolated points.
-/

@[expose] public section

open Topology WithTop Filter

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f g : 𝕜 → E} {f₂ : 𝕜 → E₂} {U : Set 𝕜}
  {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E] [SMulCommClass 𝕜 R E]

variable (E U) in
/-- The equivalence of meromorphic functions `𝕜 → E` by `=ᶠ[codiscreteWithin U]`. -/
def MeromorphicFun.setoid : Setoid {f : 𝕜 → E // MeromorphicOn f U} where
  r := (·.val =ᶠ[codiscreteWithin U] ·.val)
  iseqv := {
    refl _ := rfl.eventuallyEq
    symm h := h.symm
    trans h₁ h₂ := h₁.trans h₂
  }

variable (E U) in
/-- Equivalence classes of meromorphic functions `𝕜 → E`, denoted as `𝕜 →ℳ[U] E` (or `𝕜 →ℳ E`
when `U = Set.univ`). -/
def MeromorphicFun := Quotient (MeromorphicFun.setoid E U)

@[inherit_doc MeromorphicFun]
notation:25 α " →ℳ[" U "] " β => MeromorphicFun β (U : Set α)

@[inherit_doc MeromorphicFun]
notation:25 α " →ℳ " β => MeromorphicFun β (Set.univ : Set α)

namespace MeromorphicFun

/-- Get the `MeromophicFun` of a meromorphic function. -/
def mk (f : 𝕜 → E) (hf : MeromorphicOn f U) : 𝕜 →ℳ[U] E := Quotient.mk _ ⟨f, hf⟩

/-- Choose a representative function. This is only for intermediate definition. Use the
`FunLike` coercion for a better representative that is `MeromorphicNFOn`. -/
noncomputable def out (f : 𝕜 →ℳ[U] E) : 𝕜 → E := (Quotient.out f).val

theorem meromorphicOn_out (f : 𝕜 →ℳ[U] E) : MeromorphicOn f.out U := (Quotient.out f).prop

@[simp]
theorem mk_out (f : 𝕜 →ℳ[U] E) : mk f.out f.meromorphicOn_out = f := Quotient.out_eq f

theorem out_mk_eventuallyEq {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    (mk f hf).out =ᶠ[codiscreteWithin U] f :=
  Quotient.mk_out ⟨f, hf⟩ (s := setoid E U)

@[simp]
theorem mk_eq_mk (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    mk f hf = mk g hg ↔ f =ᶠ[codiscreteWithin U] g := Quotient.eq

/-- Lift a function on meromorphic functions to `MeromophicFun` -/
def lift {α : Type*} (F : {f : 𝕜 → E // MeromorphicOn f U} → α)
    (h : ∀ f g : {f : 𝕜 → E // MeromorphicOn f U},
    f.val =ᶠ[codiscreteWithin U] g.val → F f = F g) :
    (𝕜 →ℳ[U] E) → α :=
  Quotient.lift F h

@[simp]
theorem lift_mk {α : Type*} (F : {f : 𝕜 → E // MeromorphicOn f U} → α)
    (h : ∀ f g : {f : 𝕜 → E // MeromorphicOn f U},
    f.val =ᶠ[codiscreteWithin U] g.val → F f = F g) (hf : MeromorphicOn f U) :
    lift F h (mk f hf) = F ⟨f, hf⟩ :=
  rfl

/-- Lift a binary function on meromorphic functions to `MeromophicFun`. -/
def lift₂ {α : Type*} (F : {f : 𝕜 → E // MeromorphicOn f U} → {f : 𝕜 → E₂ // MeromorphicOn f U} → α)
    (h : ∀ f₁ g₁ f₂ g₂,
    f₁.val =ᶠ[codiscreteWithin U] f₂.val → g₁.val =ᶠ[codiscreteWithin U] g₂.val →
    F f₁ g₁ = F f₂ g₂) :
    (𝕜 →ℳ[U] E) → (𝕜 →ℳ[U] E₂) → α :=
  Quotient.lift₂ F h

@[simp]
theorem lift₂_mk {α : Type*}
    (F : {f : 𝕜 → E // MeromorphicOn f U} → {f : 𝕜 → E₂ // MeromorphicOn f U} → α)
    (h : ∀ f₁ g₁ f₂ g₂,
    f₁.val =ᶠ[codiscreteWithin U] f₂.val → g₁.val =ᶠ[codiscreteWithin U] g₂.val →
    F f₁ g₁ = F f₂ g₂) (hf : MeromorphicOn f U) (hf₂ : MeromorphicOn f₂ U) :
    lift₂ F h (mk f hf) (mk f₂ hf₂) = F ⟨f, hf⟩ ⟨f₂, hf₂⟩ :=
  rfl

/-- The induction principal for `MeromophicFun`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem ind {motive : (𝕜 →ℳ[U] E) → Prop} (mk : ∀ f hf, motive (mk f hf)) :
    ∀ f, motive f := Quotient.ind (fun f ↦ mk f.val f.prop)

/-! ## Normal form -/

/-- Choose a `MeromorphicNFOn` representative function. Do not use this directly. Use the coercion
from `FunLike` instead. -/
noncomputable
def toNF (f : 𝕜 →ℳ[U] E) : 𝕜 → E := toMeromorphicNFOn f.out U

private theorem toNF_mk_eventuallyEq (hf : MeromorphicOn f U) :
    (mk f hf).toNF =ᶠ[codiscreteWithin U] f := by
  simpa [toNF] using (toMeromorphicNFOn_eqOn_codiscrete (mk f hf).meromorphicOn_out).symm.trans <|
    out_mk_eventuallyEq hf

/-- We create a `FunLike` instance for `MeromorphicFun` so it can be directly used as a
function. This function is `MeromorphicNFOn`, and its value is canonically defined to equal to
`toMeromorphicNFOn` of any member in the equivalence class for all accumulation points in `U`.
See `MeromorphicFun.apply_eq` and `MeromorphicFun.coe_eq_toMeromorphicNFOn` that characterizes this.
-/
noncomputable
instance : FunLike (𝕜 →ℳ[U] E) 𝕜 E where
  coe := toNF
  coe_injective f g h := by
    cases f with | mk f hf
    cases g with | mk g hg
    rw [mk_eq_mk]
    apply (toNF_mk_eventuallyEq hf).symm.trans
    rw [h]
    exact (toNF_mk_eventuallyEq hg)

theorem meromorphicNFOn_coeFn (f : 𝕜 →ℳ[U] E) : MeromorphicNFOn f U :=
  meromorphicNFOn_toMeromorphicNFOn f.out U

theorem meromorphicOn_coeFn (f : 𝕜 →ℳ[U] E) : MeromorphicOn f U :=
  f.meromorphicNFOn_coeFn.meromorphicOn

@[fun_prop]
theorem meromorphic_coeFn (f : 𝕜 →ℳ E) : Meromorphic f := by
  simpa using f.meromorphicOn_coeFn

theorem coeFn_mk_eventuallyEq (hf : MeromorphicOn f U) : mk f hf =ᶠ[codiscreteWithin U] f :=
  toNF_mk_eventuallyEq hf

@[ext]
theorem ext {f g : 𝕜 →ℳ[U] E} (h : f =ᶠ[codiscreteWithin U] g) : f = g := by
  cases f with | mk f hf
  cases g with | mk g hg
  grw [mk_eq_mk, ← coeFn_mk_eventuallyEq hf, ← coeFn_mk_eventuallyEq hg]
  exact h

@[simp]
theorem mk_coeFn (f : 𝕜 →ℳ[U] E) : mk f f.meromorphicOn_coeFn = f := by
  cases f with | mk f hf
  simpa using coeFn_mk_eventuallyEq hf

theorem apply_eq (hf : MeromorphicOn f U) {x : 𝕜} (hx : x ∈ U) (hacc : AccPt x (𝓟 U)) :
    mk f hf x = toMeromorphicNFOn f U x := by
  let g := (mk f hf).out
  have hg : MeromorphicOn g U := (mk f hf).meromorphicOn_out
  change toMeromorphicNFOn g U x = toMeromorphicNFOn f U x
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hg hx]
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf hx]
  apply toMeromorphicNFAt_congr
  exact MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
    (hg x hx) (hf x hx) hx hacc (out_mk_eventuallyEq hf)

theorem apply_eq_self (hf : MeromorphicOn f U) {x : 𝕜} (hx : x ∈ U)
    (h : MeromorphicNFAt f x) (hacc : AccPt x (𝓟 U)) :
    mk f hf x = f x := by
  rw [apply_eq hf hx hacc, toMeromorphicNFOn_eq_toMeromorphicNFAt hf hx,
    toMeromorphicNFAt_eq_self.mpr h]

theorem coeFn_eq_toMeromorphicNFOn (hf : MeromorphicOn f Set.univ) :
    mk f hf = toMeromorphicNFOn f Set.univ :=
  funext <| fun x ↦ apply_eq hf (Set.mem_univ x) <| PerfectSpace.univ_preperfect x (Set.mem_univ x)

theorem coeFn_eq_self (hf : MeromorphicNFOn f Set.univ) : mk f hf.meromorphicOn = f :=
  funext <| fun x ↦ apply_eq_self hf.meromorphicOn (Set.mem_univ x) (hf (Set.mem_univ x))
    <| PerfectSpace.univ_preperfect x (Set.mem_univ x)

/-! ## Composition with meromorphic-preserving functions -/

/-- Composition with a unary operator. -/
def comp (o : E → E₂) (h : ∀ f, MeromorphicOn f U → MeromorphicOn (o ∘ f) U) (f : 𝕜 →ℳ[U] E) :
    𝕜 →ℳ[U] E₂ :=
  lift (fun f ↦ mk (o ∘ f.val) (h f.val f.prop))
    (fun f g h ↦ by simpa using EventuallyEq.fun_comp h o) f

@[simp]
theorem comp_mk (o : E → E₂) (h : ∀ f, MeromorphicOn f U → MeromorphicOn (o ∘ f) U)
    (hf : MeromorphicOn f U) :
    (mk f hf).comp o h = mk (o ∘ f) (h f hf) :=
  rfl

theorem coeFn_comp (o : E → E₂) (h : ∀ f, MeromorphicOn f U → MeromorphicOn (o ∘ f) U)
    (f : 𝕜 →ℳ[U] E) :
    ⇑(f.comp o h) =ᶠ[codiscreteWithin U] o ∘ f := by
  cases f with | mk f hf
  rw [comp_mk]
  apply (coeFn_mk_eventuallyEq _).trans
  exact EventuallyEq.fun_comp (coeFn_mk_eventuallyEq hf).symm _

/-- Composition with a binary operator. -/
def comp₂ (o : E → E₂ → E₃)
    (h : ∀ f g, MeromorphicOn f U → MeromorphicOn g U → MeromorphicOn (fun x ↦ o (f x) (g x)) U)
    (f : 𝕜 →ℳ[U] E) (g : 𝕜 →ℳ[U] E₂) :
    𝕜 →ℳ[U] E₃ :=
  lift₂ (fun f g ↦ mk (fun x ↦ o (f.val x) (g.val x)) (h f.val g.val f.prop g.prop))
    (fun f₁ g₁ f₂ g₂ hf hg ↦ by simpa using Filter.EventuallyEq.comp₂ hf o hg) f g

theorem comp₂_mk (o : E → E₂ → E₃)
    (h : ∀ f g, MeromorphicOn f U → MeromorphicOn g U → MeromorphicOn (fun x ↦ o (f x) (g x)) U)
    (hf : MeromorphicOn f U) (hf₂ : MeromorphicOn f₂ U) :
    (mk f hf).comp₂ o h (mk f₂ hf₂) = mk (fun x ↦ o (f x) (f₂ x)) (h f f₂ hf hf₂) :=
  rfl

theorem coeFn_comp₂ (o : E → E₂ → E₃)
    (h : ∀ f g, MeromorphicOn f U → MeromorphicOn g U → MeromorphicOn (fun x ↦ o (f x) (g x)) U)
    (f : 𝕜 →ℳ[U] E) (g : 𝕜 →ℳ[U] E₂) :
    ⇑(f.comp₂ o h g) =ᶠ[codiscreteWithin U] fun x ↦ o (f x) (g x):= by
  cases f with | mk f hf
  cases g with | mk g hg
  rw [comp₂_mk]
  apply (coeFn_mk_eventuallyEq _).trans
  exact EventuallyEq.comp₂ (coeFn_mk_eventuallyEq hf).symm _ (coeFn_mk_eventuallyEq hg).symm

/-! ## Order -/

open Classical in
/-- The meromorphic order at a point `x` for `MeromorphicFun E U`. If the point is outside of `U`,
or it is not `AccPt x (𝓟 U)`, we return the junk value 0. -/
noncomputable
def orderAt (f : 𝕜 →ℳ[U] E) (x : 𝕜) : WithTop ℤ :=
  if hx : x ∈ U ∧ AccPt x (𝓟 U) then
    lift (fun f ↦ meromorphicOrderAt f.val x) (fun f g h ↦ meromorphicOrderAt_congr <|
      (f.prop x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (g.prop x hx.1)
      hx.1 hx.2 h) f
  else
    0

theorem orderAt_of_notMem (f : 𝕜 →ℳ[U] E) {x : 𝕜} (hx : x ∉ U) : f.orderAt x = 0 := by
  simp [orderAt, hx]

theorem orderAt_of_not_accPt (f : 𝕜 →ℳ[U] E) {x : 𝕜} (hx : ¬ AccPt x (𝓟 U)) : f.orderAt x = 0 := by
  simp [orderAt, hx]

theorem orderAt_of_not_mem_and_accPt (f : 𝕜 →ℳ[U] E) {x : 𝕜} (hx : ¬ (x ∈ U ∧ AccPt x (𝓟 U))) :
    f.orderAt x = 0 := by
  simp [orderAt, hx]

theorem orderAt_mk (hf : MeromorphicOn f U) {x : 𝕜} (hx : x ∈ U) (hacc : AccPt x (𝓟 U)) :
    (mk f hf).orderAt x = meromorphicOrderAt f x := by
  simp [orderAt, hx, hacc]

@[simp]
theorem orderAt_mk_univ (hf : MeromorphicOn f Set.univ) :
    (mk f hf).orderAt = meromorphicOrderAt f := by
  ext x
  rw [orderAt_mk hf (Set.mem_univ x) (PerfectSpace.univ_preperfect x (Set.mem_univ x))]

theorem orderAt_eq_meromorphicOrder_coeFn (f : 𝕜 →ℳ[U] E) {x : 𝕜} (hx : x ∈ U)
    (hacc : AccPt x (𝓟 U)) :
    f.orderAt x = meromorphicOrderAt f x := by
  cases f with | mk f hf
  rw [orderAt_mk hf hx hacc]
  exact meromorphicOrderAt_congr <|
    (hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin (meromorphicOn_coeFn _ x hx)
    hx hacc (coeFn_mk_eventuallyEq hf).symm

theorem orderAt_eq_meromorphicOrder_coeFn_univ (f : 𝕜 →ℳ E) : f.orderAt = meromorphicOrderAt f := by
  ext x
  rw [f.orderAt_eq_meromorphicOrder_coeFn (Set.mem_univ x)
    (PerfectSpace.univ_preperfect x (Set.mem_univ x))]

theorem orderAt_eq_zero_iff {f : 𝕜 →ℳ[U] E} {x : 𝕜} (hx : x ∈ U) (hacc : AccPt x (𝓟 U)) :
    f.orderAt x = 0 ↔ f x ≠ 0 := by
  rw [f.orderAt_eq_meromorphicOrder_coeFn hx hacc,
    (f.meromorphicNFOn_coeFn hx).meromorphicOrderAt_eq_zero_iff]

theorem orderAt_eq_zero_iff_univ {f : 𝕜 →ℳ E} {x : 𝕜} : f.orderAt x = 0 ↔ f x ≠ 0 :=
  f.orderAt_eq_zero_iff (Set.mem_univ x) (PerfectSpace.univ_preperfect x (Set.mem_univ x))

theorem orderAt_nonneg_iff_analyticAt {f : 𝕜 →ℳ[U] E} {x : 𝕜} (hx : x ∈ U) (hacc : AccPt x (𝓟 U)) :
    0 ≤ f.orderAt x ↔ AnalyticAt 𝕜 f x := by
  rw [f.orderAt_eq_meromorphicOrder_coeFn hx hacc,
    (f.meromorphicNFOn_coeFn hx).meromorphicOrderAt_nonneg_iff_analyticAt]

theorem orderAt_nonneg_iff_analyticAt_univ {f : 𝕜 →ℳ E} {x : 𝕜} :
    0 ≤ f.orderAt x ↔ AnalyticAt 𝕜 f x :=
  f.orderAt_nonneg_iff_analyticAt (Set.mem_univ x) (PerfectSpace.univ_preperfect x (Set.mem_univ x))

/-! ## Add -/

instance : Add (𝕜 →ℳ[U] E) where
  add := comp₂ Add.add fun _ _ hf hg ↦ hf.add hg

theorem mk_add_mk (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    mk f hf + mk g hg = mk (f + g) (hf.add hg) :=
  rfl

theorem coeFn_add (f g : 𝕜 →ℳ[U] E) : ⇑(f + g) =ᶠ[codiscreteWithin U] f + g :=
  coeFn_comp₂ _ _ f g

theorem orderAt_add (f g : 𝕜 →ℳ[U] E) (x : 𝕜) :
    min (f.orderAt x) (g.orderAt x) ≤ (f + g).orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2]
    convert meromorphicOrderAt_add (f.meromorphicOn_coeFn x hx.1) (g.meromorphicOn_coeFn x hx.1)
      using 1
    apply meromorphicOrderAt_congr
    exact ((f + g).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      ((f.meromorphicOn_coeFn x hx.1).add (g.meromorphicOn_coeFn x hx.1)) hx.1 hx.2 (f.coeFn_add g)
  · simp [orderAt_of_not_mem_and_accPt _ hx]

theorem orderAt_add_eq_left_of_lt {f g : 𝕜 →ℳ[U] E} {x : 𝕜} (h : f.orderAt x < g.orderAt x) :
    (f + g).orderAt x = f.orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2] at ⊢ h
    convert meromorphicOrderAt_add_eq_left_of_lt (g.meromorphicOn_coeFn x hx.1) h
      using 1
    apply meromorphicOrderAt_congr
    exact ((f + g).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      ((f.meromorphicOn_coeFn x hx.1).add (g.meromorphicOn_coeFn x hx.1)) hx.1 hx.2 (f.coeFn_add g)
  · simp [orderAt_of_not_mem_and_accPt _ hx]

theorem orderAt_add_eq_right_of_lt {f g : 𝕜 →ℳ[U] E} {x : 𝕜} (h : g.orderAt x < f.orderAt x) :
    (f + g).orderAt x = g.orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2] at ⊢ h
    convert meromorphicOrderAt_add_eq_right_of_lt (f.meromorphicOn_coeFn x hx.1) h
      using 1
    apply meromorphicOrderAt_congr
    exact ((f + g).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      ((f.meromorphicOn_coeFn x hx.1).add (g.meromorphicOn_coeFn x hx.1)) hx.1 hx.2 (f.coeFn_add g)
  · simp [orderAt_of_not_mem_and_accPt _ hx]

theorem orderAt_add_of_ne {f g : 𝕜 →ℳ[U] E} {x : 𝕜} (h : f.orderAt x ≠ g.orderAt x) :
    (f + g).orderAt x = min (f.orderAt x) (g.orderAt x) := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2] at ⊢ h
    convert meromorphicOrderAt_add_of_ne (f.meromorphicOn_coeFn x hx.1)
      (g.meromorphicOn_coeFn x hx.1) h using 1
    apply meromorphicOrderAt_congr
    exact ((f + g).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      ((f.meromorphicOn_coeFn x hx.1).add (g.meromorphicOn_coeFn x hx.1)) hx.1 hx.2 (f.coeFn_add g)
  · simp [orderAt_of_not_mem_and_accPt _ hx]

instance : Zero (𝕜 →ℳ[U] E) where
  zero := mk 0 (.const 0)

theorem zero_def : (0 : 𝕜 →ℳ[U] E) = mk 0 (.const 0) := rfl

theorem coeFn_zero : ⇑(0 : 𝕜 →ℳ[U] E) =ᶠ[codiscreteWithin U] 0 :=
  coeFn_mk_eventuallyEq _

theorem orderAt_zero {x : 𝕜} (hx : x ∈ U) (hacc : AccPt x (𝓟 U)) :
    (0 : 𝕜 →ℳ[U] E).orderAt x = ⊤ := by
  simp [zero_def, orderAt_mk _ hx hacc, meromorphicOrderAt_eq_top_iff]

/-! ## Neg / Sub -/

instance : Neg (𝕜 →ℳ[U] E) where
  neg := comp Neg.neg fun _ h ↦ h.neg

theorem neg_mk (hf : MeromorphicOn f U) : -mk f hf = mk (-f) hf.neg :=
  rfl

theorem coeFn_neg (f : 𝕜 →ℳ[U] E) : ⇑(-f) =ᶠ[codiscreteWithin U] -f:=
  coeFn_comp _ _ f

@[simp]
theorem orderAt_neg (f : 𝕜 →ℳ[U] E) (x : 𝕜) : (-f).orderAt x = f.orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2]
    refine Eq.trans ?_ meromorphicOrderAt_neg.symm
    apply meromorphicOrderAt_congr
    exact ((-f).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      (f.meromorphicOn_coeFn x hx.1).neg hx.1 hx.2 f.coeFn_neg
  · simp [orderAt_of_not_mem_and_accPt _ hx]

instance : Sub (𝕜 →ℳ[U] E) where
  sub := comp₂ Sub.sub fun _ _ hf hg ↦ hf.sub hg

theorem mk_sub_mk (hf : MeromorphicOn f U) (hg : MeromorphicOn g U) :
    mk f hf - mk g hg = mk (f - g) (hf.sub hg)  :=
  rfl

theorem coeFn_sub (f g : 𝕜 →ℳ[U] E) : ⇑(f - g) =ᶠ[codiscreteWithin U] f - g :=
  coeFn_comp₂ _ _ f g

instance : NSMul (𝕜 →ℳ[U] E) where
  nsmul := nsmulRec

instance : ZSMul (𝕜 →ℳ[U] E) where
  zsmul := zsmulRec

instance : AddCommGroup (𝕜 →ℳ[U] E) where
  zero_add f := by
    cases f with | mk f hf
    simp [zero_def, mk_add_mk]
  add_zero f := by
    cases f with | mk f hf
    simp [zero_def, mk_add_mk]
  add_assoc f g h := by
    cases f with | mk f hf
    cases g with | mk g hg
    cases h with | mk h hh
    simp [mk_add_mk, add_assoc]
  add_comm f g := by
    cases f with | mk f hf
    cases g with | mk g hg
    simp [mk_add_mk, add_comm]
  sub_eq_add_neg f g := by
    cases f with | mk f hf
    cases g with | mk g hg
    simp [mk_sub_mk, neg_mk, mk_add_mk, sub_eq_add_neg]
  neg_add_cancel f := by
    cases f with | mk f hf
    simp [neg_mk, mk_add_mk, zero_def]

/-! ## SMul -/

instance : SMul R (𝕜 →ℳ[U] E) where
  smul c := comp (c • ·) fun _ h ↦ h.const_smul c

theorem smul_mk (hf : MeromorphicOn f U) (c : R) : c • mk f hf = mk (c • f) (hf.const_smul c) :=
  rfl

theorem coeFn_smul (f : 𝕜 →ℳ[U] E) (c : R) : ⇑(c • f) =ᶠ[codiscreteWithin U] c • f:=
  coeFn_comp _ _ f

instance : Module R (𝕜 →ℳ[U] E) where
  mul_smul c d f := by
    cases f with | mk f hf
    simp [smul_mk, mul_smul]
  one_smul f := by
    cases f with | mk f hf
    simp [smul_mk]
  smul_zero c := by
    simp [zero_def, smul_mk]
  zero_smul f := by
    cases f with | mk f hf
    simp [smul_mk, zero_def]
  smul_add c f g := by
    cases f with | mk f hf
    cases g with | mk g hg
    simp [mk_add_mk, smul_mk]
  add_smul c d f := by
    cases f with | mk f hf
    simp [smul_mk, add_smul, mk_add_mk]

/-! ## One -/

instance [One E] : AddCommGroupWithOne (𝕜 →ℳ[U] E) where
  one := mk 1 (.const 1)

theorem one_def [One E] : (1 : 𝕜 →ℳ[U] E) = mk 1 (.const 1) := rfl

theorem coeFn_one [One E] : ⇑(1 : 𝕜 →ℳ[U] E) =ᶠ[codiscreteWithin U] 1 :=
  coeFn_mk_eventuallyEq _

@[simp]
theorem orderAt_one [One E] [NeZero (1 : E)] (x : 𝕜) : (1 : 𝕜 →ℳ[U] E).orderAt x = 0 := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · classical
    simp [one_def, orderAt_mk _ hx.1 hx.2, Pi.one_def, meromorphicOrderAt_const]
  · simp [orderAt_of_not_mem_and_accPt _ hx]

theorem natCast_eq (n : ℕ) : (n : 𝕜 →ℳ[U] 𝕜') = mk (n : 𝕜 → 𝕜') (.const (n : 𝕜')) := by
  induction n with
  | zero =>
    simp [zero_def, Pi.zero_def]
  | succ n ih =>
    simp only [Nat.cast_add, ih, Nat.cast_one, one_def, mk_add_mk]

@[simp]
theorem orderAt_natCast {n : ℕ} (hn : (n : 𝕜') ≠ 0) (x : 𝕜) : (n : 𝕜 →ℳ[U] 𝕜').orderAt x = 0 := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · classical
    simpa [natCast_eq, orderAt_mk _ hx.1 hx.2, Pi.natCast_def, meromorphicOrderAt_const,] using hn
  · simp [orderAt_of_not_mem_and_accPt _ hx]

/-! ## Mul -/

instance : Mul (𝕜 →ℳ[U] 𝕜') where
  mul := comp₂ Mul.mul fun _ _ hf hg ↦ hf.mul hg

theorem mk_mul_mk {f : 𝕜 → 𝕜'} (hf : MeromorphicOn f U) {g : 𝕜 → 𝕜'} (hg : MeromorphicOn g U) :
    mk f hf * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl

theorem coeFn_mul (f g : 𝕜 →ℳ[U] 𝕜') : ⇑(f * g) =ᶠ[codiscreteWithin U] f * g :=
  coeFn_comp₂ _ _ f g

theorem orderAt_mul (f g : 𝕜 →ℳ[U] 𝕜') (x : 𝕜) : (f * g).orderAt x = f.orderAt x + g.orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2]
    refine Eq.trans ?_ <|
      meromorphicOrderAt_mul (f.meromorphicOn_coeFn x hx.1) (g.meromorphicOn_coeFn x hx.1)
    apply meromorphicOrderAt_congr
    exact ((f * g).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      ((f.meromorphicOn_coeFn x hx.1).mul (g.meromorphicOn_coeFn x hx.1)) hx.1 hx.2 (f.coeFn_mul g)
  · simp [orderAt_of_not_mem_and_accPt _ hx]

instance : NPow (𝕜 →ℳ[U] 𝕜') where
  npow n := comp (· ^ n) fun _ h ↦ h.pow n

theorem mk_pow {f : 𝕜 → 𝕜'} (hf : MeromorphicOn f U) (n : ℕ) :
    mk f hf ^ n = mk (f ^ n) (hf.pow n) :=
  rfl

theorem coeFn_pow (f : 𝕜 →ℳ[U] 𝕜') (n : ℕ) : ⇑(f ^ n) =ᶠ[codiscreteWithin U] f ^ n :=
  coeFn_comp _ _ f

theorem orderAt_pow (f : 𝕜 →ℳ[U] 𝕜') (n : ℕ) (x : 𝕜) : (f ^ n).orderAt x = n * f.orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2]
    refine Eq.trans ?_ <| meromorphicOrderAt_pow (f.meromorphicOn_coeFn x hx.1)
    apply meromorphicOrderAt_congr
    exact ((f ^ n).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      ((f.meromorphicOn_coeFn x hx.1).pow n) hx.1 hx.2 (f.coeFn_pow n)
  · simp [orderAt_of_not_mem_and_accPt _ hx]

instance : CommRing (𝕜 →ℳ[U] 𝕜') where
  one_mul f := by
    cases f with | mk f hf
    simp [one_def, mk_mul_mk]
  mul_one f := by
    cases f with | mk f hf
    simp [one_def, mk_mul_mk]
  zero_mul f := by
    cases f with | mk f hf
    simp [zero_def, mk_mul_mk]
  mul_zero f := by
    cases f with | mk f hf
    simp [zero_def, mk_mul_mk]
  mul_assoc f g h := by
    cases f with | mk f hf
    cases g with | mk g hg
    cases h with | mk h hh
    simp [mk_mul_mk, mul_assoc]
  left_distrib f g h := by
    cases f with | mk f hf
    cases g with | mk g hg
    cases h with | mk h hh
    simp [mk_mul_mk, mk_add_mk, mul_add]
  right_distrib f g h := by
    cases f with | mk f hf
    cases g with | mk g hg
    cases h with | mk h hh
    simp [mk_mul_mk, mk_add_mk, add_mul]
  mul_comm f g := by
    cases f with | mk f hf
    cases g with | mk g hg
    simp [mk_mul_mk, mul_comm]
  npow_zero f := by
    cases f with | mk f hf
    simp [one_def, mk_pow]
  npow_succ n f := by
    cases f with | mk f hf
    simp [pow_succ, mk_mul_mk, mk_pow]

variable {R : Type*} [NormedCommRing R] [Algebra R 𝕜'] [IsBoundedSMul R 𝕜'] [SMulCommClass 𝕜 R 𝕜']

instance : Algebra R (𝕜 →ℳ[U] 𝕜') where
  algebraMap := {
    toFun c := mk (algebraMap R (𝕜 → 𝕜') c) (.const (algebraMap R 𝕜' c))
    map_zero' := by simp [zero_def]
    map_add' f g := by
      simp_rw [map_add]
      apply mk_add_mk
      · exact MeromorphicOn.const (algebraMap R 𝕜' f)
      · exact MeromorphicOn.const (algebraMap R 𝕜' g)
    map_one' := by simp [one_def]
    map_mul' f g := by
      simp_rw [map_mul]
      apply mk_mul_mk
      · exact MeromorphicOn.const (algebraMap R 𝕜' f)
      · exact MeromorphicOn.const (algebraMap R 𝕜' g)
  }
  commutes' c f := by
    cases f with | mk f hf
    simp [mul_comm]
  smul_def' c f := by
    cases f with | mk f hf
    simp_rw [smul_mk, Pi.smul_def, Algebra.smul_def]
    apply mk_mul_mk
    · exact MeromorphicOn.const (algebraMap R 𝕜' c)
    · exact hf

theorem algebraMap_def (c : R) :
    algebraMap R (𝕜 →ℳ[U] 𝕜') c =
    mk (algebraMap R (𝕜 → 𝕜') c) (.const (algebraMap R 𝕜' c)) :=
  rfl

theorem coeFn_algebraMap (c : R) :
    ⇑(algebraMap R (𝕜 →ℳ[U] 𝕜') c) =ᶠ[codiscreteWithin U] (algebraMap R (𝕜 → 𝕜') c) :=
  coeFn_mk_eventuallyEq _

/-! ## Inv / Div -/

instance : Inv (𝕜 →ℳ[U] 𝕜') where
  inv := comp Inv.inv fun _ h ↦ h.inv

theorem inv_mk {f : 𝕜 → 𝕜'} (hf : MeromorphicOn f U) :
    (mk f hf)⁻¹ = mk f⁻¹ hf.inv :=
  rfl

@[simp]
theorem inv_zero : (0 : 𝕜 →ℳ[U] 𝕜')⁻¹ = 0 := by
  simp [zero_def, inv_mk, Pi.inv_def, Pi.zero_def]

theorem coeFn_inv (f : 𝕜 →ℳ[U] 𝕜') : ⇑(f⁻¹) =ᶠ[codiscreteWithin U] f⁻¹ :=
  coeFn_comp _ _ f

@[simp]
theorem orderAt_inv (f : 𝕜 →ℳ[U] 𝕜) (x : 𝕜) : (f⁻¹).orderAt x = -f.orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2]
    refine Eq.trans ?_ meromorphicOrderAt_inv
    apply meromorphicOrderAt_congr
    exact ((f⁻¹).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      (f.meromorphicOn_coeFn x hx.1).inv hx.1 hx.2 f.coeFn_inv
  · simp [orderAt_of_not_mem_and_accPt _ hx]

instance : Div (𝕜 →ℳ[U] 𝕜') where
  div := comp₂ Div.div fun _ _ hf hg ↦ hf.div hg

theorem mk_div_mk {f : 𝕜 → 𝕜'} (hf : MeromorphicOn f U) {g : 𝕜 → 𝕜'} (hg : MeromorphicOn g U) :
    mk f hf / mk g hg = mk (f / g) (hf.div hg) :=
  rfl

theorem coeFn_div (f g : 𝕜 →ℳ[U] 𝕜') : ⇑(f / g) =ᶠ[codiscreteWithin U] f / g :=
  coeFn_comp₂ _ _ f g

theorem orderAt_div (f g : 𝕜 →ℳ[U] 𝕜') (x : 𝕜) : (f / g).orderAt x = f.orderAt x - g.orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2]
    refine Eq.trans ?_ <|
      meromorphicOrderAt_div (f.meromorphicOn_coeFn x hx.1) (g.meromorphicOn_coeFn x hx.1)
    apply meromorphicOrderAt_congr
    exact ((f / g).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      ((f.meromorphicOn_coeFn x hx.1).div (g.meromorphicOn_coeFn x hx.1)) hx.1 hx.2 (f.coeFn_div g)
  · simp [orderAt_of_not_mem_and_accPt _ hx]

@[simp]
theorem div_zero (f : 𝕜 →ℳ[U] 𝕜') : f / 0 = 0 := by
  cases f with | mk f hf
  simp [zero_def, mk_div_mk, Pi.div_def, Pi.zero_def]

instance : ZPow (𝕜 →ℳ[U] 𝕜') where
  zpow n := comp (· ^ n) fun _ h ↦ h.zpow n

theorem mk_zpow {f : 𝕜 → 𝕜'} (hf : MeromorphicOn f U) (n : ℤ) :
    (mk f hf) ^ n = mk (f ^ n) (hf.zpow n) :=
  rfl

theorem coeFn_zpow (f : 𝕜 →ℳ[U] 𝕜') (n : ℤ) : ⇑(f ^ n) =ᶠ[codiscreteWithin U] f ^ n :=
  coeFn_comp _ _ f

theorem orderAt_zpow (f : 𝕜 →ℳ[U] 𝕜') (n : ℤ) (x : 𝕜) :
    (f ^ n).orderAt x = n * f.orderAt x := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · simp_rw [orderAt_eq_meromorphicOrder_coeFn _ hx.1 hx.2]
    refine Eq.trans ?_ <| meromorphicOrderAt_zpow (f.meromorphicOn_coeFn x hx.1)
    apply meromorphicOrderAt_congr
    exact ((f ^ n).meromorphicOn_coeFn x hx.1).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      ((f.meromorphicOn_coeFn x hx.1).zpow n) hx.1 hx.2 (f.coeFn_zpow n)
  · simp [orderAt_of_not_mem_and_accPt _ hx]

instance : DivInvOneMonoid (𝕜 →ℳ[U] 𝕜') where
  div_eq_mul_inv f g := by
    cases f with | mk f hf
    cases g with | mk g hg
    simp [mk_div_mk, inv_mk, mk_mul_mk, div_eq_mul_inv]
  inv_one := by simp [one_def, inv_mk]
  zpow_zero' f := by
    cases f with | mk f hf
    simp [one_def, mk_zpow]
  zpow_succ' n f := by
    cases f with | mk f hf
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, zpow_natCast, mk_mul_mk, mk_eq_mk,
      mk_zpow]
    apply EventuallyEq.of_eq
    ext x
    by_cases h : f x = 0
    · simp [h, zero_zpow_eq]
      grind
    · simp [zpow_add_one₀ h]
  zpow_neg' n f := by
    cases f with | mk f hf
    simp only [zpow_negSucc, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, inv_mk, mk_eq_mk,
      mk_zpow]
    apply EventuallyEq.of_eq
    simp only [inv_inj]
    norm_cast

/-- All meromorphic functions on a nontrivial preconnected domain form a field. -/
@[implicit_reducible]
def field (hnontrivial : U.Nontrivial) (hc : IsPreconnected U) : Field (𝕜 →ℳ[U] 𝕜') where
  nnqsmul := _
  qsmul := _
  exists_pair_ne := by
    use 0, 1
    simpa [zero_def, one_def, EventuallyEq, hc.isDiscrete_iff_subsingleton] using hnontrivial
  mul_inv_cancel f h := by
    cases f with | mk f hf
    simp only [inv_mk, mk_mul_mk, one_def, mk_eq_mk]
    exact hf.mul_inv_eventuallyEq hc (by simpa [zero_def] using h)
  inv_zero := by
    simp only [zero_def, inv_mk, mk_eq_mk]
    apply Eventually.of_forall
    simp

instance [PreconnectedSpace 𝕜] : Field (𝕜 →ℳ 𝕜') :=
  field (Set.nontrivial_univ_iff.mpr inferInstance) (preconnectedSpace_iff_univ.mp ‹_›)

/-! ## Derivative -/

/-- Derivative of the meromorphic function. -/
protected noncomputable
def deriv [CompleteSpace E] : (𝕜 →ℳ[U] E) →ₗ[𝕜] (𝕜 →ℳ[U] E) where
  toFun := lift (fun f ↦ mk (deriv f.val) f.prop.deriv) (fun f g h ↦ by
    simpa using MeromorphicOn.deriv_eventuallyEq_codiscreteWithin f.prop g.prop h)
  map_add' f g := by
    cases f with | mk f hf
    cases g with | mk g hg
    simp only [mk_add_mk, lift_mk, mk_eq_mk]
    filter_upwards [hf.eventually_codiscreteWithin_analyticAt,
      hg.eventually_codiscreteWithin_analyticAt] with x hf hg
      using deriv_add hf.differentiableAt hg.differentiableAt
  map_smul' c f := by
    cases f with | mk f hf
    simp only [smul_mk, lift_mk, RingHom.id_apply, mk_eq_mk]
    filter_upwards [hf.eventually_codiscreteWithin_analyticAt] with x hf
      using deriv_const_smul c hf.differentiableAt

theorem deriv_mk [CompleteSpace E] {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    (mk f hf).deriv = mk (deriv f) hf.deriv := by
  rfl

theorem coeFn_deriv [CompleteSpace E] (f : 𝕜 →ℳ[U] E) :
    f.deriv =ᶠ[codiscreteWithin U] deriv f := by
  cases f with | mk f hf
  rw [deriv_mk]
  apply (coeFn_mk_eventuallyEq _).trans
  apply MeromorphicOn.deriv_eventuallyEq_codiscreteWithin hf (meromorphicOn_coeFn _)
  exact (coeFn_mk_eventuallyEq hf).symm

@[simp]
theorem deriv_natCast [CompleteSpace 𝕜'] (n : ℕ) : (n : 𝕜 →ℳ[U] 𝕜').deriv = 0 := by
  simp [natCast_eq, deriv_mk, zero_def]

@[simp]
theorem deriv_one [CompleteSpace E] [One E] : (1 : 𝕜 →ℳ[U] E).deriv = 0 := by
  simp [one_def, deriv_mk, zero_def]

@[simp]
theorem deriv_algebraMap [CompleteSpace 𝕜'] (c : R) : (algebraMap R (𝕜 →ℳ[U] 𝕜') c).deriv = 0 := by
  simp [algebraMap_def, deriv_mk, Pi.algebraMap_def, ← Pi.zero_def, zero_def]

/-- `MeromorphicFun.deriv` as a `Derivation`. -/
noncomputable
def derivation [CompleteSpace 𝕜'] : Derivation 𝕜 (𝕜 →ℳ[U] 𝕜') (𝕜 →ℳ[U] 𝕜') where
  __ := MeromorphicFun.deriv
  map_one_eq_zero' := deriv_one
  leibniz' f g := by
    cases f with | mk f hf
    cases g with | mk g hg
    simp only [smul_eq_mul, mk_mul_mk, deriv_mk, mk_add_mk, mk_eq_mk]
    filter_upwards [hf.eventually_codiscreteWithin_analyticAt,
      hg.eventually_codiscreteWithin_analyticAt] with x hf hg
    rw [add_comm, mul_comm g]
    simpa using deriv_mul hf.differentiableAt hg.differentiableAt

@[simp]
theorem derivation_apply [CompleteSpace 𝕜'] (f : 𝕜 →ℳ[U] 𝕜') : derivation f = f.deriv := rfl

protected theorem deriv_mul [CompleteSpace 𝕜'] (f g : 𝕜 →ℳ[U] 𝕜') :
    (f * g).deriv = f.deriv * g + f * g.deriv := by
  rw [← derivation_apply, derivation.leibniz f g]
  simp_rw [derivation_apply, smul_eq_mul]
  ring

protected theorem deriv_pow [CompleteSpace 𝕜'] (f : 𝕜 →ℳ[U] 𝕜') (n : ℕ) :
    (f ^ n).deriv = n * f ^ (n - 1) * f.deriv := by
  simp [← derivation_apply, ← mul_assoc]

protected theorem deriv_inv [CompleteSpace 𝕜'] (f : 𝕜 →ℳ[U] 𝕜') :
    (f⁻¹).deriv = -f.deriv / f ^ 2 := by
  -- One might want to use `Derivation.leibniz_inv`, but the theorem here is slightly more general:
  -- `𝕜 →ℳ[U] 𝕜'` is not required to be connected, and thus not necessarily a field.
  cases f with | mk f hf
  simp only [inv_mk, deriv_mk, neg_mk, mk_pow, mk_div_mk, mk_eq_mk]
  filter_upwards [hf.eventually_codiscreteWithin_analyticAt] with x hf
  by_cases h0 : f x = 0
  · suffices deriv f⁻¹ x = 0 by simpa [h0]
    by_cases hnhds : f =ᶠ[𝓝 x] 0
    · rw [hnhds.inv.deriv_eq]
      simp [Pi.inv_def]
    simp_rw [EventuallyEq, Pi.zero_apply] at hnhds
    have hnhds : ∀ᶠ z in 𝓝[≠] x, f z ≠ 0 :=
      hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left hnhds
    have htop : meromorphicOrderAt f x ≠ ⊤ :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf.meromorphicAt).mpr hnhds
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    have hpos : 0 < meromorphicOrderAt f x := by
      rw [← tendsto_zero_iff_meromorphicOrderAt_pos hf.meromorphicAt, ← h0]
      exact (hf.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hcobounded : Tendsto f⁻¹ (𝓝[≠] x) (Bornology.cobounded 𝕜') := by
      rw [tendsto_cobounded_iff_meromorphicOrderAt_neg hf.meromorphicAt.inv, meromorphicOrderAt_inv]
      rw [← hn] at ⊢ hpos
      norm_cast at ⊢ hpos
      simpa using hpos
    refine deriv_zero_of_not_differentiableAt fun h ↦ ?_
    have htendsto : Tendsto f⁻¹ (𝓝[≠] x) (𝓝 0) := by
      simpa [h0] using h.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact htendsto.not_tendsto (Metric.disjoint_nhds_cobounded 0) hcobounded
  rw [inv_eq_one_div, deriv_div (by fun_prop) hf.differentiableAt h0]
  simp

protected theorem deriv_div [CompleteSpace 𝕜'] (f g : 𝕜 →ℳ[U] 𝕜') :
    (f / g).deriv = (f.deriv * g - f * g.deriv) / g ^ 2 := by
  suffices MeromorphicFun.deriv f * g⁻¹ = MeromorphicFun.deriv f * (g * (g ^ 2)⁻¹) by
    simpa [div_eq_mul_inv, f.deriv_mul, g.deriv_inv, ← sub_eq_add_neg, sub_mul, mul_assoc]
  congrm MeromorphicFun.deriv f * ?_
  cases g with | mk g hg
  simp only [inv_mk, mk_pow, mk_mul_mk, mk_eq_mk]
  refine Eventually.of_forall fun x ↦ ?_
  simp
  field

protected theorem deriv_zpow [CompleteSpace 𝕜'] (f : 𝕜 →ℳ[U] 𝕜') (n : ℤ) :
    (f ^ n).deriv = n * f ^ (n - 1) * f.deriv := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, f.deriv_pow, Int.cast_natCast]
    cases n with
    | zero => simp
    | succ n => simp
  | negSucc n =>
    cases f with | mk f hf
    simp only [zpow_negSucc, MeromorphicFun.deriv_inv, MeromorphicFun.deriv_pow, Nat.cast_add,
      Nat.cast_one, add_tsub_cancel_right, deriv_mk, Int.cast_negSucc, neg_add_rev,
      Int.negSucc_sub_one]
    simp only [natCast_eq, one_def, mk_add_mk, mk_pow, mk_mul_mk, neg_mk, mk_div_mk, inv_mk,
      mk_eq_mk]
    refine Eventually.of_forall fun x ↦ ?_
    by_cases h0 : f x = 0
    · simp [h0]
    simp
    field

theorem orderAt_deriv [CompleteSpace E] {f : 𝕜 →ℳ[U] E} {x : 𝕜} {n : ℤ} (hn : (↑(n + 1) : 𝕜) ≠ 0)
    (horder : f.orderAt x = ↑(n + 1)) :
    f.deriv.orderAt x = ↑n := by
  by_cases hx : x ∈ U ∧ AccPt x (𝓟 U)
  · cases f with | mk f hf
    simp_rw [deriv_mk, orderAt_mk _ hx.1 hx.2]
    rw [orderAt_mk _ hx.1 hx.2] at horder
    exact meromorphicOrderAt_deriv hn horder
  · rw [f.orderAt_of_not_mem_and_accPt hx, zero_eq_coe] at horder
    simp [horder] at hn

end MeromorphicFun
