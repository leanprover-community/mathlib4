/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Implicit function theorem

In this file, we apply the generalised implicit function theorem to the more familiar case and show
that the implicit function preserves the smoothness class of the implicit equation.

Let `E`, `F`, and `G` be real or complex Banach spaces. Let `f : E × F → G` be a function that is
$C^n$ at a point `(a, b) : E × F`, where `n ≥ 1`. Let `f'` be the derivative of `f` at `(a, b)`. If
the map `y ↦ f' (0, y)` is a Banach space isomorphism, then there exists a function `φ : E → F` such
that `φ a = b`, and `f x (φ x) = f a b` holds for all `x` in a neighbourhood of `a`. Furthermore,
`φ` is $C^n$ at `a`.

## TODO
* Local uniqueness of the implicit function
* Derivative of the implicit function

## Tags

implicit function, inverse function
-/

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

namespace ImplicitFunctionData

/-- The implicit function defined by a $C^n$ implicit equation is $C^n$. This applies to the general
form of the implicit function theorem. -/
theorem contDiff_implicitFunction {φ : ImplicitFunctionData 𝕜 E F G} {n : WithTop ℕ∞}
    (hl : ContDiffAt 𝕜 n φ.leftFun φ.pt) (hr : ContDiffAt 𝕜 n φ.rightFun φ.pt) (hn : 1 ≤ n) :
    ContDiffAt 𝕜 n φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
  rw [implicitFunction, Function.uncurry_curry, toOpenPartialHomeomorph,
    ← HasStrictFDerivAt.localInverse_def]
  exact (hl.prodMk hr).to_localInverse (φ.hasStrictFDerivAt |>.hasFDerivAt) hn

end ImplicitFunctionData

open Filter

open LinearMap (ker range)

open scoped Topology

/-- A predicate stating the sufficient conditions on an implicit equation `f : E × F → F` that will
lead to a $C^n$ implicit function `φ : E → F`. -/
structure IsContDiffImplicitAt (n : WithTop ℕ∞) (f : E × F → G) (f' : E × F →L[𝕜] G) (a : E × F) :
    Prop where
  hasFDerivAt : HasFDerivAt f f' a
  contDiffAt : ContDiffAt 𝕜 n f a
  bijective : Function.Bijective (f'.comp (ContinuousLinearMap.inr 𝕜 E F))
  one_le : 1 ≤ n

namespace IsContDiffImplicitAt

variable
  {n : WithTop ℕ∞} {f : E × F → G} {f' : E × F →L[𝕜] G} {a : E × F}

/-- We record the parameters of our specific case in order to apply the general implicit function
theorem. -/
def implicitFunctionData (h : IsContDiffImplicitAt n f f' a) :
    ImplicitFunctionData 𝕜 (E × F) E G where
  leftFun := Prod.fst
  leftDeriv := ContinuousLinearMap.fst 𝕜 E F
  rightFun := f
  rightDeriv := f'
  pt := a
  hasStrictFDerivAt_leftFun := by fun_prop
  hasStrictFDerivAt_rightFun := h.contDiffAt.hasStrictFDerivAt' h.hasFDerivAt h.one_le
  range_leftDeriv := LinearMap.range_eq_top_of_surjective _ fun x ↦ ⟨(x, 0), rfl⟩
  range_rightDeriv := by
    apply top_unique
    rw [← LinearMap.range_eq_top_of_surjective _ h.bijective.surjective]
    exact LinearMap.range_comp_le_range _ _
  isCompl_ker := by
    apply IsCompl.of_eq
    · ext x
      rw [Submodule.mem_inf, Submodule.mem_bot, LinearMap.mem_ker, ContinuousLinearMap.coe_fst',
        LinearMap.mem_ker]
      constructor
      · intro ⟨h1, h2⟩
        rw [← Prod.mk.eta (p := x), h1] at h2
        rw [Prod.ext_iff]
        refine ⟨h1, h.bijective.injective ?_⟩
        simp [h2, map_zero]
      · rintro rfl
        exact ⟨rfl, map_zero _⟩
    · ext x
      simp only [Submodule.mem_sup, Submodule.mem_top, iff_true]
      obtain ⟨y, hy⟩ := h.bijective.surjective (f' x)
      exact ⟨(0, y), by simp, x - (0, y), by simp [map_sub, ← hy], by abel⟩

@[simp]
lemma implicitFunctionData_pt (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.pt = a := rfl

@[simp]
lemma implicitFunctionData_leftFun_pt (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.leftFun a = a.1 := rfl

@[simp]
lemma implicitFunctionData_rightFun_pt (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunctionData.rightFun a = f a := rfl

/-- The implicit function provided by the general theorem, from which we construct the more useful
form `IsContDiffImplicitAt.implicitFunction`. -/
noncomputable def implicitFunctionAux (h : IsContDiffImplicitAt n f f' a) : E → G → E × F :=
  h.implicitFunctionData.implicitFunction

lemma implicitFunctionAux_fst (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ p in 𝓝 (a.1, f a), (h.implicitFunctionAux p.1 p.2).1 = p.1 :=
  h.implicitFunctionData.prod_map_implicitFunction.mono fun _ ↦ congr_arg Prod.fst

lemma comp_implicitFunctionAux_eq_snd (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ p in 𝓝 (a.1, f a), f (h.implicitFunctionAux p.1 p.2) = p.2 :=
  h.implicitFunctionData.prod_map_implicitFunction.mono fun _ ↦ congr_arg Prod.snd

/-- Implicit function `φ` defined by `f (x, φ x) = f a`. -/
noncomputable def implicitFunction (h : IsContDiffImplicitAt n f f' a) : E → F :=
  fun x ↦ (h.implicitFunctionAux x (f a)).2

lemma implicitFunction_def (h : IsContDiffImplicitAt n f f' a) :
    h.implicitFunction = fun x ↦ (h.implicitFunctionData.implicitFunction.uncurry (x, (f a))).2 :=
  rfl

/-- `implicitFunction` is indeed the (local) implicit function defined by `f`. -/
lemma apply_implicitFunction (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ x in 𝓝 a.1, f (x, h.implicitFunction x) = f a := by
  have := h.comp_implicitFunctionAux_eq_snd
  have hfst := h.implicitFunctionAux_fst
  rw [nhds_prod_eq, eventually_swap_iff] at this hfst
  apply this.curry.self_of_nhds.mp
  apply hfst.curry.self_of_nhds.mono
  simp_rw [Prod.swap_prod_mk]
  intro x h1 h2
  rw [← h2]
  congr 1
  ext
  · rw [h1]
  · rfl

/-
ImplicitContDiff:
leftFun : E × F → E
rightFun : E × F → G
pt : E × F := (a, b)
φ : E → F

Show φ is locally unique.

For all (x, y) close to a, if f (x, y) = f a, then y = φ x.

E := E × F
F := E
G := G
f : E × F → E := Prod.fst
g : E × F → G := f
a : E × F := a
φ : E → G → E × F := h.implicitFunctionAux

Lemma to apply:
For all (y, z) close to (f a, g a) and for all x close to a,
(f x = y and g x = z) implies x = φ y z

Our variables:
For all (x, z) close to (a.1, f a) and for all xy close to a,
(xy.1 = x and f xy = z) implies xy = h.implicitFunctionAux x z

Specialise to z = f a
For all x close to a.1 and for all xy close to a,
(xy.1 = x and f xy = f a) implies xy = h.implicitFunctionAux x (f a)

Specialise to xy.1 = x
For all x close to a.1 and for all y close to a.2,
f (x, y) = f a implies (x, y) = h.implicitFunctionAux x (f a)

Use def
For all x close to a.1 and for all y close to a.2,
f (x, y) = f a implies y = h.implicitFunction x

-----

(E × F) × E × G
(E × F) × G × E
E × F × G × E
F × G × E × E
(F × G) × E × E

-/

-- theorem Tendsto.eventually_congr {α β : Type*} {f : α → β} {l₁ : Filter α} {l₂ : Filter β}
--     {p : β → Prop} {q : α → Prop} (hf : Tendsto f l₁ l₂) (hiff : ∀ᶠ x in l₁, q x ↔ p (f x))
--     (h : ∀ᶠ y in l₂, p y) : ∀ᶠ x in l₁, q x := by
--   rw [Filter.eventually_congr hiff]
--   exact Filter.Tendsto.eventually hf h

theorem eventually_assoc_iff {α β γ : Type*}
    {f : Filter α} {g : Filter β} {h : Filter γ} {p : (α × β) × γ → Prop} :
    (∀ᶠ x : (α × β) × γ in (f ×ˢ g) ×ˢ h, p x) ↔
      ∀ᶠ y : α × β × γ in f ×ˢ g ×ˢ h, p ((y.1, y.2.1), y.2.2) := by
  rw [← prod_assoc]; rfl

theorem eventually_assoc_symm_iff {α β γ : Type*}
    {f : Filter α} {g : Filter β} {h : Filter γ} {p : α × β × γ → Prop} :
    (∀ᶠ x : α × β × γ in f ×ˢ g ×ˢ h, p x) ↔
      ∀ᶠ y : (α × β) × γ in (f ×ˢ g) ×ˢ h, p (y.1.1, y.1.2, y.2) := by
  rw [← prod_assoc_symm]; rfl

theorem eventually_swap4_prod_iff {α β γ δ : Type*}
    {f : Filter α} {g : Filter β} {h : Filter γ} {k : Filter δ} {p : (α × β) × γ × δ → Prop} :
    (∀ᶠ x : (α × β) × γ × δ in (f ×ˢ g) ×ˢ h ×ˢ k, p x) ↔
      ∀ᶠ y : (α × γ) × β × δ in (f ×ˢ h) ×ˢ g ×ˢ k, p ((y.1.1, y.2.1), y.1.2, y.2.2) := by
  rw [← map_swap4_prod]; rfl

theorem implicitFunction_unique (h : IsContDiffImplicitAt n f f' a) :
    ∀ᶠ xy in 𝓝 a, f xy = f a → xy.2 = h.implicitFunction xy.1 := by
  have := h.implicitFunctionData.eq_implicitFunction_of_prodFun_eq
  have hnhds :
      𝓝 (h.implicitFunctionData.pt, h.implicitFunctionData.prodFun h.implicitFunctionData.pt) =
        (𝓝 a.1 ×ˢ 𝓝 a.2) ×ˢ 𝓝 a.1 ×ˢ 𝓝 (f a) := by
    rw [implicitFunctionData_pt, ImplicitFunctionData.prodFun_apply,
      implicitFunctionData_leftFun_pt, implicitFunctionData_rightFun_pt, nhds_prod_eq, nhds_prod_eq,
      nhds_prod_eq]
  rw [hnhds, eventually_swap4_prod_iff] at this
  replace := Filter.Eventually.diag_of_prod_left this
  rw [eventually_assoc_symm_iff, ← nhds_prod_eq] at this
  dsimp only at this
  replace := this.curry
  filter_upwards [this] with xy hxy heq
  replace hxy := hxy.self_of_nhds
  rw [implicitFunction, implicitFunctionAux, ← hxy]
  rw [ImplicitFunctionData.prodFun_apply]
  ext
  · rfl
  · rw [← heq]
    rfl

/-- If the implicit equation `f` is $C^n$ at `(x, y)`, then its implicit function `φ` around `x` is
also $C^n$ at `x`. -/
theorem contDiffAt_implicitFunction (h : IsContDiffImplicitAt n f f' a) :
    ContDiffAt 𝕜 n h.implicitFunction a.1 := by
  have := h.implicitFunctionData.contDiff_implicitFunction contDiffAt_fst h.contDiffAt h.one_le
  rw [implicitFunction_def]
  fun_prop

end IsContDiffImplicitAt
