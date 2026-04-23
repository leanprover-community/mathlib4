/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Prod
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem. First we define a structure
`ImplicitFunctionData` that holds arguments for the most general version of the implicit function
theorem, see `ImplicitFunctionData.implicitFunction` and
`ImplicitFunctionData.hasStrictFDerivAt_implicitFunction`. This version allows a user to choose a
specific implicit function but provides only a little convenience over the inverse function theorem.

Then we define `HasStrictFDerivAt.implicitFunctionDataOfComplemented`: implicit function defined by
`f (g z y) = z`, where `f : E → F` is a function strictly differentiable at `a` such that its
derivative `f'` is surjective and has a `complemented` kernel.

Finally, if the codomain of `f` is a finite-dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `HasStrictFDerivAt`
and `f'.range = ⊤`. This version is named `HasStrictFDerivAt.implicitFunction`.

For the version where the implicit equation is defined by a $C^n$ function `f : E × F → G` with an
invertible derivative `∂f/∂y`, see `ContDiffAt.implicitFunction`.

## TODO

* Add a version for `f : 𝕜 × 𝕜 → 𝕜` proving `HasStrictDerivAt` and `deriv φ = ...`.
* Prove that in a real vector space the implicit function has the same smoothness as the original
  one.
* If the original function is differentiable in a neighborhood, then the implicit function is
  differentiable in a neighborhood as well. Current setup only proves differentiability at one
  point for the implicit function constructed in this file (as opposed to an unspecified implicit
  function). One of the ways to overcome this difficulty is to use uniqueness of the implicit
  function in the general version of the theorem. Another way is to prove that *any* implicit
  function satisfying some predicate is strictly differentiable.

## Tags

implicit function, inverse function
-/

public section

noncomputable section

open scoped Topology

open Filter

open ContinuousLinearMap (fst snd smulRight ker_prod)

open ContinuousLinearEquiv (ofBijective)

open LinearMap (ker range)

/-!
### General version

Consider two functions `f : E → F` and `g : E → G` and a point `a` such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`.

Note that the map `x ↦ (f x, g x)` has a bijective derivative, hence it is an open partial
homeomorphism between `E` and `F × G`. We use this fact to define a function `φ : F → G → E`
(see `ImplicitFunctionData.implicitFunction`) such that for `(y, z)` close enough to `(f a, g a)`
we have `f (φ y z) = y` and `g (φ y z) = z`. We also prove a formula for `∂φ / ∂z`.

Though this statement is almost symmetric with respect to `F`, `G`, we interpret it in the following
way. Consider a family of surfaces `{x | f x = y}`, `y ∈ 𝓝 (f a)`. Each of these surfaces is
parametrized by `φ y`.

There are many ways to choose a (differentiable) function `φ` such that `f (φ y z) = y` but the
extra condition `g (φ y z) = z` allows a user to select one of these functions. If we imagine
that the level surfaces `f = const` form a local horizontal foliation, then the choice of
`g` fixes a transverse foliation `g = const`, and `φ` is the inverse function of the projection
of `{x | f x = y}` along this transverse foliation.

This version of the theorem is used to prove the other versions and can be used if a user
needs to have a complete control over the choice of the implicit function.
-/


/-- Data for the general version of the implicit function theorem. It holds two functions
`f : E → F` and `g : E → G` (named `leftFun` and `rightFun`) and a point `a` (named `pt`) such that

* both functions are strictly differentiable at `a`;
* the derivatives are surjective;
* the kernels of the derivatives are complementary subspaces of `E`. -/
structure ImplicitFunctionData (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace G] where
  /-- Left function -/
  leftFun : E → F
  /-- Derivative of the left function -/
  leftDeriv : E →L[𝕜] F
  /-- Right function -/
  rightFun : E → G
  /-- Derivative of the right function -/
  rightDeriv : E →L[𝕜] G
  /-- The point at which `leftFun` and `rightFun` are strictly differentiable -/
  pt : E
  hasStrictFDerivAt_leftFun : HasStrictFDerivAt leftFun leftDeriv pt
  hasStrictFDerivAt_rightFun : HasStrictFDerivAt rightFun rightDeriv pt
  range_leftDeriv : leftDeriv.range = ⊤
  range_rightDeriv : rightDeriv.range = ⊤
  isCompl_ker : IsCompl leftDeriv.ker rightDeriv.ker

namespace ImplicitFunctionData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G)

/-- The function given by `x ↦ (leftFun x, rightFun x)`. -/
def prodFun (x : E) : F × G :=
  (φ.leftFun x, φ.rightFun x)

@[simp]
theorem prodFun_apply (x : E) : φ.prodFun x = (φ.leftFun x, φ.rightFun x) := by
  rfl

protected theorem hasStrictFDerivAt :
    HasStrictFDerivAt φ.prodFun
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.range_leftDeriv φ.range_rightDeriv
          φ.isCompl_ker :
        E →L[𝕜] F × G)
      φ.pt :=
  φ.hasStrictFDerivAt_leftFun.prodMk φ.hasStrictFDerivAt_rightFun

theorem isInvertible_fderiv_prodFun : (fderiv 𝕜 φ.prodFun φ.pt).IsInvertible := by
  rw [φ.hasStrictFDerivAt.hasFDerivAt.fderiv]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `x ↦ (f x, g x)` defines an open partial homeomorphism between
`E` and `F × G`. In particular, `{x | f x = f a}` is locally homeomorphic to `G`. -/
def toOpenPartialHomeomorph : OpenPartialHomeomorph E (F × G) :=
  φ.hasStrictFDerivAt.toOpenPartialHomeomorph _

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `implicitFunction` is the unique (germ of a) map
`φ : F → G → E` such that `f (φ y z) = y` and `g (φ y z) = z`. -/
def implicitFunction : F → G → E :=
  Function.curry <| φ.toOpenPartialHomeomorph.symm

theorem implicitFunction_def :
    implicitFunction φ = Function.curry (φ.hasStrictFDerivAt.toOpenPartialHomeomorph _).symm := by
  rfl

lemma implicitFunction_apply {x : F} {y : G} :
    φ.implicitFunction x y = φ.toOpenPartialHomeomorph.symm (x, y) := by
  rfl

@[simp]
theorem toOpenPartialHomeomorph_coe : ⇑φ.toOpenPartialHomeomorph = φ.prodFun := by
  rfl

theorem toOpenPartialHomeomorph_apply (x : E) :
    φ.toOpenPartialHomeomorph x = (φ.leftFun x, φ.rightFun x) := by
  rfl

theorem pt_mem_toOpenPartialHomeomorph_source : φ.pt ∈ φ.toOpenPartialHomeomorph.source :=
  φ.hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source

theorem map_pt_mem_toOpenPartialHomeomorph_target :
    (φ.leftFun φ.pt, φ.rightFun φ.pt) ∈ φ.toOpenPartialHomeomorph.target :=
  φ.toOpenPartialHomeomorph.map_source <| φ.pt_mem_toOpenPartialHomeomorph_source

theorem prodFun_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prodFun (φ.implicitFunction p.1 p.2) = p :=
  φ.hasStrictFDerivAt.eventually_right_inverse.mono fun ⟨_, _⟩ h => h

@[deprecated (since := "2026-01-27")]
alias prod_map_implicitFunction := prodFun_implicitFunction

theorem leftFun_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.leftFun (φ.implicitFunction p.1 p.2) = p.1 :=
  φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.fst

@[deprecated (since := "2026-01-27")]
alias left_map_implicitFunction := leftFun_implicitFunction

theorem rightFun_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.rightFun (φ.implicitFunction p.1 p.2) = p.2 :=
  φ.prodFun_implicitFunction.mono fun _ => congr_arg Prod.snd

@[deprecated (since := "2026-01-27")]
alias right_map_implicitFunction := rightFun_implicitFunction

theorem implicitFunction_apply_image :
    ∀ᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.leftFun x) (φ.rightFun x) = x :=
  φ.hasStrictFDerivAt.eventually_left_inverse

theorem leftFun_implicitFunction_eq_leftFun : ∀ᶠ x in 𝓝 φ.pt,
    φ.leftFun (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.leftFun φ.pt := by
  have := φ.leftFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

theorem rightFun_implicitFunction_eq_rightFun : ∀ᶠ x in 𝓝 φ.pt,
    φ.rightFun (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.rightFun x := by
  have := φ.rightFun_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

theorem leftFun_eq_iff_implicitFunction : ∀ᶠ x in 𝓝 φ.pt,
    φ.leftFun x = φ.leftFun φ.pt ↔ φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x) = x := by
  filter_upwards [φ.implicitFunction_apply_image, φ.leftFun_implicitFunction_eq_leftFun] with x _ _
  constructor <;> exact fun h => by rwa [← h]

theorem map_nhds_eq : map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt) :=
  show map (Prod.fst ∘ φ.prodFun) (𝓝 φ.pt) = 𝓝 (φ.prodFun φ.pt).1 by
    rw [← map_map, φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, map_fst_nhds]

/-- The implicit function is strictly differentiable. -/
theorem hasStrictFDerivAt_implicitFunction_fderiv :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt))
      (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt)) (φ.rightFun φ.pt) := by
  have := φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  convert this
  exact this.hasFDerivAt.fderiv

theorem differentiableAt_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) :
    DifferentiableAt 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) :=
  φ.hasStrictFDerivAt_implicitFunction_fderiv.hasFDerivAt.differentiableAt

theorem fderiv_implicitFunction_apply_eq_iff (φ : ImplicitFunctionData 𝕜 E F G) {x : G} {y : E} :
    fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x = y ↔
      φ.leftDeriv y = 0 ∧ φ.rightDeriv y = x := by
  unfold implicitFunction Function.curry toOpenPartialHomeomorph
  simp only [← HasStrictFDerivAt.localInverse_def]
  rw [φ.hasStrictFDerivAt.to_localInverse.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _)) |>.hasFDerivAt |>.fderiv]
  simp [ContinuousLinearEquiv.symm_apply_eq, @eq_comm _ (φ.leftDeriv _),
    @eq_comm _ (φ.rightDeriv _)]

@[simp]
theorem leftDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : G) :
    φ.leftDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x) = 0 := by
  exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl |>.left

@[simp]
theorem rightDeriv_fderiv_implicitFunction (φ : ImplicitFunctionData 𝕜 E F G) (x : G) :
    φ.rightDeriv (fderiv 𝕜 (φ.implicitFunction (φ.leftFun φ.pt)) (φ.rightFun φ.pt) x) = x := by
  exact φ.fderiv_implicitFunction_apply_eq_iff.mp rfl |>.right

theorem hasStrictFDerivAt_implicitFunction (g'inv : G →L[𝕜] E)
    (hg'inv : φ.rightDeriv.comp g'inv = ContinuousLinearMap.id 𝕜 G)
    (hg'invf : φ.leftDeriv.comp g'inv = 0) :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt)) g'inv (φ.rightFun φ.pt) := by
  convert φ.hasStrictFDerivAt_implicitFunction_fderiv
  ext1 x
  rw [eq_comm, fderiv_implicitFunction_apply_eq_iff]
  simp_all [DFunLike.ext_iff]

@[deprecated (since := "2026-01-27")]
alias implicitFunction_hasStrictFDerivAt := hasStrictFDerivAt_implicitFunction

theorem map_implicitFunction_nhdsWithin_preimage (φ : ImplicitFunctionData 𝕜 E F G)
    (s : Set E) :
    (𝓝[φ.implicitFunction (φ.leftFun φ.pt) ⁻¹' s] (φ.rightFun φ.pt)).map
      (φ.implicitFunction (φ.leftFun φ.pt)) = 𝓝[s ∩ φ.leftFun ⁻¹' {φ.leftFun φ.pt}] φ.pt := by
  have H : φ.implicitFunction (φ.leftFun φ.pt) =
      φ.toOpenPartialHomeomorph.symm ∘ (φ.leftFun φ.pt, ·) := rfl
  rw [H, ← Filter.map_map, (isInducing_prodMkRight _).map_nhdsWithin_eq, ← Set.singleton_prod,
    OpenPartialHomeomorph.map_nhdsWithin_eq, ← prodFun_apply, ← toOpenPartialHomeomorph_coe,
    φ.toOpenPartialHomeomorph.leftInvOn φ.pt_mem_toOpenPartialHomeomorph_source,
    OpenPartialHomeomorph.image_source_inter_eq']
  · conv_rhs =>
      rw [← φ.toOpenPartialHomeomorph.nhdsWithin_source_inter
        φ.pt_mem_toOpenPartialHomeomorph_source]
    congr 1
    ext x
    suffices x ∈ φ.toOpenPartialHomeomorph.source → φ.leftFun x = φ.leftFun φ.pt →
        (φ.toOpenPartialHomeomorph.symm (φ.leftFun φ.pt, φ.rightFun x) ∈ s ↔ x ∈ s) by
      simpa [@and_comm (_ = _)]
    intro hxs hx_eq
    rw [← hx_eq, ← prodFun_apply, ← toOpenPartialHomeomorph_coe,
      φ.toOpenPartialHomeomorph.leftInvOn hxs]
  · exact φ.toOpenPartialHomeomorph.mapsTo φ.pt_mem_toOpenPartialHomeomorph_source

theorem eventuallyEq_implicitFunction {ψ : F → G → E}
    (h : ∀ᶠ x in 𝓝 φ.pt, ψ (φ.leftFun x) (φ.rightFun x) = x) :
    Function.uncurry ψ =ᶠ[𝓝 (φ.prodFun φ.pt)] Function.uncurry φ.implicitFunction :=
  HasStrictFDerivAt.localInverse_unique _ h

end ImplicitFunctionData

namespace HasStrictFDerivAt

section Complemented

/-!
### Case of a complemented kernel

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` and a point `a : E` such that `f` is strictly differentiable at `a`, its derivative `f'`
is surjective and the kernel of `f'` is a complemented subspace of `E` (i.e., it has a closed
complementary subspace). Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}

section Defs

variable (f f')

/-- Data used to apply the generic implicit function theorem to the case of a strictly
differentiable map such that its derivative is surjective and has a complemented kernel. -/
@[simp]
def implicitFunctionDataOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : ImplicitFunctionData 𝕜 E F f'.ker where
  leftFun := f
  leftDeriv := f'
  rightFun x := Classical.choose hker (x - a)
  rightDeriv := Classical.choose hker
  pt := a
  hasStrictFDerivAt_leftFun := hf
  hasStrictFDerivAt_rightFun :=
    (Classical.choose hker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
  range_leftDeriv := hf'
  range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
  isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker)

/-- An open partial homeomorphism between `E` and `F × f'.ker` sending level surfaces of `f`
to vertical subspaces. -/
def implicitToOpenPartialHomeomorphOfComplemented (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    OpenPartialHomeomorph E (F × f'.ker) :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).toOpenPartialHomeomorph

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) : F → f'.ker → E :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction

end Defs

@[simp]
theorem implicitToOpenPartialHomeomorphOfComplemented_fst (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (x : E) :
    (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x).fst = f x := by
  rfl

theorem implicitToOpenPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (y : E) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker y =
      (f y, Classical.choose hker (y - a)) := by
  rfl

@[simp]
theorem implicitToOpenPartialHomeomorphOfComplemented_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) (y : f'.ker) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker (y + a) = (f (y + a), y) := by
  simp only [implicitToOpenPartialHomeomorphOfComplemented_apply, add_sub_cancel_right,
    Classical.choose_spec hker]

@[simp]
theorem implicitToOpenPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker a = (f a, 0) := by
  simp [hf.implicitToOpenPartialHomeomorphOfComplemented_apply]

theorem mem_implicitToOpenPartialHomeomorphOfComplemented_source (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    a ∈ (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).source :=
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

theorem mem_implicitToOpenPartialHomeomorphOfComplemented_target (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    (f a, (0 : f'.ker)) ∈
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).target := by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using
    (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).map_source <|
      hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker

/-- `HasStrictFDerivAt.implicitFunctionOfComplemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    ∀ᶠ p : F × f'.ker in 𝓝 (f a, 0),
      f (hf.implicitFunctionOfComplemented f f' hf' hker p.1 p.2) = p.1 :=
  ((hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicitToOpenPartialHomeomorphOfComplemented_target hf' hker).mono
    fun ⟨_, _⟩ h => congr_arg Prod.fst h

/-- Any point in some neighborhood of `a` can be represented as
`HasStrictFDerivAt.implicitFunctionOfComplemented` of some point. -/
theorem eq_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    ∀ᶠ x in 𝓝 a, hf.implicitFunctionOfComplemented f f' hf' hker (f x)
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker x).snd = x :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_apply_image

@[simp]
theorem implicitFunctionOfComplemented_apply_image (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (hker : f'.ker.ClosedComplemented) :
    hf.implicitFunctionOfComplemented f f' hf' hker (f a) 0 = a := by
  simpa only [implicitToOpenPartialHomeomorphOfComplemented_self] using
      (hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToOpenPartialHomeomorphOfComplemented_source hf' hker)

theorem to_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (hker : f'.ker.ClosedComplemented) :
    HasStrictFDerivAt (hf.implicitFunctionOfComplemented f f' hf' hker (f a))
      f'.ker.subtypeL 0 := by
  convert (implicitFunctionDataOfComplemented f f' hf hf' hker).hasStrictFDerivAt_implicitFunction
    f'.ker.subtypeL _ _
  swap
  · ext
    simp only [Classical.choose_spec hker, implicitFunctionDataOfComplemented,
      ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL', Submodule.coe_subtype,
      ContinuousLinearMap.id_apply]
  swap
  · ext
    simp only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL', Submodule.coe_subtype,
      ContinuousLinearMap.apply_val_ker, ContinuousLinearMap.zero_apply]
  simp only [implicitFunctionDataOfComplemented, map_sub, sub_self]

end Complemented

/-!
### Finite-dimensional case

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` from a Banach normed space to a finite-dimensional space.
Take a point `a : E` such that `f` is strictly differentiable at `a` and its derivative `f'`
is surjective. Then there exists a function `φ : F → ker f' → E` such that for `(y, z)`
close to `(f a, 0)` we have `f (φ y z) = y` and the derivative of `φ (f a)` at zero is the
embedding `ker f' → E`.

This version deduces that `ker f'` is a complemented subspace from the fact that `F` is a finite
dimensional space, then applies the previous version.

Note that a map with these properties is not unique. E.g., different choices of a subspace
complementary to `ker f'` lead to different maps `φ`.
-/

section FiniteDimensional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F] (f : E → F) (f' : E →L[𝕜] F) {a : E}

/-- Given a map `f : E → F` to a finite-dimensional space with a surjective derivative `f'`,
returns an open partial homeomorphism between `E` and `F × ker f'`. -/
def implicitToOpenPartialHomeomorph (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    OpenPartialHomeomorph E (F × f'.ker) :=
  have := FiniteDimensional.complete 𝕜 F
  hf.implicitToOpenPartialHomeomorphOfComplemented f f' hf'
    f'.ker_closedComplemented_of_finiteDimensional_range

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) : F → f'.ker → E :=
  Function.curry <| (hf.implicitToOpenPartialHomeomorph f f' hf').symm

variable {f f'}

@[simp]
theorem implicitToOpenPartialHomeomorph_fst (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤)
    (x : E) : (hf.implicitToOpenPartialHomeomorph f f' hf' x).fst = f x := by
  rfl

@[simp]
theorem implicitToOpenPartialHomeomorph_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) (y : f'.ker) :
    hf.implicitToOpenPartialHomeomorph f f' hf' (y + a) = (f (y + a), y) :=
  have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_apply_ker ..

@[simp]
theorem implicitToOpenPartialHomeomorph_self (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    hf.implicitToOpenPartialHomeomorph f f' hf' a = (f a, 0) :=
  have := FiniteDimensional.complete 𝕜 F
  implicitToOpenPartialHomeomorphOfComplemented_self ..

theorem mem_implicitToOpenPartialHomeomorph_source (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) : a ∈ (hf.implicitToOpenPartialHomeomorph f f' hf').source :=
  have := FiniteDimensional.complete 𝕜 F
  ImplicitFunctionData.pt_mem_toOpenPartialHomeomorph_source _

theorem mem_implicitToOpenPartialHomeomorph_target (hf : HasStrictFDerivAt f f' a)
    (hf' : f'.range = ⊤) :
    (f a, (0 : f'.ker)) ∈ (hf.implicitToOpenPartialHomeomorph f f' hf').target :=
  have := FiniteDimensional.complete 𝕜 F
  mem_implicitToOpenPartialHomeomorphOfComplemented_target ..

theorem tendsto_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) {α : Type*}
    {l : Filter α} {g₁ : α → F} {g₂ : α → f'.ker} (h₁ : Tendsto g₁ l (𝓝 <| f a))
    (h₂ : Tendsto g₂ l (𝓝 0)) :
    Tendsto (fun t => hf.implicitFunction f f' hf' (g₁ t) (g₂ t)) l (𝓝 a) := by
  refine ((hf.implicitToOpenPartialHomeomorph f f' hf').tendsto_symm
    (hf.mem_implicitToOpenPartialHomeomorph_source hf')).comp ?_
  rw [implicitToOpenPartialHomeomorph_self]
  exact h₁.prodMk_nhds h₂

alias _root_.Filter.Tendsto.implicitFunction := tendsto_implicitFunction

/-- `HasStrictFDerivAt.implicitFunction` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicitFunction_eq (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    ∀ᶠ p : F × f'.ker in 𝓝 (f a, 0), f (hf.implicitFunction f f' hf' p.1 p.2) = p.1 :=
  have := FiniteDimensional.complete 𝕜 F
  map_implicitFunctionOfComplemented_eq ..

@[simp]
theorem implicitFunction_apply_image (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    hf.implicitFunction f f' hf' (f a) 0 = a := by
  have := FiniteDimensional.complete 𝕜 F
  apply implicitFunctionOfComplemented_apply_image

/-- Any point in some neighborhood of `a` can be represented as `HasStrictFDerivAt.implicitFunction`
of some point. -/
theorem eq_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    ∀ᶠ x in 𝓝 a,
      hf.implicitFunction f f' hf' (f x) (hf.implicitToOpenPartialHomeomorph f f' hf' x).snd = x :=
  have := FiniteDimensional.complete 𝕜 F
  eq_implicitFunctionOfComplemented ..

theorem to_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : f'.range = ⊤) :
    HasStrictFDerivAt (hf.implicitFunction f f' hf' (f a)) f'.ker.subtypeL 0 :=
  have := FiniteDimensional.complete 𝕜 F
  to_implicitFunctionOfComplemented ..

end FiniteDimensional

end HasStrictFDerivAt

end
