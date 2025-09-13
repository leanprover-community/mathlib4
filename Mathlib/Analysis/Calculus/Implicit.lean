/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Normed.Module.Complemented

/-!
# Implicit function theorem

We prove four versions of the implicit function theorem. First we define a structure
`ImplicitFunctionData` that holds arguments for the most general version of the implicit function
theorem, see `ImplicitFunctionData.implicitFunction` and
`ImplicitFunctionData.implicitFunction_hasStrictFDerivAt`. This version allows a user to choose a
specific implicit function but provides only a little convenience over the inverse function theorem.

Then we define `HasStrictFDerivAt.implicitFunctionDataOfComplemented`: implicit function defined by
`f (g z y) = z`, where `f : E → F` is a function strictly differentiable at `a` such that its
derivative `f'` is surjective and has a `complemented` kernel.

Third, if the codomain of `f` is a finite dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `HasStrictFDerivAt`
and `f'.range = ⊤`. This version is named `HasStrictFDerivAt.implicitFunction`.

Lastly we consider the common case of a bivariate `f`, the second of whose partial derivatives is
invertible. Then we may apply the general theorem to obtain `ψ` such that for `(y₁, y₂)` in a
neighbourhood of `(x₁, x₂)` we have `f y₁ y₂ = f x₁ x₂ ↔ ψ y₁ = y₂`.

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

Note that the map `x ↦ (f x, g x)` has a bijective derivative, hence it is a partial homeomorphism
between `E` and `F × G`. We use this fact to define a function `φ : F → G → E`
(see `ImplicitFunctionData.implicitFunction`) such that for `(y, z)` close enough to `(f a, g a)`
we have `f (φ y z) = y` and `g (φ y z) = z`.

We also prove a formula for $$\frac{\partial\varphi}{\partial z}.$$

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
  left_has_deriv : HasStrictFDerivAt leftFun leftDeriv pt
  right_has_deriv : HasStrictFDerivAt rightFun rightDeriv pt
  left_range : range leftDeriv = ⊤
  right_range : range rightDeriv = ⊤
  isCompl_ker : IsCompl (ker leftDeriv) (ker rightDeriv)

namespace ImplicitFunctionData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G)

/-- The function given by `x ↦ (leftFun x, rightFun x)`. -/
def prodFun (x : E) : F × G :=
  (φ.leftFun x, φ.rightFun x)

@[simp]
theorem prodFun_apply (x : E) : φ.prodFun x = (φ.leftFun x, φ.rightFun x) :=
  rfl

protected theorem hasStrictFDerivAt :
    HasStrictFDerivAt φ.prodFun
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.left_range φ.right_range
          φ.isCompl_ker :
        E →L[𝕜] F × G)
      φ.pt :=
  φ.left_has_deriv.prodMk φ.right_has_deriv

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `x ↦ (f x, g x)` defines a partial homeomorphism between
`E` and `F × G`. In particular, `{x | f x = f a}` is locally homeomorphic to `G`. -/
def toPartialHomeomorph : PartialHomeomorph E (F × G) :=
  φ.hasStrictFDerivAt.toPartialHomeomorph _

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `implicitFunction` is the unique (germ of a) map
`φ : F → G → E` such that `f (φ y z) = y` and `g (φ y z) = z`. -/
def implicitFunction : F → G → E :=
  Function.curry <| φ.toPartialHomeomorph.symm

@[simp]
theorem toPartialHomeomorph_coe : ⇑φ.toPartialHomeomorph = φ.prodFun :=
  rfl

theorem toPartialHomeomorph_apply (x : E) : φ.toPartialHomeomorph x = (φ.leftFun x, φ.rightFun x) :=
  rfl

theorem pt_mem_toPartialHomeomorph_source : φ.pt ∈ φ.toPartialHomeomorph.source :=
  φ.hasStrictFDerivAt.mem_toPartialHomeomorph_source

theorem map_pt_mem_toPartialHomeomorph_target :
    (φ.leftFun φ.pt, φ.rightFun φ.pt) ∈ φ.toPartialHomeomorph.target :=
  φ.toPartialHomeomorph.map_source <| φ.pt_mem_toPartialHomeomorph_source

theorem prod_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prodFun (φ.implicitFunction p.1 p.2) = p :=
  φ.hasStrictFDerivAt.eventually_right_inverse.mono fun ⟨_, _⟩ h => h

theorem left_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.leftFun (φ.implicitFunction p.1 p.2) = p.1 :=
  φ.prod_map_implicitFunction.mono fun _ => congr_arg Prod.fst

theorem right_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.rightFun (φ.implicitFunction p.1 p.2) = p.2 :=
  φ.prod_map_implicitFunction.mono fun _ => congr_arg Prod.snd

theorem implicitFunction_apply_image :
    ∀ᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.leftFun x) (φ.rightFun x) = x :=
  φ.hasStrictFDerivAt.eventually_left_inverse

theorem leftFun_implicitFunction : ∀ᶠ x in 𝓝 φ.pt,
    φ.leftFun (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.leftFun φ.pt := by
  have := φ.left_map_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

theorem rightFun_implicitFunction : ∀ᶠ x in 𝓝 φ.pt,
    φ.rightFun (φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x)) = φ.rightFun x := by
  have := φ.right_map_implicitFunction.curry_nhds.self_of_nhds.prod_inr_nhds (φ.leftFun φ.pt)
  rwa [← prodFun_apply, ← φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, eventually_map] at this

theorem leftFun_eq_iff_implicitFunction : ∀ᶠ x in 𝓝 φ.pt,
    φ.leftFun x = φ.leftFun φ.pt ↔ φ.implicitFunction (φ.leftFun φ.pt) (φ.rightFun x) = x := by
  filter_upwards [φ.implicitFunction_apply_image, φ.leftFun_implicitFunction] with x hx₁ hx₂
  constructor <;> exact fun h => by rwa [← h]

theorem map_nhds_eq : map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt) :=
  show map (Prod.fst ∘ φ.prodFun) (𝓝 φ.pt) = 𝓝 (φ.prodFun φ.pt).1 by
    rw [← map_map, φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, map_fst_nhds]

theorem implicitFunction_hasStrictFDerivAt (g'inv : G →L[𝕜] E)
    (hg'inv : φ.rightDeriv.comp g'inv = ContinuousLinearMap.id 𝕜 G)
    (hg'invf : φ.leftDeriv.comp g'inv = 0) :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt)) g'inv (φ.rightFun φ.pt) := by
  have := φ.hasStrictFDerivAt.to_localInverse
  simp only [prodFun] at this
  convert this.comp (φ.rightFun φ.pt)
    ((hasStrictFDerivAt_const _ _).prodMk (hasStrictFDerivAt_id _))
  simp only [ContinuousLinearMap.ext_iff, ContinuousLinearMap.comp_apply] at hg'inv hg'invf ⊢
  simp [ContinuousLinearEquiv.eq_symm_apply, *]

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
def implicitFunctionDataOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) : ImplicitFunctionData 𝕜 E F (ker f') where
  leftFun := f
  leftDeriv := f'
  rightFun x := Classical.choose hker (x - a)
  rightDeriv := Classical.choose hker
  pt := a
  left_has_deriv := hf
  right_has_deriv :=
    (Classical.choose hker).hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
  left_range := hf'
  right_range := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
  isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker)

/-- A partial homeomorphism between `E` and `F × f'.ker` sending level surfaces of `f`
to vertical subspaces. -/
def implicitToPartialHomeomorphOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) : PartialHomeomorph E (F × ker f') :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).toPartialHomeomorph

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) : F → ker f' → E :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction

end Defs

@[simp]
theorem implicitToPartialHomeomorphOfComplemented_fst (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (x : E) :
    (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker x).fst = f x :=
  rfl

theorem implicitToPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (y : E) :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker y =
      (f y, Classical.choose hker (y - a)) :=
  rfl

@[simp]
theorem implicitToPartialHomeomorphOfComplemented_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (y : ker f') :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker (y + a) = (f (y + a), y) := by
  simp only [implicitToPartialHomeomorphOfComplemented_apply, add_sub_cancel_right,
    Classical.choose_spec hker]

@[simp]
theorem implicitToPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker a = (f a, 0) := by
  simp [hf.implicitToPartialHomeomorphOfComplemented_apply]

theorem mem_implicitToPartialHomeomorphOfComplemented_source (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    a ∈ (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).source :=
  ImplicitFunctionData.pt_mem_toPartialHomeomorph_source _

theorem mem_implicitToPartialHomeomorphOfComplemented_target (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    (f a, (0 : ker f')) ∈ (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).target := by
  simpa only [implicitToPartialHomeomorphOfComplemented_self] using
    (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).map_source <|
      hf.mem_implicitToPartialHomeomorphOfComplemented_source hf' hker

/-- `HasStrictFDerivAt.implicitFunctionOfComplemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    ∀ᶠ p : F × ker f' in 𝓝 (f a, 0),
      f (hf.implicitFunctionOfComplemented f f' hf' hker p.1 p.2) = p.1 :=
  ((hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicitToPartialHomeomorphOfComplemented_target hf' hker).mono
    fun ⟨_, _⟩ h => congr_arg Prod.fst h

/-- Any point in some neighborhood of `a` can be represented as
`HasStrictFDerivAt.implicitFunctionOfComplemented` of some point. -/
theorem eq_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    ∀ᶠ x in 𝓝 a, hf.implicitFunctionOfComplemented f f' hf' hker (f x)
      (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker x).snd = x :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_apply_image

@[simp]
theorem implicitFunctionOfComplemented_apply_image (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    hf.implicitFunctionOfComplemented f f' hf' hker (f a) 0 = a := by
  simpa only [implicitToPartialHomeomorphOfComplemented_self] using
      (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToPartialHomeomorphOfComplemented_source hf' hker)

theorem to_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    HasStrictFDerivAt (hf.implicitFunctionOfComplemented f f' hf' hker (f a))
      (ker f').subtypeL 0 := by
  convert (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_hasStrictFDerivAt
    (ker f').subtypeL _ _
  swap
  · ext
    simp only [Classical.choose_spec hker, implicitFunctionDataOfComplemented,
      ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL', Submodule.coe_subtype,
      ContinuousLinearMap.id_apply]
  swap
  · ext
    simp only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL', Submodule.coe_subtype,
      LinearMap.map_coe_ker, ContinuousLinearMap.zero_apply]
  simp only [implicitFunctionDataOfComplemented, map_sub, sub_self]

end Complemented

/-!
### Finite dimensional case

In this section we prove the following version of the implicit function theorem. Consider a map
`f : E → F` from a Banach normed space to a finite dimensional space.
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

/-- Given a map `f : E → F` to a finite dimensional space with a surjective derivative `f'`,
returns a partial homeomorphism between `E` and `F × ker f'`. -/
def implicitToPartialHomeomorph (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    PartialHomeomorph E (F × ker f') :=
  haveI := FiniteDimensional.complete 𝕜 F
  hf.implicitToPartialHomeomorphOfComplemented f f' hf'
    f'.ker_closedComplemented_of_finiteDimensional_range

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) : F → ker f' → E :=
  Function.curry <| (hf.implicitToPartialHomeomorph f f' hf').symm

variable {f f'}

@[simp]
theorem implicitToPartialHomeomorph_fst (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (x : E) : (hf.implicitToPartialHomeomorph f f' hf' x).fst = f x :=
  rfl

@[simp]
theorem implicitToPartialHomeomorph_apply_ker (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (y : ker f') : hf.implicitToPartialHomeomorph f f' hf' (y + a) = (f (y + a), y) :=
  haveI := FiniteDimensional.complete 𝕜 F
  implicitToPartialHomeomorphOfComplemented_apply_ker ..

@[simp]
theorem implicitToPartialHomeomorph_self (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    hf.implicitToPartialHomeomorph f f' hf' a = (f a, 0) :=
  haveI := FiniteDimensional.complete 𝕜 F
  implicitToPartialHomeomorphOfComplemented_self ..

theorem mem_implicitToPartialHomeomorph_source (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) : a ∈ (hf.implicitToPartialHomeomorph f f' hf').source :=
  haveI := FiniteDimensional.complete 𝕜 F
  ImplicitFunctionData.pt_mem_toPartialHomeomorph_source _

theorem mem_implicitToPartialHomeomorph_target (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) : (f a, (0 : ker f')) ∈ (hf.implicitToPartialHomeomorph f f' hf').target :=
  haveI := FiniteDimensional.complete 𝕜 F
  mem_implicitToPartialHomeomorphOfComplemented_target ..

theorem tendsto_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) {α : Type*}
    {l : Filter α} {g₁ : α → F} {g₂ : α → ker f'} (h₁ : Tendsto g₁ l (𝓝 <| f a))
    (h₂ : Tendsto g₂ l (𝓝 0)) :
    Tendsto (fun t => hf.implicitFunction f f' hf' (g₁ t) (g₂ t)) l (𝓝 a) := by
  refine ((hf.implicitToPartialHomeomorph f f' hf').tendsto_symm
    (hf.mem_implicitToPartialHomeomorph_source hf')).comp ?_
  rw [implicitToPartialHomeomorph_self]
  exact h₁.prodMk_nhds h₂

alias _root_.Filter.Tendsto.implicitFunction := tendsto_implicitFunction

/-- `HasStrictFDerivAt.implicitFunction` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicitFunction_eq (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    ∀ᶠ p : F × ker f' in 𝓝 (f a, 0), f (hf.implicitFunction f f' hf' p.1 p.2) = p.1 :=
  haveI := FiniteDimensional.complete 𝕜 F
  map_implicitFunctionOfComplemented_eq ..

@[simp]
theorem implicitFunction_apply_image (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    hf.implicitFunction f f' hf' (f a) 0 = a := by
  haveI := FiniteDimensional.complete 𝕜 F
  apply implicitFunctionOfComplemented_apply_image

/-- Any point in some neighborhood of `a` can be represented as `HasStrictFDerivAt.implicitFunction`
of some point. -/
theorem eq_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    ∀ᶠ x in 𝓝 a,
      hf.implicitFunction f f' hf' (f x) (hf.implicitToPartialHomeomorph f f' hf' x).snd = x :=
  haveI := FiniteDimensional.complete 𝕜 F
  eq_implicitFunctionOfComplemented ..

theorem to_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    HasStrictFDerivAt (hf.implicitFunction f f' hf' (f a)) (ker f').subtypeL 0 :=
  haveI := FiniteDimensional.complete 𝕜 F
  to_implicitFunctionOfComplemented ..

end FiniteDimensional

section ProdDomain

/-!
### Bivariate case

Here we identify `E` with `E₁ × E₂`, `G` with `E₁` and `g : E → G` with the first projection. Now
given `f : E₁ → E₂ → F` and its two partial derivatives, the second invertible, we may construct an
instance of the `ImplicitFunctionData` data structure and extract `ψ : E₁ → E₂` with the desired
properties. This functionality is wrapped by `HasStrictFDerivAt.implicitFunOfProdDomain` for
uncurried `f` in this section and `implicitFunOfBivariate` for curried `f` in the next. A formula
for the first derivative of `ψ` is immediately derived.

## TODO

* Derive a formula for the second derivative of `ψ`.
-/

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁] [NormedAddCommGroup E₂]
  [NormedSpace 𝕜 E₂] [CompleteSpace E₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- Given linear maps `f₁ : E₁ →L[𝕜] F` and `f₂ : E₂ ≃L[𝕜] F` (the second invertible) and that
`HasStrictFDerivAt f (f₁.coprod f₂) x`, we prove that the kernels of `f : E → F` and `g : E → G` in
the original formulation are complementary and construct an object of type `ImplicitFunctionData`
thereby permitting use of the general machinery provided above. -/
def implicitFunDataOfProdDomain {f : E₁ × E₂ → F} {x : E₁ × E₂}
    {f₁ : E₁ →L[𝕜] F} {f₂ : E₂ ≃L[𝕜] F} (dfx : HasStrictFDerivAt f (f₁.coprod f₂) x) :
    ImplicitFunctionData 𝕜 (E₁ × E₂) F E₁ where
  leftFun := f
  rightFun := Prod.fst
  pt := x
  leftDeriv := f₁.coprod f₂
  left_has_deriv := dfx
  rightDeriv := ContinuousLinearMap.fst 𝕜 E₁ E₂
  right_has_deriv := hasStrictFDerivAt_fst
  left_range := by
    rw [ContinuousLinearMap.range_coprod]
    convert sup_top_eq _
    exact LinearEquivClass.range f₂
  right_range := Submodule.range_fst
  isCompl_ker := by
    constructor
    · rw [Submodule.disjoint_def]
      aesop
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro (h₁, h₂)
      use (h₁, f₂.symm (f₁ (-h₁))), (0, h₂ - f₂.symm (f₁ (-h₁)))
      simp

/-- Implicit function `ψ : E₁ → E₂` associated with the (uncurried) bivariate function
`f : E₁ × E₂ → F` at `x`. -/
def implicitFunOfProdDomain {f : E₁ × E₂ → F} {x : E₁ × E₂}
    {f₁ : E₁ →L[𝕜] F} {f₂ : E₂ ≃L[𝕜] F} (dfx : HasStrictFDerivAt f (f₁.coprod f₂) x) :
    E₁ → E₂ :=
  fun u => (dfx.implicitFunDataOfProdDomain.implicitFunction (f x) u).2

theorem hasStrictFDerivAt_implicitFunOfProdDomain {f : E₁ × E₂ → F} {x₁ : E₁} {x₂ : E₂}
    {f₁ : E₁ →L[𝕜] F} {f₂ : E₂ ≃L[𝕜] F} (dfx : HasStrictFDerivAt f (f₁.coprod f₂) (x₁, x₂)) :
    HasStrictFDerivAt dfx.implicitFunOfProdDomain (-f₂.symm ∘L f₁) x₁ := by
  set ψ' : E₁ →L[𝕜] E₂ := -f₂.symm ∘L f₁
  apply HasStrictFDerivAt.snd (f₂' := (ContinuousLinearMap.id 𝕜 E₁).prod ψ')
  apply dfx.implicitFunDataOfProdDomain.implicitFunction_hasStrictFDerivAt
  · apply ContinuousLinearMap.fst_comp_prod
  · change f₁ + f₂ ∘L ψ' = 0
    simp [ψ', ← ContinuousLinearMap.comp_assoc]

theorem image_eq_iff_implicitFunOfProdDomain {f : E₁ × E₂ → F} {x : E₁ × E₂}
    {f₁ : E₁ →L[𝕜] F} {f₂ : E₂ ≃L[𝕜] F} (dfx : HasStrictFDerivAt f (f₁.coprod f₂) x) :
    ∀ᶠ y in 𝓝 x, f y = f x ↔ dfx.implicitFunOfProdDomain y.1 = y.2 := by
  let φ := dfx.implicitFunDataOfProdDomain
  filter_upwards [φ.leftFun_eq_iff_implicitFunction, φ.rightFun_implicitFunction] with y h h'
  exact Iff.trans h ⟨congrArg _, by aesop⟩

theorem tendsto_implicitFunOfProdDomain {f : E₁ × E₂ → F} {x₁ : E₁} {x₂ : E₂}
    {f₁ : E₁ →L[𝕜] F} {f₂ : E₂ ≃L[𝕜] F} (dfx : HasStrictFDerivAt f (f₁.coprod f₂) (x₁, x₂)) :
    Tendsto dfx.implicitFunOfProdDomain (𝓝 x₁) (𝓝 x₂) := by
  have := dfx.hasStrictFDerivAt_implicitFunOfProdDomain.continuousAt.tendsto
  rwa [dfx.image_eq_iff_implicitFunOfProdDomain.self_of_nhds.mp rfl] at this

theorem image_implicitFunOfProdDomain {f : E₁ × E₂ → F} {x₁ : E₁} {x₂ : E₂}
    {f₁ : E₁ →L[𝕜] F} {f₂ : E₂ ≃L[𝕜] F} (dfx : HasStrictFDerivAt f (f₁.coprod f₂) (x₁, x₂)) :
    ∀ᶠ u in 𝓝 x₁, f (u, dfx.implicitFunOfProdDomain u) = f (x₁, x₂) := by
  have hψ := dfx.tendsto_implicitFunOfProdDomain
  set ψ := dfx.implicitFunOfProdDomain
  suffices ∀ᶠ u in 𝓝 x₁, f (u, ψ u) = f (x₁, x₂) ↔ ψ u = ψ u by simpa
  apply Eventually.image_of_prod (r := fun u v => f (u, v) = f (x₁, x₂) ↔ ψ u = v) hψ
  rw [← nhds_prod_eq]
  exact dfx.image_eq_iff_implicitFunOfProdDomain

end ProdDomain

end HasStrictFDerivAt

section Bivariate

variable {𝕜 E₁ E₂ F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁] [NormedAddCommGroup E₂]
  [NormedSpace 𝕜 E₂] [CompleteSpace E₂] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

variable {f : E₁ → E₂ → F} {x₁ : E₁} {x₂ : E₂}
  {f₁ : E₁ → E₂ → E₁ →L[𝕜] F} (cf₁ : ContinuousAt ↿f₁ (x₁, x₂))
  (df₁ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f · y.2) (f₁ y.1 y.2) y.1)
  {f₂ : E₁ → E₂ → E₂ →L[𝕜] F} (cf₂ : ContinuousAt ↿f₂ (x₁, x₂))
  (df₂ : ∀ᶠ y in 𝓝 (x₁, x₂), HasFDerivAt (f y.1 ·) (f₂ y.1 y.2) y.2)
  {f₂x : E₂ ≃L[𝕜] F} (hf₂x : f₂ x₁ x₂ = f₂x)

/-- Implicit function `ψ : E₁ → E₂` associated with the (curried) bivariate function
`f : E₁ → E₂ → F` at `(x₁, x₂)`. -/
def implicitFunOfBivariate : E₁ → E₂ :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂ |>.implicitFunOfProdDomain

theorem hasStrictFDerivAt_implicitFunOfBivariate :
    HasStrictFDerivAt (implicitFunOfBivariate cf₁ df₁ cf₂ df₂ hf₂x) (-f₂x.symm ∘L f₁ x₁ x₂) x₁ :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂
    |>.hasStrictFDerivAt_implicitFunOfProdDomain

theorem image_eq_iff_implicitFunOfBivariate :
    ∀ᶠ y in 𝓝 (x₁, x₂), ↿f y = f x₁ x₂ ↔ implicitFunOfBivariate cf₁ df₁ cf₂ df₂ hf₂x y.1 = y.2 :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂ |>.image_eq_iff_implicitFunOfProdDomain

theorem tendsto_implicitFunOfBivariate :
    Tendsto (implicitFunOfBivariate cf₁ df₁ cf₂ df₂ hf₂x) (𝓝 x₁) (𝓝 x₂) :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂ |>.tendsto_implicitFunOfProdDomain

theorem image_implicitFunOfBivariate :
    ∀ᶠ u in 𝓝 x₁, f u (implicitFunOfBivariate cf₁ df₁ cf₂ df₂ hf₂x u) = f x₁ x₂ :=
  hf₂x ▸ hasStrictFDerivAt_uncurry_coprod cf₁ df₁ cf₂ df₂ |>.image_implicitFunOfProdDomain

end Bivariate
