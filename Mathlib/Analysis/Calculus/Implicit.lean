/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.NormedSpace.Complemented

#align_import analysis.calculus.implicit from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Implicit function theorem

We prove three versions of the implicit function theorem. First we define a structure
`ImplicitFunctionData` that holds arguments for the most general version of the implicit function
theorem, see `ImplicitFunctionData.implicitFunction` and
`ImplicitFunctionData.implicitFunction_hasStrictFDerivAt`. This version allows a user to choose a
specific implicit function but provides only a little convenience over the inverse function theorem.

Then we define `HasStrictFDerivAt.implicitFunctionDataOfComplemented`: implicit function defined by
`f (g z y) = z`, where `f : E → F` is a function strictly differentiable at `a` such that its
derivative `f'` is surjective and has a `complemented` kernel.

Finally, if the codomain of `f` is a finite dimensional space, then we can automatically prove
that the kernel of `f'` is complemented, hence the only assumptions are `HasStrictFDerivAt`
and `f'.range = ⊤`. This version is named `HasStrictFDerivAt.implicitFunction`.

## TODO

* Add a version for a function `f : E × F → G` such that $$\frac{\partial f}{\partial y}$$ is
  invertible.
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
-- Porting note(#5171): linter not yet ported @[nolint has_nonempty_instance]
structure ImplicitFunctionData (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*)
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    [CompleteSpace G] where
  leftFun : E → F
  leftDeriv : E →L[𝕜] F
  rightFun : E → G
  rightDeriv : E →L[𝕜] G
  pt : E
  left_has_deriv : HasStrictFDerivAt leftFun leftDeriv pt
  right_has_deriv : HasStrictFDerivAt rightFun rightDeriv pt
  left_range : range leftDeriv = ⊤
  right_range : range rightDeriv = ⊤
  isCompl_ker : IsCompl (ker leftDeriv) (ker rightDeriv)
#align implicit_function_data ImplicitFunctionData

namespace ImplicitFunctionData

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
  (φ : ImplicitFunctionData 𝕜 E F G)

/-- The function given by `x ↦ (leftFun x, rightFun x)`. -/
def prodFun (x : E) : F × G :=
  (φ.leftFun x, φ.rightFun x)
#align implicit_function_data.prod_fun ImplicitFunctionData.prodFun

@[simp]
theorem prodFun_apply (x : E) : φ.prodFun x = (φ.leftFun x, φ.rightFun x) :=
  rfl
#align implicit_function_data.prod_fun_apply ImplicitFunctionData.prodFun_apply

protected theorem hasStrictFDerivAt :
    HasStrictFDerivAt φ.prodFun
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv φ.left_range φ.right_range
          φ.isCompl_ker :
        E →L[𝕜] F × G)
      φ.pt :=
  φ.left_has_deriv.prod φ.right_has_deriv
#align implicit_function_data.has_strict_fderiv_at ImplicitFunctionData.hasStrictFDerivAt

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `x ↦ (f x, g x)` defines a partial homeomorphism between
`E` and `F × G`. In particular, `{x | f x = f a}` is locally homeomorphic to `G`. -/
def toPartialHomeomorph : PartialHomeomorph E (F × G) :=
  φ.hasStrictFDerivAt.toPartialHomeomorph _
#align implicit_function_data.to_local_homeomorph ImplicitFunctionData.toPartialHomeomorph

/-- Implicit function theorem. If `f : E → F` and `g : E → G` are two maps strictly differentiable
at `a`, their derivatives `f'`, `g'` are surjective, and the kernels of these derivatives are
complementary subspaces of `E`, then `implicitFunction` is the unique (germ of a) map
`φ : F → G → E` such that `f (φ y z) = y` and `g (φ y z) = z`. -/
def implicitFunction : F → G → E :=
  Function.curry <| φ.toPartialHomeomorph.symm
#align implicit_function_data.implicit_function ImplicitFunctionData.implicitFunction

@[simp]
theorem toPartialHomeomorph_coe : ⇑φ.toPartialHomeomorph = φ.prodFun :=
  rfl
#align implicit_function_data.to_local_homeomorph_coe ImplicitFunctionData.toPartialHomeomorph_coe

theorem toPartialHomeomorph_apply (x : E) : φ.toPartialHomeomorph x = (φ.leftFun x, φ.rightFun x) :=
  rfl
#align implicit_function_data.to_local_homeomorph_apply ImplicitFunctionData.toPartialHomeomorph_apply

theorem pt_mem_toPartialHomeomorph_source : φ.pt ∈ φ.toPartialHomeomorph.source :=
  φ.hasStrictFDerivAt.mem_toPartialHomeomorph_source
#align implicit_function_data.pt_mem_to_local_homeomorph_source ImplicitFunctionData.pt_mem_toPartialHomeomorph_source

theorem map_pt_mem_toPartialHomeomorph_target :
    (φ.leftFun φ.pt, φ.rightFun φ.pt) ∈ φ.toPartialHomeomorph.target :=
  φ.toPartialHomeomorph.map_source <| φ.pt_mem_toPartialHomeomorph_source
#align implicit_function_data.map_pt_mem_to_local_homeomorph_target ImplicitFunctionData.map_pt_mem_toPartialHomeomorph_target

theorem prod_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.prodFun (φ.implicitFunction p.1 p.2) = p :=
  φ.hasStrictFDerivAt.eventually_right_inverse.mono fun ⟨_, _⟩ h => h
#align implicit_function_data.prod_map_implicit_function ImplicitFunctionData.prod_map_implicitFunction

theorem left_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.leftFun (φ.implicitFunction p.1 p.2) = p.1 :=
  φ.prod_map_implicitFunction.mono fun _ => congr_arg Prod.fst
#align implicit_function_data.left_map_implicit_function ImplicitFunctionData.left_map_implicitFunction

theorem right_map_implicitFunction :
    ∀ᶠ p : F × G in 𝓝 (φ.prodFun φ.pt), φ.rightFun (φ.implicitFunction p.1 p.2) = p.2 :=
  φ.prod_map_implicitFunction.mono fun _ => congr_arg Prod.snd
#align implicit_function_data.right_map_implicit_function ImplicitFunctionData.right_map_implicitFunction

theorem implicitFunction_apply_image :
    ∀ᶠ x in 𝓝 φ.pt, φ.implicitFunction (φ.leftFun x) (φ.rightFun x) = x :=
  φ.hasStrictFDerivAt.eventually_left_inverse
#align implicit_function_data.implicit_function_apply_image ImplicitFunctionData.implicitFunction_apply_image

theorem map_nhds_eq : map φ.leftFun (𝓝 φ.pt) = 𝓝 (φ.leftFun φ.pt) :=
  show map (Prod.fst ∘ φ.prodFun) (𝓝 φ.pt) = 𝓝 (φ.prodFun φ.pt).1 by
    rw [← map_map, φ.hasStrictFDerivAt.map_nhds_eq_of_equiv, map_fst_nhds]
#align implicit_function_data.map_nhds_eq ImplicitFunctionData.map_nhds_eq

theorem implicitFunction_hasStrictFDerivAt (g'inv : G →L[𝕜] E)
    (hg'inv : φ.rightDeriv.comp g'inv = ContinuousLinearMap.id 𝕜 G)
    (hg'invf : φ.leftDeriv.comp g'inv = 0) :
    HasStrictFDerivAt (φ.implicitFunction (φ.leftFun φ.pt)) g'inv (φ.rightFun φ.pt) := by
  have := φ.hasStrictFDerivAt.to_localInverse
  simp only [prodFun] at this
  convert this.comp (φ.rightFun φ.pt) ((hasStrictFDerivAt_const _ _).prod (hasStrictFDerivAt_id _))
  -- Porting note: added parentheses to help `simp`
  simp only [ContinuousLinearMap.ext_iff, (ContinuousLinearMap.comp_apply)] at hg'inv hg'invf ⊢
  -- porting note (#10745): was `simp [ContinuousLinearEquiv.eq_symm_apply]`;
  -- both `simp` and `rw` fail here, `erw` works
  intro x
  erw [ContinuousLinearEquiv.eq_symm_apply]
  simp [*]
#align implicit_function_data.implicit_function_has_strict_fderiv_at ImplicitFunctionData.implicitFunction_hasStrictFDerivAt

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
#align has_strict_fderiv_at.implicit_function_data_of_complemented HasStrictFDerivAt.implicitFunctionDataOfComplemented

/-- A partial homeomorphism between `E` and `F × f'.ker` sending level surfaces of `f`
to vertical subspaces. -/
def implicitToPartialHomeomorphOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) : PartialHomeomorph E (F × ker f') :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).toPartialHomeomorph
#align has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented HasStrictFDerivAt.implicitToPartialHomeomorphOfComplemented

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) : F → ker f' → E :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction
#align has_strict_fderiv_at.implicit_function_of_complemented HasStrictFDerivAt.implicitFunctionOfComplemented

end Defs

@[simp]
theorem implicitToPartialHomeomorphOfComplemented_fst (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (x : E) :
    (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker x).fst = f x :=
  rfl
#align has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_fst HasStrictFDerivAt.implicitToPartialHomeomorphOfComplemented_fst

theorem implicitToPartialHomeomorphOfComplemented_apply (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (y : E) :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker y =
      (f y, Classical.choose hker (y - a)) :=
  rfl
#align has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_apply HasStrictFDerivAt.implicitToPartialHomeomorphOfComplemented_apply

@[simp]
theorem implicitToPartialHomeomorphOfComplemented_apply_ker (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) (y : ker f') :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker (y + a) = (f (y + a), y) := by
  simp only [implicitToPartialHomeomorphOfComplemented_apply, add_sub_cancel_right,
    Classical.choose_spec hker]
#align has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_apply_ker HasStrictFDerivAt.implicitToPartialHomeomorphOfComplemented_apply_ker

@[simp]
theorem implicitToPartialHomeomorphOfComplemented_self (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker a = (f a, 0) := by
  simp [hf.implicitToPartialHomeomorphOfComplemented_apply]
#align has_strict_fderiv_at.implicit_to_local_homeomorph_of_complemented_self HasStrictFDerivAt.implicitToPartialHomeomorphOfComplemented_self

theorem mem_implicitToPartialHomeomorphOfComplemented_source (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    a ∈ (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).source :=
  ImplicitFunctionData.pt_mem_toPartialHomeomorph_source _
#align has_strict_fderiv_at.mem_implicit_to_local_homeomorph_of_complemented_source HasStrictFDerivAt.mem_implicitToPartialHomeomorphOfComplemented_source

theorem mem_implicitToPartialHomeomorphOfComplemented_target (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    (f a, (0 : ker f')) ∈ (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).target := by
  simpa only [implicitToPartialHomeomorphOfComplemented_self] using
    (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).map_source <|
      hf.mem_implicitToPartialHomeomorphOfComplemented_source hf' hker
#align has_strict_fderiv_at.mem_implicit_to_local_homeomorph_of_complemented_target HasStrictFDerivAt.mem_implicitToPartialHomeomorphOfComplemented_target

/-- `HasStrictFDerivAt.implicitFunctionOfComplemented` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicitFunctionOfComplemented_eq (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    ∀ᶠ p : F × ker f' in 𝓝 (f a, 0),
      f (hf.implicitFunctionOfComplemented f f' hf' hker p.1 p.2) = p.1 :=
  ((hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).eventually_right_inverse <|
        hf.mem_implicitToPartialHomeomorphOfComplemented_target hf' hker).mono
    fun ⟨_, _⟩ h => congr_arg Prod.fst h
#align has_strict_fderiv_at.map_implicit_function_of_complemented_eq HasStrictFDerivAt.map_implicitFunctionOfComplemented_eq

/-- Any point in some neighborhood of `a` can be represented as
`HasStrictFDerivAt.implicitFunctionOfComplemented` of some point. -/
theorem eq_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    ∀ᶠ x in 𝓝 a, hf.implicitFunctionOfComplemented f f' hf' hker (f x)
      (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker x).snd = x :=
  (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_apply_image
#align has_strict_fderiv_at.eq_implicit_function_of_complemented HasStrictFDerivAt.eq_implicitFunctionOfComplemented

@[simp]
theorem implicitFunctionOfComplemented_apply_image (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) (hker : (ker f').ClosedComplemented) :
    hf.implicitFunctionOfComplemented f f' hf' hker (f a) 0 = a := by
  simpa only [implicitToPartialHomeomorphOfComplemented_self] using
      (hf.implicitToPartialHomeomorphOfComplemented f f' hf' hker).left_inv
      (hf.mem_implicitToPartialHomeomorphOfComplemented_source hf' hker)
#align has_strict_fderiv_at.implicit_function_of_complemented_apply_image HasStrictFDerivAt.implicitFunctionOfComplemented_apply_image

theorem to_implicitFunctionOfComplemented (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (hker : (ker f').ClosedComplemented) :
    HasStrictFDerivAt (hf.implicitFunctionOfComplemented f f' hf' hker (f a))
      (ker f').subtypeL 0 := by
  convert (implicitFunctionDataOfComplemented f f' hf hf' hker).implicitFunction_hasStrictFDerivAt
    (ker f').subtypeL _ _
  swap
  · ext
    -- Porting note: added parentheses to help `simp`
    simp only [Classical.choose_spec hker, implicitFunctionDataOfComplemented,
      ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL', Submodule.coeSubtype,
      ContinuousLinearMap.id_apply]
  swap
  · ext
    -- Porting note: added parentheses to help `simp`
    simp only [(ContinuousLinearMap.comp_apply), Submodule.coe_subtypeL', Submodule.coeSubtype,
      LinearMap.map_coe_ker, (ContinuousLinearMap.zero_apply)]
  simp only [implicitFunctionDataOfComplemented, map_sub, sub_self]
#align has_strict_fderiv_at.to_implicit_function_of_complemented HasStrictFDerivAt.to_implicitFunctionOfComplemented

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
#align has_strict_fderiv_at.implicit_to_local_homeomorph HasStrictFDerivAt.implicitToPartialHomeomorph

/-- Implicit function `g` defined by `f (g z y) = z`. -/
def implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) : F → ker f' → E :=
  Function.curry <| (hf.implicitToPartialHomeomorph f f' hf').symm
#align has_strict_fderiv_at.implicit_function HasStrictFDerivAt.implicitFunction

variable {f f'}

@[simp]
theorem implicitToPartialHomeomorph_fst (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (x : E) : (hf.implicitToPartialHomeomorph f f' hf' x).fst = f x :=
  rfl
#align has_strict_fderiv_at.implicit_to_local_homeomorph_fst HasStrictFDerivAt.implicitToPartialHomeomorph_fst

@[simp]
theorem implicitToPartialHomeomorph_apply_ker (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤)
    (y : ker f') : hf.implicitToPartialHomeomorph f f' hf' (y + a) = (f (y + a), y) :=
  -- Porting note: had to add `haveI` (here and below)
  haveI := FiniteDimensional.complete 𝕜 F
  implicitToPartialHomeomorphOfComplemented_apply_ker ..
#align has_strict_fderiv_at.implicit_to_local_homeomorph_apply_ker HasStrictFDerivAt.implicitToPartialHomeomorph_apply_ker

@[simp]
theorem implicitToPartialHomeomorph_self (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    hf.implicitToPartialHomeomorph f f' hf' a = (f a, 0) :=
  haveI := FiniteDimensional.complete 𝕜 F
  implicitToPartialHomeomorphOfComplemented_self ..
#align has_strict_fderiv_at.implicit_to_local_homeomorph_self HasStrictFDerivAt.implicitToPartialHomeomorph_self

theorem mem_implicitToPartialHomeomorph_source (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) : a ∈ (hf.implicitToPartialHomeomorph f f' hf').source :=
  haveI := FiniteDimensional.complete 𝕜 F
  ImplicitFunctionData.pt_mem_toPartialHomeomorph_source _
#align has_strict_fderiv_at.mem_implicit_to_local_homeomorph_source HasStrictFDerivAt.mem_implicitToPartialHomeomorph_source

theorem mem_implicitToPartialHomeomorph_target (hf : HasStrictFDerivAt f f' a)
    (hf' : range f' = ⊤) : (f a, (0 : ker f')) ∈ (hf.implicitToPartialHomeomorph f f' hf').target :=
  haveI := FiniteDimensional.complete 𝕜 F
  mem_implicitToPartialHomeomorphOfComplemented_target ..
#align has_strict_fderiv_at.mem_implicit_to_local_homeomorph_target HasStrictFDerivAt.mem_implicitToPartialHomeomorph_target

theorem tendsto_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) {α : Type*}
    {l : Filter α} {g₁ : α → F} {g₂ : α → ker f'} (h₁ : Tendsto g₁ l (𝓝 <| f a))
    (h₂ : Tendsto g₂ l (𝓝 0)) :
    Tendsto (fun t => hf.implicitFunction f f' hf' (g₁ t) (g₂ t)) l (𝓝 a) := by
  refine ((hf.implicitToPartialHomeomorph f f' hf').tendsto_symm
    (hf.mem_implicitToPartialHomeomorph_source hf')).comp ?_
  rw [implicitToPartialHomeomorph_self]
  exact h₁.prod_mk_nhds h₂
#align has_strict_fderiv_at.tendsto_implicit_function HasStrictFDerivAt.tendsto_implicitFunction

alias _root_.Filter.Tendsto.implicitFunction := tendsto_implicitFunction
#align filter.tendsto.implicit_function Filter.Tendsto.implicitFunction

/-- `HasStrictFDerivAt.implicitFunction` sends `(z, y)` to a point in `f ⁻¹' z`. -/
theorem map_implicitFunction_eq (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    ∀ᶠ p : F × ker f' in 𝓝 (f a, 0), f (hf.implicitFunction f f' hf' p.1 p.2) = p.1 :=
  haveI := FiniteDimensional.complete 𝕜 F
  map_implicitFunctionOfComplemented_eq ..
#align has_strict_fderiv_at.map_implicit_function_eq HasStrictFDerivAt.map_implicitFunction_eq

@[simp]
theorem implicitFunction_apply_image (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    hf.implicitFunction f f' hf' (f a) 0 = a := by
  haveI := FiniteDimensional.complete 𝕜 F
  apply implicitFunctionOfComplemented_apply_image
#align has_strict_fderiv_at.implicit_function_apply_image HasStrictFDerivAt.implicitFunction_apply_image

/-- Any point in some neighborhood of `a` can be represented as `HasStrictFDerivAt.implicitFunction`
of some point. -/
theorem eq_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    ∀ᶠ x in 𝓝 a,
      hf.implicitFunction f f' hf' (f x) (hf.implicitToPartialHomeomorph f f' hf' x).snd = x :=
  haveI := FiniteDimensional.complete 𝕜 F
  eq_implicitFunctionOfComplemented ..
#align has_strict_fderiv_at.eq_implicit_function HasStrictFDerivAt.eq_implicitFunction

theorem to_implicitFunction (hf : HasStrictFDerivAt f f' a) (hf' : range f' = ⊤) :
    HasStrictFDerivAt (hf.implicitFunction f f' hf' (f a)) (ker f').subtypeL 0 :=
  haveI := FiniteDimensional.complete 𝕜 F
  to_implicitFunctionOfComplemented ..
#align has_strict_fderiv_at.to_implicit_function HasStrictFDerivAt.to_implicitFunction

end FiniteDimensional

end HasStrictFDerivAt
