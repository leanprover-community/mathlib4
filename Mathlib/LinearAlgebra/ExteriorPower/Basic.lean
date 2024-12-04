/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating

/-!
# Exterior powers

We study the exterior powers of a module `M` over a commutative ring `R`.

## Definitions

* `exteriorPower.ιMulti` is the canonical alternating map on `M` with values in `⋀[R]^n M`.

* `exteriorPower.presentation R n M` is the standard presentation of the `R`-module `⋀[R]^n M`.

## Theorems
* `ιMulti_span`: The image of `exteriorPower.ιMulti` spans `⋀[R]^n M`.

* We construct `exteriorPower.alternatingMapLinearEquiv` which
expresses the universal property of the exterior power as a
linear equivalence `(M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] ⋀[R]^n M →ₗ[R] N` between
alternating maps and linear maps from the exterior power.

-/

open scoped TensorProduct

universe u v uM uN uN' uN'' uE uF

variable (R : Type u) [CommRing R] (n : ℕ) {M N N' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module R N']

namespace exteriorPower

open Function

/-! The canonical alternating map from `Fin n → M` to `⋀[R]^n M`. -/

/-- `exteriorAlgebra.ιMulti` is the alternating map from `Fin n → M` to `⋀[r]^n M`
induced by `exteriorAlgebra.ιMulti`, i.e. sending a family of vectors `m : Fin n → M` to the
product of its entries. -/
def ιMulti : M [⋀^Fin n]→ₗ[R] (⋀[R]^n M) :=
  (ExteriorAlgebra.ιMulti R n).codRestrict (⋀[R]^n M) fun _ =>
    ExteriorAlgebra.ιMulti_range R n <| Set.mem_range_self _

@[simp] lemma ιMulti_apply_coe (a : Fin n → M) : ιMulti R n a = ExteriorAlgebra.ιMulti R n a := rfl

variable (M)
/-- The image of `ExteriorAlgebra.ιMulti R n` spans the `n`th exterior power. Variant of
`ExteriorAlgebra.ιMulti_span_fixedDegree`, useful in rewrites. -/
lemma ιMulti_span_fixedDegree :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) = ⋀[R]^n M :=
  ExteriorAlgebra.ιMulti_span_fixedDegree R n

/-- The image of `exteriorPower.ιMulti` spans `⋀[R]^n M`. -/
lemma ιMulti_span :
    Submodule.span R (Set.range (ιMulti R n)) = (⊤ : Submodule R (⋀[R]^n M)) := by
  apply LinearMap.map_injective (Submodule.ker_subtype (⋀[R]^n M))
  rw [LinearMap.map_span, ← Set.image_univ, Set.image_image]
  simp only [Submodule.coe_subtype, ιMulti_apply_coe, Set.image_univ, Submodule.map_top,
    Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_fixedDegree R n

namespace presentation

/-- The index type for the relations in the standard presentation of `⋀[R]^n M`,
in the particular case `ι` is `Fin n`. -/
inductive Rels (ι : Type*) (M : Type*)
  | add (m : ι → M) (i : ι) (x y : M)
  | smul (m : ι → M) (i : ι) (r : R) (x : M)
  | alt (m : ι → M) (i j : ι) (hm : m i = m j) (hij : i ≠ j)

/-- The relations in the standard presentation of `⋀[R]^n M` with generators and relations. -/
@[simps]
noncomputable def relations (ι : Type*) [DecidableEq ι] (M : Type*)
    [AddCommGroup M] [Module R M] :
    Module.Relations R where
  G := ι → M
  R := Rels R ι M
  relation r := match r with
    | .add m i x y => Finsupp.single (update m i x) 1 +
        Finsupp.single (update m i y) 1 -
        Finsupp.single (update m i (x + y)) 1
    | .smul m i r x => Finsupp.single (update m i (r • x)) 1 -
        r • Finsupp.single (update m i x) 1
    | .alt m _ _ _ _ => Finsupp.single m 1

variable {R} in
/-- The solutions in a module `N` to the linear equations
given by `exteriorPower.relations R ι M` identify to alternating maps to `N`. -/
@[simps!]
def relationsSolutionEquiv {ι : Type*} [DecidableEq ι] {M : Type*}
    [AddCommGroup M] [Module R M] :
    (relations R ι M).Solution N ≃ AlternatingMap R M N ι where
  toFun s :=
    { toFun := fun m ↦ s.var m
      map_update_add' := fun m i x y ↦ by
        have := s.linearCombination_var_relation (.add m i x y)
        dsimp at this ⊢
        rw [map_sub, map_add, Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
        convert this.symm -- `convert` is necessary due to the implementation of `MultilinearMap`
      map_update_smul' := fun m i r x ↦ by
        have := s.linearCombination_var_relation (.smul m i r x)
        dsimp at this ⊢
        rw [Finsupp.smul_single, smul_eq_mul, mul_one, map_sub,
          Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, sub_eq_zero] at this
        convert this
      map_eq_zero_of_eq' := fun v i j hm hij ↦
        by simpa using s.linearCombination_var_relation (.alt v i j hm hij) }
  invFun f :=
    { var := fun m ↦ f m
      linearCombination_var_relation := by
        rintro (⟨m, i, x, y⟩ | ⟨m, i, r, x⟩ | ⟨v, i, j, hm, hij⟩)
        · simp
        · simp
        · simpa using f.map_eq_zero_of_eq v hm hij }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The universal property of the exterior power. -/
def isPresentationCore :
    (relationsSolutionEquiv.symm (ιMulti R n (M := M))).IsPresentationCore where
  desc s := LinearMap.comp (ExteriorAlgebra.liftAlternating
      (Function.update 0 n (relationsSolutionEquiv s))) (Submodule.subtype _)
  postcomp_desc s := by aesop
  postcomp_injective {N _ _ f f' h} := by
    rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _ (ιMulti_span R n M)]
    rintro ⟨_, ⟨f, rfl⟩⟩
    exact Module.Relations.Solution.congr_var h f

end presentation

/-- The standard presentation of the `R`-module `⋀[R]^n M`. -/
@[simps! G R relation var]
noncomputable def presentation : Module.Presentation R (⋀[R]^n M) :=
  .ofIsPresentation (presentation.isPresentationCore R n M).isPresentation

variable {R M n}

/-- Two linear maps on `⋀[R]^n M` that agree on the image of `exteriorPower.ιMulti`
are equal. -/
@[ext]
lemma linearMap_ext {f : ⋀[R]^n M →ₗ[R] N} {g : ⋀[R]^n M →ₗ[R] N}
    (heq : f.compAlternatingMap (ιMulti R n) = g.compAlternatingMap (ιMulti R n)) : f = g :=
  (presentation R n M).postcomp_injective (by ext f; apply DFunLike.congr_fun heq )

/-- The linear equivalence between `n`-fold alternating maps from `M` to `N` and linear maps from
`⋀[R]^n M` to `N`: this is the universal property of the `n`th exterior power of `M`. -/
noncomputable def alternatingMapLinearEquiv : (M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] ⋀[R]^n M →ₗ[R] N :=
  LinearEquiv.symm
    (Equiv.toLinearEquiv
      ((presentation R n M).linearMapEquiv.trans presentation.relationsSolutionEquiv)
      { map_add := fun _ _ => rfl
        map_smul := fun _ _ => rfl })

@[simp]
lemma alternatingMapLinearEquiv_comp_ιMulti (f : M [⋀^Fin n]→ₗ[R] N) :
    (alternatingMapLinearEquiv f).compAlternatingMap (ιMulti R n) = f := by
  obtain ⟨φ, rfl⟩ := alternatingMapLinearEquiv.symm.surjective f
  dsimp [alternatingMapLinearEquiv]
  simp only [LinearEquiv.symm_apply_apply]
  rfl

@[simp]
lemma alternatingMapLinearEquiv_apply_ιMulti (f : M [⋀^Fin n]→ₗ[R] N) (a : Fin n → M) :
    alternatingMapLinearEquiv f (ιMulti R n a) = f a :=
  DFunLike.congr_fun (alternatingMapLinearEquiv_comp_ιMulti f) a

@[simp]
lemma alternatingMapLinearEquiv_symm_apply (F : ⋀[R]^n M →ₗ[R] N) (m : Fin n → M) :
    alternatingMapLinearEquiv.symm F m = F.compAlternatingMap (ιMulti R n) m := by
  obtain ⟨f, rfl⟩ := alternatingMapLinearEquiv.surjective F
  simp only [LinearEquiv.symm_apply_apply, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]
lemma alternatingMapLinearEquiv_ιMulti :
    alternatingMapLinearEquiv (ιMulti R n (M := M)) = LinearMap.id := by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, ιMulti_apply_coe,
    LinearMap.compAlternatingMap_apply, LinearMap.id_coe, id_eq]

/-- If `f` is an alternating map from `M` to `N`,
`alternatingMapLinearEquiv f` is the corresponding linear map from `⋀[R]^n M` to `N`,
and if `g` is a linear map from `N` to `N'`, then
the alternating map `g.compAlternatingMap f` from `M` to `N'` corresponds to the linear
map `g.comp (alternatingMapLinearEquiv f)` on `⋀[R]^n M`. -/
lemma alternatingMapLinearEquiv_comp (g : N →ₗ[R] N') (f : M [⋀^Fin n]→ₗ[R] N) :
    alternatingMapLinearEquiv (g.compAlternatingMap f) = g.comp (alternatingMapLinearEquiv f) := by
  ext
  simp only [alternatingMapLinearEquiv_comp_ιMulti, LinearMap.compAlternatingMap_apply,
    LinearMap.coe_comp, comp_apply, alternatingMapLinearEquiv_apply_ιMulti]

end exteriorPower
