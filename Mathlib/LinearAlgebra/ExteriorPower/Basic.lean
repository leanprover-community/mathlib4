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

* `exteriorPower.map n f : ⋀[R]^n M →ₗ[R] ⋀[R]^n N` is the linear map on `nth` exterior powers
  induced by a linear map `f : M →ₗ[R] N`. (See the file `Algebra.Category.ModuleCat.ExteriorPower`
  for the corresponding functor `ModuleCat R ⥤ ModuleCat R`.)

## Theorems
* `exteriorPower.ιMulti_span`: The image of `exteriorPower.ιMulti` spans `⋀[R]^n M`.

* We construct `exteriorPower.alternatingMapLinearEquiv` which
  expresses the universal property of the exterior power as a
  linear equivalence `(M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] ⋀[R]^n M →ₗ[R] N` between
  alternating maps and linear maps from the exterior power.

-/

open scoped TensorProduct

universe u

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

/-- Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, produce the
family of `n`fold exterior products of elements of `v`, seen as members of the
`n`th exterior power. -/
noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M)
    (s : {s : Finset I // Finset.card s = n}) : ⋀[R]^n M :=
  ιMulti R n fun i ↦ v <| Finset.orderIsoOfFin s.val s.property i

@[simp] lemma ιMulti_family_apply_coe {I : Type*} [LinearOrder I] (v : I → M)
    (s : {s : Finset I // Finset.card s = n}) :
    ιMulti_family R n v s = ExteriorAlgebra.ιMulti_family R n v s := rfl

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
  relation
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
noncomputable def relationsSolutionEquiv {ι : Type*} [DecidableEq ι] {M : Type*}
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

/-- The universal property of the exterior power. -/
noncomputable def isPresentationCore :
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
  (presentation R n M).postcomp_injective (by ext f; apply DFunLike.congr_fun heq)

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

/-! Functoriality of the exterior powers. -/

variable (n) in
/-- The linear map between `n`th exterior powers induced by a linear map between the modules. -/
noncomputable def map (f : M →ₗ[R] N) : ⋀[R]^n M →ₗ[R] ⋀[R]^n N :=
  alternatingMapLinearEquiv ((ιMulti R n).compLinearMap f)

@[simp] lemma alternatingMapLinearEquiv_symm_map (f : M →ₗ[R] N) :
    alternatingMapLinearEquiv.symm (map n f) = (ιMulti R n).compLinearMap f := by
  simp only [map, LinearEquiv.symm_apply_apply]

@[simp]
theorem map_comp_ιMulti (f : M →ₗ[R] N) :
    (map n f).compAlternatingMap (ιMulti R n) = (ιMulti R n).compLinearMap f := by
  simp only [map, alternatingMapLinearEquiv_comp_ιMulti]

@[simp]
theorem map_apply_ιMulti (f : M →ₗ[R] N) (m : Fin n → M) :
    map n f (ιMulti R n m) = ιMulti R n (f ∘ m) := by
  simp only [map, alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply,
    Function.comp_def]

@[simp]
lemma map_comp_ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) (f : M →ₗ[R] N) :
    (map n f) ∘ (ιMulti_family R n v) = ιMulti_family R n (f ∘ v) := by
  ext ⟨s, hs⟩
  simp only [ιMulti_family, Function.comp_apply, map_apply_ιMulti]
  rfl

@[simp]
lemma map_apply_ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) (f : M →ₗ[R] N)
    (s : {s : Finset I // s.card = n}) :
    (map n f) (ιMulti_family R n v s) = ιMulti_family R n (f ∘ v) s := by
  simp only [ιMulti_family, map, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

@[simp]
theorem map_id :
    map n (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  aesop

@[simp]
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    map n (g ∘ₗ f) = map n g ∘ₗ map n f := by
  aesop

/-! Linear equivalences in degrees 0 and 1. -/

variable (R M) in
/-- The linear equivalence ` ⋀[R]^0 M ≃ₗ[R] R`. -/
@[simps! -isSimp symm_apply]
noncomputable def zeroEquiv : ⋀[R]^0 M ≃ₗ[R] R :=
  LinearEquiv.ofLinear
    (alternatingMapLinearEquiv (AlternatingMap.constOfIsEmpty R _ _ 1))
    { toFun := fun r ↦ r • (ιMulti _ _ (by rintro ⟨i, hi⟩; simp at hi))
      map_add' := by intros; simp only [add_smul]
      map_smul' := by intros; simp only [smul_eq_mul, mul_smul, RingHom.id_apply]}
    (by aesop) (by aesop)

@[simp]
lemma zeroEquiv_ιMulti (f : Fin 0 → M) :
    zeroEquiv R M (ιMulti _ _ f) = 1 := by
  simp [zeroEquiv]

lemma zeroEquiv_naturality (f : M →ₗ[R] N) :
    (zeroEquiv R N).comp (map 0 f) = zeroEquiv R M := by aesop

variable (R M) in
/-- The linear equivalence `M ≃ₗ[R] ⋀[R]^1 M`. -/
@[simps! -isSimp symm_apply]
noncomputable def oneEquiv : ⋀[R]^1 M ≃ₗ[R] M :=
  LinearEquiv.ofLinear
    (alternatingMapLinearEquiv (AlternatingMap.ofSubsingleton R M M (0 : Fin 1) .id)) (by
      have h (m : M) : (fun (_ : Fin 1) ↦ m) = update (fun _ ↦ 0) 0 m := by
        ext i
        fin_cases i
        rfl
      exact
        { toFun := fun m ↦ ιMulti _ _ (fun _ ↦ m)
          map_add' := fun m₁ m₂ ↦ by
            rw [h]; nth_rw 2 [h]; nth_rw 3 [h]
            simp only [Fin.isValue, AlternatingMap.map_update_add]
          map_smul' := fun r m ↦ by
            dsimp
            rw [h]; nth_rw 2 [h]
            simp only [Fin.isValue, AlternatingMap.map_update_smul] })
    (by aesop) (by aesop)

@[simp]
lemma oneEquiv_ιMulti (f : Fin 1 → M) :
    oneEquiv R M (ιMulti _ _ f) = f 0 := by
  simp [oneEquiv]

lemma oneEquiv_naturality (f : M →ₗ[R] N) :
    (oneEquiv R N).comp (map 1 f) = f.comp (oneEquiv R M).toLinearMap := by aesop

end exteriorPower
