/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.TensorPower

/-!
# Exterior powers

We study the exterior powers of a module `M` over a commutative ring `R`.

## Definitions

* `exteriorPower.ιMulti` is the canonical alternating map on `M` with values in `⋀[R]^n M`.

* `exteriorPower.presentation R n M` is the standard presentation of the `R`-module `⋀[R]^n M`.

* `exteriorPower.map n f : ⋀[R]^n M →ₗ[R] ⋀[R]^n N` is the linear map on `nth` exterior powers
induced by a linear map `f : M →ₗ[R] N`. (See the file `Algebra.Category.ModuleCat.ExteriorPower`
for the corresponding functor `ModuleCat R ⥤ ModuleCat R`.)

* `exteriorPower.toTensorPower`: linear map from the `n`th exterior power to the `n`th
  tensor power (coming from `MultilinearMap.alternatization` via the universal property of
  exterior powers).

## Theorems
* The image of `exteriorPower.ιMulti` spans `⋀[R]^n M`.

* We construct `exteriorPower.alternatingMapLinearEquiv` which
expresses the universal property of the exterior power as a
linear equivalence `(M [⋀^Fin n]→ₗ[R] N) ≃ₗ[R] ⋀[R]^n M →ₗ[R] N` between
alternating maps and linear maps from the exterior power.

* `exteriorPower.map_injective_field`: If `f : M →ₗ[R] N` is injective and `R` is a field, then
  `exteriorPower.map n f` is injective.

* `exteriorPower.map_surjective`: If `f : M →ₗ[R] N` is surjective, then `exteriorPower.map n f`
  is surjective.

* `exteriorPower.mem_exteriorPower_is_mem_finite`: Every element of `⋀[R]^n M` is in the image of
  `⋀[R]^n P` for some finitely generated submodule `P` of `M`.

-/


open scoped TensorProduct

universe u v uM uN uN' uN'' uE uF

variable (R : Type u) (n : ℕ) {M : Type uM} {N : Type uN} {N' : Type uN'} {N'' : Type uN''}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup N']
  [Module R N'] [AddCommGroup N''] [Module R N'']

variable {K : Type v} {E : Type uE} {F : Type uF} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

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
    | .add m i x y => Finsupp.single ((update m i x)) 1 +
        Finsupp.single ((update m i y)) 1 -
        Finsupp.single ((update m i (x + y))) 1
    | .smul m i r x => Finsupp.single ((update m i (r • x))) 1 -
        r • Finsupp.single ((update m i x)) 1
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
      map_add' := fun m i x y ↦ by
        have := s.linearCombination_var_relation (.add m i x y)
        dsimp at this ⊢
        rw [map_sub, map_add, Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, one_smul,
          Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
        convert this.symm -- `convert` is necessary due to the implementation of `MultilinearMap`
      map_smul' := fun m i r x ↦ by
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
`alternatingMapLinearEqui n f` is the corresponding linear map from `⋀[R]^n M` to `N`,
and if `g` is a linear map from `N` to `N'`, then
the alternating map `g.compAlternatingMap f` from `M` to `N'` corresponds to the linear
map `g.comp (alternatingMapLinearEquiv n f)` on `⋀[R]^n M`. -/
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
  simp only [map, alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  rfl

@[simp]
theorem map_id :
    map n (LinearMap.id (R := R) (M := M)) = LinearMap.id := by
  aesop

@[simp]
theorem map_comp (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    map n (g ∘ₗ f) = map n g ∘ₗ map n f := by
  aesop

/-! Exactness properties of the exterior power functor. -/

variable (n)

/-- If a linear map has a retraction, then the map it induces on exterior powers is injective. -/
lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
    Function.Injective (map n f) :=
  let ⟨g, hgf⟩ := hf
  Function.RightInverse.injective (g := map n g)
    (fun _ ↦ by rw [← LinearMap.comp_apply, ← map_comp, hgf, map_id, LinearMap.id_coe, id_eq])

/-- If the base ring is a field, then any injective linear map induces an injective map on
exterior powers. -/
lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
    Function.Injective (map n f) :=
  map_injective n (LinearMap.exists_leftInverse_of_injective f hf)

/-- If a linear map is surjective, then the map it induces on exterior powers is surjective. -/
lemma map_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (map n f) := by
  rw [← LinearMap.range_eq_top]
  conv_lhs => rw [LinearMap.range_eq_map]
  rw [← ιMulti_span, ← ιMulti_span,
    Submodule.map_span, ← Set.range_comp, ← LinearMap.coe_compAlternatingMap, map_comp_ιMulti,
    AlternatingMap.coe_compLinearMap, Set.range_comp]
  conv_rhs => rw [← Set.image_univ]
  congr; apply congrArg
  exact Set.range_iff_surjective.mpr (fun y ↦ ⟨fun i => Classical.choose (hf (y i)),
    by ext i; simp only [Function.comp_apply]; exact Classical.choose_spec (hf (y i))⟩)

/-! From a family of vectors of `M` to a family of vectors if its `n`th exterior power. -/

variable (R)

/-- Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, produce the
family of `n`fold exterior products of elements of `v`, seen as members of the
`n`th exterior power. -/
noncomputable def ιMultiFamily {I : Type*} [LinearOrder I] (v : I → M) :
    {s : Finset I // Finset.card s = n} → ⋀[R]^n M :=
  fun ⟨s, hs⟩ => ιMulti R n (fun i => v (Finset.orderIsoOfFin s hs i))

@[simp]
lemma ιMultiFamily_coe {I : Type*} [LinearOrder I] (v : I → M) :
    ExteriorAlgebra.ιMulti_family R n v = (Submodule.subtype _) ∘ (ιMultiFamily R n v) := by
  ext s
  unfold ιMultiFamily
  simp only [Submodule.coe_subtype, Finset.coe_orderIsoOfFin_apply, Function.comp_apply,
    ιMulti_apply_coe]
  rfl

lemma map_ιMultiFamily {I : Type*} [LinearOrder I] (v : I → M) (f : M →ₗ[R] N) :
    (map n f) ∘ (ιMultiFamily R n v) = ιMultiFamily R n (f ∘ v) := by
  ext ⟨s, hs⟩
  unfold ιMultiFamily
  simp only [Finset.coe_orderIsoOfFin_apply, Function.comp_apply, map_apply_ιMulti,
    ιMulti_apply_coe]
  rfl

/-! Map to the tensor power. -/

variable (M)

/-- The linear map from the `n`th exterior power to the `n`th tensor power induced by
`MultilinearMap.alternarization`. -/
noncomputable def toTensorPower : ⋀[R]^n M →ₗ[R] (⨂[R]^n) M :=
  alternatingMapLinearEquiv <|
    MultilinearMap.alternatization (PiTensorProduct.tprod R (s := fun (_ : Fin n) => M))

variable {M}

open Equiv in
@[simp]
lemma toTensorPower_apply_ιMulti (v : Fin n → M) :
    toTensorPower R n M (ιMulti R n v) =
      ∑ σ : Perm (Fin n), Perm.sign σ • PiTensorProduct.tprod R (fun i => v (σ i)) := by
  simp only [toTensorPower, alternatingMapLinearEquiv_apply_ιMulti,
    MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply]

/-! Linear form on the exterior power induced by a family of linear forms on the module. This
is used to prove the linear independence of some families in the exterior power, cf.
`exteriorPower.linearFormOfBasis` and `exteriorPower.ιMulti_family_linearIndependent_ofBasis`. -/

/-- A family `f` indexed by `Fin n` of linear forms on `M` defines a linear form on the `n`th
exterior power of `M`, by composing the map `exteriorPower.toTensorPower` to the `n`th tensor
power and then applying `TensorPower.linearFormOfFamily` (which takes the product of the
components of `f`). -/
noncomputable def linearFormOfFamily (f : (_ : Fin n) → (M →ₗ[R] R)) :
    ⋀[R]^n M →ₗ[R] R :=
  TensorPower.linearFormOfFamily R n f ∘ₗ toTensorPower R n M

@[simp]
lemma linearFormOfFamily_apply (f : (_ : Fin n) → (M →ₗ[R] R)) (x : ⋀[R]^n M) :
    linearFormOfFamily R n f x = TensorPower.linearFormOfFamily R n f (toTensorPower R n M x) :=
  rfl

lemma linearFormOfFamily_apply_ιMulti (f : (_ : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    linearFormOfFamily R n f (ιMulti R n m) =
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, f i (m (σ i)) := by
  simp only [linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum,
    LinearMap.map_smul_of_tower, TensorPower.linearFormOfFamily_apply_tprod]

/-- If `f` is a family of linear forms on `M` (index by `Fin n`) and `p` is a linear map
from `N` to `M`, then the composition of `exteriorPower.linearFormOfFamily R n f` and
of `exteriorPower.map p` is equal to the linear form induced by the family
`fun i ↦ (f i).comp p`.. -/
lemma linearFormOfFamily_comp_map (f : (_ : Fin n) → (M →ₗ[R] R)) (p : N →ₗ[R] M) :
    (linearFormOfFamily R n f).comp (map n p) =
    linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) := by
  apply LinearMap.ext_on (ιMulti_span R n (M := N))
  intro x hx
  obtain ⟨y, h⟩ := Set.mem_range.mp hx
  simp only [← h, LinearMap.coe_comp, Function.comp_apply, map_apply_ιMulti,
    linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum, LinearMap.map_smul_of_tower,
    TensorPower.linearFormOfFamily_apply_tprod]

lemma linearFormOfFamily_comp_map_apply (f : (_ : Fin n) → (M →ₗ[R] R))
    (p : N →ₗ[R] M) (x : ⋀[R]^n N) :
    (linearFormOfFamily R n f) (map n p x) =
    linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) x := by
  rw [← LinearMap.comp_apply, linearFormOfFamily_comp_map]

/-- A family `f` of linear forms on `M` indexed by `Fin n` defines an `n`-fold alternating form
on `M`, by composing the linear form on `⋀[R]^n M` indeuced by `f` (defined in
`exteriorPower.linearFormOfFamily`) with the canonical `n`-fold alternating map from `M` to its
`n`th exterior power. -/
noncomputable def alternatingFormOfFamily (f : (_ : Fin n) → (M →ₗ[R] R)) :
    M [⋀^Fin n]→ₗ[R] R :=
  (linearFormOfFamily R n f).compAlternatingMap (ιMulti R n)

@[simp]
lemma alternatingFormOfFamily_apply (f : (_ : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    alternatingFormOfFamily R n f m = linearFormOfFamily R n f (ιMulti R n m) :=
  rfl

variable {R}

-- TO BE MOVED
lemma _root_.Submodule.exists_mem_span_finset {R : Type*} [Semiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {G : Set M} (hG : Submodule.span R G = ⊤) (v : M) :
    ∃ (S : Finset M) (_ : S ≤ G), v ∈ Submodule.span R (S : Set M) := by
  wlog hv : v ∈ Submodule.span R G
  · simp [hG] at hv
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨{v}, by simpa using hv, Submodule.subset_span (by simp)⟩
  | zero => exact ⟨⊥, by simp, by simp⟩
  | add v₁ v₂ _ _ h₁ h₂ =>
      classical
      obtain ⟨S₁, h₁, hv₁⟩ := h₁
      obtain ⟨S₂, h₂, hv₂⟩ := h₂
      refine ⟨S₁ ⊔ S₂, ?_, ?_⟩
      · simp only [Finset.sup_eq_union, Finset.coe_union, Set.le_eq_subset, Set.union_subset_iff]
        exact ⟨h₁, h₂⟩
      · exact Submodule.add_mem _ (Submodule.span_mono (le_sup_left (a := S₁)) hv₁)
          (Submodule.span_mono (le_sup_right (b := S₂)) hv₂)
  | smul r v _ h =>
      obtain ⟨S, hS, h'⟩ := h
      exact ⟨S, hS, Submodule.smul_mem _ _ h'⟩

/-- Every element of `⋀[R]^n M` is in the image of `⋀[R]^n P` for some finitely generated
submodule `P` of `M`. -/
lemma mem_exteriorPower_is_mem_finite (x : ⋀[R]^n M) :
    ∃ (P : Submodule R M), Submodule.FG P ∧ x ∈ LinearMap.range (map n (Submodule.subtype P)) := by
  classical
  obtain ⟨S, hS, hx⟩ := Submodule.exists_mem_span_finset (ιMulti_span R n M) x
  let m (s : S) : Fin n → M := (hS s.2).choose
  let φ : (Fin n → M) → Finset M := fun s ↦ Finset.image s ⊤
  refine ⟨_, Submodule.fg_span (Finset.finite_toSet ((Finset.image m ⊤).sup φ)),
    (?_ : Submodule.span _ _ ≤ _) hx⟩
  rw [Submodule.span_le]
  rintro s hs
  exact ⟨ιMulti _ _ (fun i ↦ ⟨m ⟨s, hs⟩ i, Submodule.subset_span
    (((Finset.le_sup (f := φ) (Finset.mem_image_of_mem _ (by simp)))
      (Finset.mem_image_of_mem _ (by simp))))⟩), by simpa using (hS hs).choose_spec⟩

end exteriorPower
