/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.TensorPower

/-! Add description.


This file introduces the notation `Λ[R]^n M` for `ExteriorPower R n M`, which in turn is
an abbreviation for `LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n`.
-/

open BigOperators
open scoped TensorProduct

universe u v uM uN uN' uN'' uE uF

variable {R : Type u}{n : ℕ} {M : Type uM} {N : Type uN} {N' : Type uN'} {N'' : Type uN''}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup N']
  [Module R N'] [AddCommGroup N''] [Module R N'']

variable {K : Type v} {E : Type uE} {F: Type uF} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

variable (R M n)

/--Definition of the `n`th exterior power of a `R`-module `M`. We introduce the notation
`Λ[R]^n M` for `ExteriorPower R n M`.-/
@[reducible]
def ExteriorPower := (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n)

@[inherit_doc]
notation:100 "Λ[" R "]^" n:arg => ExteriorPower R n

variable {M}

namespace ExteriorPower

/-! The canonical alternating from `Fin n → M` to `Λ[R]^n M`.-/

/-- `ExteriorAlgebra.ιMulti` is the alternating map from `Fin n → M` to `Λ[r]^n M`
induced by `ExteriorAlgebra.ιMulti`, i.e. sending a family of vectors `m : Fin n → M` to the
product of its entries.-/
def ιMulti : AlternatingMap R M ((Λ[R]^n) M) (Fin n) :=
  AlternatingMap.codRestrict (ExteriorAlgebra.ιMulti R n) ((Λ[R]^n) M)
  (fun _ => ExteriorAlgebra.ιMulti_range R n (by simp only [Set.mem_range, exists_apply_eq_apply]))

@[simp] lemma ιMulti_apply (a : Fin n → M) :
ιMulti R n a = ExteriorAlgebra.ιMulti R n a := by
  unfold ιMulti
  simp only [AlternatingMap.codRestrict_apply_coe]

/-- The image of `ExteriorAlgebra.ιMulti R n` spans the `n`th exterior power. Variant of
`ExteriorAlgebra.ιMulti_span_fixedDegree`, useful in rewrites.-/
lemma ιMulti_span_fixedDegree :
    Submodule.span R (Set.range (ExteriorAlgebra.ιMulti R n)) = (Λ[R]^n) M :=
  ExteriorAlgebra.ιMulti_span_fixedDegree R n

/-- The image of `ExteriorPower.ιMulti` spans `Λ[R]^n M`.-/
lemma ιMulti_span :
    Submodule.span R (Set.range (ιMulti R n)) = (⊤ : Submodule R ((Λ[R]^n) M)) := by
  apply LinearMap.map_injective (Submodule.ker_subtype ((Λ[R]^n) M))
  rw [LinearMap.map_span, ← Set.image_univ, Set.image_image]
  simp only [Submodule.coeSubtype, ιMulti_apply, Set.image_univ, Submodule.map_top,
    Submodule.range_subtype]
  exact ExteriorAlgebra.ιMulti_span_fixedDegree R n

/-- Two linear maps on `Λ[R]^n M` that agree on the image of `ExteriorPower.ιMulti`
are equal.-/
@[ext]
lemma lhom_ext ⦃f : (Λ[R]^n) M →ₗ[R] N⦄ ⦃g : (Λ[R]^n) M →ₗ[R] N⦄
    (heq : (LinearMap.compAlternatingMap f) (ιMulti R n) =
    (LinearMap.compAlternatingMap g) (ιMulti R n)) : f = g := by
  ext u
  have hu : u ∈ (⊤ : Submodule R ((Λ[R]^n) M)) := Submodule.mem_top
  rw [← ιMulti_span] at hu
  apply Submodule.span_induction hu (p := fun u => f u = g u)
  · exact fun _ h ↦ by
      let ⟨a, ha⟩ := Set.mem_range.mpr h
      apply_fun (fun F => F a) at heq; simp only [LinearMap.compAlternatingMap_apply] at heq
      rw [← ha, heq]
  · rw [LinearMap.map_zero, LinearMap.map_zero]
  · exact fun _ _ h h' => by rw [LinearMap.map_add, LinearMap.map_add, h, h']
  · exact fun _ _ h => by rw [LinearMap.map_smul, LinearMap.map_smul, h]

/-! The universal property of the `n`th exterior power of `M`: linear maps from
`Λ[R]^n M` to a module `N` are in linear equivalence with `n`-fold alternating maps from
`M` to `N`-/

variable {R}

def liftAlternating_aux : (AlternatingMap R M N (Fin n)) →ₗ[R]
((i : ℕ) → AlternatingMap R M N (Fin i)) :=
  LinearMap.pi (fun i ↦ if h : i = n then by rw [h]; exact LinearMap.id else 0)

/-- The linear map from `n`-fold alternating maps from `M` to `N` to linear maps from
`Λ[R]^n M` to `N`-/
def liftAlternating : (AlternatingMap R M N (Fin n)) →ₗ[R] (Λ[R]^n) M →ₗ[R] N where
  toFun f := LinearMap.domRestrict (LinearMap.comp (ExteriorAlgebra.liftAlternating (R := R)
    (M := M) (N :=N)) (liftAlternating_aux n) f) ((Λ[R]^n) M)
  map_add' f g := by ext u; simp only [map_add, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.compAlternatingMap_apply, LinearMap.domRestrict_apply, ιMulti_apply,
    LinearMap.add_apply, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  map_smul' a f := by ext u; simp only [map_smul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.compAlternatingMap_apply, LinearMap.domRestrict_apply, ιMulti_apply,
    LinearMap.smul_apply, ExteriorAlgebra.liftAlternating_apply_ιMulti, RingHom.id_apply]

variable (R)

@[simp] lemma liftAlternating_apply_ιMulti (f : AlternatingMap R M N (Fin n)) (a : Fin n → M) :
    liftAlternating n f (ιMulti R n a) = f a := by
  unfold liftAlternating
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.domRestrict_apply]
  rw [ιMulti_apply, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  unfold liftAlternating_aux
  simp only [eq_mpr_eq_cast, LinearMap.pi_apply, cast_eq, dite_eq_ite, ite_true,
    LinearMap.id_coe, id_eq]

@[simp] lemma liftAlternating_comp_ιMulti (f : AlternatingMap R M N (Fin n)) :
    (LinearMap.compAlternatingMap (liftAlternating n f)) (ιMulti R n) = f := by
  ext a
  simp only [LinearMap.compAlternatingMap_apply]
  rw [liftAlternating_apply_ιMulti]

@[simp] lemma liftAlternating_ιMulti :
    liftAlternating n (R := R) (M := M) (ιMulti R n) = LinearMap.id := by
  ext u
  simp only [liftAlternating_comp_ιMulti, ιMulti_apply, LinearMap.compAlternatingMap_apply,
    LinearMap.id_coe, id_eq]

/-- If `f` is an alternating map from `M` to `N`, `liftAlternating n f` is the corresponding
linear map from `Λ[R]^n M` to `N` and `g` is a linear map from `N` to `N'`, then
the alternating map `g.compAlternatingMap f` from `M` to `N'` corresponds to the linear
map `g.comp (liftAlternating n f)` on `Λ[R]^n M`.-/
@[simp]
lemma liftAlternating_comp (g : N →ₗ[R] N') (f : AlternatingMap R M N (Fin n)) :
    liftAlternating n (g.compAlternatingMap f) = g.comp (liftAlternating n f) := by
  ext u
  simp only [liftAlternating_comp_ιMulti, LinearMap.compAlternatingMap_apply, LinearMap.coe_comp,
    Function.comp_apply, liftAlternating_apply_ιMulti]

/-- The linear equivalence between `n`-fold alternating maps from `M` to `N` and linear maps from
`Λ[R]^n M` to `N`.-/
@[simps!]
def liftAlternatingEquiv : AlternatingMap R M N (Fin n) ≃ₗ[R] (Λ[R]^n) M →ₗ[R] N :=
  LinearEquiv.ofLinear (liftAlternating n)
  {toFun := fun F ↦ F.compAlternatingMap (ιMulti R n)
   map_add' := by intro F G; ext x
                  simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply,
                    AlternatingMap.add_apply]
   map_smul' := by intro a F; ext x
                   simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
                     RingHom.id_apply, AlternatingMap.smul_apply]}
  (by ext _; simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        liftAlternating_comp, liftAlternating_ιMulti, LinearMap.comp_id,
        LinearMap.compAlternatingMap_apply, LinearMap.id_coe, id_eq])
  (by ext _; simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        liftAlternating_comp_ιMulti, LinearMap.id_coe, id_eq])

@[simp]
lemma liftAlternatingEquiv_apply (f :AlternatingMap R M N (Fin n)) (x : (Λ[R]^n) M) :
  ExteriorPower.liftAlternatingEquiv R n f x = ExteriorPower.liftAlternating n f x := rfl

@[simp]
lemma liftAlternatingEquiv_symm_apply (F : (Λ[R]^n) M →ₗ[R] N) (m : Fin n → M) :
  (ExteriorPower.liftAlternatingEquiv R n).symm F m = F.compAlternatingMap (ιMulti R n) m := rfl

/-! Functoriality of the exterior powers.-/

variable {R}

/-- The linear map between `n`th exterior powers induced by a linear map between the modules.-/
def map (f : M →ₗ[R] N) : (Λ[R]^n) M →ₗ[R] (Λ[R]^n) N := by
  refine LinearMap.restrict (AlgHom.toLinearMap (ExteriorAlgebra.map f)) ?_
  intro x hx
  rw [← ιMulti_span_fixedDegree] at hx ⊢
  have hx := Set.mem_image_of_mem (ExteriorAlgebra.map f) hx
  rw [← Submodule.map_coe, LinearMap.map_span, ←Set.range_comp] at hx
  erw [← (LinearMap.coe_compAlternatingMap (ExteriorAlgebra.map f).toLinearMap
    (ExteriorAlgebra.ιMulti R n))] at hx
  rw [ExteriorAlgebra.map_comp_ιMulti, AlternatingMap.coe_compLinearMap] at hx
  exact Set.mem_of_mem_of_subset hx (Submodule.span_mono (Set.range_comp_subset_range _ _))

@[simp]
theorem map_apply_ιMulti (f : M →ₗ[R] N) (m : Fin n → M) :
    (map n f) ((ιMulti R n) m) = (ιMulti R n) (f ∘ m) := by
  unfold map
  rw [LinearMap.restrict_apply, ← SetCoe.ext_iff]
  simp only [ιMulti_apply, AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti]

@[simp]
theorem map_comp_ιMulti (f : M →ₗ[R] N) :
    (map n f).compAlternatingMap (ιMulti R n (M := M)) = (ιMulti R n (M := N)).compLinearMap f := by
  unfold map
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.restrict_coe_apply, ιMulti_apply,
    AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti, AlternatingMap.compLinearMap_apply]
  congr

@[simp]
theorem map_id :
    map n (LinearMap.id) = LinearMap.id (R := R) (M := (Λ[R]^n) M) := by
  unfold map
  ext m
  simp only [ExteriorAlgebra.map_id, AlgHom.toLinearMap_id, LinearMap.compAlternatingMap_apply,
    LinearMap.restrict_coe_apply, ιMulti_apply, LinearMap.id_coe, id_eq]

@[simp]
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    LinearMap.comp (map n g) (map n f) = map n (LinearMap.comp g f) := by
  unfold map
  ext m
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.restrict_coe_apply, ιMulti_apply, AlgHom.toLinearMap_apply,
    ExteriorAlgebra.map_apply_ιMulti, Function.comp.assoc]

/-! Exactness properties of the exterior power functor.-/

/-- If a linear map has a retraction, then the map it induces on exterior powers is injective.-/
lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
    Function.Injective (map n f) :=
  let ⟨g, hgf⟩ := hf
  Function.RightInverse.injective (g := map n g)
    (fun _ ↦ by rw [← LinearMap.comp_apply, map_comp_map, hgf, map_id, LinearMap.id_coe, id_eq])

/-- If the base ring is a field, then any injective linear map induces an injective map on
exterior powers.-/
lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
    Function.Injective (map n f) :=
  map_injective n (LinearMap.exists_leftInverse_of_injective f hf)

/-- If a linear map is surjective, then the map it induces on exterior powers is surjective.-/
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

/-! From a family of vectors of `M` to a family of vectors if its `n`th exterior power.-/

variable (R)

/-- Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, produce the
family of `n`fold exterior products of elements of `v`, seen as members of the
`n`th exterior power.-/
noncomputable def ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) :
    {s : Finset I // Finset.card s = n} → (Λ[R]^n) M :=
  fun ⟨s, hs⟩ => ιMulti R n (fun i => v (Finset.orderIsoOfFin s hs i))

@[simp]
lemma ιMulti_family_coe {I : Type*} [LinearOrder I] (v : I → M) :
    ExteriorAlgebra.ιMulti_family R n v = (Submodule.subtype _) ∘ (ιMulti_family R n v) := by
  ext s
  unfold ιMulti_family
  simp only [Submodule.coeSubtype, Finset.coe_orderIsoOfFin_apply, Function.comp_apply,
    ιMulti_apply]
  rfl

lemma map_ιMulti_family {I : Type*} [LinearOrder I] (v : I → M) (f : M →ₗ[R] N) :
    (map n f) ∘ (ιMulti_family R n v) = ιMulti_family R n (f ∘ v) := by
  ext ⟨s, hs⟩
  unfold ιMulti_family
  simp only [Finset.coe_orderIsoOfFin_apply, Function.comp_apply, map_apply_ιMulti, ιMulti_apply]
  congr

/-! Map to the tensor power.-/

variable (M)

/-- The linear map from the `n`th exterior power to the `n`th tensor power induced by
`MultilinearMap.alternarization`.-/
noncomputable def toTensorPower : (Λ[R]^n) M →ₗ[R] (⨂[R]^n) M :=
  liftAlternatingEquiv R n
  (MultilinearMap.alternatization (PiTensorProduct.tprod R (s := fun (_ : Fin n) => M)))

variable {M}

open Equiv in
@[simp]
lemma toTensorPower_apply_ιMulti (v : Fin n → M) : toTensorPower R n M (ιMulti R n v) =
    ∑ σ : Perm (Fin n), Perm.sign σ • (PiTensorProduct.tprod R (fun i => v (σ i))) := by
  unfold toTensorPower
  simp only [liftAlternatingEquiv_apply, liftAlternating_apply_ιMulti]
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply]

/-! Linear form on the exterior power induced by a family of linear forms on the module.-/

/-- A family `f` indexed by `Fin n` of linear forms on `M` defines a linear form on the `n`th
exterior power of `M`, by composing the map `ExteriorPower.toTensorPower` to the `n`th tensor
power and then applying `TensorPower.linearFormOfFamily` (which takes the product of the
components of `f`).-/
noncomputable def linearFormOfFamily (f : (_ : Fin n) → (M →ₗ[R] R)) :
    (Λ[R]^n) M →ₗ[R] R :=
  LinearMap.comp (TensorPower.linearFormOfFamily R n f) (toTensorPower R n M)

@[simp]
lemma linearFormOfFamily_apply (f : (_ : Fin n) → (M →ₗ[R] R)) (x : (Λ[R]^n) M) :
    linearFormOfFamily R n f x = TensorPower.linearFormOfFamily R n f (toTensorPower R n M x) := by
  unfold linearFormOfFamily
  simp only [LinearMap.coe_comp, Function.comp_apply]

@[simp]
lemma linearFormOfFamily_apply_ιMulti (f : (_ : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    linearFormOfFamily R n f (ιMulti R n m) =
    ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, f i (m (σ i)) := by
  simp only [linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum,
    LinearMap.map_smul_of_tower, TensorPower.linearFormOfFamily_apply_tprod]

/-- If `f` is a family of linear forms on `M` (index by `Fin n`) and `p` is a linear map
from `N` to `M`, then the composition of `ExteriorPower.linearFormOfFamily R n f` and
of `ExteriorPower.map p` is equal to the linear form induced by the family
`fun i ↦ (f i).comp p`..-/
lemma linearFormOfFamily_comp_map (f : (_ : Fin n) → (M →ₗ[R] R)) (p : N →ₗ[R] M) :
    (linearFormOfFamily R n f).comp (map n p) =
    linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) := by
  apply LinearMap.ext_on (ιMulti_span R n (M := N))
  intro x hx
  obtain ⟨y, h⟩ := Set.mem_range.mp hx
  simp only [← h, LinearMap.coe_comp, Function.comp_apply, map_apply_ιMulti,
    linearFormOfFamily_apply, toTensorPower_apply_ιMulti, map_sum, LinearMap.map_smul_of_tower,
    TensorPower.linearFormOfFamily_apply_tprod]

@[simp]
lemma linearFormOfFamily_comp_map_apply (f : (_ : Fin n) → (M →ₗ[R] R))
    (p : N →ₗ[R] M) (x : (Λ[R]^n) N) :
    (linearFormOfFamily R n f) (map n p x) =
    linearFormOfFamily R n (fun (i : Fin n) => (f i).comp p) x := by
  rw [← LinearMap.comp_apply, linearFormOfFamily_comp_map]

/-- A family `f` of linear forms on `M` indexed by `Fin n` defines an `n`-fold alternating form
on `M`, by composing the linear form on `Λ[R]^n M` indeuced by `f` (defined in
`ExteriorPower.linearFormOfFamily`) with the canonical `n`-fold alternating map from `M` to its
`n`th exterior power.-/
noncomputable def alternatingFormOfFamily (f : (_ : Fin n) → (M →ₗ[R] R)) :
    AlternatingMap R M R (Fin n) :=
  (linearFormOfFamily R n f).compAlternatingMap (ιMulti R n)

@[simp]
lemma alternatingFormOfFamily_apply (f : (_ : Fin n) → (M →ₗ[R] R)) (m : Fin n → M) :
    alternatingFormOfFamily R n f m = linearFormOfFamily R n f (ιMulti R n m) := by
  unfold alternatingFormOfFamily
  rw [LinearMap.compAlternatingMap_apply]

variable {R}

/-
lemma _root_.Submodule.map_subtype (P Q : Submodule R M) (hPQ : P ≤ Q) :
    ∃ (f : P →ₗ[R] Q), Q.subtype.comp f = P.subtype :=
  ⟨Submodule.inclusion hPQ, Submodule.subtype_comp_inclusion P Q hPQ⟩
-/

lemma sum_range_map (f : N →ₗ[R] M) (f' : N' →ₗ[R] M) (f'' : N''→ₗ[R] M)
  (hf : ∃ (g : N →ₗ[R] N''), f''.comp g = f) (hf' : ∃ (g' : N' →ₗ[R] N''), f''.comp g' = f') :
    LinearMap.range (map n f) ⊔ LinearMap.range (map n f') ≤ LinearMap.range (map n f'') := by
  let ⟨g, hg⟩ := hf
  let ⟨g', hg'⟩ := hf'
  intro x
  simp only [Submodule.mem_sup, LinearMap.mem_range]
  intro ⟨x₁, ⟨⟨y, hy⟩, ⟨x₂, ⟨⟨y', hy'⟩, hx⟩⟩⟩⟩
  existsi map n g y + map n g' y'
  rw [← hx, ← hy, ← hy', ← hg, ← hg', ← map_comp_map, ← map_comp_map, map_add,
    LinearMap.comp_apply, LinearMap.comp_apply]

/-- Every element of `Λ[R]^n M` is in the image of `Λ[R]^n P` for some finitely generated
submodule P of M.-/
lemma mem_exteriorPower_is_mem_finite (x : (Λ[R]^n) M) :
    ∃ (P : Submodule R M), Submodule.FG P ∧ x ∈ LinearMap.range (map n (Submodule.subtype P)) := by
  have hx : x ∈ (⊤ : Submodule R ((Λ[R]^n) M)) := by simp only [Submodule.mem_top]
  rw [← ιMulti_span] at hx
  refine Submodule.span_induction hx (p := fun x => ∃ (P : Submodule R M),
    P.FG ∧ x ∈ LinearMap.range (map n P.subtype)) ?_ ⟨(⊥ : Submodule R M), ⟨Submodule.fg_bot,
    Submodule.zero_mem _⟩⟩ (fun _ _ ⟨Px, hx⟩ ⟨Py, hy⟩ ↦ ⟨Px ⊔ Py, ⟨Submodule.FG.sup hx.1 hy.1,
      sum_range_map n Px.subtype Py.subtype _
      ⟨Submodule.inclusion le_sup_left, Submodule.subtype_comp_inclusion Px _ le_sup_left⟩
      ⟨Submodule.inclusion le_sup_right, Submodule.subtype_comp_inclusion Py _ le_sup_right⟩
      (Submodule.add_mem_sup hx.2 hy.2)⟩⟩)
      (fun a x ⟨P, h⟩ ↦ ⟨P, ⟨h.1, Submodule.smul_mem _ a h.2⟩⟩)
  intro x hx
  obtain ⟨m, hmx⟩ := Set.mem_range.mp hx
  existsi Submodule.span R (Set.range m)
  rw [and_iff_right (Submodule.fg_span (Set.finite_range m)), LinearMap.mem_range]
  existsi ιMulti R n (fun i => ⟨m i, Submodule.subset_span (by simp only [Set.mem_range,
    exists_apply_eq_apply])⟩)
  simp only [Subtype.mk.injEq, map_apply_ιMulti, Submodule.coeSubtype,
    Function.comp_apply, ← hmx]
  congr

end ExteriorPower
