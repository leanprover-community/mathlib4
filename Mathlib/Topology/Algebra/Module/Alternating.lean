/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Sébastien Gouëzel
-/
import Mathlib.LinearAlgebra.Alternating
import Mathlib.Topology.Algebra.Module.Multilinear

/-!
# Continuous alternating multilinear maps

In this file we define bundled continuous alternating maps and develop basic API about these
maps, by reusing API about continuous multilinear maps and alternating maps.

## Keywords

multilinear map, alternating map, continuous
-/

open Function Matrix

open scoped BigOperators

/-- A continuous alternating map is a continuous map from `ι → M` to `N` that is

- multilinear : `f (update m i (c • x)) = c • f (update m i x)` and
  `f (update m i (x + y)) = f (update m i x) + f (update m i y)`;
- alternating `f v = 0` whenever `v` has two equal coordinates.
-/
structure ContinuousAlternatingMap (R M N ι : Type _) [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] [AddCommMonoid N] [Module R N] [TopologicalSpace N] extends
    ContinuousMultilinearMap R (fun _ : ι => M) N where
  map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → toFun v = 0
#align continuous_alternating_map ContinuousAlternatingMap

notation "Λ^" ι "⟮" R "; " M "; " N "⟯" => ContinuousAlternatingMap R M N ι

namespace ContinuousAlternatingMap

section Semiring

variable {R M M' N N' ι : Type _} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N] [Module R N]
  [TopologicalSpace N] [AddCommMonoid N'] [Module R N'] [TopologicalSpace N'] {n : ℕ}
  (f g : Λ^ι⟮R; M; N⟯)

theorem toContinuousMultilinearMap_injective :
    Injective (ContinuousAlternatingMap.toContinuousMultilinearMap :
      Λ^ι⟮R; M; N⟯ → ContinuousMultilinearMap R (fun _ : ι => M) N)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align continuous_alternating_map.to_continuous_multilinear_map_injective ContinuousAlternatingMap.toContinuousMultilinearMap_injective

theorem range_toContinuousMultilinearMap :
    Set.range
        (toContinuousMultilinearMap :
          Λ^ι⟮R; M; N⟯ → ContinuousMultilinearMap R (fun _ : ι => M) N) =
      {f | ∀ (v : ι → M) (i j : ι), v i = v j → i ≠ j → f v = 0} :=
  Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.2, fun h => ⟨⟨f, h⟩, rfl⟩⟩
#align continuous_alternating_map.range_to_continuous_multilinear_map ContinuousAlternatingMap.range_toContinuousMultilinearMap

instance continuousMapClass : ContinuousMapClass Λ^ι⟮R; M; N⟯ (ι → M) N
    where
  coe f := f.toFun
  coe_injective' _ _ h := toContinuousMultilinearMap_injective <| FunLike.ext' h
  map_continuous f := f.cont
#align continuous_alternating_map.continuous_map_class ContinuousAlternatingMap.continuousMapClass

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (f : Λ^ι⟮R; M; N⟯) : (ι → M) → N :=
  f
#align continuous_alternating_map.simps.apply ContinuousAlternatingMap.Simps.apply

initialize_simps_projections ContinuousAlternatingMap (toFun → apply)

@[continuity]
theorem coe_continuous : Continuous f := f.cont
#align continuous_alternating_map.coe_continuous ContinuousAlternatingMap.coe_continuous

@[simp]
theorem coe_toContinuousMultilinearMap : ⇑f.toContinuousMultilinearMap = f :=
  rfl
#align continuous_alternating_map.coe_to_continuous_multilinear_map ContinuousAlternatingMap.coe_toContinuousMultilinearMap

@[simp]
theorem coe_mk (f : ContinuousMultilinearMap R (fun _ : ι => M) N) (h) : ⇑(mk f h) = f :=
  rfl
#align continuous_alternating_map.coe_mk ContinuousAlternatingMap.coe_mk

@[ext]
theorem ext {f g : Λ^ι⟮R; M; N⟯} (H : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ H
#align continuous_alternating_map.ext ContinuousAlternatingMap.ext

theorem ext_iff {f g : Λ^ι⟮R; M; N⟯} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align continuous_alternating_map.ext_iff ContinuousAlternatingMap.ext_iff

/-- Projection to `AlternatingMap`s. -/
def toAlternatingMap : AlternatingMap R M N ι :=
  { f with }
#align continuous_alternating_map.to_alternating_map ContinuousAlternatingMap.toAlternatingMap

@[simp] theorem toAlternatingMap_coe : ⇑f.toAlternatingMap = f := rfl
theorem toAlternatingMap_apply : f.toAlternatingMap v = f v := rfl

theorem toAlternatingMap_injective :
    Injective (toAlternatingMap : Λ^ι⟮R; M; N⟯ → AlternatingMap R M N ι) := fun f g h =>
  FunLike.ext' <| by convert FunLike.ext'_iff.1 h
#align continuous_alternating_map.to_alternating_map_injective ContinuousAlternatingMap.toAlternatingMap_injective

@[simp]
theorem range_toAlternatingMap :
    Set.range (toAlternatingMap : Λ^ι⟮R; M; N⟯ → AlternatingMap R M N ι) =
      {f : AlternatingMap R M N ι | Continuous f} :=
  Set.ext fun f => ⟨fun ⟨g, hg⟩ => hg ▸ g.cont, fun h => ⟨{ f with cont := h }, FunLike.ext' rfl⟩⟩
#align continuous_alternating_map.range_to_alternating_map ContinuousAlternatingMap.range_toAlternatingMap

@[simp]
theorem map_add [DecidableEq ι] (m : ι → M) (i : ι) (x y : M) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_add' m i x y
#align continuous_alternating_map.map_add ContinuousAlternatingMap.map_add

@[simp]
theorem map_smul [DecidableEq ι] (m : ι → M) (i : ι) (c : R) (x : M) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_smul' m i c x
#align continuous_alternating_map.map_smul ContinuousAlternatingMap.map_smul

theorem map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h
#align continuous_alternating_map.map_coord_zero ContinuousAlternatingMap.map_coord_zero

@[simp]
theorem map_update_zero [DecidableEq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
  f.toMultilinearMap.map_update_zero m i
#align continuous_alternating_map.map_update_zero ContinuousAlternatingMap.map_update_zero

@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero
#align continuous_alternating_map.map_zero ContinuousAlternatingMap.map_zero

theorem map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) : f v = 0 :=
  f.map_eq_zero_of_eq' v i j h hij
#align continuous_alternating_map.map_eq_zero_of_eq ContinuousAlternatingMap.map_eq_zero_of_eq

theorem map_eq_zero_of_not_injective (v : ι → M) (hv : ¬Function.Injective v) : f v = 0 :=
  f.toAlternatingMap.map_eq_zero_of_not_injective v hv
#align continuous_alternating_map.map_eq_zero_of_not_injective ContinuousAlternatingMap.map_eq_zero_of_not_injective

/-- Restrict the codomain of a continuous alternating map to a submodule. -/
@[simps!]
def codRestrict (f : Λ^ι⟮R; M; N⟯) (p : Submodule R N) (h : ∀ v, f v ∈ p) : Λ^ι⟮R; M; p⟯ :=
  { f.toAlternatingMap.codRestrict p h with toContinuousMultilinearMap := f.1.codRestrict p h }
#align continuous_alternating_map.cod_restrict ContinuousAlternatingMap.codRestrict

instance : Zero Λ^ι⟮R; M; N⟯ :=
  ⟨⟨0, (0 : AlternatingMap R M N ι).map_eq_zero_of_eq⟩⟩

instance : Inhabited Λ^ι⟮R; M; N⟯ :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : Λ^ι⟮R; M; N⟯) = 0 :=
  rfl
#align continuous_alternating_map.coe_zero ContinuousAlternatingMap.coe_zero

@[simp]
theorem toContinuousMultilinearMap_zero : (0 : Λ^ι⟮R; M; N⟯).toContinuousMultilinearMap = 0 :=
  rfl
#align continuous_alternating_map.to_continuous_multilinear_map_zero ContinuousAlternatingMap.toContinuousMultilinearMap_zero

@[simp]
theorem toAlternatingMap_zero : (0 : Λ^ι⟮R; M; N⟯).toAlternatingMap = 0 :=
  rfl
#align continuous_alternating_map.to_alternating_map_zero ContinuousAlternatingMap.toAlternatingMap_zero

section SMul

variable {R' R'' A : Type _} [Monoid R'] [Monoid R''] [Semiring A] [Module A M] [Module A N]
  [DistribMulAction R' N] [ContinuousConstSMul R' N] [SMulCommClass A R' N] [DistribMulAction R'' N]
  [ContinuousConstSMul R'' N] [SMulCommClass A R'' N]

instance : SMul R' Λ^ι⟮A; M; N⟯ :=
  ⟨fun c f => ⟨c • f.1, (c • f.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]
theorem coe_smul (f : Λ^ι⟮A; M; N⟯) (c : R') : ⇑(c • f) = c • ⇑f :=
  rfl
#align continuous_alternating_map.coe_smul ContinuousAlternatingMap.coe_smul

theorem smul_apply (f : Λ^ι⟮A; M; N⟯) (c : R') (v : ι → M) : (c • f) v = c • f v :=
  rfl
#align continuous_alternating_map.smul_apply ContinuousAlternatingMap.smul_apply

@[simp]
theorem toContinuousMultilinearMap_smul (c : R') (f : Λ^ι⟮A; M; N⟯) :
    (c • f).toContinuousMultilinearMap = c • f.toContinuousMultilinearMap :=
  rfl
#align continuous_alternating_map.to_continuous_multilinear_map_smul ContinuousAlternatingMap.toContinuousMultilinearMap_smul

@[simp]
theorem toAlternatingMap_smul (c : R') (f : Λ^ι⟮A; M; N⟯) :
    (c • f).toAlternatingMap = c • f.toAlternatingMap :=
  rfl
#align continuous_alternating_map.to_alternating_map_smul ContinuousAlternatingMap.toAlternatingMap_smul

instance [SMulCommClass R' R'' N] : SMulCommClass R' R'' Λ^ι⟮A; M; N⟯ :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

instance [SMul R' R''] [IsScalarTower R' R'' N] : IsScalarTower R' R'' Λ^ι⟮A; M; N⟯ :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

instance [DistribMulAction R'ᵐᵒᵖ N] [IsCentralScalar R' N] : IsCentralScalar R' Λ^ι⟮A; M; N⟯ :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

instance : MulAction R' Λ^ι⟮A; M; N⟯ :=
  toContinuousMultilinearMap_injective.mulAction toContinuousMultilinearMap fun _ _ => rfl

end SMul

section ContinuousAdd

variable [ContinuousAdd N]

instance : Add Λ^ι⟮R; M; N⟯ :=
  ⟨fun f g => ⟨f.1 + g.1, (f.toAlternatingMap + g.toAlternatingMap).map_eq_zero_of_eq⟩⟩

@[simp]
theorem coe_add : ⇑(f + g) = ⇑f + ⇑g :=
  rfl
#align continuous_alternating_map.coe_add ContinuousAlternatingMap.coe_add

@[simp]
theorem add_apply (v : ι → M) : (f + g) v = f v + g v :=
  rfl
#align continuous_alternating_map.add_apply ContinuousAlternatingMap.add_apply

@[simp]
theorem toContinuousMultilinearMap_add (f g : Λ^ι⟮R; M; N⟯) : (f + g).1 = f.1 + g.1 :=
  rfl
#align continuous_alternating_map.to_continuous_multilinear_map_add ContinuousAlternatingMap.toContinuousMultilinearMap_add

@[simp]
theorem toAlternatingMap_add (f g : Λ^ι⟮R; M; N⟯) :
    (f + g).toAlternatingMap = f.toAlternatingMap + g.toAlternatingMap :=
  rfl
#align continuous_alternating_map.to_alternating_map_add ContinuousAlternatingMap.toAlternatingMap_add

instance addCommMonoid : AddCommMonoid Λ^ι⟮R; M; N⟯ :=
  toContinuousMultilinearMap_injective.addCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align continuous_alternating_map.add_comm_monoid ContinuousAlternatingMap.addCommMonoid

/-- Evaluation of a `ContinuousAlternatingMap` at a vector as an `AddMonoidHom`. -/
def applyAddHom (v : ι → M) : Λ^ι⟮R; M; N⟯ →+ N :=
  ⟨⟨fun f => f v, rfl⟩, fun _ _ => rfl⟩
#align continuous_alternating_map.apply_add_hom ContinuousAlternatingMap.applyAddHom

@[simp]
theorem sum_apply {α : Type _} (f : α → Λ^ι⟮R; M; N⟯) (m : ι → M) {s : Finset α} :
    (∑ a in s, f a) m = ∑ a in s, f a m :=
  (applyAddHom m).map_sum f s
#align continuous_alternating_map.sum_apply ContinuousAlternatingMap.sum_apply

/-- Projection to `ContinuousMultilinearMap`s as a bundled `AddMonoidHom`. -/
@[simps]
def toMultilinearAddHom : Λ^ι⟮R; M; N⟯ →+ ContinuousMultilinearMap R (fun _ : ι => M) N :=
  ⟨⟨fun f => f.1, rfl⟩, fun _ _ => rfl⟩
#align continuous_alternating_map.to_multilinear_add_hom ContinuousAlternatingMap.toMultilinearAddHom

end ContinuousAdd

/-- If `f` is a continuous alternating map, then `f.to_continuous_linear_map m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
@[simps! apply]
def toContinuousLinearMap [DecidableEq ι] (m : ι → M) (i : ι) : M →L[R] N :=
  f.1.toContinuousLinearMap m i
#align continuous_alternating_map.to_continuous_linear_map ContinuousAlternatingMap.toContinuousLinearMap

/-- The cartesian product of two continuous alternating maps, as a continuous alternating map. -/
@[simps!]
def prod (f : Λ^ι⟮R; M; N⟯) (g : Λ^ι⟮R; M; N'⟯) : Λ^ι⟮R; M; N × N'⟯ :=
  ⟨f.1.prod g.1, (f.toAlternatingMap.prod g.toAlternatingMap).map_eq_zero_of_eq⟩
#align continuous_alternating_map.prod ContinuousAlternatingMap.prod

/-- Combine a family of continuous alternating maps with the same domain and codomains `M' i` into a
continuous alternating map taking values in the space of functions `Π i, M' i`. -/
def pi {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, Λ^ι⟮R; M; M' i⟯) : Λ^ι⟮R; M; ∀ i, M' i⟯ :=
  ⟨ContinuousMultilinearMap.pi fun i => (f i).1,
    (AlternatingMap.pi fun i => (f i).toAlternatingMap).map_eq_zero_of_eq⟩
#align continuous_alternating_map.pi ContinuousAlternatingMap.pi

@[simp]
theorem coe_pi {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, Λ^ι⟮R; M; M' i⟯) :
    ⇑(pi f) = fun m j => f j m :=
  rfl
#align continuous_alternating_map.coe_pi ContinuousAlternatingMap.coe_pi

theorem pi_apply {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, Λ^ι⟮R; M; M' i⟯) (m : ι → M)
    (j : ι') : pi f m j = f j m :=
  rfl
#align continuous_alternating_map.pi_apply ContinuousAlternatingMap.pi_apply

section

variable (R M)

/-- The evaluation map from `ι → M₂` to `M₂` is alternating at a given `i` when `ι` is subsingleton.
-/
@[simps! toContinuousMultilinearMap apply]
def ofSubsingleton [Subsingleton ι] (i' : ι) : Λ^ι⟮R; M; M⟯ :=
  { AlternatingMap.ofSubsingleton R _ i' with
    toContinuousMultilinearMap := ContinuousMultilinearMap.ofSubsingleton R _ i' }
#align continuous_alternating_map.of_subsingleton ContinuousAlternatingMap.ofSubsingleton

@[simp]
theorem ofSubsingleton_toAlternatingMap [Subsingleton ι] (i' : ι) :
    (ofSubsingleton R M i').toAlternatingMap = AlternatingMap.ofSubsingleton R M i' :=
  rfl
#align continuous_alternating_map.of_subsingleton_to_alternating_map ContinuousAlternatingMap.ofSubsingleton_toAlternatingMap

variable (ι)

/-- The constant map is alternating when `ι` is empty. -/
@[simps! toContinuousMultilinearMap apply]
def constOfIsEmpty [IsEmpty ι] (m : N) : Λ^ι⟮R; M; N⟯ :=
  { AlternatingMap.constOfIsEmpty R M ι m with
    toContinuousMultilinearMap := ContinuousMultilinearMap.constOfIsEmpty R (fun _ => M) m }
#align continuous_alternating_map.const_of_is_empty ContinuousAlternatingMap.constOfIsEmpty

@[simp]
theorem constOfIsEmpty_toAlternatingMap [IsEmpty ι] (m : N) :
    (constOfIsEmpty R M ι m).toAlternatingMap = AlternatingMap.constOfIsEmpty R M ι m :=
  rfl
#align continuous_alternating_map.const_of_is_empty_to_alternating_map ContinuousAlternatingMap.constOfIsEmpty_toAlternatingMap

end

/-- If `g` is continuous alternating and `f` is a collection of continuous linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a continuous alternating map, that we call
`g.comp_continuous_linear_map f`. -/
def compContinuousLinearMap (g : Λ^ι⟮R; M; N⟯) (f : M' →L[R] M) : Λ^ι⟮R; M'; N⟯ :=
  { g.toAlternatingMap.compLinearMap (f : M' →ₗ[R] M) with
    toContinuousMultilinearMap := g.1.compContinuousLinearMap fun _ => f }
#align continuous_alternating_map.comp_continuous_linear_map ContinuousAlternatingMap.compContinuousLinearMap

@[simp]
theorem compContinuousLinearMap_apply (g : Λ^ι⟮R; M; N⟯) (f : M' →L[R] M) (m : ι → M') :
    g.compContinuousLinearMap f m = g (f ∘ m) :=
  rfl
#align continuous_alternating_map.comp_continuous_linear_map_apply ContinuousAlternatingMap.compContinuousLinearMap_apply

/-- Composing a continuous alternating map with a continuous linear map gives again a
continuous alternating map. -/
def _root_.ContinuousLinearMap.compContinuousAlternatingMap (g : N →L[R] N') (f : Λ^ι⟮R; M; N⟯) :
    Λ^ι⟮R; M; N'⟯ :=
  { (g : N →ₗ[R] N').compAlternatingMap f.toAlternatingMap with
    toContinuousMultilinearMap := g.compContinuousMultilinearMap f.1 }
#align continuous_linear_map.comp_continuous_alternating_map ContinuousLinearMap.compContinuousAlternatingMap

@[simp]
theorem _root_.ContinuousLinearMap.compContinuousAlternatingMap_coe (g : N →L[R] N')
    (f : Λ^ι⟮R; M; N⟯) : ⇑(g.compContinuousAlternatingMap f) = g ∘ f :=
  rfl
#align continuous_linear_map.comp_continuous_alternating_map_coe ContinuousLinearMap.compContinuousAlternatingMap_coe

/-- A continuous linear equivalence of domains defines an equivalence between continuous
alternating maps. -/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapComp (e : M ≃L[R] M') :
    Λ^ι⟮R; M; N⟯ ≃ Λ^ι⟮R; M'; N⟯ where
  toFun f := f.compContinuousLinearMap ↑e.symm
  invFun f := f.compContinuousLinearMap ↑e
  left_inv f := by ext; simp [(· ∘ ·)]
  right_inv f := by ext; simp [(· ∘ ·)]
#align continuous_linear_equiv.continuous_alternating_map_comp ContinuousLinearEquiv.continuousAlternatingMapComp

/-- A continuous linear equivalence of codomains defines an equivalence between continuous
alternating maps. -/
def _root_.ContinuousLinearEquiv.compContinuousAlternatingMap (e : N ≃L[R] N') :
    Λ^ι⟮R; M; N⟯ ≃ Λ^ι⟮R; M; N'⟯ where
  toFun := (e : N →L[R] N').compContinuousAlternatingMap
  invFun := (e.symm : N' →L[R] N).compContinuousAlternatingMap
  left_inv f := by ext; simp [(· ∘ ·)]
  right_inv f := by ext; simp [(· ∘ ·)]
#align continuous_linear_equiv.comp_continuous_alternating_map ContinuousLinearEquiv.compContinuousAlternatingMap

@[simp]
theorem _root_.ContinuousLinearEquiv.compContinuousAlternatingMap_coe
    (e : N ≃L[R] N') (f : Λ^ι⟮R; M; N⟯) : ⇑(e.compContinuousAlternatingMap f) = e ∘ f :=
  rfl
#align continuous_linear_equiv.comp_continuous_alternating_map_coe ContinuousLinearEquiv.compContinuousAlternatingMap_coe

/-- Continuous linear equivalences between domains and codomains define an equivalence between the
spaces of continuous alternating maps. -/
def _root_.ContinuousLinearEquiv.continuousAlternatingMapCongr (e : M ≃L[R] M') (e' : N ≃L[R] N') :
    Λ^ι⟮R; M; N⟯ ≃ Λ^ι⟮R; M'; N'⟯ :=
  e.continuousAlternatingMapComp.trans e'.compContinuousAlternatingMap
#align continuous_linear_equiv.continuous_alternating_map_congr ContinuousLinearEquiv.continuousAlternatingMapCongr

/-- `ContinuousAlternatingMap.pi` as an `Equiv`. -/
@[simps]
def piEquiv {ι' : Type _} {N : ι' → Type _} [∀ i, AddCommMonoid (N i)] [∀ i, TopologicalSpace (N i)]
    [∀ i, Module R (N i)] : (∀ i, Λ^ι⟮R; M; N i⟯) ≃ Λ^ι⟮R; M; ∀ i, N i⟯ where
  toFun := pi
  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] N i).compContinuousAlternatingMap f
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
#align continuous_alternating_map.pi_equiv ContinuousAlternatingMap.piEquiv

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
additivity of a alternating map along the first variable. -/
theorem cons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (x y : M) :
    f (Fin.cons (x + y) m) = f (Fin.cons x m) + f (Fin.cons y m) :=
  f.toMultilinearMap.cons_add m x y
#align continuous_alternating_map.cons_add ContinuousAlternatingMap.cons_add

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
additivity of a alternating map along the first variable. -/
theorem vecCons_add (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (x y : M) :
    f (vecCons (x + y) m) = f (vecCons x m) + f (vecCons y m) :=
  f.toMultilinearMap.cons_add m x y
#align continuous_alternating_map.vec_cons_add ContinuousAlternatingMap.vecCons_add

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a alternating map along the first variable. -/
theorem cons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (c : R)
    (x : M) : f (Fin.cons (c • x) m) = c • f (Fin.cons x m) :=
  f.toMultilinearMap.cons_smul m c x
#align continuous_alternating_map.cons_smul ContinuousAlternatingMap.cons_smul

/-- In the specific case of continuous alternating maps on spaces indexed by `Fin (n+1)`, where one
can build an element of `Π(i : Fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a alternating map along the first variable. -/
theorem vecCons_smul (f : ContinuousAlternatingMap R M N (Fin (n + 1))) (m : Fin n → M) (c : R)
    (x : M) : f (vecCons (c • x) m) = c • f (vecCons x m) :=
  f.toMultilinearMap.cons_smul m c x
#align continuous_alternating_map.vec_cons_smul ContinuousAlternatingMap.vecCons_smul

theorem map_piecewise_add [DecidableEq ι] (m m' : ι → M) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _
#align continuous_alternating_map.map_piecewise_add ContinuousAlternatingMap.map_piecewise_add

/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ι → M) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _
#align continuous_alternating_map.map_add_univ ContinuousAlternatingMap.map_add_univ

section ApplySum

open Fintype Finset

variable {α : ι → Type _} [Fintype ι] [DecidableEq ι] (g' : ∀ i, α i → M) (A : ∀ i, Finset (α i))

/-- If `f` is continuous alternating, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset :
    (f fun i => ∑ j in A i, g' i j) = ∑ r in piFinset A, f fun i => g' i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _
#align continuous_alternating_map.map_sum_finset ContinuousAlternatingMap.map_sum_finset

/-- If `f` is continuous alternating, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g' i j) = ∑ r : ∀ i, α i, f fun i => g' i (r i) :=
  f.toMultilinearMap.map_sum _
#align continuous_alternating_map.map_sum ContinuousAlternatingMap.map_sum

end ApplySum

section RestrictScalar

variable (R)
variable {A : Type _} [Semiring A] [SMul R A] [Module A M] [Module A N] [IsScalarTower R A M]
  [IsScalarTower R A N]

/-- Reinterpret an `A`-alternating map as an `R`-alternating map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrictScalars (f : Λ^ι⟮A; M; N⟯) : Λ^ι⟮R; M; N⟯ :=
  { f with toContinuousMultilinearMap := f.1.restrictScalars R }
#align continuous_alternating_map.restrict_scalars ContinuousAlternatingMap.restrictScalars

@[simp]
theorem coe_restrictScalars (f : Λ^ι⟮A; M; N⟯) : ⇑(f.restrictScalars R) = f :=
  rfl
#align continuous_alternating_map.coe_restrict_scalars ContinuousAlternatingMap.coe_restrictScalars

end RestrictScalar

end Semiring

section Ring

variable {R M M' N N' ι : Type _} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [AddCommGroup N] [Module R N]
  [TopologicalSpace N] [AddCommGroup N'] [Module R N'] [TopologicalSpace N'] {n : ℕ}
  (f g : Λ^ι⟮R; M; N⟯)

@[simp]
theorem map_sub [DecidableEq ι] (m : ι → M) (i : ι) (x y : M) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_sub _ _ _ _
#align continuous_alternating_map.map_sub ContinuousAlternatingMap.map_sub

section TopologicalAddGroup

variable [TopologicalAddGroup N]

instance : Neg Λ^ι⟮R; M; N⟯ :=
  ⟨fun f => { -f.toAlternatingMap with toContinuousMultilinearMap := -f.1 }⟩

@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl
#align continuous_alternating_map.coe_neg ContinuousAlternatingMap.coe_neg

theorem neg_apply (m : ι → M) : (-f) m = -f m :=
  rfl
#align continuous_alternating_map.neg_apply ContinuousAlternatingMap.neg_apply

instance : Sub Λ^ι⟮R; M; N⟯ :=
  ⟨fun f g =>
    { f.toAlternatingMap - g.toAlternatingMap with toContinuousMultilinearMap := f.1 - g.1 }⟩

@[simp] theorem coe_sub : ⇑(f - g) = ⇑f - ⇑g := rfl
#align continuous_alternating_map.coe_sub ContinuousAlternatingMap.coe_sub

theorem sub_apply (m : ι → M) : (f - g) m = f m - g m := rfl
#align continuous_alternating_map.sub_apply ContinuousAlternatingMap.sub_apply

instance : AddCommGroup Λ^ι⟮R; M; N⟯ :=
  toContinuousMultilinearMap_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end TopologicalAddGroup

end Ring

section CommSemiring

variable {R M M' N N' ι : Type _} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N]
  [Module R N] [TopologicalSpace N] [AddCommMonoid N'] [Module R N'] [TopologicalSpace N'] {n : ℕ}
  (f g : Λ^ι⟮R; M; N⟯)

theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ι → M) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _
#align continuous_alternating_map.map_piecewise_smul ContinuousAlternatingMap.map_piecewise_smul

/-- Multiplicativity of a continuous alternating map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ι → M) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _
#align continuous_alternating_map.map_smul_univ ContinuousAlternatingMap.map_smul_univ

end CommSemiring

section DistribMulAction

variable {R A M N ι : Type _} [Monoid R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [Module A M] [Module A N] [DistribMulAction R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

instance [ContinuousAdd N] : DistribMulAction R Λ^ι⟮A; M; N⟯ :=
  Function.Injective.distribMulAction toMultilinearAddHom
    toContinuousMultilinearMap_injective fun _ _ => rfl

end DistribMulAction

section Module

variable {R A M N ι : Type _} [Semiring R] [Semiring A] [AddCommMonoid M] [AddCommMonoid N]
  [TopologicalSpace M] [TopologicalSpace N] [ContinuousAdd N] [Module A M] [Module A N] [Module R N]
  [ContinuousConstSMul R N] [SMulCommClass A R N]

/-- The space of continuous alternating maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
instance : Module R Λ^ι⟮A; M; N⟯ :=
  Function.Injective.module _ toMultilinearAddHom toContinuousMultilinearMap_injective fun _ _ =>
    rfl

/-- Linear map version of the map `to_multilinear_map` associating to a continuous alternating map
the corresponding multilinear map. -/
@[simps]
def toContinuousMultilinearMapLinear :
    Λ^ι⟮A; M; N⟯ →ₗ[R] ContinuousMultilinearMap A (fun _ : ι => M) N where
  toFun := toContinuousMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align continuous_alternating_map.to_continuous_multilinear_map_linear ContinuousAlternatingMap.toContinuousMultilinearMapLinear

/-- `ContinuousAlternatingMap.pi` as a `LinearEquiv`. -/
@[simps (config := { simpRhs := true })]
def piLinearEquiv {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, ContinuousAdd (M' i)] [∀ i, Module R (M' i)]
    [∀ i, Module A (M' i)] [∀ i, SMulCommClass A R (M' i)] [∀ i, ContinuousConstSMul R (M' i)] :
    (∀ i, Λ^ι⟮A; M; M' i⟯) ≃ₗ[R] Λ^ι⟮A; M; ∀ i, M' i⟯ :=
  { piEquiv with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
#align continuous_alternating_map.pi_linear_equiv ContinuousAlternatingMap.piLinearEquiv

end Module

section SmulRight

variable {R A M N ι : Type _} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M]
  [Module R N] [TopologicalSpace R] [TopologicalSpace M] [TopologicalSpace N] [ContinuousSMul R N]
  (f : Λ^ι⟮R; M; R⟯) (z : N)

/-- Given a continuous `R`-alternating map `f` taking values in `R`, `f.smul_right z` is the
continuous alternating map sending `m` to `f m • z`. -/
@[simps! toContinuousMultilinearMap apply]
def smulRight : Λ^ι⟮R; M; N⟯ :=
  { f.toAlternatingMap.smulRight z with toContinuousMultilinearMap := f.1.smulRight z }
#align continuous_alternating_map.smul_right ContinuousAlternatingMap.smulRight

end SmulRight

section Semiring

variable {R M M' N N' ι : Type _} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M] [AddCommMonoid M'] [Module R M'] [TopologicalSpace M'] [AddCommMonoid N]
  [Module R N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul R N] [AddCommMonoid N']
  [Module R N'] [TopologicalSpace N'] [ContinuousAdd N'] [ContinuousConstSMul R N']

/-- `ContinuousAlternatingMap.compContinuousLinearMap` as a bundled `LinearMap`. -/
@[simps]
def compContinuousLinearMapₗ (f : M →L[R] M') : Λ^ι⟮R; M'; N⟯ →ₗ[R] Λ^ι⟮R; M; N⟯ where
  toFun g := g.compContinuousLinearMap f
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp
#align continuous_alternating_map.comp_continuous_linear_mapₗ ContinuousAlternatingMap.compContinuousLinearMapₗ

variable (R M N N')

/-- `ContinuousLinearMap.compContinuousAlternatingMap` as a bundled bilinear map. -/
def _root_.ContinuousLinearMap.compContinuousAlternatingMapₗ :
    (N →L[R] N') →ₗ[R] Λ^ι⟮R; M; N⟯ →ₗ[R] Λ^ι⟮R; M; N'⟯ :=
  LinearMap.mk₂ R ContinuousLinearMap.compContinuousAlternatingMap (fun f₁ f₂ g => rfl)
    (fun c f g => rfl) (fun f g₁ g₂ => by ext1; apply f.map_add) fun c f g => by ext1; simp
#align continuous_linear_map.comp_continuous_alternating_mapₗ ContinuousLinearMap.compContinuousAlternatingMapₗ

end Semiring

end ContinuousAlternatingMap

namespace ContinuousMultilinearMap

variable {R M N ι : Type _} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [TopologicalAddGroup N] [Fintype ι]
  [DecidableEq ι] (f g : ContinuousMultilinearMap R (fun _ : ι => M) N)

/-- Alternatization of a continuous multilinear map. -/
@[simps (config := { isSimp := false }) apply_toContinuousMultilinearMap]
def alternatization : ContinuousMultilinearMap R (fun _ : ι => M) N →+ Λ^ι⟮R; M; N⟯ where
  toFun f :=
    { toContinuousMultilinearMap := ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ
      map_eq_zero_of_eq' := fun v i j hv hne => by
        simpa [MultilinearMap.alternatization_apply]
          using f.1.alternatization.map_eq_zero_of_eq' v i j hv hne }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [Finset.sum_add_distrib]
#align continuous_multilinear_map.alternatization ContinuousMultilinearMap.alternatization

theorem alternatization_apply_apply (v : ι → M) :
    alternatization f v = ∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f (v ∘ σ) := by
  simp [alternatization, (· ∘ ·)]
#align continuous_multilinear_map.alternatization_apply_apply ContinuousMultilinearMap.alternatization_apply_apply

@[simp]
theorem alternatization_apply_toAlternatingMap :
    (alternatization f).toAlternatingMap = MultilinearMap.alternatization f.1 := by
  ext v
  simp [alternatization_apply_apply, MultilinearMap.alternatization_apply, (· ∘ ·)]
#align continuous_multilinear_map.alternatization_apply_to_alternating_map ContinuousMultilinearMap.alternatization_apply_toAlternatingMap

end ContinuousMultilinearMap

