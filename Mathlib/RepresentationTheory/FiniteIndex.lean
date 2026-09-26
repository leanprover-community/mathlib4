/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jiaxi Mo
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Induced

/-!
# (Co)induced representations of a finite index subgroup

Given a commutative ring `k`, a finite index subgroup `S ≤ G`, and a `k`-linear `S`-representation
`A`, this file defines an isomorphism $Ind_S^G(A) ≅ Coind_S^G(A)$. Given `g : G` and `a : A`, the
forward map sends `⟦g ⊗ₜ[k] a⟧` to the function `G → A` supported at `sg` by `ρ(s)(a)` for `s : S`
and which is 0 elsewhere. Meanwhile, the inverse sends `f : G → A` to `∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for
`1 ≤ i ≤ n`, where `g₁, ..., gₙ` is a set of right coset representatives of `S`.

## Main definitions

* `Rep.indCoindIso A`: An isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)` for a finite index subgroup
  `S ≤ G` and a `k`-linear `S`-representation `A`.
* `Rep.indCoindNatIso k S`: A natural isomorphism between the functors `Ind_S^G` and `Coind_S^G`.
-/

@[expose] public section

namespace Representation

variable {k G V W : Type*} [CommRing k] [Group G] {S : Subgroup G} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] {ρ : Representation k S V}

variable (ρ) in
/-- The function `G → End V` supported on `S`, with value `ρ s` at `s : S`. -/
noncomputable def indToCoindAux (g : G) : Module.End k V :=
  open scoped Classical in if hg : g ∈ S then ρ ⟨g, hg⟩ else 0

@[simp]
lemma indToCoindAux_coe (s : S) : ρ.indToCoindAux (s : G) = ρ s := dite_eq_left s.prop

@[simp]
lemma indToCoindAux_one : ρ.indToCoindAux 1 = 1 := (ρ.indToCoindAux_coe 1).trans ρ.map_one

@[simp]
lemma indToCoindAux_of_notMem {g : G} (hg : g ∉ S) : ρ.indToCoindAux g = 0 := dite_eq_right hg

@[simp]
lemma indToCoindAux_coe_mul (s : S) (g : G) :
    ρ.indToCoindAux (s * g) = ρ s * ρ.indToCoindAux g := by
  by_cases hg : g ∈ S
  · lift g to S using hg; simpa using ρ.indToCoindAux_coe (s * g)
  · simp [hg, mul_mem_cancel_left]

@[simp]
lemma indToCoindAux_mul_coe (s : S) (g : G) :
    ρ.indToCoindAux (g * s) = ρ.indToCoindAux g * ρ s := by
  by_cases hg : g ∈ S
  · lift g to S using hg; simp
  · simp [hg, mul_mem_cancel_right]

lemma indToCoindAux_comm {σ : Representation k S W} (f : ρ.IntertwiningMap σ) (g : G) (v : V) :
    σ.indToCoindAux g (f v) = f (ρ.indToCoindAux g v) := by
  by_cases hg : g ∈ S <;> simp [indToCoindAux, hg, f.isIntertwining]

variable (ρ) in
/-- Let `S ≤ G` be a subgroup and `V` a `k`-linear `S`-representation. This is the intertwining map
`Ind_S^G(V) → Coind_S^G(V)` sending `(⟦g ⊗ₜ[k] v⟧, sg) ↦ ρ(s)(v)`. -/
noncomputable def indToCoind :
    (ind S.subtype ρ).IntertwiningMap (coind S.subtype ρ) :=
  ind.lift _ ⟨(LinearMap.pi ρ.indToCoindAux).codRestrict _ (by simp), fun _ => by ext; simp⟩

@[simp]
lemma indToCoind_apply_mk (g h : G) (v : V) :
    ρ.indToCoind (IndV.mk S.subtype ρ g v) h = ρ.indToCoindAux (h * g⁻¹) v := by
  simp [indToCoind]

variable (ρ) in
/-- The summand of `coindToInd` at the coset `gS`: `f ↦ ⟦g⁻¹ ⊗ₜ f g⁻¹⟧`. -/
noncomputable def coindToIndAux (c : G ⧸ S) :
    coindV S.subtype ρ →ₗ[k] IndV S.subtype ρ :=
  Quotient.liftOn c (fun g => IndV.mk _ ρ g⁻¹ ∘ₗ LinearMap.proj g⁻¹ ∘ₗ (coindV _ ρ).subtype)
    fun g₁ g₂ hrel => LinearMap.ext fun f => by
      have : g₂ = g₁ * S.subtype ⟨_, QuotientGroup.leftRel_apply.mp hrel⟩ :=
        (mul_inv_cancel_left _ _).symm
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply]
      rw [this, mul_inv_rev, IndV.mk_map_inv_mul, ← mem_coindV.mp f.prop]
      simp

@[simp]
lemma coindToIndAux_mk (g : G) (f : coindV S.subtype ρ) :
    ρ.coindToIndAux g f = IndV.mk S.subtype ρ g⁻¹ (f g⁻¹) := rfl

variable [S.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable (ρ) in
/-- Let `S ≤ G` be a finite index subgroup and `ρ` a `k`-linear `S`-representation. This is the
intertwining map `Coind_S^G(ρ) → Ind_S^G(ρ)` sending `f` to `∑_{gS ∈ G ⧸ S} ⟦g⁻¹ ⊗ₜ f g⁻¹⟧`. -/
noncomputable def coindToInd : (coind S.subtype ρ).IntertwiningMap (ind S.subtype ρ) where
  toLinearMap := ∑ c : G ⧸ S, coindToIndAux ρ c
  isIntertwining' g := LinearMap.ext fun _ => by
    simpa using Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun c => c.inductionOn (by simp)

lemma coindToInd_apply (f : coindV S.subtype ρ) :
    ρ.coindToInd f = ∑ c : G ⧸ S, coindToIndAux ρ c f :=
  LinearMap.sum_apply _ _ _

@[simp]
lemma indToCoind_coindToInd (f : coindV S.subtype ρ) :
    ρ.indToCoind (ρ.coindToInd f) = f := by
  ext h
  simp only [coindToInd_apply, map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  refine (Fintype.sum_eq_single ((h⁻¹ : G) : G ⧸ S) ?_).trans (by simp)
  simp +contextual [QuotientGroup.forall_mk, QuotientGroup.eq, ← mul_inv_rev]

@[simp]
lemma coindToInd_indToCoind (x : IndV S.subtype ρ) :
    ρ.coindToInd (ρ.indToCoind x) = x := by
  refine x.inductionOn (fun g v => ?_) fun _ _ hx hy => by simp [hx, hy]
  refine (coindToInd_apply _).trans ((Fintype.sum_eq_single ((g⁻¹ : G) : G ⧸ S) ?_).trans (by simp))
  simp +contextual [QuotientGroup.forall_mk, QuotientGroup.eq]

end Representation

namespace Rep

universe w u v

open CategoryTheory Representation

variable {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G} [S.FiniteIndex]

/-- Let `S ≤ G` be a finite index subgroup, `g₁, ..., gₙ` a set of right coset representatives of
`S`, and `A` a `k`-linear `S`-representation. This is an isomorphism `Ind_S^G(A) ≅ Coind_S^G(A)`.
The forward map sends `(⟦g ⊗ₜ[k] a⟧, sg) ↦ ρ(s)(a)`, and the inverse sends `f : G → A` to
`∑ᵢ ⟦gᵢ ⊗ₜ[k] f(gᵢ)⟧` for `1 ≤ i ≤ n`. -/
@[simps]
noncomputable def indCoindIso (A : Rep.{max w u} k S) :
    ind S.subtype A ≅ coind S.subtype A where
  hom := ofHom A.ρ.indToCoind
  inv := ofHom A.ρ.coindToInd
  hom_inv_id := hom_ext (IntertwiningMap.ext (LinearMap.ext A.ρ.coindToInd_indToCoind))
  inv_hom_id := hom_ext (IntertwiningMap.ext (LinearMap.ext A.ρ.indToCoind_coindToInd))

variable (k S)
/-- Given a finite index subgroup `S ≤ G`, this is a natural isomorphism between the `Ind_S^G` and
`Coind_S^G` functors `Rep k S ⥤ Rep k G`. -/
@[implicit_reducible, simps (rhsMd := .default) hom_app inv_app]
noncomputable def indCoindNatIso :
    indFunctor.{max w u} k S.subtype ≅ coindFunctor.{max w u} k S.subtype :=
  NatIso.ofComponents indCoindIso.{w} fun f => by
    simp only [indFunctor_obj, coindFunctor_obj]
    ext
    simp [indToCoindAux_comm]

/-- Given a finite index subgroup `S ≤ G`, `Ind_S^G` is right adjoint to the restriction functor
`res : Res k G ⥤ Res k S`, since it is naturally isomorphic to `Coind_S^G`. -/
noncomputable def resIndAdjunction :
    resFunctor.{max w u v} S.subtype ⊣ indFunctor.{max w u v} k S.subtype :=
  (resCoindAdjunction.{max w u v} k S.subtype).ofNatIsoRight (indCoindNatIso.{max w u v} k S).symm

instance instIsRightAdjointSubtypeMemSubgroupIndFunctorSubtype :
    (indFunctor.{max w u v} k S.subtype).IsRightAdjoint :=
  open scoped Classical in (resIndAdjunction k S).isRightAdjoint

variable {k S}

@[simp]
lemma resIndAdjunction_counit_app (A : Rep.{max w u v} k S) :
    (resIndAdjunction.{w} k S).counit.app A =
      (resFunctor.{max w u v} S.subtype).map (indCoindIso.{max w u v} A).hom ≫
      (resCoindAdjunction.{max w u v} k S.subtype).counit.app A := rfl

@[simp]
lemma resIndAdjunction_unit_app (B : Rep.{max w u v} k G) :
    (resIndAdjunction.{w} k S).unit.app B =
      (resCoindAdjunction.{max w u v} k S.subtype).unit.app B ≫
      (indCoindIso.{max w u v} (res S.subtype B)).inv := rfl

lemma resIndAdjunction_homEquiv_apply (A : Rep.{max w u v} k S)
    {B : Rep.{max w u v} k G} (f : res.{u} S.subtype B ⟶ A) :
    (resIndAdjunction.{w} k S).homEquiv B A f =
      resCoindHomEquiv.{max w u v} S.subtype B A f ≫ (indCoindIso.{max w u v} A).inv := by
  rw [resIndAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply]
  simp

lemma resIndAdjunction_homEquiv_symm_apply (A : Rep.{max w u v} k S)
    {B : Rep.{max w u v} k G}
    (f : B ⟶ ind S.subtype A) :
    ((resIndAdjunction.{w} k S).homEquiv _ _).symm f =
      (resCoindHomEquiv.{max w u v} S.subtype B A).symm (f ≫ (indCoindIso.{max w u v} A).hom) := rfl

variable (k S) in
/-- Given a finite index subgroup `S ≤ G`, `Coind_S^G` is left adjoint to the restriction functor
`res : Rep k G ⥤ Rep k S`, since it is naturally isomorphic to `Ind_S^G`. -/
noncomputable def coindResAdjunction :
    coindFunctor.{max w u v} k S.subtype ⊣ resFunctor.{max w u v} S.subtype :=
  (indResAdjunction.{max w u v} S.subtype).ofNatIsoLeft (indCoindNatIso.{max w u v} k S)

instance : (coindFunctor.{max w u v} k S.subtype).IsLeftAdjoint :=
  open scoped Classical in (coindResAdjunction k S).isLeftAdjoint

@[simp]
lemma coindResAdjunction_counit_app (B : Rep.{max w u v} k G) :
    (coindResAdjunction.{w} k S).counit.app B =
      (indCoindIso.{max w u v} (res S.subtype B)).inv ≫
      (indResAdjunction.{max w u v} S.subtype).counit.app B := rfl

@[simp]
lemma coindResAdjunction_unit_app (A : Rep.{max w u v} k S) :
    (coindResAdjunction.{w} k S).unit.app A =
      (indResAdjunction.{max w u v} S.subtype).unit.app A ≫
      (resFunctor.{max w u v} S.subtype).map (indCoindIso.{max w u v} A).hom := rfl

lemma coindResAdjunction_homEquiv_apply (A : Rep.{max w u v} k S)
    {B : Rep.{max w u v} k G} (f : coind S.subtype A ⟶ B) :
    (coindResAdjunction.{w} k S).homEquiv _ _ f =
      indResHomEquiv.{max w u v} S.subtype A B ((indCoindIso.{max w u v} A).hom ≫ f) := rfl

lemma coindResAdjunction_homEquiv_symm_apply (A : Rep.{max w u v} k S)
    {B : Rep.{max w u v} k G} (f : A ⟶ res S.subtype B) :
    ((coindResAdjunction.{w} k S).homEquiv _ _).symm f =
      (indCoindIso.{max w u v} A).inv ≫ (indResHomEquiv.{max w u v} S.subtype A B).symm f := by
  simp_rw [coindResAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    indResAdjunction_homEquiv, indCoindNatIso_inv_app, LinearEquiv.coe_symm_toEquiv]

end Rep
