/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Rep'.Basic
public import Mathlib.RepresentationTheory.Rep'.Res

/-!
# Coinduced representations

Given a commutative ring `k`, a monoid homomorphism `φ : G →* H`, and a `k`-linear
`G`-representation `A`, this file introduces the coinduced representation $Coind_G^H(A)$ of `A` as
an `H`-representation.

By `coind φ A` we mean the submodule of functions `H → A` such that for all `g : G`, `h : H`,
`f (φ g * h) = ρ g (f h)`. We define a representation of `H` on this submodule by sending `h : H`
and `f : coind φ A` to the function `H → A` sending `h₁` to `f (h₁ * h)`.

Alternatively, we could define $Coind_G^H(A)$ as the morphisms $Hom(k[H], A)$ in the category
`Rep k G`, which we equip with the `H`-representation sending `h : H` and `f : k[H] ⟶ A` to the
representation morphism sending `r · h₁` to `r • f (h₁ * h)`. We include this definition as
`coind' φ A` and prove the two representations are isomorphic.

We also prove that the restriction functor `Rep k H ⥤ Rep k G` along `φ` is left adjoint to the
coinduction functor and hence that the coinduction functor preserves limits.

## Main definitions

* `Representation.coind φ ρ` : the coinduction of `ρ` along `φ` defined as the `k`-submodule of
  `G`-equivariant functions `H → A`, with `H`-action given by `(h • f) h₁ := f (h₁ * h)` for
  `f : H → A`, `h, h₁ : H`.
* `Representation.coind' φ A` : the coinduction of `A` along `φ` defined as the set of
  `G`-representation morphisms `k[H] ⟶ A`, with `H`-action given by
  `(h • f) (r • h₁) := r • f(h₁ * h)` for `f : k[H] ⟶ A`, `h, h₁ : H`, `r : k`.
* `Rep.resCoindAdjunction k φ`: given a monoid homomorphism `φ : G →* H`, this is the adjunction
  between the restriction functor `Rep k H ⥤ Rep k G` along `φ` and the coinduction functor
  along `φ`.

-/

@[expose] public section

universe t u' u v' v w' w

namespace Representation

variable {k G H : Type*} [Semiring k] [Monoid G] [Monoid H] (φ : G →* H) {A B : Type*}
  [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B] (σ : Representation k G A)
  (ρ : Representation k G B)

/--
If `ρ : Representation k G A` and `φ : G →* H` then `coindV φ ρ` is the sub-`k`-module of
functions `H → A` underlying the coinduction of `ρ` along `φ`, i.e., the functions `f : H → A`
such that `f (φ g * h) = (ρ g) (f h)` for all `g : G` and `h : H`.
-/
@[simps]
def coindV : Submodule k (H → A) where
  carrier := {f : H → A | ∀ (g : G) (h : H), f (φ g * h) = σ g (f h) }
  add_mem' _ _ _ _ := by simp_all
  zero_mem' := by simp
  smul_mem' _ _ _ := by simp_all

@[simp]
lemma mem_coindV (f : H → A) : f ∈ coindV φ σ ↔ ∀ (g : G) (h : H), f (φ g * h) = σ g (f h) :=
  Iff.rfl

/--
If `ρ : Representation k G A` and `φ : G →* H` then `coind φ ρ` is the representation
coinduced by `ρ` along `φ`, defined as the following action of `H` on the submodule `coindV φ ρ`
of `G`-equivariant functions from `H` to `A`: we let `h : H` send the function `f : H → A`
to the function sending `h₁` to `f (h₁ * h)`.

See also `Rep.coind` and `Representation.coind'` for variants involving the category `Rep k G`.
-/
@[simps]
def coind : Representation k H (coindV φ ρ) where
  toFun h := (LinearMap.funLeft _ _ (· * h)).restrict fun x hx g h₁ => by
    simpa [mul_assoc] using hx g (h₁ * h)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

variable {σ ρ} in
def coindMap (f : σ.IntertwiningMap ρ) : (coind φ σ).IntertwiningMap (coind φ ρ) where
  __ : _ →ₗ[k] _ := (f.toLinearMap.compLeft H).restrict fun x h ↦ by
    simp only [mem_coindV, LinearMap.compLeft_apply, Function.comp_apply,
      IntertwiningMap.toLinearMap_apply] at h ⊢
    intro g h0
    simpa [h] using LinearMap.ext_iff.1 (f.2 g) (x h0)
  isIntertwining' h := by ext; simp

lemma coindMap_coe_apply (f : σ.IntertwiningMap ρ) (x : coindV φ σ) :
    (coindMap φ f) x = (f.toLinearMap.compLeft H) x := rfl

@[simp]
lemma coindMap_coe_apply_apply (f : σ.IntertwiningMap ρ) (x : coindV φ σ) (h : H) :
    ((coindMap φ f) x).1 h = f (x.1 h) := rfl

end Representation

namespace Rep

open CategoryTheory Finsupp

variable {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Monoid G] [Monoid H]
  (φ : G →* H) (A : Rep k G)

section Coind

/--
If `φ : G →* H` and  `A : Rep k G` then `coind φ A` is the coinduction of `A` along `φ`,
defined by letting `H` act on the `G`-equivariant functions `H → A` by `(h • f) h₁ := f (h₁ * h)`.
-/
noncomputable abbrev coind : Rep k H := Rep.of (Representation.coind φ A.ρ)

set_option backward.isDefEq.respectTransparency false in
/-- Given a monoid morphism `φ : G →* H` and a morphism of `G`-representations `f : A ⟶ B`, there
is a natural `H`-representation morphism `coind φ A ⟶ coind φ B`, given by postcomposition by
`f`. -/
-- @[simps!]
noncomputable abbrev coindMap {A B : Rep k G} (f : A ⟶ B) : coind φ A ⟶ coind φ B :=
  ofHom <| Representation.coindMap φ f.hom

-- lemma coindMap_coe_apply {A B : Rep k G} (f : A ⟶ B) (x : Representation.coindV φ A.ρ) :
--     ((coindMap φ f).hom x).1 = (f.hom.toLinearMap.compLeft H) x.1 := rfl

-- @[simp]
-- lemma coindMap_coe_apply_apply {A B : Rep k G} (f : A ⟶ B)
--     (x : Representation.coindV φ A.ρ) (h : H) :
--     ((coindMap φ f).hom x).1 h = f.hom (x.1 h) := rfl

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the coinduced `H`-representation `coind φ A`, with action on maps given by postcomposition. -/
@[simps obj map]
noncomputable def coindFunctor : Rep.{t} k G ⥤ Rep k H where
  obj A := coind φ A
  map f := coindMap φ f

set_option backward.isDefEq.respectTransparency false in
instance {G : Type v'} [Group G] (S : Subgroup G) :
    (coindFunctor k S.subtype).PreservesEpimorphisms where
  preserves {X Y} f := (epi_iff_surjective k G _).2 fun y => by
    letI := QuotientGroup.rightRel S
    choose! s hs using (Rep.epi_iff_surjective _ _ f).1 ‹_›
    choose! i hi using Quotient.mk'_surjective (α := G)
    let γ (g : G) : S := ⟨g * (i (Quotient.mk' g))⁻¹,
      (QuotientGroup.rightRel_apply.1 (Quotient.eq'.1 (hi (Quotient.mk' g))))⟩
    have hmk (s : S) (g : G) : Quotient.mk' (s.1 * g) = Quotient.mk' g :=
      Quotient.eq'.2 (QuotientGroup.rightRel_apply.2 (by simp))
    have hγ (s : S) (g : G) : γ (s.1 * g) = s * γ g := by ext; simp [mul_assoc, γ, hmk]
    let x (g : G) : X := X.ρ (γ g) (s (y.1 (i (Quotient.mk' g))))
    refine ⟨⟨x, fun _ _ => ?_⟩, Subtype.ext <| funext fun g => ?_⟩
    · simp [x, ← Module.End.mul_apply, ← map_mul, hmk, hγ]
    · simp only [coindFunctor_obj, coindFunctor_map, hom_ofHom,
        Representation.coindMap_coe_apply_apply, hom_comm_apply, x]
      simp_all [← y.2 (γ g), γ]

end Coind
section Coind'

set_option backward.isDefEq.respectTransparency false in
/--
If `φ : G →* H` and `A : Rep k G` then `coind' φ A`, the coinduction of `A` along `φ`,
is defined as an `H`-action on `Hom_{k[G]}(k[H], A)`. If `f : k[H] → A` is `G`-equivariant
then `(h • f) (r • h₁) := r • f (h₁ * h)`, where `r : k`.
-/
@[simps]
noncomputable def _root_.Representation.coind' :
    Representation k H (res φ (leftRegular k H) ⟶ A) where
  toFun h :=
  { toFun f := (resFunctor φ).map ((leftRegularHomEquiv (leftRegular k H)).symm.toLinearMap
      (Finsupp.single h 1)) ≫ f
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := by
    ext f : 3
    simp only [res_obj_V, res_obj_ρ, LinearEquiv.trans_symm, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearEquiv.coe_symm_mk', Equiv.invFun_as_coe, LinearMap.coe_mk,
      AddHom.coe_mk, hom_comp, hom_ofHom, Representation.IntertwiningMap.comp_toLinearMap,
      Module.End.one_apply, homEquiv, Equiv.coe_fn_symm_mk, hom_ofHom]
    ext; simp
  map_mul' _ _ := by
    ext f : 3
    simp only [res_obj_V, res_obj_ρ, LinearEquiv.trans_symm, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, LinearEquiv.coe_symm_mk', homEquiv, Equiv.invFun_as_coe,
      Equiv.coe_fn_symm_mk, hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk, hom_comp,
      Representation.IntertwiningMap.comp_toLinearMap, Module.End.mul_apply]
    ext; simp [mul_assoc]

/--
If `φ : G →* H` and `A : Rep k G` then `coind' φ A`, the coinduction of `A` along `φ`,
is defined as an `H`-action on `Hom_{k[G]}(k[H], A)`. If `f : k[H] → A` is `G`-equivariant
then `(h • f) (r • h₁) := r • f (h₁ * h)`, where `r : k`.
-/
noncomputable abbrev coind' : Rep k H := Rep.of (Representation.coind' φ A)

variable {A} in
@[ext]
lemma coind'_ext {f g : coind' φ A} (hfg : ∀ h, f.hom.toLinearMap (.single h 1) =
    g.hom.toLinearMap (.single h 1)) : f = g :=
  Rep.hom_ext <| by ext1; dsimp; ext h; simpa using hfg h

/-- Given a monoid morphism `φ : G →* H` and a morphism of `G`-representations `f : A ⟶ B`, there
is a natural `H`-representation morphism `coind' φ A ⟶ coind' φ B`, given by postcomposition
by `f`. -/
-- @[simps! hom]
noncomputable def coindMap' {A B : Rep k G} (f : A ⟶ B) : coind' φ A ⟶ coind' φ B := Rep.ofHom
  { __ := Linear.rightComp k _ f
    isIntertwining' h := by ext; simp }

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the coinduced `H`-representation `coind' φ A`, with action on maps given by postcomposition. -/
@[simps obj map]
noncomputable def coindFunctor' : Rep k G ⥤ Rep k H where
  obj A := coind' φ A
  map f := coindMap' φ f

end Coind'
noncomputable section CoindIso

set_option backward.isDefEq.respectTransparency false in
/-- If `φ : G →* H` and `A : Rep k G` then the `k`-submodule of functions `f : H → A`
such that for all `g : G`, `h : H`, `f (φ g * h) = A.ρ g (f h)`, is `k`-linearly equivalent
to the `G`-representation morphisms `k[H] ⟶ A`. -/
@[simps]
noncomputable def coindVEquiv :
    A.ρ.coindV φ ≃ₗ[k] (res φ (leftRegular k H) ⟶ A) where
  toFun f := Rep.ofHom ⟨linearCombination _ f.1, fun g ↦ by dsimp; ext; simp [f.2 g]⟩
  map_add' _ _ := coind'_ext φ <| by simp [Rep.add_hom]
  map_smul' _ _ := coind'_ext φ <| by simp [smul_hom]
  invFun f := ⟨fun h ↦ f.hom.toLinearMap (.single h 1), fun g h ↦ by
    simp only [res_obj_V, res_obj_ρ, Representation.IntertwiningMap.toLinearMap_apply]
    have := by simpa using (hom_comm_apply f g (.single h 1)).symm
    rw [← this]⟩
  left_inv x := by simp
  right_inv x := coind'_ext φ fun _ => by simp

set_option backward.isDefEq.respectTransparency false in
/-- `coind φ A` and `coind' φ A` are isomorphic representations, with the underlying
`k`-linear equivalence given by `coindVEquiv`. -/
-- @[simps! hom_hom_hom inv_hom_hom]
noncomputable def coindIso : coind φ A ≅ coind' φ A :=
  Rep.mkIso <| .mk (coindVEquiv φ A) fun h => by ext; simp [homEquiv]

set_option backward.isDefEq.respectTransparency false in
/-- Given a monoid homomorphism `φ : G →* H`, the coinduction functors `Rep k G ⥤ Rep k H` given by
`coindFunctor k φ` and `coindFunctor' k φ` are naturally isomorphic, with isomorphism on objects
given by `coindIso φ`. -/
@[simps!]
noncomputable def coindFunctorIso : coindFunctor k φ ≅ coindFunctor' k φ :=
  NatIso.ofComponents (coindIso φ) fun {X Y} f => by
    simp only [coindFunctor_obj, coindFunctor'_obj, coindFunctor_map, coindFunctor'_map]
    ext : 2
    simp only [coindMap, coindIso, hom_comp, mkIso_hom_hom, hom_ofHom,
      Representation.IntertwiningMap.comp_toLinearMap, Representation.Equiv.toLinearMap_mk',
      coindMap']
    ext ⟨l, hl⟩ : 3
    simp [Representation.coindMap]

end CoindIso

noncomputable section Adjunction

set_option backward.isDefEq.respectTransparency false in
def resCoindToHom (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) : B ⟶ (coind φ A) :=
  Rep.ofHom (σ := B.ρ) (ρ := (coind φ A).ρ) ⟨(LinearMap.pi fun h => f.hom.toLinearMap ∘ₗ
    Rep.ρ B h).codRestrict _ fun _ _ _ => by simpa using hom_comm_apply f _ _, fun g ↦ by
    dsimp; ext; simp⟩

@[simp]
lemma resCoindToHom_hom_hom_apply_coe (B : Rep k H) (A : Rep k G) (f : res φ B ⟶ A) (c : ↑B.V)
    (i : H) : ((resCoindToHom φ B A f).hom.toLinearMap c).1 i = (Hom.hom f) ((B.ρ i) c) := rfl

-- unif_hint (G H : Type*) [Monoid G] [Monoid H] (φ : G →* H) (A : Rep k G) where ⊢
--   A.ρ.coind φ ≟ (coind φ A).ρ

attribute [pp_with_univ] Rep coind

set_option backward.isDefEq.respectTransparency false in
-- set_option maxHeartbeats 10000000 in
/-- Given a monoid homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-representation
`A`, there is a `k`-linear equivalence between the `G`-representation morphisms `B ⟶ A` and the
`H`-representation morphisms `B ⟶ coind φ A`. -/
@[simps]
def resCoindHomEquiv (B : Rep.{max w t} k H) (A : Rep.{max w t} k G) :
    (res φ B ⟶ A) ≃ₗ[k] (B ⟶ coind φ A) where
  toFun f := resCoindToHom φ B A f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := Rep.ofHom ⟨LinearMap.proj 1 ∘ₗ (A.ρ.coindV φ).subtype ∘ₗ f.hom.toLinearMap,
    fun g => by
      ext x
      have := ((f.hom x).2 g 1).symm
      have := hom_comm_apply f (φ g) x
      simp_all [Representation.IntertwiningMap.toLinearMap_apply]⟩
  left_inv x := by
    ext; simp [resCoindToHom_hom_hom_apply_coe _,
      ← Representation.IntertwiningMap.toLinearMap_apply]
  right_inv z := by
    ext (b : B.V)
    have := hom_comm_apply z
    simp only [Representation.coind_apply, resCoindToHom, res_obj_V, res_obj_ρ, hom_ofHom,
      Representation.IntertwiningMap.toLinearMap_mk, LinearMap.codRestrict_apply,
      LinearMap.pi_apply, LinearMap.coe_comp, LinearMap.coe_proj, Submodule.coe_subtype,
      Function.comp_apply, Function.eval,
      Representation.IntertwiningMap.toLinearMap_apply] at this ⊢
    simp [this]

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `@[simps! counit_app_hom_hom unit_app_hom_hom]`,
but removing it seems to be harmless. -/
variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, the coinduction functor `Rep k G ⥤ Rep k H` is right
adjoint to the restriction functor along `φ`. -/
noncomputable abbrev resCoindAdjunction : resFunctor.{max w t} φ ⊣ coindFunctor k φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y := (resCoindHomEquiv φ X Y).toEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; ext; rfl }

noncomputable instance : (coindFunctor.{max w t} k φ).IsRightAdjoint :=
  (resCoindAdjunction k φ).isRightAdjoint

noncomputable instance : (resFunctor.{max w t} (k := k) φ).IsLeftAdjoint :=
  (resCoindAdjunction k φ).isLeftAdjoint

instance {G : Type w} [Group G] (S : Subgroup G) :
    (resFunctor.{max w t} (k := k) S.subtype).PreservesProjectiveObjects  :=
  (resFunctor S.subtype).preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (resCoindAdjunction k S.subtype)

end Adjunction
end Rep
