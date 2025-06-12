/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Rep

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
  between the restriction functor `Rep k H ⥤ Rep k G` along `φ` and  the coinduction functor
  along `φ`.

-/

universe u

namespace Representation

variable {k G H : Type*} [CommSemiring k] [Monoid G] [Monoid H] (φ : G →* H) {A : Type*}
  [AddCommMonoid A] [Module k A] (ρ : Representation k G A)

/--
If `ρ : Representation k G A` and `φ : G →* H` then `coindV φ ρ` is the sub-`k`-module of
functions `H → A` underlying the coinduction of `ρ` along `φ`, i.e., the functions `f : H → A`
such that `f (φ g * h) = (ρ g) (f h)` for all `g : G` and `h : H`.
-/
@[simps]
def coindV : Submodule k (H → A) where
  carrier := {f : H → A | ∀ (g : G) (h : H), f (φ g * h) = ρ g (f h) }
  add_mem' _ _ _ _ := by simp_all
  zero_mem' := by simp
  smul_mem' _ _ _ := by simp_all

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

end Representation

namespace Rep

open CategoryTheory Finsupp

variable {k G H : Type u} [CommRing k] [Monoid G] [Monoid H] (φ : G →* H) (A : Rep k G)

section Coind

/--
If `φ : G →* H` and  `A : Rep k G` then `coind φ A` is the coinduction of `A` along `φ`,
defined by letting `H` act on the `G`-equivariant functions `H → A` by `(h • f) h₁ := f (h₁ * h)`.
-/
noncomputable abbrev coind : Rep k H := Rep.of (Representation.coind φ A.ρ)

/-- Given a monoid morphism `φ : G →* H` and a morphism of `G`-representations `f : A ⟶ B`, there
is a natural `H`-representation morphism `coind φ A ⟶ coind φ B`, given by postcomposition by
`f`. -/
@[simps]
noncomputable def coindMap {A B : Rep k G} (f : A ⟶ B) : coind φ A ⟶ coind φ B where
  hom := ModuleCat.ofHom <| (f.hom.hom.compLeft H).restrict
    fun x h y z => by simp [h y z, hom_comm_apply]
  comm _ := by ext; simp [ModuleCat.endRingEquiv]

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the coinduced `H`-representation `coind φ A`, with action on maps given by postcomposition. -/
@[simps obj map]
noncomputable def coindFunctor : Rep k G ⥤ Rep k H where
  obj A := coind φ A
  map f := coindMap φ f

end Coind
section Coind'

/--
If `φ : G →* H` and `A : Rep k G` then `coind' φ A`, the coinduction of `A` along `φ`,
is defined as an `H`-action on `Hom_{k[G]}(k[H], A)`. If `f : k[H] → A` is `G`-equivariant
then `(h • f) (r • h₁) := r • f (h₁ * h)`, where `r : k`.
-/
@[simps]
noncomputable def _root_.Representation.coind' :
    Representation k H ((Action.res _ φ).obj (leftRegular k H) ⟶ A) where
  toFun h := {
    toFun f := (Action.res _ φ).map ((leftRegularHomEquiv (leftRegular k H)).symm (single h 1)) ≫ f
    map_add' _ _ := by rfl
    map_smul' _ _ := by rfl }
  map_one' := by
    ext x : 3
    refine lhom_ext' fun _ => LinearMap.ext_ring ?_
    simp [leftRegularHomEquiv_symm_apply (leftRegular k H)]
  map_mul' _ _ := by
    ext x : 3
    refine lhom_ext' fun _ => LinearMap.ext_ring ?_
    simp [leftRegularHomEquiv_symm_apply (leftRegular k H), mul_assoc]

/--
If `φ : G →* H` and `A : Rep k G` then `coind' φ A`, the coinduction of `A` along `φ`,
is defined as an `H`-action on `Hom_{k[G]}(k[H], A)`. If `f : k[H] → A` is `G`-equivariant
then `(h • f) (r • h₁) := r • f (h₁ * h)`, where `r : k`.
-/
noncomputable abbrev coind' : Rep k H := Rep.of (Representation.coind' φ A)

variable {A} in
@[ext]
lemma coind'_ext {f g : coind' φ A}
    (hfg : ∀ h, f.hom (single h 1) = g.hom (single h 1)) : f = g :=
  Action.Hom.ext <| ModuleCat.hom_ext <| lhom_ext' fun h => LinearMap.ext_ring <| hfg h

/-- Given a monoid morphism `φ : G →* H` and a morphism of `G`-representations `f : A ⟶ B`, there
is a natural `H`-representation morphism `coind' φ A ⟶ coind' φ B`, given by postcomposition
by `f`. -/
@[simps]
noncomputable def coindMap' {A B : Rep k G} (f : A ⟶ B) : coind' φ A ⟶ coind' φ B where
  hom := ModuleCat.ofHom <| Linear.rightComp k _ f
  comm h := by ext; simp [ModuleCat.endRingEquiv]

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, this is the functor sending a `G`-representation `A`
to the coinduced `H`-representation `coind' φ A`, with action on maps given by postcomposition. -/
@[simps obj map]
noncomputable def coindFunctor' : Rep k G ⥤ Rep k H where
  obj A := coind' φ A
  map f := coindMap' φ f

end Coind'
section CoindIso

/--
If `φ : G →* H` and `A : Rep k G` then the `k`-submodule of functions `f : H → A`
such that for all `g : G`, `h : H`, `f (φ g * h) = A.ρ g (f h)`, is `k`-linearly equivalent
to the `G`-representation morphisms `k[H] ⟶ A`.
-/
@[simps]
noncomputable def coindVEquiv :
    A.ρ.coindV φ ≃ₗ[k] ((Action.res _ φ).obj (leftRegular k H) ⟶ A) where
  toFun f := {
    hom := ModuleCat.ofHom <| linearCombination _ f.1
    comm g := ModuleCat.hom_ext <| lhom_ext' fun _ => LinearMap.ext_ring <| by
      simp [ModuleCat.endRingEquiv, f.2 g] }
  map_add' _ _ := coind'_ext φ fun _ => by simp
  map_smul' _ _ := coind'_ext φ fun _ => by simp
  invFun f := {
    val h := f.hom (single h 1)
    property g h := by have := (hom_comm_apply f g (single h 1)).symm; simp_all [Rep.res_obj_ρ φ] }
  left_inv x := by simp
  right_inv x := coind'_ext φ fun _ => by simp

/-- `coind φ A` and `coind' φ A` are isomorphic representations, with the underlying
`k`-linear equivalence given by `coindVEquiv`. -/
@[simps! hom_hom_hom inv_hom_hom]
noncomputable def coindIso : coind φ A ≅ coind' φ A :=
  Action.mkIso (coindVEquiv φ A).toModuleIso fun h => by
    ext
    simp [ModuleCat.endRingEquiv, leftRegularHomEquiv_symm_apply (leftRegular k H)]

/-- Given a monoid homomorphism `φ : G →* H`, the coinduction functors `Rep k G ⥤ Rep k H` given by
`coindFunctor k φ` and `coindFunctor' k φ` are naturally isomorphic, with isomorphism on objects
given by `coindIso φ`. -/
@[simps!]
noncomputable def coindFunctorIso : coindFunctor k φ ≅ coindFunctor' k φ :=
  NatIso.ofComponents (coindIso φ) fun _ => by
    simp only [coindFunctor_obj, coindFunctor'_obj]
    ext
    simp

end CoindIso
section Adjunction

/-- Given a monoid homomorphism `φ : G →* H`, an `H`-representation `B`, and a `G`-representation
`A`, there is a `k`-linear equivalence between the `G`-representation morphisms `B ⟶ A` and the
`H`-representation morphisms `B ⟶ coind φ A`. -/
@[simps]
noncomputable def resCoindHomEquiv (B : Rep k H) (A : Rep k G) :
    ((Action.res _ φ).obj B ⟶ A) ≃ₗ[k] (B ⟶ coind φ A) where
  toFun f := {
    hom := ModuleCat.ofHom <| (LinearMap.pi fun h => f.hom.hom ∘ₗ Rep.ρ B h).codRestrict _
      fun _ _ _ => by simpa using hom_comm_apply f _ _
    comm _ := by ext; simp [ModuleCat.endRingEquiv] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := {
    hom := ModuleCat.ofHom (LinearMap.proj 1 ∘ₗ ((Rep.ρ A).coindV φ).subtype ∘ₗ f.hom.hom)
    comm g := by
      ext x
      have := ((f.hom x).2 g 1).symm
      have := hom_comm_apply f (φ g) x
      simp_all }
  left_inv := by intro; ext; simp
  right_inv z := by ext; have := hom_comm_apply z; simp_all

variable (k) in
/-- Given a monoid homomorphism `φ : G →* H`, the coinduction functor `Rep k G ⥤ Rep k H` is right
adjoint to the restriction functor along `φ`. -/
@[simps! counit_app_hom_hom unit_app_hom_hom]
noncomputable abbrev resCoindAdjunction : Action.res _ φ ⊣ coindFunctor k φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y := (resCoindHomEquiv φ X Y).toEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; ext; rfl }

noncomputable instance : Limits.PreservesLimits (coindFunctor k φ) :=
  (resCoindAdjunction k φ).rightAdjoint_preservesLimits

end Adjunction
end Rep
