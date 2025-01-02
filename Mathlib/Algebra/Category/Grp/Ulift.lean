/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Module.CharacterModule

/-!
# Properties of the universe lift functor for groups

This file shows that the functors `Grp.uliftFunctor` and `CommGrp.uliftFunctor`
(as well as the additive versions) are fully faithful, preserves all limits and
create small limits.

Full faithfulness is pretty obvious. To prove that the functors preserves limits,
we use the fact that the forgetful functor from `Grp` or `CommGrp` into `Type`
creates all limits (because of the way limits are constructed in `Grp` and `CommGrp`),
and that the universe lift functor on `Type` preserves all limits. Once we know
that `Grp.uliftFunctor` preserves all limits and is fully faithful, it will
automatically create all limits that exist, i.e. all small ones.

We then switch to `AddCommGrp` and show that `AddCommGrp.uliftFunctor` preserves zero morphisms
and is an additive functor, which again is pretty obvious.

The last result is a proof that `AddCommGrp.uliftFunctor` preserves all colimits
(and hence creates small colimits). This is the only non-formal part of this file,
as we follow the same strategy as for the categories `Type`.

Suppose that we have a functor `K : J ⥤ AddCommGrp.{u}` (with `J` any category), a
colimit cocone `c` of `K` and a cocone `lc` of `K ⋙ uliftFunctor.{u v}`. We want to
construct a morphism of cocones `uliftFunctor.mapCocone c → lc` witnessing the fact
that `uliftFunctor.mapCocone c` is also a colimit cocone, but we have no direct way
to do this. The idea is to use that `AddCommGrp.{max v u}` has a small cogenerator,
which is just the additive (rational) circle `ℚ / ℤ`, so any abelian group of
any size can be recovered from its morphisms into `ℚ / ℤ`. More precisely, the functor
sending an abelian group `A` to its dual `A →+ ℚ / ℤ` is fully faithful, *if* we consider
the dual as a (right) module over the endomorphism ring of `ℚ / ℤ`. So an abelian
group `C` is totally determined by the restriction of the coyoneda
functor `A ↦ (C →+ A)` to the category of abelian groups at a smaller universe level.
We do not develop this totally here but do a direct construction. Every time we have
a morphism from `lc.pt` into `ℚ / ℤ`, or more generally into any small abelian group
`A`, we can construct a cocone of `K ⋙ uliftFunctor` by sticking `ULift A` at the
cocone point (this is `CategoryTheory.Limits.Cocone.extensions`), and this cocone is
actually made up of `u`-small abelian groups, hence gives a cocone of `K`. Using
the universal property of `c`, we get a morphism `c.pt →+ A`. So we have constructed
a map `(lc.pt →+ A) → (c.pt →+ A)`, and it is easy to prove that it is compatible with
postcomposition of morphisms of small abelian groups. To actually get the
morphism `c.pt →+ lc.pt`, we apply this to the canonical embedding of `lc.pt` into
`Π (_ : lc.pt →+ ℚ / ℤ), ℚ / ℤ` (this group is not small but is a product of small
groups, so our construction extends). To show that the image of `c.pt` in this product
is contained in that of `lc.pt`, we use the compatibility with postcomposition and the
fact that we can detect elements of the image just by applying morphisms from
`Π (_ : lc.pt →+ ℚ / ℤ), ℚ / ℤ` to `ℚ / ℤ`.

Note that this does *not* work for noncommutative groups, because the existence of
simple groups of arbitrary size implies that a general object `G` of `Grp` is not
determined by the restriction of `coyoneda.obj G` to the category of groups at
a smaller universe level. Indeed, the functor `Grp.uliftFunctor` does not commute
with arbitrary colimits: if we take an increasing family `K` of simple groups in
`Grp.{u}` of unbounded cardinality indexed by a linearly ordered type
(for example finitary alternating groups on a family of types in `u` of unbouded cardinality),
then the colimit of `K` in `Grp.{u}` exists and is the trivial group; meanwhile, the colimit
of `K ⋙ Grp.uliftFunctor.{u + 1}` is nontrivial (it is the "union" of all the `K j`, which is
too big to be in `Grp.{u}`).
-/

universe v w w' u

open CategoryTheory Limits

namespace Grp

/-- The universe lift functor for groups is fully faithful.
-/
@[to_additive
  "The universe lift functor for additive groups is fully faithful."]
def uliftFunctorFullyFaithful : uliftFunctor.{u, v}.FullyFaithful where
  preimage f := Grp.ofHom (MulEquiv.ulift.toMonoidHom.comp
    (f.comp MulEquiv.ulift.symm.toMonoidHom))
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- The universe lift functor for groups is faithful.
-/
@[to_additive
  "The universe lift functor for additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful := uliftFunctorFullyFaithful.faithful


/-- The universe lift functor for groups is full.
-/
@[to_additive
  "The universe lift functor for additive groups is full."]
instance : uliftFunctor.{u, v}.Full := uliftFunctorFullyFaithful.full

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ Grp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
  preserves lc := ⟨isLimitOfReflects (forget Grp.{max u v})
    (isLimitOfPreserves CategoryTheory.uliftFunctor (isLimitOfPreserves (forget Grp) lc))⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/--
The universe lift for groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where

/--
The universe lift functor on `Grp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddGrp.{u}` creates `u`-small limits."]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end Grp

namespace CommGrp

/-- The universe lift functor for commutative groups is fully faithful.
-/
@[to_additive
  "The universe lift functor for commutative additive groups is fully faithful."]
def uliftFunctorFullyFaithful : uliftFunctor.{u, v}.FullyFaithful where
  preimage f := Grp.ofHom (MulEquiv.ulift.toMonoidHom.comp
    (f.comp MulEquiv.ulift.symm.toMonoidHom))
  map_preimage _ := rfl
  preimage_map _ := rfl

-- The universe lift functor for commutative groups is faithful. -/
@[to_additive
  "The universe lift functor for commutative additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful := uliftFunctorFullyFaithful.faithful

-- The universe lift functor for commutative groups is full. -/
@[to_additive
  "The universe lift functor for commutative additive groups is full."]
instance : uliftFunctor.{u, v}.Full := uliftFunctorFullyFaithful.full

@[to_additive]
noncomputable instance uliftFunctor_preservesLimit {J : Type w} [Category.{w'} J]
    (K : J ⥤ CommGrp.{u}) : PreservesLimit K uliftFunctor.{v, u} where
  preserves lc := ⟨isLimitOfReflects (forget CommGrp.{max u v})
    (isLimitOfPreserves CategoryTheory.uliftFunctor (isLimitOfPreserves (forget CommGrp) lc))⟩

@[to_additive]
noncomputable instance uliftFunctor_preservesLimitsOfShape {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J uliftFunctor.{v, u} where

/--
The universe lift for commutative groups preserves limits of arbitrary size.
-/
@[to_additive
  "The universe lift functor for commutative additive groups preserves limits of arbitrary size."]
noncomputable instance uliftFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} where

/--
The universe lift functor on `CommGrp.{u}` creates `u`-small limits.
-/
@[to_additive
  "The universe lift functor on `AddCommGrp.{u}` creates `u`-small limits."]
noncomputable instance : CreatesLimitsOfSize.{w, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := { CreatesLimit := fun {_} ↦ createsLimitOfFullyFaithfulOfPreserves }

end CommGrp

namespace AddCommGrp

/-- The universe lift for commutative additive groups is additive.
-/
instance uliftFunctor_additive :
    AddCommGrp.uliftFunctor.{u,v}.Additive where

variable {J : Type w} [Category.{w'} J] {K : J ⥤ AddCommGrp.{u}} {c : Cocone K} (hc : IsColimit c)
  {lc : Cocone (K ⋙ AddCommGrp.uliftFunctor.{v,u})}

variable {A A' : Type} [AddCommGroup A] [AddCommGroup A']

/-- Let `K : J ⥤ AddCommGrp.{u}`, `lc` be a cocone of
`K ⋙ uliftFunctor` and `f` be a morphism from `c.pt` to a small abelian group `A`.
We form a cocone of `K` by taking as a point the lift of `A` to `Type u`, and as
morphisms `K j →+ A` the composition of `lc.ι.j : K j →+ lc.pt` and of `f`
(modulo universe changes).
-/
def coconeOfChar (f : lc.pt →+ A) : Cocone K where
  pt := AddCommGrp.of (ULift A)
  ι :=
  { app j := AddCommGrp.ofHom (((@AddEquiv.ulift A _).symm.toAddMonoidHom.comp f).comp
             ((lc.ι.app j).comp (@AddEquiv.ulift (K.obj j) _).symm.toAddMonoidHom))
    naturality {j j'} u := by
      ext a
      have := lc.ι.naturality u
      apply_fun (fun f ↦ f {down := a}) at this
      change lc.ι.app j' {down := K.map u a} = _ at this
      change ({down := f (lc.ι.app j' {down := K.map u a})} : ULift A) = _
      rw [this]
      rfl
  }

/-- Let `K : J ⥤ AddCommGrp.{u}`, `c` be a colimit cocone of `K`, `lc` be a cocone of
`K ⋙ uliftFunctor` and `f` be a morphism from `lc.pt` to a small abelian group `A`.
We get a morphism `descChar : c.pt →+ A` by applying the universal property of the colimit to
the cocone `coconeOfChar lc f` of `K`, whose point if `ULift A`.
-/
def descChar (f : lc.pt →+ A) : c.pt →+ A :=
  AddEquiv.ulift.toAddMonoidHom.comp (hc.desc (coconeOfChar f))

/--
The morphism `descChar : c.pt →+ A` underlies a morphism of cocones `c → coconeOfChar f`.
-/
lemma descChar_fac (f : lc.pt →+ A) (j : J) (a : K.obj j) :
    (descChar hc f) (c.ι.app j a) = f ((lc.ι.app j {down := a})) := by
  have := hc.fac (coconeOfChar f) j
  apply_fun (fun f ↦ f a) at this
  change hc.desc (coconeOfChar f) ((c.ι.app j) a) = _ at this
  simp only [descChar, AddEquiv.toAddMonoidHom_eq_coe, Functor.const_obj_obj, AddMonoidHom.coe_comp,
    AddMonoidHom.coe_coe, Function.comp_apply, Functor.comp_obj, AddCommGrp.uliftFunctor_obj,
    AddCommGrp.coe_of]
  simp only [Functor.const_obj_obj] at this
  conv_lhs => rw [this]
  rfl

/--
The morphism `descChar hc f : c.pt →+ A` is the unique morphism that underlies a morphism of
cocones `c → coconeOfChar f`.
-/
lemma descChar_uniq (f : lc.pt →+ A) (m : c.pt →+ A) (hm : ∀ (j : J) (a : K.obj j),
    m (c.ι.app j a) = f ((lc.ι.app j {down := a}))) : m = descChar hc f := by
  refine AddMonoidHom.ext_iff.mpr (congrFun ?_)
  dsimp [descChar]
  rw [← AddEquiv.symm_comp_eq]
  suffices AddEquiv.ulift.symm.toAddMonoidHom.comp m = hc.desc (coconeOfChar f) by rw [← this]; rfl
  refine hc.uniq (coconeOfChar f) ((@AddEquiv.ulift A _).symm.toAddMonoidHom.comp m) (fun j ↦ ?_)
  ext
  change ({down := m (c.ι.app j _)} : ULift A) = _
  rw [hm j]
  rfl

/-- Let `K : J ⥤ AddCommGrp.{u}`, `c` be a colimit cocone of `K` and `lc` be a cocone of
`K ⋙ uliftFunctor`. The function `descChar` sends any morphism `f : lc.pt →+ A`, with `A`
a small abelian group, to a morphism `c.pt →+ A`. Here we show that this construction is
compatible with postcomposition of `f` by morphisms of small abelian groups.
-/
lemma descChar_comp (f : lc.pt →+ A) (g : A →+ A') :
    descChar hc (g.comp f) = g.comp (descChar hc f) := by
  apply (AddMonoidHom.postcompEquiv (@AddEquiv.ulift A' _).symm _).injective
  refine (hc.uniq (coconeOfChar (g.comp f)) (AddEquiv.ulift.symm.toAddMonoidHom.comp
    (g.comp (descChar hc f))) (fun j ↦ ?_)).symm
  ext
  dsimp [coconeOfChar]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  have := descChar_fac hc f j
  simp only [Functor.const_obj_obj, Functor.comp_obj, uliftFunctor_obj, coe_of] at this
  conv_lhs => rw [this]
  rfl

/--
Let `K : J ⥤ AddCommGrp.{u}`, `c` be a colimit cocone of `K` and `lc` be a cocone of
`K ⋙ uliftFunctor`. The function `descChar` sends the zero morphism `lc.pt →+ A`
to the zero morphism `c.pt →+ A`.
-/
lemma descChar_zero_eq_zero : descChar hc (0 : lc.pt →+ A) = 0 := by
  have heq : (0 : lc.pt →+ A) = (0 : Unit →+ A).comp (0 : lc.pt →+ Unit) := by ext _; simp
  rw [heq, descChar_comp]
  simp

variable {ι : Type*} (B : ι → Type) [∀ (i : ι), AddCommGroup (B i)] (f : (i : ι) → lc.pt →+ B i)

/-- Let `K : J ⥤ AddCommGrp.{u}`, `c` be a colimit cocone of `K`, `lc` be a cocone of
`K ⋙ uliftFunctor` and `f i` be a family of morphisms from `lc.pt` to small abelian
groups `B i`.
We get a morphism `c.pt →+ Π i, B i` by applying the `descChar` construction to each `f i`
and taking the product. Note that the type `ι` indexing the family doesn't have to
be small.
-/
def descCharFamily : c.pt →+ ((i : ι) → B i) := Pi.addMonoidHom (fun i ↦ descChar hc (f i))

/-- Let `K : J ⥤ AddCommGrp.{u}`, `c` be a colimit cocone of `K` and `lc` be a cocone of
`K ⋙ uliftFunctor`. The function `descCharFamily` sends a family of morphisms
`f i : lc.pt →+ B i`, with the `B i` small abelian groups, to a morphism
`c.pt →+ Π i, B i`. Here we show that if we compose this morphism by a morphism
`g : Π i, B i →+ A` with `A` small, we recover `descChar` applied to
`g.comp (Pi.addMonoidHom f) : lc.pt →+ A`.
-/
lemma descCharFamily_comp (g : ((i : ι) → B i) →+ A) :
    descChar hc (g.comp (Pi.addMonoidHom f)) = g.comp (descCharFamily hc B f) := by
  apply (AddMonoidHom.postcompEquiv AddEquiv.ulift.symm _).injective
  refine (hc.uniq (coconeOfChar (g.comp (Pi.addMonoidHom f)))
    (AddEquiv.ulift.symm.toAddMonoidHom.comp (g.comp (descCharFamily hc B f)))
    (fun j ↦ ?_)).symm
  ext
  dsimp [coconeOfChar]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  congr 1
  ext i
  dsimp [descCharFamily]
  have := descChar_fac hc (f i) j
  simp only [Functor.const_obj_obj, Functor.comp_obj, uliftFunctor_obj, coe_of] at this
  rw [this]
  rfl

variable (lc)

open CharacterModule in
/-- Let `K : J ⥤ AddCommGrp.{u}`, `c` be a colimit cocone of `K` and `lc` be a cocone of
`K ⋙ uliftFunctor`. We construct a morphism `descHom: c.pt →+ lc.pt` such that, for every
morphism `χ : lc.pt →+ ℚ / ℤ`, the morphism `descHom.comp χ : c.pt →+ ℚ / ℤ` is equal to
`descChar hc χ` (this last statenant is proved in `descHom_property`).
-/
noncomputable def descHom : c.pt →+ lc.pt := by
  set u := descCharFamily hc (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ)) (fun c ↦ c)
  have h : (QuotientAddGroup.mk' (AddMonoidHom.range (homToPi lc.pt))).comp u = 0 := by
    refine hom_eq_zero_of_character_apply (fun c ↦ ?_)
    rw [← AddMonoidHom.comp_assoc, ← descCharFamily_comp hc
      (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ)) (fun c ↦ c)]
    convert descChar_zero_eq_zero hc
    ext
    change (c.comp ((QuotientAddGroup.mk' (AddMonoidHom.range (homToPi lc.pt))).comp
      (homToPi lc.pt))) _ = 0
    rw [(AddMonoidHom.range_le_ker_iff _ _).mp (le_of_eq (QuotientAddGroup.ker_mk' _).symm),
      c.comp_zero, AddMonoidHom.zero_apply]
  rw [← AddMonoidHom.range_le_ker_iff, ← (QuotientAddGroup.ker_mk' _).symm] at h
  exact (AddMonoidHom.ofInjective (homToPi_injective lc.pt)).symm.toAddMonoidHom.comp
    ((AddSubgroup.inclusion h).comp (AddMonoidHom.rangeRestrict u))

open CharacterModule in
lemma descHom_property (χ : lc.pt →+ AddCircle (1 : ℚ)) : χ.comp (descHom hc lc) =
    descChar hc χ := by
  change ((Pi.evalAddMonoidHom (fun (_ : CharacterModule lc.pt) ↦ AddCircle (1 : ℚ)) χ).comp
    (homToPi lc.pt)).comp (descHom hc lc) = _
  refine AddMonoidHom.ext (fun a ↦ ?_)
  rw [AddMonoidHom.comp_assoc, AddMonoidHom.comp_apply]
  erw [AddMonoidHom.apply_ofInjective_symm (homToPi_injective lc.pt),
    AddMonoidHom.coe_rangeRestrict, ← AddMonoidHom.comp_apply (Pi.evalAddMonoidHom
    (fun x ↦ AddCircle 1) χ) (descCharFamily hc (fun x ↦ AddCircle 1) fun c ↦ c)]

/-- Let `K : J ⥤ AddCommGrp.{u}`, `c` be a colimit cocone of `K` and `lc` be a cocone of
`K ⋙ uliftFunctor`. The morphism `descHom: c.pt →+ lc.pt` underlies a morphism of
cocones.
-/
lemma descHom_fac (j : J) (a : K.obj j) :
    descHom hc lc (c.ι.app j a) = lc.ι.app j {down := a} := by
  rw [← add_neg_eq_zero]
  refine CharacterModule.eq_zero_of_character_apply (fun χ ↦ ?_)
  rw [χ.map_add]
  change (χ.comp ((descHom hc lc).comp (c.ι.app j))) a + _ = 0
  rw [← AddMonoidHom.comp_assoc, descHom_property]
  change descChar hc χ _ + _ = _
  have := descChar_fac hc χ
  simp only [Functor.const_obj_obj, Functor.comp_obj, uliftFunctor_obj, coe_of] at this
  rw [this]
  simp

/-- Let `K : J ⥤ AddCommGrp.{u}`, `c` be a colimit cocone of `K` and `lc` be a cocone of
`K ⋙ uliftFunctor`. The morphism `descHom: c.pt →+ lc.pt` is the unique morphism
underlying a morphism of cocones.
-/
lemma descHom_uniq (m : c.pt →+ lc.pt) (hm : ∀ (j : J) (a : K.obj j),
    m (c.ι.app j a) = lc.ι.app j {down := a}) : m = descHom hc lc := by
  rw [← add_neg_eq_zero]
  refine CharacterModule.hom_eq_zero_of_character_apply (fun χ ↦ ?_)
  rw [AddMonoidHom.comp_add, AddMonoidHom.comp_neg, descHom_property, add_neg_eq_zero]
  refine descChar_uniq _ _ _ (fun j a ↦ ?_)
  have := hm j a
  simp only [Functor.const_obj_obj, AddMonoidHom.coe_comp, Function.comp_apply, Functor.comp_obj,
    uliftFunctor_obj, coe_of] at this ⊢
  rw [this]

/--
The functor `AddCommGr.uliftFunctor.{v,u} : AddCommGrp.{u} ⥤ AddCommGrp.{max v u}`
preserves colimits of arbitrary size.
-/
noncomputable instance : PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u} where
  preservesColimitsOfShape {J _} :=
  { preservesColimit := fun {F} ↦
    { preserves := fun {c} hc ↦ ⟨{
        desc := fun lc ↦ AddCommGrp.ofHom ((descHom hc lc).comp AddEquiv.ulift.toAddMonoidHom)
        fac := fun lc j ↦ by ext ⟨⟩; erw [← descHom_fac hc lc j]; rfl
        uniq := fun lc f hf ↦ by
          apply (AddMonoidHom.precompEquiv AddEquiv.ulift.symm _).injective
          refine descHom_uniq hc lc (f.comp AddEquiv.ulift.symm.toAddMonoidHom) (fun j a ↦ ?_)
          simp only [Functor.mapCocone_pt, AddCommGrp.uliftFunctor_obj, AddCommGrp.coe_of,
            AddEquiv.toAddMonoidHom_eq_coe, Functor.const_obj_obj, AddMonoidHom.coe_comp,
            AddMonoidHom.coe_coe, Function.comp_apply, Functor.comp_obj]
          rw [← hf j]
          rfl }⟩ } }

/--
The functor `AddCommGrp.uliftFunctor.{v,u} : AddCommGrp.{u} ⥤ AddCommGrp.{max v u}`
creates `u`-small colimits.
-/
noncomputable instance : CreatesColimitsOfSize.{u, u} uliftFunctor.{v, u} where
  CreatesColimitsOfShape := { CreatesColimit := fun {_} ↦ createsColimitOfFullyFaithfulOfPreserves }

end AddCommGrp
