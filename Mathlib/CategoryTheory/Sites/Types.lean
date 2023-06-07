/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module category_theory.sites.types
! leanprover-community/mathlib commit 9f9015c645d85695581237cc761981036be8bd37
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Sites.Canonical

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a Grothendieck topology on the category of types,
and construct the canonical functor that sends a type to a sheaf over
the category of types, and make this an equivalence of categories.

Then we prove that the topology defined is the canonical topology.
-/


universe u

namespace CategoryTheory

open scoped CategoryTheory.Type

/-- A Grothendieck topology associated to the category of all types.
A sieve is a covering iff it is jointly surjective. -/
def typesGrothendieckTopology : GrothendieckTopology (Type u)
    where
  sieves α S := ∀ x : α, S fun _ : PUnit => x
  top_mem' α x := trivial
  pullback_stable' α β S f hs x := hs (f x)
  transitive' α S hs R hr x := hr (hs x) PUnit.unit
#align category_theory.types_grothendieck_topology CategoryTheory.typesGrothendieckTopology

/-- The discrete sieve on a type, which only includes arrows whose image is a subsingleton. -/
@[simps]
def discreteSieve (α : Type u) : Sieve α
    where
  arrows β f := ∃ x, ∀ y, f y = x
  downward_closed' := fun β γ f ⟨x, hx⟩ g => ⟨x, fun y => hx <| g y⟩
#align category_theory.discrete_sieve CategoryTheory.discreteSieve

theorem discreteSieve_mem (α : Type u) : discreteSieve α ∈ typesGrothendieckTopology α := fun x =>
  ⟨x, fun y => rfl⟩
#align category_theory.discrete_sieve_mem CategoryTheory.discreteSieve_mem

/-- The discrete presieve on a type, which only includes arrows whose domain is a singleton. -/
def discretePresieve (α : Type u) : Presieve α := fun β f => ∃ x : β, ∀ y : β, y = x
#align category_theory.discrete_presieve CategoryTheory.discretePresieve

theorem generate_discretePresieve_mem (α : Type u) :
    Sieve.generate (discretePresieve α) ∈ typesGrothendieckTopology α := fun x =>
  ⟨PUnit, id, fun _ => x, ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩, rfl⟩
#align category_theory.generate_discrete_presieve_mem CategoryTheory.generate_discretePresieve_mem

open Presieve

theorem isSheaf_yoneda' {α : Type u} : IsSheaf typesGrothendieckTopology (yoneda.obj α) :=
  fun β S hs x hx =>
  ⟨fun y => x _ (hs y) PUnit.unit, fun γ f h =>
    funext fun z =>
      by
      have := congr_fun (hx (𝟙 _) (fun _ => z) (hs <| f z) h rfl) PUnit.unit
      convert this
      exact rfl,
    fun f hf => funext fun y => by convert congr_fun (hf _ (hs y)) PUnit.unit⟩
#align category_theory.is_sheaf_yoneda' CategoryTheory.isSheaf_yoneda'

/-- The yoneda functor that sends a type to a sheaf over the category of types -/
@[simps]
def yoneda' : Type u ⥤ SheafOfTypes typesGrothendieckTopology
    where
  obj α := ⟨yoneda.obj α, isSheaf_yoneda'⟩
  map α β f := ⟨yoneda.map f⟩
#align category_theory.yoneda' CategoryTheory.yoneda'

@[simp]
theorem yoneda'_comp : yoneda'.{u} ⋙ sheafOfTypesToPresheaf _ = yoneda :=
  rfl
#align category_theory.yoneda'_comp CategoryTheory.yoneda'_comp

open Opposite

/-- Given a presheaf `P` on the category of types, construct
a map `P(α) → (α → P(*))` for all type `α`. -/
def eval (P : Type uᵒᵖ ⥤ Type u) (α : Type u) (s : P.obj (op α)) (x : α) : P.obj (op PUnit) :=
  P.map (↾fun _ => x).op s
#align category_theory.eval CategoryTheory.eval

/-- Given a sheaf `S` on the category of types, construct a map
`(α → S(*)) → S(α)` that is inverse to `eval`. -/
noncomputable def typesGlue (S : Type uᵒᵖ ⥤ Type u) (hs : IsSheaf typesGrothendieckTopology S)
    (α : Type u) (f : α → S.obj (op PUnit)) : S.obj (op α) :=
  (hs.IsSheafFor _ _ (generate_discretePresieve_mem α)).amalgamate
    (fun β g hg => S.map (↾fun x => PUnit.unit).op <| f <| g <| Classical.choose hg)
    fun β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h =>
    (hs.IsSheafFor _ _ (generate_discretePresieve_mem δ)).IsSeparatedFor.ext fun ε g ⟨x, hx⟩ =>
      by
      have : f₁ (Classical.choose hf₁) = f₂ (Classical.choose hf₂) :=
        Classical.choose_spec hf₁ (g₁ <| g x) ▸
          Classical.choose_spec hf₂ (g₂ <| g x) ▸ congr_fun h _
      simp_rw [← functor_to_types.map_comp_apply, this, ← op_comp]
      rfl
#align category_theory.types_glue CategoryTheory.typesGlue

theorem eval_typesGlue {S hs α} (f) : eval.{u} S α (typesGlue S hs α f) = f :=
  funext fun x =>
    (IsSheafFor.valid_glue _ _ _ <| ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩).trans <| by
      convert functor_to_types.map_id_apply _ _; rw [← op_id]; congr
#align category_theory.eval_types_glue CategoryTheory.eval_typesGlue

theorem typesGlue_eval {S hs α} (s) : typesGlue.{u} S hs α (eval S α s) = s :=
  (hs.IsSheafFor _ _ (generate_discretePresieve_mem α)).IsSeparatedFor.ext fun β f hf =>
    (IsSheafFor.valid_glue _ _ _ hf).trans <|
      (FunctorToTypes.map_comp_apply _ _ _ _).symm.trans <| by rw [← op_comp]; congr 2;
        exact funext fun x => congr_arg f (Classical.choose_spec hf x).symm
#align category_theory.types_glue_eval CategoryTheory.typesGlue_eval

/-- Given a sheaf `S`, construct an equivalence `S(α) ≃ (α → S(*))`. -/
@[simps]
noncomputable def evalEquiv (S : Type uᵒᵖ ⥤ Type u) (hs : IsSheaf typesGrothendieckTopology S)
    (α : Type u) : S.obj (op α) ≃ (α → S.obj (op PUnit))
    where
  toFun := eval S α
  invFun := typesGlue S hs α
  left_inv := typesGlue_eval
  right_inv := eval_typesGlue
#align category_theory.eval_equiv CategoryTheory.evalEquiv

theorem eval_map (S : Type uᵒᵖ ⥤ Type u) (α β) (f : β ⟶ α) (s x) :
    eval S β (S.map f.op s) x = eval S α s (f x) := by
  simp_rw [eval, ← functor_to_types.map_comp_apply, ← op_comp]; rfl
#align category_theory.eval_map CategoryTheory.eval_map

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps]
noncomputable def equivYoneda (S : Type uᵒᵖ ⥤ Type u) (hs : IsSheaf typesGrothendieckTopology S) :
    S ≅ yoneda.obj (S.obj (op PUnit)) :=
  NatIso.ofComponents (fun α => Equiv.toIso <| evalEquiv S hs <| unop α) fun α β f =>
    funext fun s => funext fun x => eval_map S (unop α) (unop β) f.unop _ _
#align category_theory.equiv_yoneda CategoryTheory.equivYoneda

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps]
noncomputable def equivYoneda' (S : SheafOfTypes typesGrothendieckTopology) :
    S ≅ yoneda'.obj (S.1.obj (op PUnit))
    where
  Hom := ⟨(equivYoneda S.1 S.2).Hom⟩
  inv := ⟨(equivYoneda S.1 S.2).inv⟩
  hom_inv_id' := by ext1; apply (equiv_yoneda S.1 S.2).hom_inv_id
  inv_hom_id' := by ext1; apply (equiv_yoneda S.1 S.2).inv_hom_id
#align category_theory.equiv_yoneda' CategoryTheory.equivYoneda'

theorem eval_app (S₁ S₂ : SheafOfTypes.{u} typesGrothendieckTopology) (f : S₁ ⟶ S₂) (α : Type u)
    (s : S₁.1.obj (op α)) (x : α) :
    eval S₂.1 α (f.val.app (op α) s) x = f.val.app (op PUnit) (eval S₁.1 α s x) :=
  (congr_fun (f.val.naturality (↾fun _ : PUnit => x).op) s).symm
#align category_theory.eval_app CategoryTheory.eval_app

/-- `yoneda'` induces an equivalence of category between `Type u` and
`Sheaf types_grothendieck_topology`. -/
@[simps]
noncomputable def typeEquiv : Type u ≌ SheafOfTypes typesGrothendieckTopology :=
  Equivalence.mk yoneda' (sheafOfTypesToPresheaf _ ⋙ (evaluation _ _).obj (op PUnit))
    (NatIso.ofComponents
      (fun α =>
        -- α ≅ punit ⟶ α
        { Hom := fun x _ => x
          inv := fun f => f PUnit.unit
          hom_inv_id' := funext fun x => rfl
          inv_hom_id' := funext fun f => funext fun y => PUnit.casesOn y rfl })
      fun α β f => rfl)
    (Iso.symm <|
      NatIso.ofComponents (fun S => equivYoneda' S) fun S₁ S₂ f =>
        SheafOfTypes.Hom.ext _ _ <|
          NatTrans.ext _ _ <|
            funext fun α => funext fun s => funext fun x => eval_app S₁ S₂ f (unop α) s x)
#align category_theory.type_equiv CategoryTheory.typeEquiv

theorem subcanonical_typesGrothendieckTopology : Sheaf.Subcanonical typesGrothendieckTopology.{u} :=
  Sheaf.Subcanonical.of_yoneda_isSheaf _ fun X => isSheaf_yoneda'
#align category_theory.subcanonical_types_grothendieck_topology CategoryTheory.subcanonical_typesGrothendieckTopology

theorem typesGrothendieckTopology_eq_canonical :
    typesGrothendieckTopology.{u} = Sheaf.canonicalTopology (Type u) :=
  le_antisymm subcanonical_typesGrothendieckTopology <|
    sInf_le
      ⟨yoneda.obj (ULift Bool), ⟨_, rfl⟩,
        GrothendieckTopology.ext <|
          funext fun α =>
            Set.ext fun S =>
              ⟨fun hs x =>
                by_contradiction fun hsx =>
                  have :
                    (fun _ => ULift.up true : (yoneda.obj (ULift Bool)).obj (op PUnit)) = fun _ =>
                      ULift.up false :=
                    (hs PUnit fun _ => x).IsSeparatedFor.ext fun β f hf =>
                      funext fun y => hsx.elim <| S.2 hf fun _ => y
                  Bool.noConfusion <| ULift.up.inj <| (congr_fun this PUnit.unit : _),
                fun hs β f => isSheaf_yoneda' _ fun y => hs _⟩⟩
#align category_theory.types_grothendieck_topology_eq_canonical CategoryTheory.typesGrothendieckTopology_eq_canonical

end CategoryTheory

