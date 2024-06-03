/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.CategoryTheory.Sites.Canonical

#align_import category_theory.sites.types from "leanprover-community/mathlib"@"9f9015c645d85695581237cc761981036be8bd37"

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a Grothendieck topology on the category of types,
and construct the canonical functor that sends a type to a sheaf over
the category of types, and make this an equivalence of categories.

Then we prove that the topology defined is the canonical topology.
-/


universe u

namespace CategoryTheory

--open scoped CategoryTheory.Type -- Porting note: unknown namespace

/-- A Grothendieck topology associated to the category of all types.
A sieve is a covering iff it is jointly surjective. -/
def typesGrothendieckTopology : GrothendieckTopology (Type u) where
  sieves α S := ∀ x : α, S fun _ : PUnit => x
  top_mem' _ _ := trivial
  pullback_stable' _ _ _ f hs x := hs (f x)
  transitive' _ _ hs _ hr x := hr (hs x) PUnit.unit
#align category_theory.types_grothendieck_topology CategoryTheory.typesGrothendieckTopology

/-- The discrete sieve on a type, which only includes arrows whose image is a subsingleton. -/
@[simps]
def discreteSieve (α : Type u) : Sieve α where
  arrows _ f := ∃ x, ∀ y, f y = x
  downward_closed := fun ⟨x, hx⟩ g => ⟨x, fun y => hx <| g y⟩
#align category_theory.discrete_sieve CategoryTheory.discreteSieve

theorem discreteSieve_mem (α : Type u) : discreteSieve α ∈ typesGrothendieckTopology α :=
  fun x => ⟨x, fun _ => rfl⟩
#align category_theory.discrete_sieve_mem CategoryTheory.discreteSieve_mem

/-- The discrete presieve on a type, which only includes arrows whose domain is a singleton. -/
def discretePresieve (α : Type u) : Presieve α :=
  fun β _ => ∃ x : β, ∀ y : β, y = x
#align category_theory.discrete_presieve CategoryTheory.discretePresieve

theorem generate_discretePresieve_mem (α : Type u) :
    Sieve.generate (discretePresieve α) ∈ typesGrothendieckTopology α :=
  fun x => ⟨PUnit, id, fun _ => x, ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩, rfl⟩
#align category_theory.generate_discrete_presieve_mem CategoryTheory.generate_discretePresieve_mem

open Presieve

theorem isSheaf_yoneda' {α : Type u} : IsSheaf typesGrothendieckTopology (yoneda.obj α) :=
  fun β S hs x hx =>
  ⟨fun y => x _ (hs y) PUnit.unit, fun γ f h =>
    funext fun z => by
      convert congr_fun (hx (𝟙 _) (fun _ => z) (hs <| f z) h rfl) PUnit.unit using 1,
    fun f hf => funext fun y => by convert congr_fun (hf _ (hs y)) PUnit.unit⟩
#align category_theory.is_sheaf_yoneda' CategoryTheory.isSheaf_yoneda'

/-- The yoneda functor that sends a type to a sheaf over the category of types. -/
@[simps]
def yoneda' : Type u ⥤ SheafOfTypes typesGrothendieckTopology where
  obj α := ⟨yoneda.obj α, isSheaf_yoneda'⟩
  map f := ⟨yoneda.map f⟩
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
  (hs.isSheafFor _ _ (generate_discretePresieve_mem α)).amalgamate
    (fun β g hg => S.map (↾fun _ => PUnit.unit).op <| f <| g <| Classical.choose hg)
    fun β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h =>
    (hs.isSheafFor _ _ (generate_discretePresieve_mem δ)).isSeparatedFor.ext fun ε g ⟨x, _⟩ => by
      have : f₁ (Classical.choose hf₁) = f₂ (Classical.choose hf₂) :=
        Classical.choose_spec hf₁ (g₁ <| g x) ▸
          Classical.choose_spec hf₂ (g₂ <| g x) ▸ congr_fun h _
      simp_rw [← FunctorToTypes.map_comp_apply, this, ← op_comp]
      rfl
#align category_theory.types_glue CategoryTheory.typesGlue

theorem eval_typesGlue {S hs α} (f) : eval.{u} S α (typesGlue S hs α f) = f := by
  funext x
  apply (IsSheafFor.valid_glue _ _ _ <| ⟨PUnit.unit, fun _ => Subsingleton.elim _ _⟩).trans
  convert FunctorToTypes.map_id_apply S _
#align category_theory.eval_types_glue CategoryTheory.eval_typesGlue

theorem typesGlue_eval {S hs α} (s) : typesGlue.{u} S hs α (eval S α s) = s := by
  apply (hs.isSheafFor _ _ (generate_discretePresieve_mem α)).isSeparatedFor.ext
  intro β f hf
  apply (IsSheafFor.valid_glue _ _ _ hf).trans
  apply (FunctorToTypes.map_comp_apply _ _ _ _).symm.trans
  rw [← op_comp]
  --congr 2 -- Porting note: This tactic didn't work. Find an alternative.
  suffices ((↾fun _ ↦ PUnit.unit) ≫ ↾fun _ ↦ f (Classical.choose hf)) = f by rw [this]
  funext x
  exact congr_arg f (Classical.choose_spec hf x).symm
#align category_theory.types_glue_eval CategoryTheory.typesGlue_eval

/-- Given a sheaf `S`, construct an equivalence `S(α) ≃ (α → S(*))`. -/
@[simps]
noncomputable def evalEquiv (S : Type uᵒᵖ ⥤ Type u) (hs : IsSheaf typesGrothendieckTopology S)
    (α : Type u) : S.obj (op α) ≃ (α → S.obj (op PUnit)) where
  toFun := eval S α
  invFun := typesGlue S hs α
  left_inv := typesGlue_eval
  right_inv := eval_typesGlue
#align category_theory.eval_equiv CategoryTheory.evalEquiv

theorem eval_map (S : Type uᵒᵖ ⥤ Type u) (α β) (f : β ⟶ α) (s x) :
    eval S β (S.map f.op s) x = eval S α s (f x) := by
  simp_rw [eval, ← FunctorToTypes.map_comp_apply, ← op_comp]; rfl
#align category_theory.eval_map CategoryTheory.eval_map

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps!]
noncomputable def equivYoneda (S : Type uᵒᵖ ⥤ Type u) (hs : IsSheaf typesGrothendieckTopology S) :
    S ≅ yoneda.obj (S.obj (op PUnit)) :=
  NatIso.ofComponents (fun α => Equiv.toIso <| evalEquiv S hs <| unop α) fun {α β} f =>
    funext fun _ => funext fun _ => eval_map S (unop α) (unop β) f.unop _ _
#align category_theory.equiv_yoneda CategoryTheory.equivYoneda

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps]
noncomputable def equivYoneda' (S : SheafOfTypes typesGrothendieckTopology) :
    S ≅ yoneda'.obj (S.1.obj (op PUnit)) where
  hom := ⟨(equivYoneda S.1 S.2).hom⟩
  inv := ⟨(equivYoneda S.1 S.2).inv⟩
  hom_inv_id := by ext1; apply (equivYoneda S.1 S.2).hom_inv_id
  inv_hom_id := by ext1; apply (equivYoneda S.1 S.2).inv_hom_id
#align category_theory.equiv_yoneda' CategoryTheory.equivYoneda'

theorem eval_app (S₁ S₂ : SheafOfTypes.{u} typesGrothendieckTopology) (f : S₁ ⟶ S₂) (α : Type u)
    (s : S₁.1.obj (op α)) (x : α) :
    eval S₂.1 α (f.val.app (op α) s) x = f.val.app (op PUnit) (eval S₁.1 α s x) :=
  (congr_fun (f.val.naturality (↾fun _ : PUnit => x).op) s).symm
#align category_theory.eval_app CategoryTheory.eval_app

/-- `yoneda'` induces an equivalence of category between `Type u` and
`SheafOfTypes typesGrothendieckTopology`. -/
@[simps!]
noncomputable def typeEquiv : Type u ≌ SheafOfTypes typesGrothendieckTopology :=
  Equivalence.mk yoneda' (sheafOfTypesToPresheaf _ ⋙ (evaluation _ _).obj (op PUnit))
    (NatIso.ofComponents
      (fun _α => -- α ≅ PUnit ⟶ α
        { hom := fun x _ => x
          inv := fun f => f PUnit.unit
          hom_inv_id := funext fun _ => rfl
          inv_hom_id := funext fun _ => funext fun y => PUnit.casesOn y rfl })
      fun _ => rfl)
    (Iso.symm <|
      NatIso.ofComponents (fun S => equivYoneda' S) fun {S₁ S₂} f =>
        SheafOfTypes.Hom.ext _ _ <|
          NatTrans.ext _ _ <|
            funext fun α => funext fun s => funext fun x => eval_app S₁ S₂ f (unop α) s x)
#align category_theory.type_equiv CategoryTheory.typeEquiv

theorem subcanonical_typesGrothendieckTopology : Sheaf.Subcanonical typesGrothendieckTopology.{u} :=
  Sheaf.Subcanonical.of_yoneda_isSheaf _ fun _ => isSheaf_yoneda'
#align category_theory.subcanonical_types_grothendieck_topology CategoryTheory.subcanonical_typesGrothendieckTopology

theorem typesGrothendieckTopology_eq_canonical :
    typesGrothendieckTopology.{u} = Sheaf.canonicalTopology (Type u) := by
  refine le_antisymm subcanonical_typesGrothendieckTopology (sInf_le ?_)
  refine ⟨yoneda.obj (ULift Bool), ⟨_, rfl⟩, GrothendieckTopology.ext ?_⟩
  funext α
  ext S
  refine ⟨fun hs x => ?_, fun hs β f => isSheaf_yoneda' _ fun y => hs _⟩
  by_contra hsx
  have : (fun _ => ULift.up true) = fun _ => ULift.up false :=
    (hs PUnit fun _ => x).isSeparatedFor.ext
      fun β f hf => funext fun y => hsx.elim <| S.2 hf fun _ => y
  simp [Function.funext_iff] at this
#align category_theory.types_grothendieck_topology_eq_canonical CategoryTheory.typesGrothendieckTopology_eq_canonical

end CategoryTheory
