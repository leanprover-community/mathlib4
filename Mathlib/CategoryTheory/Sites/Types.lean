/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.CategoryTheory.Sites.Canonical

/-!
# Grothendieck Topology and Sheaves on the Category of Types

In this file we define a Grothendieck topology on the category of types,
and construct the canonical functor that sends a type to a sheaf over
the category of types, and make this an equivalence of categories.

Then we prove that the topology defined is the canonical topology.
-/


universe u

namespace CategoryTheory

/-- A Grothendieck topology associated to the category of all types.
A sieve is a covering iff it is jointly surjective. -/
def typesGrothendieckTopology : GrothendieckTopology (Type u) where
  sieves α S := ∀ x : α, S fun _ : PUnit ↦ x
  top_mem' _ _ := trivial
  pullback_stable' _ _ _ f hs x := hs (f x)
  transitive' _ _ hs _ hr x := hr (hs x) PUnit.unit

/-- The discrete sieve on a type, which only includes arrows whose image is a subsingleton. -/
@[simps]
def discreteSieve (α : Type u) : Sieve α where
  arrows _ f := ∃ x, ∀ y, f y = x
  downward_closed := fun ⟨x, hx⟩ g ↦ ⟨x, fun y ↦ hx <| g y⟩

theorem discreteSieve_mem (α : Type u) : discreteSieve α ∈ typesGrothendieckTopology α :=
  fun x ↦ ⟨x, fun _ ↦ rfl⟩

/-- The discrete presieve on a type, which only includes arrows whose domain is a singleton. -/
def discretePresieve (α : Type u) : Presieve α :=
  fun β _ ↦ ∃ x : β, ∀ y : β, y = x

theorem generate_discretePresieve_mem (α : Type u) :
    Sieve.generate (discretePresieve α) ∈ typesGrothendieckTopology α :=
  fun x ↦ ⟨PUnit, id, fun _ ↦ x, ⟨PUnit.unit, fun _ ↦ Subsingleton.elim _ _⟩, rfl⟩

/-- The sheaf condition for `yoneda'`. -/
theorem Presieve.isSheaf_yoneda' {α : Type u} :
    Presieve.IsSheaf typesGrothendieckTopology (yoneda.obj α) :=
  fun β _ hs x hx ↦
  ⟨fun y ↦ x _ (hs y) PUnit.unit, fun γ f h ↦
    funext fun z ↦ by
      convert congr_fun (hx (𝟙 _) (fun _ ↦ z) (hs <| f z) h rfl) PUnit.unit using 1,
    fun f hf ↦ funext fun y ↦ by convert congr_fun (hf _ (hs y)) PUnit.unit⟩

/-- The sheaf condition for `yoneda'`. -/
theorem Presheaf.isSheaf_yoneda' {α : Type u} :
    Presheaf.IsSheaf typesGrothendieckTopology (yoneda.obj α) := by
  rw [isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_yoneda'

/-- The yoneda functor that sends a type to a sheaf over the category of types. -/
@[simps]
def yoneda' : Type u ⥤ Sheaf typesGrothendieckTopology (Type u) where
  obj α := ⟨yoneda.obj α, Presheaf.isSheaf_yoneda'⟩
  map f := ⟨yoneda.map f⟩

@[simp]
theorem yoneda'_comp : yoneda'.{u} ⋙ sheafToPresheaf _ _ = yoneda :=
  rfl

open Opposite

/-- Given a presheaf `P` on the category of types, construct
a map `P(α) → (α → P(*))` for all type `α`. -/
def eval (P : Type uᵒᵖ ⥤ Type u) (α : Type u) (s : P.obj (op α)) (x : α) : P.obj (op PUnit) :=
  P.map (↾fun _ ↦ x).op s

open Presieve

/-- Given a sheaf `S` on the category of types, construct a map
`(α → S(*)) → S(α)` that is inverse to `eval`. -/
noncomputable def typesGlue (S : Type uᵒᵖ ⥤ Type u) (hs : IsSheaf typesGrothendieckTopology S)
    (α : Type u) (f : α → S.obj (op PUnit)) : S.obj (op α) :=
  (hs.isSheafFor _ _ (generate_discretePresieve_mem α)).amalgamate
    (fun _ g hg ↦ S.map (↾fun _ ↦ PUnit.unit).op <| f <| g <| Classical.choose hg)
    fun β γ δ g₁ g₂ f₁ f₂ hf₁ hf₂ h ↦
    (hs.isSheafFor _ _ (generate_discretePresieve_mem δ)).isSeparatedFor.ext fun ε g ⟨x, _⟩ ↦ by
      have : f₁ (Classical.choose hf₁) = f₂ (Classical.choose hf₂) :=
        Classical.choose_spec hf₁ (g₁ <| g x) ▸
          Classical.choose_spec hf₂ (g₂ <| g x) ▸ congr_fun h _
      simp_rw [← FunctorToTypes.map_comp_apply, this, ← op_comp]
      rfl

theorem eval_typesGlue {S hs α} (f) : eval.{u} S α (typesGlue S hs α f) = f := by
  funext x
  apply (IsSheafFor.valid_glue _ _ _ <| ⟨PUnit.unit, fun _ ↦ Subsingleton.elim _ _⟩).trans
  convert FunctorToTypes.map_id_apply S _

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

/-- Given a sheaf `S`, construct an equivalence `S(α) ≃ (α → S(*))`. -/
@[simps]
noncomputable def evalEquiv (S : Type uᵒᵖ ⥤ Type u)
    (hs : Presheaf.IsSheaf typesGrothendieckTopology S)
    (α : Type u) : S.obj (op α) ≃ (α → S.obj (op PUnit)) where
  toFun := eval S α
  invFun := typesGlue S ((isSheaf_iff_isSheaf_of_type _ _ ).1 hs) α
  left_inv := typesGlue_eval
  right_inv := eval_typesGlue

theorem eval_map (S : Type uᵒᵖ ⥤ Type u) (α β) (f : β ⟶ α) (s x) :
    eval S β (S.map f.op s) x = eval S α s (f x) := by
  simp_rw [eval, ← FunctorToTypes.map_comp_apply, ← op_comp]; rfl

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps!]
noncomputable def equivYoneda (S : Type uᵒᵖ ⥤ Type u)
    (hs : Presheaf.IsSheaf typesGrothendieckTopology S) :
    S ≅ yoneda.obj (S.obj (op PUnit)) :=
  NatIso.ofComponents (fun α ↦ Equiv.toIso <| evalEquiv S hs <| unop α) fun {α β} f ↦
    funext fun _ ↦ funext fun _ ↦ eval_map S (unop α) (unop β) f.unop _ _

/-- Given a sheaf `S`, construct an isomorphism `S ≅ [-, S(*)]`. -/
@[simps]
noncomputable def equivYoneda' (S : Sheaf typesGrothendieckTopology (Type u)) :
    S ≅ yoneda'.obj (S.1.obj (op PUnit)) where
  hom := ⟨(equivYoneda S.1 S.2).hom⟩
  inv := ⟨(equivYoneda S.1 S.2).inv⟩
  hom_inv_id := by ext1; apply (equivYoneda S.1 S.2).hom_inv_id
  inv_hom_id := by ext1; apply (equivYoneda S.1 S.2).inv_hom_id

theorem eval_app (S₁ S₂ : Sheaf typesGrothendieckTopology (Type u)) (f : S₁ ⟶ S₂) (α : Type u)
    (s : S₁.1.obj (op α)) (x : α) :
    eval S₂.1 α (f.val.app (op α) s) x = f.val.app (op PUnit) (eval S₁.1 α s x) :=
  (congr_fun (f.val.naturality (↾fun _ : PUnit ↦ x).op) s).symm

/-- `yoneda'` induces an equivalence of category between `Type u` and
`Sheaf typesGrothendieckTopology (Type u)`. -/
@[simps!]
noncomputable def typeEquiv : Type u ≌ Sheaf typesGrothendieckTopology (Type u) where
  functor := yoneda'
  inverse := sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op PUnit)
  unitIso := NatIso.ofComponents
      (fun _α ↦ -- α ≅ PUnit ⟶ α
        { hom := fun x _ ↦ x
          inv := fun f ↦ f PUnit.unit
          hom_inv_id := funext fun _ ↦ rfl
          inv_hom_id := funext fun _ ↦ funext fun y ↦ PUnit.casesOn y rfl })
      fun _ ↦ rfl
  counitIso := Iso.symm <|
      NatIso.ofComponents (fun S ↦ equivYoneda' S) (fun {S₁ S₂} f ↦ by
        ext ⟨α⟩ s
        dsimp at s ⊢
        ext x
        exact eval_app S₁ S₂ f α s x)
  functor_unitIso_comp X := by
    ext1
    apply yonedaEquiv.injective
    dsimp [yoneda', yonedaEquiv, evalEquiv]
    erw [typesGlue_eval]

instance subcanonical_typesGrothendieckTopology : typesGrothendieckTopology.{u}.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun _ ↦ Presieve.isSheaf_yoneda'

theorem typesGrothendieckTopology_eq_canonical :
    typesGrothendieckTopology.{u} = Sheaf.canonicalTopology (Type u) := by
  refine le_antisymm typesGrothendieckTopology.le_canonical (sInf_le ?_)
  refine ⟨yoneda.obj (ULift Bool), ⟨_, rfl⟩, GrothendieckTopology.ext ?_⟩
  funext α
  ext S
  refine ⟨fun hs x ↦ ?_, fun hs β f ↦ Presieve.isSheaf_yoneda' _ fun y ↦ hs _⟩
  by_contra hsx
  have : (fun _ ↦ ULift.up true) = fun _ ↦ ULift.up false :=
    (hs PUnit fun _ ↦ x).isSeparatedFor.ext
      fun β f hf ↦ funext fun y ↦ hsx.elim <| S.2 hf fun _ ↦ y
  simp [funext_iff] at this

end CategoryTheory
