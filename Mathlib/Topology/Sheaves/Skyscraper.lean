/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
module

public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Functors

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf `𝓕 : (Pre)Sheaf C X` is the (pre)sheaf with value `A` at point `p₀` that is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specializations
of `p₀`, i.e. if `p₀ ⤳ x` then `𝓕ₓ ≅ A` and if `¬ p₀ ⤳ x` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraperPresheaf`: `skyscraperPresheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraperSheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraperPresheafStalkOfSpecializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraperPresheaf p₀ A` at `y` is `A`.
* `skyscraperPresheafStalkOfNotSpecializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraperPresheaf p₀ A` at `y` is `*` the terminal object.

TODO: generalize universe level when calculating stalks, after generalizing universe level of stalk.
TODO(@joelriou): refactor the definitions in this file so as to make them
particular cases of general constructions for points of sites from
`Mathlib/CategoryTheory/Sites/Point/Skyscraper.lean`.

-/

@[expose] public section

noncomputable section

open TopologicalSpace TopCat CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v w

variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]

section

variable {C : Type v} [Category.{w} C] [HasTerminal C] (A : C)

/-- A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps]
def skyscraperPresheaf : Presheaf C X where
  obj U := if p₀ ∈ unop U then A else terminal C
  map {U V} i :=
    if h : p₀ ∈ unop V then eqToHom <| by rw [if_pos h, if_pos (by simpa using i.unop.le h)]
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  map_id U :=
    (em (p₀ ∈ U.unop)).elim (fun h => dif_pos h) fun h =>
      ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext _ _
  map_comp {U V W} iVU iWV := by
    by_cases hW : p₀ ∈ unop W
    · have hV : p₀ ∈ unop V := leOfHom iWV.unop hW
      simp only [dif_pos hW, dif_pos hV, eqToHom_trans]
    · dsimp; rw [dif_neg hW]; apply ((if_neg hW).symm.ndrec terminalIsTerminal).hom_ext

theorem skyscraperPresheaf_eq_pushforward
    [hd : ∀ U : Opens (TopCat.of PUnit.{u + 1}), Decidable (PUnit.unit ∈ U)] :
    skyscraperPresheaf p₀ A =
      (ofHom (ContinuousMap.const (TopCat.of PUnit) p₀)) _*
        skyscraperPresheaf (X := TopCat.of PUnit) PUnit.unit A := by
  convert_to @skyscraperPresheaf X p₀ (fun U => hd <| (Opens.map <| ofHom <|
      ContinuousMap.const _ p₀).obj U)
    C _ _ A = _ <;> congr

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
def SkyscraperPresheafFunctor.map' {a b : C} (f : a ⟶ b) :
    skyscraperPresheaf p₀ a ⟶ skyscraperPresheaf p₀ b where
  app U :=
    if h : p₀ ∈ U.unop then eqToHom (if_pos h) ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V i := by
    simp only [skyscraperPresheaf_map]
    by_cases hV : p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := leOfHom i.unop hV
      simp only [skyscraperPresheaf_obj, hU, hV, ↓reduceDIte, eqToHom_trans_assoc, Category.assoc,
        eqToHom_trans]
    · apply ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext

theorem SkyscraperPresheafFunctor.map'_id {a : C} :
    SkyscraperPresheafFunctor.map' p₀ (𝟙 a) = 𝟙 _ := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]; split_ifs <;> cat_disch

theorem SkyscraperPresheafFunctor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    SkyscraperPresheafFunctor.map' p₀ (f ≫ g) =
      SkyscraperPresheafFunctor.map' p₀ f ≫ SkyscraperPresheafFunctor.map' p₀ g := by
  ext U
  simp only [SkyscraperPresheafFunctor.map'_app]
  split_ifs with h <;> cat_disch

/-- Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps]
def skyscraperPresheafFunctor : C ⥤ Presheaf C X where
  obj := skyscraperPresheaf p₀
  map := SkyscraperPresheafFunctor.map' p₀
  map_id _ := SkyscraperPresheafFunctor.map'_id p₀
  map_comp := SkyscraperPresheafFunctor.map'_comp p₀

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.
variable {C : Type v} [Category.{u} C] (A : C) [HasTerminal C]

set_option backward.isDefEq.respectTransparency false in
/-- The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ closure {p₀}`
-/
@[simps]
def skyscraperPresheafCoconeOfSpecializes {y : X} (h : p₀ ⤳ y) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := A
  ι :=
    { app := fun U => eqToHom <| if_pos <| h.mem_open U.unop.1.2 U.unop.2
      naturality := fun U V inc => by
        change dite _ _ _ ≫ _ = _; rw [dif_pos]
        swap
        · exact h.mem_open V.unop.1.2 V.unop.2
        · simp only [Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, unop_op,
            Functor.const_obj_obj, eqToHom_trans, Functor.const_obj_map, Category.comp_id] }

set_option backward.isDefEq.respectTransparency false in
/--
The cocone at `A` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfSpecializes {y : X} (h : p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCoconeOfSpecializes p₀ A h) where
  desc c := eqToHom (if_pos trivial).symm ≫ c.ι.app (op ⊤)
  fac c U := by
    dsimp
    rw [← c.w (homOfLE <| (le_top : unop U ≤ _)).op]
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _
    rw [dif_pos]
    · simp only [eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, op_unop]
    · exact h.mem_open U.unop.1.2 U.unop.2
  uniq c f h := by
    dsimp
    rw [← h, skyscraperPresheafCoconeOfSpecializes_ι_app, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]

/-- If `y ∈ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is `A`.
-/
noncomputable def skyscraperPresheafStalkOfSpecializes [HasColimits C] {y : X} (h : p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ A :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfSpecializes p₀ A h⟩

@[reassoc (attr := simp)]
lemma germ_skyscraperPresheafStalkOfSpecializes_hom [HasColimits C] {y : X} (h : p₀ ⤳ y) (U hU) :
    (skyscraperPresheaf p₀ A).germ U y hU ≫
      (skyscraperPresheafStalkOfSpecializes p₀ A h).hom = eqToHom (if_pos (h.mem_open U.2 hU)) :=
  colimit.isoColimitCocone_ι_hom _ _

/-- The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ closure {p₀}`
-/
@[simps]
def skyscraperPresheafCocone (y : X) :
    Cocone ((OpenNhds.inclusion y).op ⋙ skyscraperPresheaf p₀ A) where
  pt := terminal C
  ι :=
    { app := fun _ => terminal.from _
      naturality := fun _ _ _ => terminalIsTerminal.hom_ext _ _ }

set_option backward.isDefEq.respectTransparency false in
/--
The cocone at `*` for the stalk functor of `skyscraperPresheaf p₀ A` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraperPresheafCoconeIsColimitOfNotSpecializes {y : X} (h : ¬p₀ ⤳ y) :
    IsColimit (skyscraperPresheafCocone p₀ A y) :=
  let h1 : ∃ U : OpenNhds y, p₀ ∉ U.1 :=
    let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h
    ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩
  { desc := fun c => eqToHom (if_neg h1.choose_spec).symm ≫ c.ι.app (op h1.choose)
    fac := fun c U => by
      change _ = c.ι.app (op U.unop)
      simp only [← c.w (homOfLE <| @inf_le_left _ _ h1.choose U.unop).op, ←
        c.w (homOfLE <| @inf_le_right _ _ h1.choose U.unop).op, ← Category.assoc]
      congr 1
      refine ((if_neg ?_).symm.ndrec terminalIsTerminal).hom_ext _ _
      exact fun h => h1.choose_spec h.1
    uniq := fun c f H => by
      dsimp
      rw [← Category.id_comp f, ← H, ← Category.assoc]
      congr 1; apply terminalIsTerminal.hom_ext }

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is isomorphic to a
terminal object.
-/
noncomputable def skyscraperPresheafStalkOfNotSpecializes [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    (skyscraperPresheaf p₀ A).stalk y ≅ terminal C :=
  colimit.isoColimitCocone ⟨_, skyscraperPresheafCoconeIsColimitOfNotSpecializes _ A h⟩

/-- If `y ∉ closure {p₀}`, then the stalk of `skyscraperPresheaf p₀ A` at `y` is a terminal object
-/
def skyscraperPresheafStalkOfNotSpecializesIsTerminal [HasColimits C] {y : X} (h : ¬p₀ ⤳ y) :
    IsTerminal ((skyscraperPresheaf p₀ A).stalk y) :=
  IsTerminal.ofIso terminalIsTerminal <| (skyscraperPresheafStalkOfNotSpecializes _ _ h).symm

theorem skyscraperPresheaf_isSheaf : (skyscraperPresheaf p₀ A).IsSheaf := by
  classical exact
    (Presheaf.isSheaf_iso_iff (eqToIso <| skyscraperPresheaf_eq_pushforward p₀ A)).mpr <|
      (Sheaf.pushforward_sheaf_of_sheaf _
        (Presheaf.isSheaf_on_punit_of_isTerminal _ (by
          dsimp [skyscraperPresheaf]
          rw [if_neg]
          · exact terminalIsTerminal
          · #adaptation_note /-- 2024-03-24
            Previously the universe annotation was not needed here. -/
            exact Set.notMem_empty PUnit.unit.{u + 1})))

/--
The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assigns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
@[simps!]
def skyscraperSheaf : Sheaf C X :=
  ⟨skyscraperPresheaf p₀ A, skyscraperPresheaf_isSheaf _ _⟩

/-- Taking skyscraper sheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
def skyscraperSheafFunctor : C ⥤ Sheaf C X where
  obj c := skyscraperSheaf p₀ c
  map f := ObjectProperty.homMk <| (skyscraperPresheafFunctor p₀).map f
  map_id _ := Sheaf.hom_ext <| (skyscraperPresheafFunctor p₀).map_id _
  map_comp _ _ := Sheaf.hom_ext <| (skyscraperPresheafFunctor p₀).map_comp _ _

namespace StalkSkyscraperPresheafAdjunctionAuxs

variable [HasColimits C]

/-- If `f : 𝓕.stalk p₀ ⟶ c`, then a natural transformation `𝓕 ⟶ skyscraperPresheaf p₀ c` can be
defined by: `𝓕.germ p₀ ≫ f : 𝓕(U) ⟶ c` if `p₀ ∈ U` and the unique morphism to a terminal object
if `p₀ ∉ U`.
-/
@[simps]
def toSkyscraperPresheaf {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    𝓕 ⟶ skyscraperPresheaf p₀ c where
  app U :=
    if h : p₀ ∈ U.unop then 𝓕.germ _ p₀ h ≫ f ≫ eqToHom (if_pos h).symm
    else ((if_neg h).symm.ndrec terminalIsTerminal).from _
  naturality U V inc := by
    dsimp
    by_cases hV : p₀ ∈ V.unop
    · have hU : p₀ ∈ U.unop := leOfHom inc.unop hV
      split_ifs
      rw [← Category.assoc, 𝓕.germ_res' inc, Category.assoc, Category.assoc, eqToHom_trans]
    · split_ifs
      exact ((if_neg hV).symm.ndrec terminalIsTerminal).hom_ext ..

set_option backward.isDefEq.respectTransparency false in
/-- If `f : 𝓕 ⟶ skyscraperPresheaf p₀ c` is a natural transformation, then there is a morphism
`𝓕.stalk p₀ ⟶ c` defined as the morphism from colimit to cocone at `c`.
-/
def fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) : 𝓕.stalk p₀ ⟶ c :=
  let χ : Cocone ((OpenNhds.inclusion p₀).op ⋙ 𝓕) :=
    Cocone.mk c <|
      { app := fun U => f.app ((OpenNhds.inclusion p₀).op.obj U) ≫ eqToHom (if_pos U.unop.2)
        naturality := fun U V inc => by
          dsimp only [Functor.const_obj_map, Functor.const_obj_obj, Functor.comp_map,
            Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj]
          rw [Category.comp_id, ← Category.assoc, comp_eqToHom_iff, Category.assoc,
            eqToHom_trans, f.naturality, skyscraperPresheaf_map]
          have hV : p₀ ∈ (OpenNhds.inclusion p₀).obj V.unop := V.unop.2
          simp only [dif_pos hV] }
  colimit.desc _ χ

@[reassoc (attr := simp)]
lemma germ_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) (U) (hU) :
    𝓕.germ U p₀ hU ≫ fromStalk p₀ f = f.app (op U) ≫ eqToHom (if_pos hU) :=
  colimit.ι_desc _ _

theorem to_skyscraper_fromStalk {𝓕 : Presheaf C X} {c : C} (f : 𝓕 ⟶ skyscraperPresheaf p₀ c) :
    toSkyscraperPresheaf p₀ (fromStalk _ f) = f := by
  apply NatTrans.ext
  ext U
  dsimp
  split_ifs with h
  · simp
  · exact ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext ..

theorem fromStalk_to_skyscraper {𝓕 : Presheaf C X} {c : C} (f : 𝓕.stalk p₀ ⟶ c) :
    fromStalk p₀ (toSkyscraperPresheaf _ f) = f := by
  refine 𝓕.stalk_hom_ext fun U hxU ↦ ?_
  rw [germ_fromStalk, toSkyscraperPresheaf_app, dif_pos hxU, Category.assoc, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, Presheaf.germ]

set_option backward.isDefEq.respectTransparency false in
/-- The unit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
@[simps]
protected def unit :
    𝟭 (Presheaf C X) ⟶ Presheaf.stalkFunctor C p₀ ⋙ skyscraperPresheafFunctor p₀ where
  app _ := toSkyscraperPresheaf _ <| 𝟙 _
  naturality 𝓕 𝓖 f := by
    ext U; dsimp
    split_ifs with h
    · simp only [Category.id_comp, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Presheaf.stalkFunctor_map_germ_assoc, Presheaf.stalkFunctor_obj]
    · apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext

set_option backward.isDefEq.respectTransparency false in
/-- The counit in `Presheaf.stalkFunctor ⊣ skyscraperPresheafFunctor`
-/
@[simps]
protected def counit :
    skyscraperPresheafFunctor p₀ ⋙ (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⟶ 𝟭 C where
  app c := (skyscraperPresheafStalkOfSpecializes p₀ c specializes_rfl).hom
  naturality x y f := TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ by simp [hxU]

end StalkSkyscraperPresheafAdjunctionAuxs

section

open StalkSkyscraperPresheafAdjunctionAuxs

set_option backward.isDefEq.respectTransparency false in
/-- `skyscraperPresheafFunctor` is the right adjoint of `Presheaf.stalkFunctor`
-/
def skyscraperPresheafStalkAdjunction [HasColimits C] :
    (Presheaf.stalkFunctor C p₀ : Presheaf C X ⥤ C) ⊣ skyscraperPresheafFunctor p₀ where
  unit := StalkSkyscraperPresheafAdjunctionAuxs.unit _
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit _
  left_triangle_components X := by
    dsimp [Presheaf.stalkFunctor, toSkyscraperPresheaf]
    ext
    simp only [Functor.comp_obj, Functor.op_obj, ι_colimMap_assoc, skyscraperPresheaf_obj,
      Functor.whiskerLeft_app, Category.comp_id]
    split_ifs with h
    · simp [skyscraperPresheafStalkOfSpecializes]
      rfl
    · simp only [skyscraperPresheafStalkOfSpecializes, colimit.isoColimitCocone_ι_hom,
        skyscraperPresheafCoconeOfSpecializes_pt, skyscraperPresheafCoconeOfSpecializes_ι_app,
        Functor.comp_obj, Functor.op_obj, skyscraperPresheaf_obj, Functor.const_obj_obj]
      rw [comp_eqToHom_iff]
      apply ((if_neg h).symm.ndrec terminalIsTerminal).hom_ext
  right_triangle_components Y := by
    ext
    simp only [skyscraperPresheafFunctor_obj, Functor.id_obj, skyscraperPresheaf_obj,
      Presheaf.stalkFunctor_obj, unit_app, counit_app,
      skyscraperPresheafStalkOfSpecializes, skyscraperPresheafFunctor_map, Presheaf.comp_app,
      toSkyscraperPresheaf_app, Category.id_comp, SkyscraperPresheafFunctor.map'_app]
    split_ifs with h
    · simp [Presheaf.germ]
      rfl
    · simp
      rfl

instance [HasColimits C] : (skyscraperPresheafFunctor p₀ : C ⥤ Presheaf C X).IsRightAdjoint :=
  (skyscraperPresheafStalkAdjunction _).isRightAdjoint

instance [HasColimits C] : (Presheaf.stalkFunctor C p₀).IsLeftAdjoint :=
  -- Use a classical instance instead of the one from `variable`s
  have : ∀ U : Opens X, Decidable (p₀ ∈ U) := fun _ ↦ Classical.dec _
  (skyscraperPresheafStalkAdjunction _).isLeftAdjoint

/-- Taking stalks of a sheaf is the left adjoint functor to `skyscraperSheafFunctor`
-/
def stalkSkyscraperSheafAdjunction [HasColimits C] :
    Sheaf.forget C X ⋙ Presheaf.stalkFunctor _ p₀ ⊣ skyscraperSheafFunctor p₀ where
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext1` is changed to `Sheaf.Hom.ext`,
  unit :=
    { app := fun 𝓕 => ⟨(StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).app 𝓕.1⟩
      naturality := fun 𝓐 𝓑 f => Sheaf.hom_ext <| by
        apply (StalkSkyscraperPresheafAdjunctionAuxs.unit p₀).naturality }
  counit := StalkSkyscraperPresheafAdjunctionAuxs.counit p₀
  left_triangle_components X :=
    ((skyscraperPresheafStalkAdjunction p₀).left_triangle_components X.obj)
  right_triangle_components _ :=
    Sheaf.hom_ext ((skyscraperPresheafStalkAdjunction p₀).right_triangle_components _)

instance [HasColimits C] : (Sheaf.forget C X ⋙ Presheaf.stalkFunctor C p₀).IsLeftAdjoint :=
  have : ∀ U : Opens X, Decidable (p₀ ∈ U) := fun _ ↦ Classical.dec _
  (stalkSkyscraperSheafAdjunction p₀).isLeftAdjoint

instance [HasColimits C] : (skyscraperSheafFunctor p₀ : C ⥤ Sheaf C X).IsRightAdjoint :=
  (stalkSkyscraperSheafAdjunction _).isRightAdjoint

/-- Taking stalks is the left adjoint of `skyscraperSheafFunctor ⋙ Sheaf.forget`. Useful
only when the fact that `skyscraperPresheafFunctor` factors through `Sheaf C X` is relevant. -/
noncomputable def skyscraperSheafForgetAdjunction [HasColimits C] :
    Presheaf.stalkFunctor C p₀ ⊣ skyscraperSheafFunctor p₀ ⋙ Sheaf.forget C X :=
  skyscraperPresheafStalkAdjunction p₀

variable {A p₀} in
noncomputable
def skyscraper_terminal_of_not_mem {U : (Opens X)ᵒᵖ} (h : p₀ ∉ unop U) :
    IsTerminal ((skyscraperSheaf p₀ A).obj.obj U) := by
  dsimp
  rw [if_neg h]
  exact terminalIsTerminal

end

end
