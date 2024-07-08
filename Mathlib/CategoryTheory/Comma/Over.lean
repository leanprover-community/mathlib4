/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Functor.EpiMono

#align_import category_theory.over from "leanprover-community/mathlib"@"8a318021995877a44630c898d0b2bc376fceef3b"

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `Comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `Comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

Comma, Slice, Coslice, Over, Under
-/


namespace CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [CategoryTheory universes].
variable {T : Type u₁} [Category.{v₁} T]

/-- The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
triangles.

See <https://stacks.math.columbia.edu/tag/001G>.
-/
def Over (X : T) :=
  CostructuredArrow (𝟭 T) X
#align category_theory.over CategoryTheory.Over

instance (X : T) : Category (Over X) := commaCategory

-- Satisfying the inhabited linter
instance Over.inhabited [Inhabited T] : Inhabited (Over (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }
#align category_theory.over.inhabited CategoryTheory.Over.inhabited

namespace Over

variable {X : T}

@[ext]
theorem OverMorphism.ext {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left) : f = g := by
  let ⟨_,b,_⟩ := f
  let ⟨_,e,_⟩ := g
  congr
  simp only [eq_iff_true_of_subsingleton]
#align category_theory.over.over_morphism.ext CategoryTheory.Over.OverMorphism.ext

-- @[simp] : Porting note (#10618): simp can prove this
theorem over_right (U : Over X) : U.right = ⟨⟨⟩⟩ := by simp only
#align category_theory.over.over_right CategoryTheory.Over.over_right

@[simp]
theorem id_left (U : Over X) : CommaMorphism.left (𝟙 U) = 𝟙 U.left :=
  rfl
#align category_theory.over.id_left CategoryTheory.Over.id_left

@[simp]
theorem comp_left (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left :=
  rfl
#align category_theory.over.comp_left CategoryTheory.Over.comp_left

@[reassoc (attr := simp)]
theorem w {A B : Over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom := by have := f.w; aesop_cat
#align category_theory.over.w CategoryTheory.Over.w

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[simps! left hom]
def mk {X Y : T} (f : Y ⟶ X) : Over X :=
  CostructuredArrow.mk f
#align category_theory.over.mk CategoryTheory.Over.mk

/-- We can set up a coercion from arrows with codomain `X` to `over X`. This most likely should not
    be a global instance, but it is sometimes useful. -/
def coeFromHom {X Y : T} : CoeOut (Y ⟶ X) (Over X) where coe := mk
#align category_theory.over.coe_from_hom CategoryTheory.Over.coeFromHom

section

attribute [local instance] coeFromHom

@[simp]
theorem coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X).hom = f :=
  rfl
#align category_theory.over.coe_hom CategoryTheory.Over.coe_hom

end

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
    triangle. -/
@[simps!]
def homMk {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom := by aesop_cat) : U ⟶ V :=
  CostructuredArrow.homMk f w
#align category_theory.over.hom_mk CategoryTheory.Over.homMk

-- Porting note: simp solves this; simpNF still sees them after `-simp` (?)
attribute [-simp, nolint simpNF] homMk_right_down_down

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps!]
def isoMk {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom := by aesop_cat) :
    f ≅ g :=
  CostructuredArrow.isoMk hl hw
#align category_theory.over.iso_mk CategoryTheory.Over.isoMk

-- Porting note: simp solves this; simpNF still sees them after `-simp` (?)
attribute [-simp, nolint simpNF] isoMk_hom_right_down_down isoMk_inv_right_down_down

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain.

See <https://stacks.math.columbia.edu/tag/001G>.
-/
def forget : Over X ⥤ T :=
  Comma.fst _ _
#align category_theory.over.forget CategoryTheory.Over.forget

end

@[simp]
theorem forget_obj {U : Over X} : (forget X).obj U = U.left :=
  rfl
#align category_theory.over.forget_obj CategoryTheory.Over.forget_obj

@[simp]
theorem forget_map {U V : Over X} {f : U ⟶ V} : (forget X).map f = f.left :=
  rfl
#align category_theory.over.forget_map CategoryTheory.Over.forget_map

/-- The natural cocone over the forgetful functor `Over X ⥤ T` with cocone point `X`. -/
@[simps]
def forgetCocone (X : T) : Limits.Cocone (forget X) :=
  { pt := X
    ι := { app := Comma.hom } }
#align category_theory.over.forget_cocone CategoryTheory.Over.forgetCocone

/-- A morphism `f : X ⟶ Y` induces a functor `Over X ⥤ Over Y` in the obvious way.

See <https://stacks.math.columbia.edu/tag/001G>.
-/
def map {Y : T} (f : X ⟶ Y) : Over X ⥤ Over Y :=
  Comma.mapRight _ <| Discrete.natTrans fun _ => f
#align category_theory.over.map CategoryTheory.Over.map

section

variable {Y : T} {f : X ⟶ Y} {U V : Over X} {g : U ⟶ V}

@[simp]
theorem map_obj_left : ((map f).obj U).left = U.left :=
  rfl
#align category_theory.over.map_obj_left CategoryTheory.Over.map_obj_left

@[simp]
theorem map_obj_hom : ((map f).obj U).hom = U.hom ≫ f :=
  rfl
#align category_theory.over.map_obj_hom CategoryTheory.Over.map_obj_hom

@[simp]
theorem map_map_left : ((map f).map g).left = g.left :=
  rfl
#align category_theory.over.map_map_left CategoryTheory.Over.map_map_left

variable (Y)

/-- Mapping by the identity morphism is just the identity functor. -/
def mapId : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)
#align category_theory.over.map_id CategoryTheory.Over.mapId

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map f ⋙ map g :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)
#align category_theory.over.map_comp CategoryTheory.Over.mapComp

end

instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects {Y Z} f t := by
    let g : Z ⟶ Y := Over.homMk (inv ((forget X).map f))
      ((asIso ((forget X).map f)).inv_comp_eq.2 (Over.w f).symm)
    dsimp [forget] at t
    refine ⟨⟨g, ⟨?_,?_⟩⟩⟩
    repeat (ext; simp [g])
#align category_theory.over.forget_reflects_iso CategoryTheory.Over.forget_reflects_iso

/-- The identity over `X` is terminal. -/
noncomputable def mkIdTerminal : Limits.IsTerminal (mk (𝟙 X)) :=
  CostructuredArrow.mkIdTerminal

instance forget_faithful : (forget X).Faithful where
#align category_theory.over.forget_faithful CategoryTheory.Over.forget_faithful

-- TODO: Show the converse holds if `T` has binary products.
/--
If `k.left` is an epimorphism, then `k` is an epimorphism. In other words, `Over.forget X` reflects
epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`CategoryTheory.Over.epi_left_of_epi`.
-/
theorem epi_of_epi_left {f g : Over X} (k : f ⟶ g) [hk : Epi k.left] : Epi k :=
  (forget X).epi_of_epi_map hk
#align category_theory.over.epi_of_epi_left CategoryTheory.Over.epi_of_epi_left

/--
If `k.left` is a monomorphism, then `k` is a monomorphism. In other words, `Over.forget X` reflects
monomorphisms.
The converse of `CategoryTheory.Over.mono_left_of_mono`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem mono_of_mono_left {f g : Over X} (k : f ⟶ g) [hk : Mono k.left] : Mono k :=
  (forget X).mono_of_mono_map hk
#align category_theory.over.mono_of_mono_left CategoryTheory.Over.mono_of_mono_left

/--
If `k` is a monomorphism, then `k.left` is a monomorphism. In other words, `Over.forget X` preserves
monomorphisms.
The converse of `CategoryTheory.Over.mono_of_mono_left`.
-/
instance mono_left_of_mono {f g : Over X} (k : f ⟶ g) [Mono k] : Mono k.left := by
  refine ⟨fun { Y : T } l m a => ?_⟩
  let l' : mk (m ≫ f.hom) ⟶ f := homMk l (by
        dsimp; rw [← Over.w k, ← Category.assoc, congrArg (· ≫ g.hom) a, Category.assoc])
  suffices l' = (homMk m : mk (m ≫ f.hom) ⟶ f) by apply congrArg CommaMorphism.left this
  rw [← cancel_mono k]
  ext
  apply a
#align category_theory.over.mono_left_of_mono CategoryTheory.Over.mono_left_of_mono

section IteratedSlice

variable (f : Over X)

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simps]
def iteratedSliceForward : Over f ⥤ Over f.left where
  obj α := Over.mk α.hom.left
  map κ := Over.homMk κ.left.left (by dsimp; rw [← Over.w κ]; rfl)
#align category_theory.over.iterated_slice_forward CategoryTheory.Over.iteratedSliceForward

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simps]
def iteratedSliceBackward : Over f.left ⥤ Over f where
  obj g := mk (homMk g.hom : mk (g.hom ≫ f.hom) ⟶ f)
  map α := homMk (homMk α.left (w_assoc α f.hom)) (OverMorphism.ext (w α))
#align category_theory.over.iterated_slice_backward CategoryTheory.Over.iteratedSliceBackward

/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simps]
def iteratedSliceEquiv : Over f ≌ Over f.left where
  functor := iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso := NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _))
#align category_theory.over.iterated_slice_equiv CategoryTheory.Over.iteratedSliceEquiv

theorem iteratedSliceForward_forget :
    iteratedSliceForward f ⋙ forget f.left = forget f ⋙ forget X :=
  rfl
#align category_theory.over.iterated_slice_forward_forget CategoryTheory.Over.iteratedSliceForward_forget

theorem iteratedSliceBackward_forget_forget :
    iteratedSliceBackward f ⋙ forget f ⋙ forget X = forget f.left :=
  rfl
#align category_theory.over.iterated_slice_backward_forget_forget CategoryTheory.Over.iteratedSliceBackward_forget_forget

end IteratedSlice

section

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor `F : T ⥤ D` induces a functor `Over X ⥤ Over (F.obj X)` in the obvious way. -/
@[simps]
def post (F : T ⥤ D) : Over X ⥤ Over (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Over.homMk (F.map f.left)
    (by simp only [Functor.id_obj, mk_left, Functor.const_obj_obj, mk_hom, ← F.map_comp, w])
#align category_theory.over.post CategoryTheory.Over.post

end

end Over

namespace CostructuredArrow

variable {D : Type u₂} [Category.{v₂} D]

/-- Reinterpreting an `F`-costructured arrow `F.obj d ⟶ X` as an arrow over `X` induces a functor
    `CostructuredArrow F X ⥤ Over X`. -/
@[simps!]
def toOver (F : D ⥤ T) (X : T) : CostructuredArrow F X ⥤ Over X :=
  CostructuredArrow.pre F (𝟭 T) X

instance (F : D ⥤ T) (X : T) [F.Faithful] : (toOver F X).Faithful :=
  show (CostructuredArrow.pre _ _ _).Faithful from inferInstance

instance (F : D ⥤ T) (X : T) [F.Full] : (toOver F X).Full :=
  show (CostructuredArrow.pre _ _ _).Full from inferInstance

instance (F : D ⥤ T) (X : T) [F.EssSurj] : (toOver F X).EssSurj :=
  show (CostructuredArrow.pre _ _ _).EssSurj from inferInstance

/-- An equivalence `F` induces an equivalence `CostructuredArrow F X ≌ Over X`. -/
instance isEquivalence_toOver (F : D ⥤ T) (X : T) [F.IsEquivalence] :
    (toOver F X).IsEquivalence :=
  CostructuredArrow.isEquivalence_pre _ _ _

end CostructuredArrow

/-- The under category has as objects arrows with domain `X` and as morphisms commutative
    triangles. -/
def Under (X : T) :=
  StructuredArrow X (𝟭 T)
#align category_theory.under CategoryTheory.Under

instance (X : T) : Category (Under X) := commaCategory

-- Satisfying the inhabited linter
instance Under.inhabited [Inhabited T] : Inhabited (Under (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }
#align category_theory.under.inhabited CategoryTheory.Under.inhabited

namespace Under

variable {X : T}

@[ext]
theorem UnderMorphism.ext {X : T} {U V : Under X} {f g : U ⟶ V} (h : f.right = g.right) :
    f = g := by
  let ⟨_,b,_⟩ := f; let ⟨_,e,_⟩ := g
  congr; simp only [eq_iff_true_of_subsingleton]
#align category_theory.under.under_morphism.ext CategoryTheory.Under.UnderMorphism.ext

-- @[simp] Porting note (#10618): simp can prove this
theorem under_left (U : Under X) : U.left = ⟨⟨⟩⟩ := by simp only
#align category_theory.under.under_left CategoryTheory.Under.under_left

@[simp]
theorem id_right (U : Under X) : CommaMorphism.right (𝟙 U) = 𝟙 U.right :=
  rfl
#align category_theory.under.id_right CategoryTheory.Under.id_right

@[simp]
theorem comp_right (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).right = f.right ≫ g.right :=
  rfl
#align category_theory.under.comp_right CategoryTheory.Under.comp_right

@[reassoc (attr := simp)]
theorem w {A B : Under X} (f : A ⟶ B) : A.hom ≫ f.right = B.hom := by have := f.w; aesop_cat
#align category_theory.under.w CategoryTheory.Under.w

/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/
@[simps! right hom]
def mk {X Y : T} (f : X ⟶ Y) : Under X :=
  StructuredArrow.mk f
#align category_theory.under.mk CategoryTheory.Under.mk

/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
    commutative triangle. -/
@[simps!]
def homMk {U V : Under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom := by aesop_cat) : U ⟶ V :=
  StructuredArrow.homMk f w
#align category_theory.under.hom_mk CategoryTheory.Under.homMk

-- Porting note: simp solves this; simpNF still sees them after `-simp` (?)
attribute [-simp, nolint simpNF] homMk_left_down_down

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
def isoMk {f g : Under X} (hr : f.right ≅ g.right)
    (hw : f.hom ≫ hr.hom = g.hom := by aesop_cat) : f ≅ g :=
  StructuredArrow.isoMk hr hw
#align category_theory.under.iso_mk CategoryTheory.Under.isoMk

@[simp]
theorem isoMk_hom_right {f g : Under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
    (isoMk hr hw).hom.right = hr.hom :=
  rfl
#align category_theory.under.iso_mk_hom_right CategoryTheory.Under.isoMk_hom_right

@[simp]
theorem isoMk_inv_right {f g : Under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
    (isoMk hr hw).inv.right = hr.inv :=
  rfl
#align category_theory.under.iso_mk_inv_right CategoryTheory.Under.isoMk_inv_right

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain. -/
def forget : Under X ⥤ T :=
  Comma.snd _ _
#align category_theory.under.forget CategoryTheory.Under.forget

end

@[simp]
theorem forget_obj {U : Under X} : (forget X).obj U = U.right :=
  rfl
#align category_theory.under.forget_obj CategoryTheory.Under.forget_obj

@[simp]
theorem forget_map {U V : Under X} {f : U ⟶ V} : (forget X).map f = f.right :=
  rfl
#align category_theory.under.forget_map CategoryTheory.Under.forget_map

/-- The natural cone over the forgetful functor `Under X ⥤ T` with cone point `X`. -/
@[simps]
def forgetCone (X : T) : Limits.Cone (forget X) :=
  { pt := X
    π := { app := Comma.hom } }
#align category_theory.under.forget_cone CategoryTheory.Under.forgetCone

/-- A morphism `X ⟶ Y` induces a functor `Under Y ⥤ Under X` in the obvious way. -/
def map {Y : T} (f : X ⟶ Y) : Under Y ⥤ Under X :=
  Comma.mapLeft _ <| Discrete.natTrans fun _ => f
#align category_theory.under.map CategoryTheory.Under.map

section

variable {Y : T} {f : X ⟶ Y} {U V : Under Y} {g : U ⟶ V}

@[simp]
theorem map_obj_right : ((map f).obj U).right = U.right :=
  rfl
#align category_theory.under.map_obj_right CategoryTheory.Under.map_obj_right

@[simp]
theorem map_obj_hom : ((map f).obj U).hom = f ≫ U.hom :=
  rfl
#align category_theory.under.map_obj_hom CategoryTheory.Under.map_obj_hom

@[simp]
theorem map_map_right : ((map f).map g).right = g.right :=
  rfl
#align category_theory.under.map_map_right CategoryTheory.Under.map_map_right

/-- Mapping by the identity morphism is just the identity functor. -/
def mapId : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)
#align category_theory.under.map_id CategoryTheory.Under.mapId

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  NatIso.ofComponents fun X => isoMk (Iso.refl _)
#align category_theory.under.map_comp CategoryTheory.Under.mapComp

end

instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects {Y Z} f t := by
    let g : Z ⟶ Y := Under.homMk (inv ((Under.forget X).map f))
      ((IsIso.comp_inv_eq _).2 (Under.w f).symm)
    dsimp [forget] at t
    refine ⟨⟨g, ⟨?_,?_⟩⟩⟩
    repeat (ext; simp [g])
#align category_theory.under.forget_reflects_iso CategoryTheory.Under.forget_reflects_iso

/-- The identity under `X` is initial. -/
noncomputable def mkIdInitial : Limits.IsInitial (mk (𝟙 X)) :=
  StructuredArrow.mkIdInitial

instance forget_faithful : (forget X).Faithful where
#align category_theory.under.forget_faithful CategoryTheory.Under.forget_faithful

-- TODO: Show the converse holds if `T` has binary coproducts.
/-- If `k.right` is a monomorphism, then `k` is a monomorphism. In other words, `Under.forget X`
reflects epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`CategoryTheory.Under.mono_right_of_mono`.
-/
theorem mono_of_mono_right {f g : Under X} (k : f ⟶ g) [hk : Mono k.right] : Mono k :=
  (forget X).mono_of_mono_map hk
#align category_theory.under.mono_of_mono_right CategoryTheory.Under.mono_of_mono_right

/--
If `k.right` is an epimorphism, then `k` is an epimorphism. In other words, `Under.forget X`
reflects epimorphisms.
The converse of `CategoryTheory.Under.epi_right_of_epi`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem epi_of_epi_right {f g : Under X} (k : f ⟶ g) [hk : Epi k.right] : Epi k :=
  (forget X).epi_of_epi_map hk
#align category_theory.under.epi_of_epi_right CategoryTheory.Under.epi_of_epi_right

/--
If `k` is an epimorphism, then `k.right` is an epimorphism. In other words, `Under.forget X`
preserves epimorphisms.
The converse of `CategoryTheory.under.epi_of_epi_right`.
-/
instance epi_right_of_epi {f g : Under X} (k : f ⟶ g) [Epi k] : Epi k.right := by
  refine ⟨fun { Y : T } l m a => ?_⟩
  let l' : g ⟶ mk (g.hom ≫ m) := homMk l (by
    dsimp; rw [← Under.w k, Category.assoc, a, Category.assoc])
  -- Porting note: add type ascription here to `homMk m`
  suffices l' = (homMk m : g ⟶ mk (g.hom ≫ m)) by apply congrArg CommaMorphism.right this
  rw [← cancel_epi k]; ext; apply a
#align category_theory.under.epi_right_of_epi CategoryTheory.Under.epi_right_of_epi

section

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor `F : T ⥤ D` induces a functor `Under X ⥤ Under (F.obj X)` in the obvious way. -/
@[simps]
def post {X : T} (F : T ⥤ D) : Under X ⥤ Under (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Under.homMk (F.map f.right)
    (by simp only [Functor.id_obj, Functor.const_obj_obj, mk_right, mk_hom, ← F.map_comp, w])
#align category_theory.under.post CategoryTheory.Under.post

end

end Under

namespace StructuredArrow

variable {D : Type u₂} [Category.{v₂} D]

/-- Reinterpreting an `F`-structured arrow `X ⟶ F.obj d` as an arrow under `X` induces a functor
    `StructuredArrow X F ⥤ Under X`. -/
@[simps!]
def toUnder (X : T) (F : D ⥤ T) : StructuredArrow X F ⥤ Under X :=
  StructuredArrow.pre X F (𝟭 T)

instance (X : T) (F : D ⥤ T) [F.Faithful] : (toUnder X F).Faithful :=
  show (StructuredArrow.pre _ _ _).Faithful from inferInstance

instance (X : T) (F : D ⥤ T) [F.Full] : (toUnder X F).Full :=
  show (StructuredArrow.pre _ _ _).Full from inferInstance

instance (X : T) (F : D ⥤ T) [F.EssSurj] : (toUnder X F).EssSurj :=
  show (StructuredArrow.pre _ _ _).EssSurj from inferInstance

/-- An equivalence `F` induces an equivalence `StructuredArrow X F ≌ Under X`. -/
instance isEquivalence_toUnder (X : T) (F : D ⥤ T) [F.IsEquivalence] :
    (toUnder X F).IsEquivalence :=
  StructuredArrow.isEquivalence_pre _ _ _

end StructuredArrow

namespace Functor

variable {S : Type u₂} [Category.{v₂} S]

/-- Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Over X`, it suffices to
    provide maps `F.obj Y ⟶ X` for all `Y` making the obvious triangles involving all `F.map g`
    commute. -/
@[simps! obj_left map_left]
def toOver (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : S ⥤ Over X :=
  F.toCostructuredArrow (𝟭 _) X f h

/-- Upgrading a functor `S ⥤ T` to a functor `S ⥤ Over X` and composing with the forgetful functor
    `Over X ⥤ T` recovers the original functor. -/
def toOverCompForget (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ ≅ F :=
  Iso.refl _

@[simp]
lemma toOver_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ = F :=
  rfl

/-- Given `X : T`, to upgrade a functor `F : S ⥤ T` to a functor `S ⥤ Under X`, it suffices to
    provide maps `X ⟶ F.obj Y` for all `Y` making the obvious triangles involving all `F.map g`
    commute.  -/
@[simps! obj_right map_right]
def toUnder (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : S ⥤ Under X :=
  F.toStructuredArrow X (𝟭 _) f h

/-- Upgrading a functor `S ⥤ T` to a functor `S ⥤ Under X` and composing with the forgetful functor
    `Under X ⥤ T` recovers the original functor. -/
def toUnderCompForget (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forget _ ≅ F :=
  Iso.refl _

@[simp]
lemma toUnder_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forget _ = F :=
  rfl

end Functor

end CategoryTheory
