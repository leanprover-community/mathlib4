/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Category.Cat

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

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [category theory universes].
variable {T : Type u₁} [Category.{v₁} T]
variable {D : Type u₂} [Category.{v₂} D]

/-- The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
triangles. -/
@[stacks 001G]
def Over (X : T) :=
  CostructuredArrow (𝟭 T) X

instance (X : T) : Category (Over X) := commaCategory

-- Satisfying the inhabited linter
instance Over.inhabited [Inhabited T] : Inhabited (Over (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Over

variable {X : T}

@[ext]
theorem OverMorphism.ext {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left) : f = g := by
  let ⟨_,b,_⟩ := f
  let ⟨_,e,_⟩ := g
  congr
  simp only [eq_iff_true_of_subsingleton]

@[simp]
theorem over_right (U : Over X) : U.right = ⟨⟨⟩⟩ := by simp only

@[simp]
theorem id_left (U : Over X) : CommaMorphism.left (𝟙 U) = 𝟙 U.left :=
  rfl

@[simp, reassoc]
theorem comp_left (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left :=
  rfl

@[reassoc (attr := simp)]
theorem w {A B : Over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom := by have := f.w; cat_disch

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[simps! left hom]
def mk {X Y : T} (f : Y ⟶ X) : Over X :=
  CostructuredArrow.mk f

/-- We can set up a coercion from arrows with codomain `X` to `over X`. This most likely should not
be a global instance, but it is sometimes useful. -/
def coeFromHom {X Y : T} : CoeOut (Y ⟶ X) (Over X) where coe := mk

section

attribute [local instance] coeFromHom

@[simp]
theorem coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X).hom = f :=
  rfl

end

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
triangle. -/
@[simps! left]
def homMk {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom := by cat_disch) : U ⟶ V :=
  CostructuredArrow.homMk f w

@[simp]
lemma homMk_eta {U V : Over X} (f : U ⟶ V) (h) :
    homMk f.left h = f :=
  rfl

/-- This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equivalence. -/
lemma homMk_comp {U V W : Over X} (f : U.left ⟶ V.left) (g : V.left ⟶ W.left) (w_f w_g) :
    homMk (f ≫ g) (by simp_all) = homMk f w_f ≫ homMk g w_g := by
  ext
  simp

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps! hom_left inv_left]
def isoMk {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom := by cat_disch) :
    f ≅ g :=
  CostructuredArrow.isoMk hl hw

@[reassoc (attr := simp)]
lemma hom_left_inv_left {f g : Over X} (e : f ≅ g) :
    e.hom.left ≫ e.inv.left = 𝟙 f.left := by
  simp [← Over.comp_left]

@[reassoc (attr := simp)]
lemma inv_left_hom_left {f g : Over X} (e : f ≅ g) :
    e.inv.left ≫ e.hom.left = 𝟙 g.left := by
  simp [← Over.comp_left]

lemma forall_iff (P : Over X → Prop) :
    (∀ Y, P Y) ↔ (∀ (Y) (f : Y ⟶ X), P (.mk f)) := by
  aesop

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain. -/
@[stacks 001G]
def forget : Over X ⥤ T :=
  Comma.fst _ _

end

@[simp]
theorem forget_obj {U : Over X} : (forget X).obj U = U.left :=
  rfl

@[simp]
theorem forget_map {U V : Over X} {f : U ⟶ V} : (forget X).map f = f.left :=
  rfl

/-- The natural cocone over the forgetful functor `Over X ⥤ T` with cocone point `X`. -/
@[simps]
def forgetCocone (X : T) : Limits.Cocone (forget X) :=
  { pt := X
    ι := { app := Comma.hom } }

/-- A morphism `f : X ⟶ Y` induces a functor `Over X ⥤ Over Y` in the obvious way. -/
@[stacks 001G]
def map {Y : T} (f : X ⟶ Y) : Over X ⥤ Over Y :=
  Comma.mapRight _ <| Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Over X} {g : U ⟶ V}

@[simp]
theorem map_obj_left : ((map f).obj U).left = U.left :=
  rfl

@[simp]
theorem map_obj_hom : ((map f).obj U).hom = U.hom ≫ f :=
  rfl

@[simp]
theorem map_map_left : ((map f).map g).left = g.left :=
  rfl

/-- If `f` is an isomorphism, `map f` is an equivalence of categories. -/
def mapIso (f : X ≅ Y) : Over X ≌ Over Y :=
  Comma.mapRightIso _ <| Discrete.natIso fun _ ↦ f

@[simp] lemma mapIso_functor (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl
@[simp] lemma mapIso_inverse (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl

instance [IsIso f] : (Over.map f).IsEquivalence := (Over.mapIso <| asIso f).isEquivalence_functor

end

section coherences
/-!
This section proves various equalities between functors that
demonstrate, for instance, that over categories assemble into a
functor `mapFunctor : T ⥤ Cat`.

These equalities between functors are then converted to natural
isomorphisms using `eqToIso`. Such natural isomorphisms could be
obtained directly using `Iso.refl` but this method will have
better computational properties, when used, for instance, in
developing the theory of Beck-Chevalley transformations.
-/

/-- Mapping by the identity morphism is just the identity functor. -/
theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ := by
  fapply Functor.ext
  · intro x
    dsimp [Over, Over.map, Comma.mapRight]
    simp only [Category.comp_id]
    exact rfl
  · intro x y u
    dsimp [Over, Over.map, Comma.mapRight]
    simp

/-- The natural isomorphism arising from `mapForget_eq`. -/
@[simps!]
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ := eqToIso (mapId_eq Y)
--  NatIso.ofComponents fun X => isoMk (Iso.refl _)

/-- Mapping by `f` and then forgetting is the same as forgetting. -/
theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) = (forget X) := rfl

/-- The natural isomorphism arising from `mapForget_eq`. -/
def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) ≅ (forget X) := eqToIso (mapForget_eq f)

@[simp]
theorem eqToHom_left {X : T} {U V : Over X} (e : U = V) :
    (eqToHom e).left = eqToHom (e ▸ rfl : U.left = V.left) := by
  subst e; rfl

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map f) ⋙ (map g) := by
  fapply Functor.ext
  · simp [Over.map, Comma.mapRight]
  · intro U V k
    ext
    simp

/-- The natural isomorphism arising from `mapComp_eq`. -/
@[simps!]
def mapComp {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ (map f) ⋙ (map g) := eqToIso (mapComp_eq f g)

/-- If `f = g`, then `map f` is naturally isomorphic to `map g`. -/
@[simps!]
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun A ↦ eqToIso (by rw [h]))

variable (T) in
/-- The functor defined by the over categories -/
@[simps] def mapFunctor : T ⥤ Cat where
  obj X := Cat.of (Over X)
  map := map
  map_id := mapId_eq
  map_comp := mapComp_eq

end coherences

instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects {Y Z} f t := by
    let g : Z ⟶ Y := Over.homMk (inv ((forget X).map f))
      ((asIso ((forget X).map f)).inv_comp_eq.2 (Over.w f).symm)
    dsimp [forget] at t
    refine ⟨⟨g, ⟨?_,?_⟩⟩⟩
    repeat (ext; simp [g])

/-- The identity over `X` is terminal. -/
noncomputable def mkIdTerminal : Limits.IsTerminal (mk (𝟙 X)) :=
  CostructuredArrow.mkIdTerminal

instance forget_faithful : (forget X).Faithful where

-- TODO: Show the converse holds if `T` has binary products.
/--
If `k.left` is an epimorphism, then `k` is an epimorphism. In other words, `Over.forget X` reflects
epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`CategoryTheory.Over.epi_left_of_epi`.
-/
theorem epi_of_epi_left {f g : Over X} (k : f ⟶ g) [hk : Epi k.left] : Epi k :=
  (forget X).epi_of_epi_map hk

instance epi_homMk {U V : Over X} {f : U.left ⟶ V.left} [Epi f] (w) : Epi (homMk f w) :=
  (forget X).epi_of_epi_map ‹_›

/--
If `k.left` is a monomorphism, then `k` is a monomorphism. In other words, `Over.forget X` reflects
monomorphisms.
The converse of `CategoryTheory.Over.mono_left_of_mono`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem mono_of_mono_left {f g : Over X} (k : f ⟶ g) [hk : Mono k.left] : Mono k :=
  (forget X).mono_of_mono_map hk

instance mono_homMk {U V : Over X} {f : U.left ⟶ V.left} [Mono f] (w) : Mono (homMk f w) :=
  (forget X).mono_of_mono_map ‹_›

/--
If `k` is a monomorphism, then `k.left` is a monomorphism. In other words, `Over.forget X` preserves
monomorphisms.
The converse of `CategoryTheory.Over.mono_of_mono_left`.
-/
instance mono_left_of_mono {f g : Over X} (k : f ⟶ g) [Mono k] : Mono k.left := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : mk (m ≫ f.hom) ⟶ f := homMk l (by
        dsimp; rw [← Over.w k, ← Category.assoc, congrArg (· ≫ g.hom) a, Category.assoc])
  suffices l' = (homMk m : mk (m ≫ f.hom) ⟶ f) by apply congrArg CommaMorphism.left this
  rw [← cancel_mono k]
  ext
  apply a

section IteratedSlice

variable (f : Over X)

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simps]
def iteratedSliceForward : Over f ⥤ Over f.left where
  obj α := Over.mk α.hom.left
  map κ := Over.homMk κ.left.left (by dsimp; rw [← Over.w κ]; rfl)

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simps]
def iteratedSliceBackward : Over f.left ⥤ Over f where
  obj g := mk (homMk g.hom : mk (g.hom ≫ f.hom) ⟶ f)
  map α := homMk (homMk α.left (w_assoc α f.hom)) (OverMorphism.ext (w α))

/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simps]
def iteratedSliceEquiv : Over f ≌ Over f.left where
  functor := iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso := NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _))

theorem iteratedSliceForward_forget :
    iteratedSliceForward f ⋙ forget f.left = forget f ⋙ forget X :=
  rfl

theorem iteratedSliceBackward_forget_forget :
    iteratedSliceBackward f ⋙ forget f ⋙ forget X = forget f.left :=
  rfl

end IteratedSlice

/-- A functor `F : T ⥤ D` induces a functor `Over X ⥤ Over (F.obj X)` in the obvious way. -/
@[simps]
def post (F : T ⥤ D) : Over X ⥤ Over (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Over.homMk (F.map f.left)
    (by simp only [Functor.id_obj, mk_left, Functor.const_obj_obj, mk_hom, ← F.map_comp, w])

lemma post_comp {E : Type*} [Category E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl

/-- `post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`. -/
@[simps!]
def postComp {E : Type*} [Category E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)

/-- A natural transformation `F ⟶ G` induces a natural transformation on
`Over X` up to `Over.map`. -/
@[simps]
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post F ⋙ map (e.app X) ⟶ post G where
  app Y := Over.homMk (e.app Y.left)

/-- If `F` and `G` are naturally isomorphic, then `Over.post F` and `Over.post G` are also naturally
isomorphic up to `Over.map` -/
@[simps!]
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ⋙ map (e.hom.app X) ≅ post G :=
  NatIso.ofComponents (fun A ↦ Over.isoMk (e.app A.left))

variable (X) (F : T ⥤ D)

instance [F.Faithful] : (Over.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.left h)

instance [F.Faithful] [F.Full] : (Over.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.left
    have w : a ≫ B.hom = A.hom := F.map_injective <| by simpa [ha] using Over.w _
    exact ⟨Over.homMk a, by ext; simpa⟩

instance [F.Full] [F.EssSurj] : (Over.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨A', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.left
    obtain ⟨f, hf⟩ := F.map_surjective (e.hom ≫ B.hom)
    exact ⟨Over.mk f, ⟨Over.isoMk e⟩⟩

instance [F.IsEquivalence] : (Over.post (X := X) F).IsEquivalence where

/-- If `F` is fully faithful, then so is `Over.post F`. -/
def _root_.CategoryTheory.Functor.FullyFaithful.over (h : F.FullyFaithful) :
    (post (X := X) F).FullyFaithful where
  preimage {A B} f := Over.homMk (h.preimage f.left) <| h.map_injective (by simpa using Over.w f)

/-- If `G` is a right adjoint, then so is `post G : Over Y ⥤ Over (G Y)`.

If the left adjoint of `G` is `F`, then the left adjoint of `post G` is given by
`(X ⟶ G Y) ↦ (F X ⟶ F G Y ⟶ Y)`. -/
@[simps]
def postAdjunctionRight {Y : D} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) :
    post F ⋙ map (a.counit.app Y) ⊣ post G where
  unit.app A := homMk <| a.unit.app A.left
  counit.app A := homMk <| a.counit.app A.left

instance isRightAdjoint_post {Y : D} {G : D ⥤ T} [G.IsRightAdjoint] :
    (post (X := Y) G).IsRightAdjoint :=
  let ⟨F, ⟨a⟩⟩ := ‹G.IsRightAdjoint›; ⟨_, ⟨postAdjunctionRight a⟩⟩

/-- An equivalence of categories induces an equivalence on over categories. -/
@[simps]
def postEquiv (F : T ≌ D) : Over X ≌ Over (F.functor.obj X) where
  functor := Over.post F.functor
  inverse := Over.post (X := F.functor.obj X) F.inverse ⋙ Over.map (F.unitIso.inv.app X)
  unitIso := NatIso.ofComponents (fun A ↦ Over.isoMk (F.unitIso.app A.left))
  counitIso := NatIso.ofComponents (fun A ↦ Over.isoMk (F.counitIso.app A.left))

open Limits

variable {X} in
/-- If `X : T` is terminal, then the over category of `X` is equivalent to `T`. -/
@[simps]
def equivalenceOfIsTerminal (hX : IsTerminal X) : Over X ≌ T where
  functor := forget X
  inverse := { obj Y := mk (hX.from Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y ↦ isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ ↦ .refl _

/-- The induced functor to `Over X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`.
For the converse direction see `CategoryTheory.WithTerminal.commaFromOver`. -/
@[simps]
protected def lift {J : Type*} [Category J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X) :
    J ⥤ Over X where
  obj j := mk (s.app j)
  map f := homMk (D.map f)

/-- The induced cone on `Over X` on the lifted functor. -/
@[simps]
def liftCone {J : Type*} [Category J] (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
    (c : Cone D) (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ s.app j = p) :
    Cone (Over.lift D s) where
  pt := mk p
  π.app j := homMk (c.π.app j)

/-- The lifted cone on `Over X` is a limit cone if the original cone was limiting
and `J` is nonempty. -/
def isLimitLiftCone {J : Type*} [Category J] [Nonempty J]
    (D : J ⥤ T) {X : T} (s : D ⟶ (Functor.const J).obj X)
    (c : Cone D) (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ s.app j = p)
    (hc : IsLimit c) :
    IsLimit (Over.liftCone D s c p hp) where
  lift s := homMk (hc.lift ((forget _).mapCone s))
    (by simpa [← hp (Classical.arbitrary J)] using Over.w (s.π.app _))
  fac _ _ := by ext; simp [hc.fac]
  uniq _ _ hm := by
    ext
    exact hc.hom_ext fun j ↦ by simpa [hc.fac] using congr($(hm j).left)

end Over

namespace CostructuredArrow

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

instance (X : T) : Category (Under X) := commaCategory

-- Satisfying the inhabited linter
instance Under.inhabited [Inhabited T] : Inhabited (Under (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Under

variable {X : T}

@[ext]
theorem UnderMorphism.ext {X : T} {U V : Under X} {f g : U ⟶ V} (h : f.right = g.right) :
    f = g := by
  let ⟨_,b,_⟩ := f; let ⟨_,e,_⟩ := g
  congr; simp only [eq_iff_true_of_subsingleton]

@[simp]
theorem under_left (U : Under X) : U.left = ⟨⟨⟩⟩ := by simp only

@[simp]
theorem id_right (U : Under X) : CommaMorphism.right (𝟙 U) = 𝟙 U.right :=
  rfl

@[simp]
theorem comp_right (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).right = f.right ≫ g.right :=
  rfl

@[reassoc (attr := simp)]
theorem w {A B : Under X} (f : A ⟶ B) : A.hom ≫ f.right = B.hom := by have := f.w; cat_disch

/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/
@[simps! right hom]
def mk {X Y : T} (f : X ⟶ Y) : Under X :=
  StructuredArrow.mk f

/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
    commutative triangle. -/
@[simps! right]
def homMk {U V : Under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom := by cat_disch) : U ⟶ V :=
  StructuredArrow.homMk f w

@[simp]
lemma homMk_eta {U V : Under X} (f : U ⟶ V) (h) :
    homMk f.right h = f :=
  rfl

/-- This is useful when `homMk (· ≫ ·)` appears under `Functor.map` or a natural equivalence. -/
lemma homMk_comp {U V W : Under X} (f : U.right ⟶ V.right) (g : V.right ⟶ W.right) (w_f w_g) :
    homMk (f ≫ g) (by simp only [reassoc_of% w_f, w_g]) = homMk f w_f ≫ homMk g w_g := by
  ext
  simp

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
def isoMk {f g : Under X} (hr : f.right ≅ g.right)
    (hw : f.hom ≫ hr.hom = g.hom := by cat_disch) : f ≅ g :=
  StructuredArrow.isoMk hr hw

@[simp]
theorem isoMk_hom_right {f g : Under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
    (isoMk hr hw).hom.right = hr.hom :=
  rfl

@[simp]
theorem isoMk_inv_right {f g : Under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
    (isoMk hr hw).inv.right = hr.inv :=
  rfl

@[reassoc (attr := simp)]
lemma hom_right_inv_right {f g : Under X} (e : f ≅ g) :
    e.hom.right ≫ e.inv.right = 𝟙 f.right := by
  simp [← Under.comp_right]

@[reassoc (attr := simp)]
lemma inv_right_hom_right {f g : Under X} (e : f ≅ g) :
    e.inv.right ≫ e.hom.right = 𝟙 g.right := by
  simp [← Under.comp_right]

lemma forall_iff (P : Under X → Prop) :
    (∀ Y, P Y) ↔ (∀ (Y) (f : X ⟶ Y), P (.mk f)) := by
  aesop

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain. -/
def forget : Under X ⥤ T :=
  Comma.snd _ _

end

@[simp]
theorem forget_obj {U : Under X} : (forget X).obj U = U.right :=
  rfl

@[simp]
theorem forget_map {U V : Under X} {f : U ⟶ V} : (forget X).map f = f.right :=
  rfl

/-- The natural cone over the forgetful functor `Under X ⥤ T` with cone point `X`. -/
@[simps]
def forgetCone (X : T) : Limits.Cone (forget X) :=
  { pt := X
    π := { app := Comma.hom } }

/-- A morphism `X ⟶ Y` induces a functor `Under Y ⥤ Under X` in the obvious way. -/
def map {Y : T} (f : X ⟶ Y) : Under Y ⥤ Under X :=
  Comma.mapLeft _ <| Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Under Y} {g : U ⟶ V}

@[simp]
theorem map_obj_right : ((map f).obj U).right = U.right :=
  rfl

@[simp]
theorem map_obj_hom : ((map f).obj U).hom = f ≫ U.hom :=
  rfl

@[simp]
theorem map_map_right : ((map f).map g).right = g.right :=
  rfl

/-- If `f` is an isomorphism, `map f` is an equivalence of categories. -/
def mapIso (f : X ≅ Y) : Under Y ≌ Under X :=
  Comma.mapLeftIso _ <| Discrete.natIso fun _ ↦ f.symm

@[simp] lemma mapIso_functor (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl
@[simp] lemma mapIso_inverse (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl

instance [IsIso f] : (Under.map f).IsEquivalence := (Under.mapIso <| asIso f).isEquivalence_functor

end

section coherences
/-!
This section proves various equalities between functors that
demonstrate, for instance, that under categories assemble into a
functor `mapFunctor : Tᵒᵖ ⥤ Cat`.
-/

/-- Mapping by the identity morphism is just the identity functor. -/
theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ := by
  fapply Functor.ext
  · intro x
    dsimp [Under, Under.map, Comma.mapLeft]
    simp only [Category.id_comp]
    exact rfl
  · intro x y u
    dsimp [Under, Under.map, Comma.mapLeft]
    simp

/-- Mapping by the identity morphism is just the identity functor. -/
@[simps!]
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ := eqToIso (mapId_eq Y)

/-- Mapping by `f` and then forgetting is the same as forgetting. -/
theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget X) = (forget Y) := rfl

/-- The natural isomorphism arising from `mapForget_eq`. -/
def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget X) ≅ (forget Y) := eqToIso (mapForget_eq f)

@[simp]
theorem eqToHom_right {X : T} {U V : Under X} (e : U = V) :
    (eqToHom e).right = eqToHom (e ▸ rfl : U.right = V.right) := by
  subst e; rfl

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map g) ⋙ (map f) := by
  fapply Functor.ext
  · simp [Under.map, Comma.mapLeft]
  · intro U V k
    ext
    simp

/-- The natural isomorphism arising from `mapComp_eq`. -/
@[simps!]
def mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  eqToIso (mapComp_eq f g)

/-- If `f = g`, then `map f` is naturally isomorphic to `map g`. -/
@[simps!]
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun A ↦ eqToIso (by rw [h]))

variable (T) in
/-- The functor defined by the under categories -/
@[simps] def mapFunctor : Tᵒᵖ ⥤ Cat where
  obj X := Cat.of (Under X.unop)
  map f := map f.unop
  map_id X := mapId_eq X.unop
  map_comp f g := mapComp_eq (g.unop) (f.unop)

end coherences

instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects {Y Z} f t := by
    let g : Z ⟶ Y := Under.homMk (inv ((Under.forget X).map f))
      ((IsIso.comp_inv_eq _).2 (Under.w f).symm)
    dsimp [forget] at t
    refine ⟨⟨g, ⟨?_,?_⟩⟩⟩
    repeat (ext; simp [g])

/-- The identity under `X` is initial. -/
noncomputable def mkIdInitial : Limits.IsInitial (mk (𝟙 X)) :=
  StructuredArrow.mkIdInitial

instance forget_faithful : (forget X).Faithful where

-- TODO: Show the converse holds if `T` has binary coproducts.
/-- If `k.right` is a monomorphism, then `k` is a monomorphism. In other words, `Under.forget X`
reflects epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`CategoryTheory.Under.mono_right_of_mono`.
-/
theorem mono_of_mono_right {f g : Under X} (k : f ⟶ g) [hk : Mono k.right] : Mono k :=
  (forget X).mono_of_mono_map hk

instance mono_homMk {U V : Under X} {f : U.right ⟶ V.right} [Mono f] (w) : Mono (homMk f w) :=
  (forget X).mono_of_mono_map ‹_›

/--
If `k.right` is an epimorphism, then `k` is an epimorphism. In other words, `Under.forget X`
reflects epimorphisms.
The converse of `CategoryTheory.Under.epi_right_of_epi`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem epi_of_epi_right {f g : Under X} (k : f ⟶ g) [hk : Epi k.right] : Epi k :=
  (forget X).epi_of_epi_map hk

instance epi_homMk {U V : Under X} {f : U.right ⟶ V.right} [Epi f] (w) : Epi (homMk f w) :=
  (forget X).epi_of_epi_map ‹_›

/--
If `k` is an epimorphism, then `k.right` is an epimorphism. In other words, `Under.forget X`
preserves epimorphisms.
The converse of `CategoryTheory.under.epi_of_epi_right`.
-/
instance epi_right_of_epi {f g : Under X} (k : f ⟶ g) [Epi k] : Epi k.right := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : g ⟶ mk (g.hom ≫ m) := homMk l (by
    dsimp; rw [← Under.w k, Category.assoc, a, Category.assoc])
  suffices l' = (homMk m) by apply congrArg CommaMorphism.right this
  rw [← cancel_epi k]; ext; apply a

/-- A functor `F : T ⥤ D` induces a functor `Under X ⥤ Under (F.obj X)` in the obvious way. -/
@[simps]
def post {X : T} (F : T ⥤ D) : Under X ⥤ Under (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Under.homMk (F.map f.right)
    (by simp only [Functor.id_obj, Functor.const_obj_obj, mk_right, mk_hom, ← F.map_comp, w])

lemma post_comp {E : Type*} [Category E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl

/-- `post (F ⋙ G)` is isomorphic (actually equal) to `post F ⋙ post G`. -/
@[simps!]
def postComp {E : Type*} [Category E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)

/-- A natural transformation `F ⟶ G` induces a natural transformation on
`Under X` up to `Under.map`. -/
@[simps]
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post (X := X) F ⟶ post G ⋙ map (e.app X) where
  app Y := Under.homMk (e.app Y.right)

/-- If `F` and `G` are naturally isomorphic, then `Under.post F` and `Under.post G` are also
naturally isomorphic up to `Under.map` -/
@[simps!]
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ≅ post G ⋙ map (e.hom.app X) :=
  NatIso.ofComponents (fun A ↦ Under.isoMk (e.app A.right))

variable (X) (F : T ⥤ D)

instance [F.Faithful] : (Under.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.right h)

instance [F.Faithful] [F.Full] : (Under.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.right
    dsimp at a
    have w : A.hom ≫ a = B.hom := F.map_injective <| by simpa [ha] using Under.w f
    exact ⟨Under.homMk a, by ext; simpa⟩

instance [F.Full] [F.EssSurj] : (Under.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨B', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.right
    obtain ⟨f, hf⟩ := F.map_surjective (B.hom ≫ e.inv)
    exact ⟨Under.mk f, ⟨Under.isoMk e⟩⟩

instance [F.IsEquivalence] : (Under.post (X := X) F).IsEquivalence where

/-- If `F` is fully faithful, then so is `Under.post F`. -/
def _root_.CategoryTheory.Functor.FullyFaithful.under (h : F.FullyFaithful) :
    (post (X := X) F).FullyFaithful where
  preimage {A B} f := Under.homMk (h.preimage f.right) <| h.map_injective (by simpa using Under.w f)

/-- If `F` is a left adjoint, then so is `post F : Under X ⥤ Under (F X)`.

If the right adjoint of `F` is `G`, then the right adjoint of `post F` is given by
`(F X ⟶ Y) ↦ (X ⟶ G F X ⟶ G Y)`. -/
@[simps]
def postAdjunctionLeft {X : T} {F : T ⥤ D} {G : D ⥤ T} (a : F ⊣ G) :
    post F ⊣ post G ⋙ map (a.unit.app X) where
  unit.app A := homMk <| a.unit.app A.right
  counit.app A := homMk <| a.counit.app A.right

instance isLeftAdjoint_post [F.IsLeftAdjoint] : (post (X := X) F).IsLeftAdjoint :=
  let ⟨G, ⟨a⟩⟩ := ‹F.IsLeftAdjoint›; ⟨_, ⟨postAdjunctionLeft a⟩⟩

/-- An equivalence of categories induces an equivalence on under categories. -/
@[simps]
def postEquiv (F : T ≌ D) : Under X ≌ Under (F.functor.obj X) where
  functor := post F.functor
  inverse := post (X := F.functor.obj X) F.inverse ⋙ Under.map (F.unitIso.hom.app X)
  unitIso := NatIso.ofComponents (fun A ↦ Under.isoMk (F.unitIso.app A.right))
  counitIso := NatIso.ofComponents (fun A ↦ Under.isoMk (F.counitIso.app A.right))

open Limits

variable {X} in
/-- If `X : T` is initial, then the under category of `X` is equivalent to `T`. -/
@[simps]
def equivalenceOfIsInitial (hX : IsInitial X) : Under X ≌ T where
  functor := forget X
  inverse := { obj Y := mk (hX.to Y), map f := homMk f }
  unitIso := NatIso.ofComponents fun Y ↦ isoMk (.refl _) (hX.hom_ext _ _)
  counitIso := NatIso.ofComponents fun _ ↦ .refl _

/-- The induced functor to `Under X` from a functor `J ⥤ C` and natural maps `sᵢ : X ⟶ Dᵢ`. -/
@[simps]
protected def lift {J : Type*} [Category J] (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D) :
    J ⥤ Under X where
  obj j := .mk (s.app j)
  map f := Under.homMk (D.map f) (by simpa using (s.naturality f).symm)

/-- The induced cocone on `Under X` from on the lifted functor. -/
@[simps]
def liftCocone {J : Type*} [Category J] (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D)
    (c : Cocone D) (p : X ⟶ c.pt) (hp : ∀ j, s.app j ≫ c.ι.app j = p) :
    Cocone (Under.lift D s) where
  pt := mk p
  ι.app j := homMk (c.ι.app j)

/-- The lifted cocone on `Under X` is a colimit cocone if the original cocone was colimiting
and `J` is nonempty. -/
def isColimitLiftCocone {J : Type*} [Category J] [Nonempty J]
    (D : J ⥤ T) {X : T} (s : (Functor.const J).obj X ⟶ D)
    (c : Cocone D) (p : X ⟶ c.pt) (hp : ∀ j, s.app j ≫ c.ι.app j = p)
    (hc : IsColimit c) :
    IsColimit (liftCocone D s c p hp) where
  desc s := Under.homMk (hc.desc ((Under.forget _).mapCocone s))
    (by simpa [← hp (Classical.arbitrary _)] using Under.w (s.ι.app _))
  fac _ _ := by ext; simp [hc.fac]
  uniq _ _ hm := by
    ext
    exact hc.hom_ext fun j ↦ by simpa [hc.fac] using congr($(hm j).right)

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
variable {X : T} {F : T ⥤ D}

lemma essImage.of_overPost {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y → F.essImage Y.left :=
  fun ⟨Z, ⟨e⟩⟩ ↦ ⟨Z.left, ⟨(Over.forget _).mapIso e⟩⟩

lemma essImage.of_underPost {Y : Under (F.obj X)} :
    (Under.post F (X := X)).essImage Y → F.essImage Y.right :=
  fun ⟨Z, ⟨e⟩⟩ ↦ ⟨Z.right, ⟨(Under.forget _).mapIso e⟩⟩

/-- The essential image of `Over.post F` where `F` is full is the same as the essential image of
`F`. -/
@[simp] lemma essImage_overPost [F.Full] {Y : Over (F.obj X)} :
    (Over.post F (X := X)).essImage Y ↔ F.essImage Y.left where
  mp := .of_overPost
  mpr := fun ⟨Z, ⟨e⟩⟩ ↦ let ⟨f, hf⟩ := F.map_surjective (e.hom ≫ Y.hom); ⟨.mk f, ⟨Over.isoMk e⟩⟩

/-- The essential image of `Under.post F` where `F` is full is the same as the essential image of
`F`. -/
@[simp] lemma essImage_underPost [F.Full] {Y : Under (F.obj X)} :
    (Under.post F (X := X)).essImage Y ↔ F.essImage Y.right where
  mp := .of_underPost
  mpr := fun ⟨Z, ⟨e⟩⟩ ↦ let ⟨f, hf⟩ := F.map_surjective (Y.hom ≫ e.inv); ⟨.mk f, ⟨Under.isoMk e⟩⟩

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
    commute. -/
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

namespace StructuredArrow

/-- A functor from the structured arrow category on the projection functor for any structured
arrow category. -/
@[simps!]
def ofStructuredArrowProjEquivalence.functor (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ⥤ StructuredArrow Y (Under.forget X ⋙ F) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _ ⋙ StructuredArrow.proj Y _) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

/-- The inverse functor of `ofStructuredArrowProjEquivalence.functor`. -/
@[simps!]
def ofStructuredArrowProjEquivalence.inverse (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow Y (Under.forget X ⋙ F) ⥤ StructuredArrow X (StructuredArrow.proj Y F) :=
  Functor.toStructuredArrow
    (Functor.toStructuredArrow (StructuredArrow.proj Y _ ⋙ Under.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.right.hom) (by simp)

/-- Characterization of the structured arrow category on the projection functor of any
structured arrow category. -/
def ofStructuredArrowProjEquivalence (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ≌ StructuredArrow Y (Under.forget X ⋙ F) where
  functor := ofStructuredArrowProjEquivalence.functor F Y X
  inverse := ofStructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- The canonical functor from the structured arrow category on the diagonal functor
`T ⥤ T × T` to the structured arrow category on `Under.forget`. -/
@[simps!]
def ofDiagEquivalence.functor (X : T × T) :
    StructuredArrow X (Functor.diag _) ⥤ StructuredArrow X.2 (Under.forget X.1) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _) _
      (fun f => by exact f.hom.1) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.hom.2) (fun m => by have := m.w; cat_disch)

/-- The inverse functor of `ofDiagEquivalence.functor`. -/
@[simps!]
def ofDiagEquivalence.inverse (X : T × T) :
    StructuredArrow X.2 (Under.forget X.1) ⥤ StructuredArrow X (Functor.diag _) :=
  Functor.toStructuredArrow (StructuredArrow.proj _ _ ⋙ Under.forget _) _ _
    (fun f => (f.right.hom, f.hom)) (fun m => by have := m.w; cat_disch)

/-- Characterization of the structured arrow category on the diagonal functor `T ⥤ T × T`. -/
def ofDiagEquivalence (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.2 (Under.forget X.1) where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- A version of `StructuredArrow.ofDiagEquivalence` with the roles of the first and second
projection swapped. -/
-- noncomputability is only for performance
noncomputable def ofDiagEquivalence' (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.1 (Under.forget X.2) :=
  (ofDiagEquivalence X).trans <|
    (ofStructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans <|
    StructuredArrow.mapNatIso (Under.forget X.2).rightUnitor

section CommaFst

variable {C : Type u₃} [Category.{v₃} C] (F : C ⥤ T) (G : D ⥤ T)

/-- The functor used to define the equivalence `ofCommaSndEquivalence`. -/
@[simps]
def ofCommaSndEquivalenceFunctor (c : C) :
    StructuredArrow c (Comma.fst F G) ⥤ Comma (Under.forget c ⋙ F) G where
  obj X := ⟨Under.mk X.hom, X.right.right, X.right.hom⟩
  map f := ⟨Under.homMk f.right.left (by simpa using f.w.symm), f.right.right, by simp⟩

/-- The inverse functor used to define the equivalence `ofCommaSndEquivalence`. -/
@[simps!]
def ofCommaSndEquivalenceInverse (c : C) :
    Comma (Under.forget c ⋙ F) G ⥤ StructuredArrow c (Comma.fst F G) :=
  Functor.toStructuredArrow (Comma.preLeft (Under.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

/-- There is a canonical equivalence between the structured arrow category with domain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Under.forget c ⋙ F : Under c ⥤ T` and `G`. -/
@[simps]
def ofCommaSndEquivalence (c : C) :
    StructuredArrow c (Comma.fst F G) ≌ Comma (Under.forget c ⋙ F) G where
  functor := ofCommaSndEquivalenceFunctor F G c
  inverse := ofCommaSndEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end CommaFst

end StructuredArrow

namespace CostructuredArrow

/-- A functor from the costructured arrow category on the projection functor for any costructured
arrow category. -/
@[simps!]
def ofCostructuredArrowProjEquivalence.functor (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (CostructuredArrow.proj F Y) X ⥤ CostructuredArrow (Over.forget X ⋙ F) Y :=
  Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X ⋙ CostructuredArrow.proj F Y) _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

/-- The inverse functor of `ofCostructuredArrowProjEquivalence.functor`. -/
@[simps!]
def ofCostructuredArrowProjEquivalence.inverse (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (Over.forget X ⋙ F) Y ⥤ CostructuredArrow (CostructuredArrow.proj F Y) X :=
  Functor.toCostructuredArrow
    (Functor.toCostructuredArrow (CostructuredArrow.proj _ Y ⋙ Over.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; cat_disch)) _ _
    (fun f => f.left.hom) (by simp)

/-- Characterization of the costructured arrow category on the projection functor of any
costructured arrow category. -/
def ofCostructuredArrowProjEquivalence (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (CostructuredArrow.proj F Y) X
      ≌ CostructuredArrow (Over.forget X ⋙ F) Y where
  functor := ofCostructuredArrowProjEquivalence.functor F Y X
  inverse := ofCostructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- The canonical functor from the costructured arrow category on the diagonal functor
`T ⥤ T × T` to the costructured arrow category on `Under.forget`. -/
@[simps!]
def ofDiagEquivalence.functor (X : T × T) :
    CostructuredArrow (Functor.diag _) X ⥤ CostructuredArrow (Over.forget X.1) X.2 :=
  Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X) _
      (fun g => by exact g.hom.1) (fun m => by have := congrArg (·.1) m.w; cat_disch))
    _ _
    (fun f => f.hom.2) (fun m => by have := congrArg (·.2) m.w; cat_disch)

/-- The inverse functor of `ofDiagEquivalence.functor`. -/
@[simps!]
def ofDiagEquivalence.inverse (X : T × T) :
    CostructuredArrow (Over.forget X.1) X.2 ⥤ CostructuredArrow (Functor.diag _) X :=
  Functor.toCostructuredArrow (CostructuredArrow.proj _ _ ⋙ Over.forget _) _ X
    (fun f => (f.left.hom, f.hom)) (fun m => by have := m.w; cat_disch)

/-- Characterization of the costructured arrow category on the diagonal functor `T ⥤ T × T`. -/
def ofDiagEquivalence (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.1) X.2 where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

/-- A version of `CostructuredArrow.ofDiagEquivalence` with the roles of the first and second
projection swapped. -/
-- noncomputability is only for performance
noncomputable def ofDiagEquivalence' (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.2) X.1 :=
  (ofDiagEquivalence X).trans <|
    (ofCostructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans <|
    CostructuredArrow.mapNatIso (Over.forget X.2).rightUnitor

section CommaFst

variable {C : Type u₃} [Category.{v₃} C] (F : C ⥤ T) (G : D ⥤ T)

/-- The functor used to define the equivalence `ofCommaFstEquivalence`. -/
@[simps]
def ofCommaFstEquivalenceFunctor (c : C) :
    CostructuredArrow (Comma.fst F G) c ⥤ Comma (Over.forget c ⋙ F) G where
  obj X := ⟨Over.mk X.hom, X.left.right, X.left.hom⟩
  map f := ⟨Over.homMk f.left.left (by simpa using f.w), f.left.right, by simp⟩

/-- The inverse functor used to define the equivalence `ofCommaFstEquivalence`. -/
@[simps!]
def ofCommaFstEquivalenceInverse (c : C) :
    Comma (Over.forget c ⋙ F) G ⥤ CostructuredArrow (Comma.fst F G) c :=
  Functor.toCostructuredArrow (Comma.preLeft (Over.forget c) F G) _ _
    (fun Y => Y.left.hom) (fun _ => by simp)

/-- There is a canonical equivalence between the costructured arrow category with codomain `c` on
the functor `Comma.fst F G : Comma F G ⥤ F` and the comma category over
`Over.forget c ⋙ F : Over c ⥤ T` and `G`. -/
@[simps]
def ofCommaFstEquivalence (c : C) :
    CostructuredArrow (Comma.fst F G) c ≌ Comma (Over.forget c ⋙ F) G where
  functor := ofCommaFstEquivalenceFunctor F G c
  inverse := ofCommaFstEquivalenceInverse F G c
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end CommaFst

end CostructuredArrow

section Opposite

open Opposite

variable (X : T)

/-- The canonical equivalence between over and under categories by reversing structure arrows. -/
@[simps]
def Over.opEquivOpUnder : Over (op X) ≌ (Under X)ᵒᵖ where
  functor.obj Y := ⟨Under.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Under.homMk (f.left.unop) (by dsimp; rw [← unop_comp, Over.w])⟩
  inverse.obj Y := Over.mk (Y.unop.hom.op)
  inverse.map {Z Y} f := Over.homMk f.unop.right.op <| by dsimp; rw [← Under.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The canonical equivalence between under and over categories by reversing structure arrows. -/
@[simps]
def Under.opEquivOpOver : Under (op X) ≌ (Over X)ᵒᵖ where
  functor.obj Y := ⟨Over.mk Y.hom.unop⟩
  functor.map {Z Y} f := ⟨Over.homMk (f.right.unop) (by dsimp; rw [← unop_comp, Under.w])⟩
  inverse.obj Y := Under.mk (Y.unop.hom.op)
  inverse.map {Z Y} f := Under.homMk f.unop.left.op <| by dsimp; rw [← Over.w f.unop, op_comp]
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Opposite

end CategoryTheory
