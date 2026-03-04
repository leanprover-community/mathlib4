/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplexCategory.Truncated
public import Mathlib.CategoryTheory.Category.ReflQuiv
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Category.Cat.Terminal

/-!

# The homotopy category of a simplicial set

The homotopy category of a simplicial set is defined as a quotient of the free category on its
underlying reflexive quiver (equivalently its one truncation). The quotient imposes an additional
hom relation on this free category, asserting that `f ≫ g = h` whenever `f`, `g`, and `h` are
respectively the 2nd, 0th, and 1st faces of a 2-simplex.

In fact, the associated functor

`SSet.hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ SSet.hoFunctor₂`

is defined by first restricting from simplicial sets to 2-truncated simplicial sets (throwing away
the data that is not used for the construction of the homotopy category) and then composing with an
analogously defined `SSet.hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u,u}` implemented relative to
the syntax of the 2-truncated simplex category.

In the file `Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean` we show the functor
`SSet.hoFunctor` to be left adjoint to the nerve by providing an analogous decomposition of the
nerve functor, made by possible by the fact that nerves of categories are 2-coskeletal, and then
composing a pair of adjunctions, which factor through the category of 2-truncated simplicial sets.
-/

@[expose] public section

namespace SSet
open CategoryTheory Category Limits Functor Opposite Simplicial Nerve
open SimplexCategory.Truncated SimplicialObject.Truncated

universe v u

/-- A 2-truncated simplicial set `S` has an underlying refl quiver with `S _⦋0⦌₂` as its underlying
type. -/
def OneTruncation₂ (S : SSet.Truncated 2) := S _⦋0⦌₂

@[deprecated (since := "2025-11-01")] alias OneTruncation₂.Hom := Truncated.Edge

namespace OneTruncation₂

/-- A 2-truncated simplicial set `S` has an underlying refl quiver `SSet.OneTruncation₂ S`. -/
@[simps -isSimp]
instance reflQuiver (S : SSet.Truncated 2) : ReflQuiver (OneTruncation₂ S) where
  Hom := Truncated.Edge
  id := Truncated.Edge.id

@[ext]
lemma hom_ext
    {S : SSet.Truncated 2} {x y : OneTruncation₂ S} {f g : x ⟶ y}
    (h : f.edge = g.edge) : f = g :=
  Truncated.Edge.ext h

@[deprecated "Use reflQuiver_id" (since := "2025-11-01")]
lemma id_edge {S : SSet.Truncated 2} (x : OneTruncation₂ S) :
    Truncated.Edge.edge (𝟙rq x) = S.map (σ₂ 0).op x := by
  rfl

/-- The prefunctor on refl quivers `OneTruncation₂` induced by a morphism
of `2`-truncated simplicial sets. -/
@[simps]
def map {S T : SSet.Truncated 2} (f : S ⟶ T) :
    OneTruncation₂ S ⥤rq OneTruncation₂ T where
  obj x := f.app _ x
  map e := e.map f
  map_id x := by ext; simp [← FunctorToTypes.naturality, reflQuiver_id]

end OneTruncation₂

/-- The functor that carries a 2-truncated simplicial set to its underlying refl quiver. -/
@[simps]
def oneTruncation₂ : SSet.Truncated.{u} 2 ⥤ ReflQuiv.{u, u} where
  obj S := ReflQuiv.of (OneTruncation₂ S)
  map f := OneTruncation₂.map f

namespace OneTruncation₂

@[simp]
lemma homOfEq_edge
    {X : SSet.Truncated.{u} 2} {x₁ y₁ x₂ y₂ : OneTruncation₂ X}
    (f : x₁ ⟶ y₁) (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (Quiver.homOfEq f hx hy).edge = f.edge := by
  subst hx hy
  rfl

section
variable {C : Type u} [Category.{v} C]

/-- An equivalence between the type of objects underlying a category and the type of 0-simplices in
the 2-truncated nerve. -/
@[simps! -isSimp]
def nerveEquiv : OneTruncation₂ ((SSet.truncation 2).obj (nerve C)) ≃ C :=
  CategoryTheory.nerveEquiv

/-- A hom equivalence over the function `OneTruncation₂.nerveEquiv`. -/
def nerveHomEquiv {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))} :
    (X ⟶ Y) ≃ (nerveEquiv X ⟶ nerveEquiv Y) :=
  nerve.homEquiv

lemma nerveHomEquiv_apply {X Y : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))}
    (f : X ⟶ Y) :
    nerveHomEquiv f = eqToHom (congr_arg ComposableArrows.left f.src_eq.symm) ≫
      f.edge.hom ≫ eqToHom (congr_arg ComposableArrows.left f.tgt_eq) :=
  rfl

@[simp]
lemma nerveHomEquiv_id (X : OneTruncation₂ ((SSet.truncation 2).obj (nerve C))) :
    nerveHomEquiv (𝟙rq X) = 𝟙 _ :=
  nerve.homEquiv_id _

/-- The refl quiver underlying a nerve is isomorphic to the refl quiver underlying the category. -/
def ofNerve₂ (C : Type u) [Category.{u} C] :
    ReflQuiv.of (OneTruncation₂ ((truncation 2).obj (nerve C))) ≅ ReflQuiv.of C :=
  ReflQuiv.isoOfEquiv.{u, u} OneTruncation₂.nerveEquiv
    (fun _ _ ↦ OneTruncation₂.nerveHomEquiv) nerveHomEquiv_id

lemma nerve_hom_ext {X : (SSet.Truncated 2)} {C : Type u} [Category.{u} C]
    {F G : X ⟶ ((truncation 2).obj (nerve C))}
    (h : OneTruncation₂.map F = OneTruncation₂.map G) : F = G :=
  SSet.Truncated.IsStrictSegal.hom_ext (fun f ↦ by
    obtain ⟨x₀, x₁, f, rfl⟩ := Truncated.Edge.exists_of_simplex f
    simpa using congr_arg Truncated.Edge.edge (ReflPrefunctor.congr_hom h f))

@[deprecated (since := "2025-11-06")] alias _root_.CategoryTheory.toNerve₂.ext := nerve_hom_ext

end
end OneTruncation₂

set_option backward.isDefEq.respectTransparency false in
/-- The refl quiver underlying a nerve is naturally isomorphic to the refl quiver underlying the
category. -/
@[simps! hom_app_obj hom_app_map inv_app_obj_obj inv_app_obj_map inv_app_map]
def OneTruncation₂.ofNerve₂.natIso :
    nerveFunctor₂.{u, u} ⋙ SSet.oneTruncation₂ ≅ ReflQuiv.forget :=
  NatIso.ofComponents (fun C => OneTruncation₂.ofNerve₂ C)
    (fun F ↦ ReflPrefunctor.ext (by cat_disch) (fun x y f ↦ by
      obtain ⟨f, rfl, rfl⟩ := f
      dsimp [ofNerve₂, ReflQuiv.isoOfEquiv, ReflQuiv.isoOfQuivIso,
        Quiv.isoOfEquiv, nerveHomEquiv_apply]
      simp only [comp_id, id_comp]
      rfl))

set_option backward.privateInPublic true in
private lemma map_map_of_eq.{w} {C : Type u} [Category.{v} C] (V : Cᵒᵖ ⥤ Type w) {X Y Z : C}
    {α : X ⟶ Y} {β : Y ⟶ Z} {γ : X ⟶ Z} {φ} :
    α ≫ β = γ → V.map α.op (V.map β.op φ) = V.map γ.op φ := by
  rintro rfl
  simp

namespace Truncated

/-- The map that picks up the initial vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι0₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 1 ≫ δ₂ (n := 1) 1

/-- The map that picks up the middle vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι1₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 2

/-- The map that picks up the final vertex of a 2-simplex, as a morphism in the 2-truncated
simplex category. -/
def ι2₂ : ⦋0⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 0) 0 ≫ δ₂ (n := 1) 1

/-- The initial vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev0₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι0₂.op φ

/-- The middle vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev1₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι1₂.op φ

/-- The final vertex of a 2-simplex in a 2-truncated simplicial set. -/
def ev2₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : OneTruncation₂ V := V.map ι2₂.op φ

/-- The 0th face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ0₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 0

/-- The 1st face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ1₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 1

/-- The 2nd face of a 2-simplex, as a morphism in the 2-truncated simplex category. -/
def δ2₂ : ⦋1⦌₂ ⟶ ⦋2⦌₂ := δ₂ (n := 1) 2

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
0th face of a 2-simplex. -/
def ev12₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev1₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ0₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext
      (SimplexCategory.δ_comp_δ (i := 0) (j := 1) (by decide)).symm),
    map_map_of_eq V rfl⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
1st face of a 2-simplex. -/
def ev02₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev0₂ φ ⟶ ev2₂ φ :=
  ⟨V.map δ1₂.op φ, map_map_of_eq V rfl, map_map_of_eq V rfl⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The arrow in the ReflQuiver `OneTruncation₂ V` of a 2-truncated simplicial set arising from the
2nd face of a 2-simplex. -/
def ev01₂ {V : SSet.Truncated 2} (φ : V _⦋2⦌₂) : ev0₂ φ ⟶ ev1₂ φ :=
  ⟨V.map δ2₂.op φ,
    map_map_of_eq V (InducedCategory.hom_ext (SimplexCategory.δ_comp_δ (j := 1) le_rfl)),
    map_map_of_eq V rfl⟩

end Truncated

namespace OneTruncation₂

variable (V : SSet.Truncated.{u} 2)

/-- The 2-simplices in a 2-truncated simplicial set `V` generate a hom relation on the free
category on the underlying refl quiver of `V`. -/
inductive HoRel₂ : HomRel (Cat.FreeRefl (OneTruncation₂ V)) where
  | of_compStruct {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Truncated.Edge x₀ x₁}
    {e₁₂ : Truncated.Edge x₁ x₂} {e₀₂ : Truncated.Edge x₀ x₂}
    (h : Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    HoRel₂
      ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map
        (Quiver.Hom.toPath e₀₁ ≫ Quiver.Hom.toPath e₁₂))
      ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map (Quiver.Hom.toPath e₀₂))

@[deprecated "HoRel₂.of_compStruct" (since := "2025-11-06")]
lemma HoRel₂.mk {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Truncated.Edge x₀ x₁}
    {e₁₂ : Truncated.Edge x₁ x₂} {e₀₂ : Truncated.Edge x₀ x₂}
    (h : Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    HoRel₂ V
      ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map
        (Quiver.Hom.toPath e₀₁ ≫ Quiver.Hom.toPath e₁₂))
      ((Cat.FreeRefl.quotientFunctor (OneTruncation₂ V)).map (Quiver.Hom.toPath e₀₂)) :=
  HoRel₂.of_compStruct h

end OneTruncation₂

namespace Truncated

variable (V W : SSet.Truncated.{u} 2)

/-- The type underlying the homotopy category of a 2-truncated simplicial set `V`. -/
def HomotopyCategory : Type u :=
  Quotient (OneTruncation₂.HoRel₂ V)
  deriving Category.{u}

namespace HomotopyCategory

/-- A canonical functor from the free category on the refl quiver underlying a 2-truncated
simplicial set `V` to its homotopy category. -/
def quotientFunctor :
    Cat.FreeRefl (OneTruncation₂ V) ⥤ V.HomotopyCategory :=
  Quotient.functor _

instance : (quotientFunctor V).Full :=
  Quotient.full_functor _

variable {V}

/-- Constructor for objects of the homotopy category of a `2`-truncated simplicial set. -/
def mk (x : V _⦋0⦌₂) : V.HomotopyCategory :=
  (quotientFunctor V).obj (.mk x)

lemma mk_surjective : Function.Surjective (mk (V := V)) := by
  rintro ⟨⟨x⟩⟩
  exact ⟨x, rfl⟩

lemma ext {x y : V.HomotopyCategory} (h : x.as.as = y.as.as) : x = y := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  obtain rfl : x = y := h
  rfl

@[elab_as_elim, cases_eliminator]
protected lemma cases_on {motive : V.HomotopyCategory → Prop}
    (h : ∀ (x : V _⦋0⦌₂), motive (.mk x))
    (x : V.HomotopyCategory) :
    motive x := by
  obtain ⟨x', rfl⟩ := mk_surjective x
  exact h x'

/-- The morphism in the homotopy category of a `2`-truncated simplicial set that
is induced by an edge. -/
def homMk {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁) : mk x₀ ⟶ mk x₁ :=
  (quotientFunctor V).map (Cat.FreeRefl.homMk e)

lemma congr_arrowMk_homMk {x₀ x₁ : V _⦋0⦌₂} (e : Edge x₀ x₁)
    {y₀ y₁ : V _⦋0⦌₂} (e' : Edge y₀ y₁) (h : e.edge = e'.edge) :
    Arrow.mk (homMk e) = Arrow.mk (homMk e') := by
  obtain rfl : x₀ = y₀ := by rw [← e.src_eq, ← e'.src_eq, h]
  obtain rfl : x₁ = y₁ := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  obtain rfl : e = e' := by aesop
  rfl

@[simp]
lemma homMk_id (x : V _⦋0⦌₂) :
    homMk (.id x) = 𝟙 (mk x) := by
  rw [homMk, ← OneTruncation₂.reflQuiver_id, Cat.FreeRefl.homMk_id,
    CategoryTheory.Functor.map_id]
  rfl

@[reassoc]
lemma homMk_comp_homMk {x₀ x₁ x₂ : V _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ := by
  simpa [homMk] using CategoryTheory.Quotient.sound _
    (OneTruncation₂.HoRel₂.of_compStruct h)

variable (V) in
/-- If `V` is a `2`-truncated simplicial sets, this is the family of
morphisms in `V.HomotopyCategory` corresponding to the edges of `V`.
(Any morphism in `V.HomotopyCategory` is in the multiplicative closure
of this family of morphisms, see `multiplicativeClosure_morphismPropertyHomMk`.) -/
def morphismPropertyHomMk : MorphismProperty V.HomotopyCategory :=
  .ofHoms (fun (e : Σ (x y : V _⦋0⦌₂), Edge x y) ↦ homMk e.2.2)

lemma morphismPropertyHomMk_of_edge {x y : V _⦋0⦌₂} (e : Edge x y) :
    morphismPropertyHomMk V (homMk e) := by
  dsimp only [morphismPropertyHomMk]
  rw [MorphismProperty.ofHoms_iff]
  exact ⟨⟨x, y, e⟩, rfl⟩

lemma morphismPropertyHomMk_eq_strictMap :
    morphismPropertyHomMk V =
      (Cat.FreeRefl.morphismPropertyHomMk (OneTruncation₂ V)).strictMap (quotientFunctor V) := by
  ext _ _ f
  constructor
  · rintro ⟨_⟩
    exact MorphismProperty.map_mem_strictMap _ _ _ ⟨_⟩
  · rintro ⟨⟨_, _, e⟩⟩
    exact morphismPropertyHomMk_of_edge e

open MorphismProperty in
lemma multiplicativeClosure_morphismPropertyHomMk :
    (morphismPropertyHomMk V).multiplicativeClosure = ⊤ :=
  le_antisymm (by simp) (fun x y f _ ↦ by
    obtain ⟨f, rfl⟩ := (quotientFunctor _).map_surjective f
    rw [morphismPropertyHomMk_eq_strictMap]
    refine strictMap_multiplicativeClosure_le _ _ _ ?_
    rw [Cat.FreeRefl.multiplicativeClosure_morphismPropertyHomMk]
    exact map_mem_strictMap _ _ _ (by simp))

lemma morphismProperty_eq_top {W : MorphismProperty V.HomotopyCategory}
    [W.IsMultiplicative]
    (hW : ∀ {x y : V _⦋0⦌₂} (e : Edge x y), W (homMk e)) :
    W = ⊤ :=
  le_antisymm (by simp) (by
    rw [← multiplicativeClosure_morphismPropertyHomMk,
      MorphismProperty.multiplicativeClosure_le_iff]
    rintro _ _ _ ⟨_, _, e⟩
    exact hW e)

section

variable {D : Type*} [Category* D]

section

variable (obj : V _⦋0⦌₂ → D) (map : ∀ {x y : V _⦋0⦌₂}, Edge x y → (obj x ⟶ obj y))
  (map_id : ∀ (x : V _⦋0⦌₂), map (.id x) = 𝟙 _)
  (map_comp : ∀ {x₀ x₁ x₂ : V _⦋0⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (_ : Edge.CompStruct e₀₁ e₁₂ e₀₂), map e₀₁ ≫ map e₁₂ = map e₀₂)

/-- Constructor for functors from the homotopy category. -/
def lift : V.HomotopyCategory ⥤ D :=
  CategoryTheory.Quotient.lift _
    (Cat.FreeRefl.lift' obj (fun f ↦ map f) map_id) (by
      rintro _ _ _ _ ⟨h⟩
      simp only [Functor.map_comp]
      convert map_comp h <;> apply Cat.FreeRefl.lift'_map)

@[simp]
lemma lift_obj_mk (x : V _⦋0⦌₂) : (lift obj map map_id map_comp).obj (mk x) = obj x := rfl

@[simp]
lemma lift_map_homMk {x y : V _⦋0⦌₂} (e : Edge x y) :
    (lift obj map map_id map_comp).map (homMk e) = map e :=
  Category.id_comp _

end

variable {F G : V.HomotopyCategory ⥤ D}

section

variable (φ : ∀ (x : V _⦋0⦌₂), F.obj (mk x) ⟶ G.obj (mk x))
  (hφ : ∀ ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y),
    F.map (homMk e) ≫ φ y = φ x ≫ G.map (homMk e) := by cat_disch)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Constructor for natural transformations between functors from `V.HomotopyCategory`. -/
def mkNatTrans : F ⟶ G where
  app _ := φ _
  naturality _ _ f := by
    have : MorphismProperty.naturalityProperty (fun (x : V.HomotopyCategory) ↦ φ _) = ⊤ :=
      morphismProperty_eq_top (fun e ↦ hφ e)
    exact this.symm.le f (by simp)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
lemma mkNatTrans_app_mk (v : V _⦋0⦌₂) :
    (mkNatTrans φ hφ).app (mk v) = φ v := rfl

end

section

variable (iso : ∀ (x : V _⦋0⦌₂), F.obj (mk x) ≅ G.obj (mk x))
  (hiso : ∀ ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y), F.map (homMk e) ≫ (iso y).hom =
    (iso x).hom ≫ G.map (homMk e) := by cat_disch)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Constructor for natural isomorphisms between functors from `V.HomotopyCategory`. -/
def mkNatIso : F ≅ G :=
  NatIso.ofComponents (fun _ ↦ iso _) (fun f ↦ (mkNatTrans _ hiso).naturality f)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
lemma mkNatIso_hom_app_mk (v : V _⦋0⦌₂) :
    (mkNatIso iso hiso).hom.app (mk v) = (iso v).hom := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simp]
lemma mkNatIso_inv_app_mk (v : V _⦋0⦌₂) :
    (mkNatIso iso hiso).inv.app (mk v) = (iso v).inv := rfl

end

lemma functor_ext {F G : V.HomotopyCategory ⥤ D}
    (h₁ : ∀ (x : V _⦋0⦌₂), F.obj (mk x) = G.obj (mk x))
    (h₂ : ∀ ⦃x y : V _⦋0⦌₂⦄ (e : Edge x y),
      F.map (homMk e) = eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToHom (h₁ y).symm) :
    F = G :=
  Functor.ext_of_iso (mkNatIso (fun x ↦ eqToIso (h₁ x))
    (fun _ _ e ↦ by simp [h₂ e])) (fun _ ↦ h₁ _)

end

instance (X : Truncated.{u} 2) [Subsingleton (X _⦋0⦌₂)] :
    Subsingleton X.HomotopyCategory where
  allEq x y := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain rfl := Subsingleton.elim x y
    rfl

instance subsingleton_hom (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)]
    (x y : X.HomotopyCategory) :
    Subsingleton (x ⟶ y) :=
  letI : Unique (OneTruncation₂ X) := inferInstanceAs% (Unique (X _⦋0⦌₂))
  letI (x y : (OneTruncation₂ X)) : Subsingleton (x ⟶ y) :=
    inferInstanceAs% (Subsingleton <| X.Edge _ _)
  CategoryTheory.Quotient.instSubsingletonHom _ _ _

instance (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] : Unique X.HomotopyCategory :=
  letI : Unique (OneTruncation₂ X) := inferInstanceAs% (Unique (X _⦋0⦌₂))
  CategoryTheory.Quotient.instUnique _

/-- If `X : Truncated 2` has a unique `0`-simplex and (at most) one `1`-simplex,
then `X.HomotopyCategory` is a terminal object in `Cat`. -/
def isTerminal (X : Truncated.{u} 2) [Unique (X _⦋0⦌₂)] [Subsingleton (X _⦋1⦌₂)] :
    IsTerminal (Cat.of X.HomotopyCategory) :=
  letI : IsDiscrete (X.HomotopyCategory) := { eq_of_hom := by subsingleton }
  Cat.isTerminalOfUniqueOfIsDiscrete

end HomotopyCategory

section

open HomotopyCategory

variable {V W} (f : V ⟶ W)

/-- A map of 2-truncated simplicial sets induces a functor between homotopy categories. -/
def mapHomotopyCategory :
    V.HomotopyCategory ⥤ W.HomotopyCategory :=
  CategoryTheory.Quotient.lift _
    (((oneTruncation₂ ⋙ Cat.freeRefl).map f).toFunctor ⋙ quotientFunctor W) (by
      rintro _ _ _ _ ⟨h⟩
      exact CategoryTheory.Quotient.sound _ ⟨h.map f⟩)

@[simp]
lemma mapHomotopyCategory_obj (x : V _⦋0⦌₂) :
    (mapHomotopyCategory f).obj (.mk x) = .mk (f.app _ x) := rfl

@[simp]
lemma mapHomotopyCategory_homMk {x y : V _⦋0⦌₂} (e : Edge x y) :
    (mapHomotopyCategory f).map (homMk e) = homMk (e.map f) := rfl

end

/-- The functor that takes a 2-truncated simplicial set to its homotopy category. -/
def hoFunctor₂ : SSet.Truncated.{u} 2 ⥤ Cat.{u, u} where
  obj V := Cat.of V.HomotopyCategory
  map F := (mapHomotopyCategory F).toCatHom
  map_id _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)
  map_comp _ _ := by ext1; exact HomotopyCategory.functor_ext (by simp) (by cat_disch)

theorem hoFunctor₂_naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    ((oneTruncation₂ ⋙ Cat.freeRefl).map f).toFunctor ⋙
      SSet.Truncated.HomotopyCategory.quotientFunctor Y =
      SSet.Truncated.HomotopyCategory.quotientFunctor X ⋙ mapHomotopyCategory f := rfl

/-- By `Quotient.lift_unique'` (not `Quotient.lift`) we have that `quotientFunctor V` is an
epimorphism. -/
theorem HomotopyCategory.lift_unique' (V : SSet.Truncated.{u} 2) {D : Type*} [Category* D]
    (F₁ F₂ : V.HomotopyCategory ⥤ D)
    (h : HomotopyCategory.quotientFunctor V ⋙ F₁ = HomotopyCategory.quotientFunctor V ⋙ F₂) :
    F₁ = F₂ :=
  Quotient.lift_unique' _ _ _ h

end Truncated

/-- The functor that takes a simplicial set to its homotopy category by passing through the
2-truncation. -/
def hoFunctor : SSet.{u} ⥤ Cat.{u, u} := SSet.truncation 2 ⋙ Truncated.hoFunctor₂

/-- For a simplicial set `X`, the underlying type of `hoFunctor.obj X` is equivalent to `X _⦋0⦌`. -/
def hoFunctor.obj.equiv (X : SSet) : hoFunctor.obj X ≃ X _⦋0⦌ :=
  (Quotient.equiv.{u, u} _).trans (Quotient.equiv _)

/-- Since `⦋0⦌ : SimplexCategory` is terminal, `Δ[0]` has a unique point and thus
`OneTruncation₂ ((truncation 2).obj Δ[0])` has a unique inhabitant. -/
instance instUniqueOneTruncation₂DeltaZero : Unique (OneTruncation₂ ((truncation 2).obj Δ[0])) :=
  inferInstanceAs% (Unique (ULift.{_, 0} (⦋0⦌ ⟶ ⦋0⦌)))

/-- Since `⦋0⦌ : SimplexCategory` is terminal, `Δ[0]` has a unique edge and thus the homs of
`OneTruncation₂ ((truncation 2).obj Δ[0])` have unique inhabitants. -/
instance (x y : OneTruncation₂ ((truncation 2).obj Δ[0])) : Unique (x ⟶ y) where
  default := by
    obtain rfl : x = default := Unique.uniq _ _
    obtain rfl : y = default := Unique.uniq _ _
    exact 𝟙rq instUniqueOneTruncation₂DeltaZero.default
  uniq _ := by
    letI : Subsingleton (((truncation 2).obj Δ[0]).obj (.op ⦋1⦌₂)) :=
      inferInstanceAs% (Subsingleton (ULift.{_, 0} (⦋1⦌ ⟶ ⦋0⦌)))
    ext
    exact this.allEq _ _

instance : Unique ((truncation.{u} 2).obj Δ[0]).HomotopyCategory :=
  inferInstanceAs% (Unique <| CategoryTheory.Quotient _)

instance : IsDiscrete ((truncation.{u} 2).obj Δ[0]).HomotopyCategory where
  subsingleton x y :=
    inferInstanceAs% (Subsingleton ((_ : CategoryTheory.Quotient _) ⟶ _))
  eq_of_hom _ := by subsingleton

/-- The category `hoFunctor.obj (Δ[0])` is terminal. -/
def isTerminalHoFunctorDeltaZero : IsTerminal (hoFunctor.{u}.obj (Δ[0])) :=
  Cat.isTerminalOfUniqueOfIsDiscrete

/-- The homotopy category functor preserves generic terminal objects. -/
noncomputable def hoFunctor.terminalIso : hoFunctor.obj (⊤_ SSet) ≅ ⊤_ Cat :=
  hoFunctor.mapIso (terminalIsoIsTerminal stdSimplex.isTerminalObj₀) ≪≫
    (terminalIsoIsTerminal isTerminalHoFunctorDeltaZero).symm

instance hoFunctor.preservesTerminal : PreservesLimit (empty.{0} SSet) hoFunctor :=
  preservesTerminal_of_iso hoFunctor hoFunctor.terminalIso

instance hoFunctor.preservesTerminal' :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) hoFunctor :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

end SSet
