/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated

/-!
# 2-truncated quasicategories and homotopy relations

We define 2-truncated quasicategories `Quasicategory₂` by three horn-filling properties,
and the left and right homotopy relations `HomotopicL` and `HomotopicR` on the edges in a
2-truncated simplicial set.

We prove that for 2-truncated quasicategories, both homotopy relations are equivalence
relations, and that the left and right homotopy relations coincide.

For a 2-truncated quasicategory `X`, we define a category `HomotopyCategory₂ X` whose
morphisms are given by (left) homotopy classes of edges. The construction of this category
is different from `HomotopyCategory X` in `AlgebraicTopology.SimplicialSet.HomotopyCat`:
* `HomotopyCategory₂ X` has morphisms given by homotopy classes of edges
* `HomotopyCategory X` has morphisms given by equivalence classes of paths in the underlying
  reflexive quiver of `X`.

The two constructions agree for 2-truncated quasicategories (TODO: handled by future PR).

## Implementation notes

Throughout this file, we make use of `Edge` and `CompStruct` to conveniently deal with
edges and triangles in a 2-truncated simplicial set.
-/

@[expose] public section

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated
open Edge CompStruct

/--
A 2-truncated quasicategory is a 2-truncated simplicial set with the properties:
* (2, 1)-filling: given two consecutive `Edge`s `e₀₁` and `e₁₂`, there exists a `CompStruct`
  with (0, 1)-edge `e₀₁` and (0, 2)-edge `e₁₂`.
* (3, 1)-filling: given three `CompStruct`s `f₃`, `f₀` and `f₂` which form a (3, 1)-horn,
  there exists a fourth `CompStruct` such that the four faces form the boundary
  ∂Δ[3] of a 3-simplex.
* (3, 2)-filling: given three `CompStruct`s `f₃`, `f₀` and `f₁` which form a (3, 2)-horn,
  there exists a fourth `CompStruct` such that the four faces form the boundary
  ∂Δ[3] of a 3-simplex.
-/
class Quasicategory₂ (X : Truncated 2) where
  fill21 {x₀ x₁ x₂ : X _⦋0⦌₂}
      (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
      Nonempty (Σ e₀₂ : Edge x₀ x₂, CompStruct e₀₁ e₁₂ e₀₂)
  fill31 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₂ : CompStruct e₀₁ e₁₃ e₀₃) :
      Nonempty (CompStruct e₀₂ e₂₃ e₀₃)
  fill32 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₁ : CompStruct e₀₂ e₂₃ e₀₃) :
      Nonempty (CompStruct e₀₁ e₁₃ e₀₃)

variable {X : Truncated 2} {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}

/--
A left homotopy between two edges `f` and `g` is a `CompStruct f (id _) g`.
(See `HomotopicL` for the `Prop`-valued version.)
-/
abbrev Edge.HomotopyL (f g : Edge x₀ x₁) := CompStruct f (id x₁) g

/--
A right homotopy between two edges `f` and `g` is a `CompStruct (id _) f g`.
(See `HomotopicL` for the `Prop`-valued version.)
-/
abbrev Edge.HomotopyR (f g : Edge x₀ x₁) := CompStruct (id x₀) f g

/--
Two edges `f` and `g` are left homotopic if there is a `CompStruct` with
(0, 1)-edge `f`, (1, 2)-edge `Edge.id` and (0, 2)-edge `g`. We use `Nonempty` to
have a `Prop` valued `HomotopicL`.
-/
abbrev HomotopicL (f g : Edge x₀ x₁) :=
  Nonempty (HomotopyL f g)

/--
Two edges `f` and `g` are right homotopic if there is a `CompStruct` with
(0, 1)-edge `Edge.id`, (1, 2)-edge `f`, and (0, 2)-edge `g`. We use `Nonempty` to
have a `Prop` valued `HomotopicR`.
-/
abbrev HomotopicR (f g : Edge x₀ x₁) :=
  Nonempty (HomotopyR f g)

/-- The left homotopy relation on the edges of a `2`-truncated simplicial set is reflexive. -/
abbrev Edge.HomotopyL.refl (f : Edge x₀ x₁) : HomotopyL f f := .compId _

/-- The right homotopy relation on the edges of a `2`-truncated simplicial set is reflexive. -/
abbrev Edge.HomotopyR.refl (f : Edge x₀ x₁) : HomotopyR f f := .idComp _

/-- The associativity of the composition in a `2`-truncated quasicategory. -/
@[no_expose]
noncomputable def Edge.assoc [Quasicategory₂ X]
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂) (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₁ e₁₃ e₀₃) :
    CompStruct e₀₂ e₂₃ e₀₃ :=
  (Quasicategory₂.fill31 h₀₂ h₁₃ h).some

/-- The associativity of the composition in a `2`-truncated quasicategory. -/
@[no_expose]
noncomputable def Edge.assoc' [Quasicategory₂ X]
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂) (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₂ e₂₃ e₀₃) :
    CompStruct e₀₁ e₁₃ e₀₃ :=
  (Quasicategory₂.fill32 h₀₂ h₁₃ h).some

/-- In a `2`-truncated quasicategory, the left homotopy relation on edges
is symmetric. -/
@[no_expose]
noncomputable def Edge.HomotopyL.symm [Quasicategory₂ X]
    {f g : Edge x₀ x₁} (h : HomotopyL f g) : HomotopyL g f :=
  assoc h (idComp _) (compId _)

/-- In a `2`-truncated quasicategory, the right homotopy relation on edges
is symmetric. -/
@[no_expose]
noncomputable def Edge.HomotopyR.symm [Quasicategory₂ X]
    {f g : Edge x₀ x₁} (h : HomotopyR f g) : HomotopyR g f :=
  assoc' (compId _) h (idComp _)

/-- In a `2`-truncated quasicategory, the left homotopy relation on edges
is transitive. -/
@[no_expose]
noncomputable def Edge.HomotopyL.trans [Quasicategory₂ X]
    {f g h : Edge x₀ x₁} (h₁ : HomotopyL f g) (h₂ : HomotopyL g h) :
    HomotopyL f h :=
  assoc' h₁ (.idCompId _) h₂

/-- In a `2`-truncated quasicategory, the right homotopy relation on edges
is transitive. -/
@[no_expose]
noncomputable def Edge.HomotopyR.trans [Quasicategory₂ X]
    {f g h : Edge x₀ x₁} (h₁ : HomotopyR f g) (h₂ : HomotopyR g h) :
    HomotopyR f h :=
  assoc (.idCompId _) h₁ h₂

/-- In a `2`-truncated quasicategory, two left homotopic edges are
also right homotopic. -/
@[no_expose]
noncomputable def Edge.HomotopyL.homotopyR [Quasicategory₂ X]
    {f g : Edge x₀ x₁} (h : HomotopyL f g) :
    HomotopyR f g :=
  assoc' (.idComp f) (.compId f) h

/-- In a `2`-truncated quasicategory, two right homotopic edges are
also left homotopic. -/
@[no_expose]
noncomputable def Edge.HomotopyR.homotopyL [Quasicategory₂ X]
    {f g : Edge x₀ x₁} (h : HomotopyR f g) :
    HomotopyL f g :=
  assoc (.idComp _) (.compId _) h

section homotopy_eqrel

/--
The left homotopy relation is reflexive.
-/
lemma HomotopicL.refl {f : Edge x₀ x₁} : HomotopicL f f := ⟨HomotopyL.refl f⟩

/--
The left homotopy relation is symmetric.
-/
lemma HomotopicL.symm [Quasicategory₂ X] {f g : Edge x₀ x₁} (hfg : HomotopicL f g) :
    HomotopicL g f :=
  ⟨HomotopyL.symm hfg.some⟩

/--
The left homotopy relation is transitive.
-/
lemma HomotopicL.trans [Quasicategory₂ X] {f g h : Edge x₀ x₁} (hfg : HomotopicL f g)
    (hgh : HomotopicL g h) : HomotopicL f h :=
  ⟨hfg.some.trans hgh.some⟩

/--
The right homotopy relation is reflexive.
-/
lemma HomotopicR.refl {f : Edge x₀ x₁} : HomotopicR f f := ⟨idComp f⟩

/--
The right homotopy relation is symmetric.
-/
lemma HomotopicR.symm [Quasicategory₂ X] {x₀ x₁ : X _⦋0⦌₂} {f g : Edge x₀ x₁}
    (hfg : HomotopicR f g) :
    HomotopicR g f :=
  ⟨HomotopyR.symm hfg.some⟩

/--
The right homotopy relation is transitive.
-/
lemma HomotopicR.trans [Quasicategory₂ X] {f g h : Edge x₀ x₁} (hfg : HomotopicR f g)
    (hgh : HomotopicR g h) : HomotopicR f h :=
  ⟨hfg.some.trans hgh.some⟩

/--
In a 2-truncated quasicategory, left homotopy implies right homotopy.
-/
lemma HomotopicL.homotopicR [Quasicategory₂ X] {f g : Edge x₀ x₁}
    (h : HomotopicL f g) : HomotopicR f g :=
  ⟨h.some.homotopyR⟩

/--
In a 2-truncated quasicategory, right homotopy implies left homotopy.
-/
lemma HomotopicR.homotopicL [Quasicategory₂ X] {f g : Edge x₀ x₁}
    (h : HomotopicR f g) : HomotopicL f g :=
  ⟨h.some.homotopyL⟩

/--
In a 2-truncated quasicategory, the right and left homotopy relations coincide.
-/
theorem homotopicL_iff_homotopicR [Quasicategory₂ X] {f g : Edge x₀ x₁} :
    HomotopicL f g ↔ HomotopicR f g :=
  ⟨HomotopicL.homotopicR, HomotopicR.homotopicL⟩

end homotopy_eqrel

section homotopy_category

variable [Quasicategory₂ X]

/--
Assume we have structures `CompStruct f g h` and `CompStruct f' g' h'`.
If `f` and `f'` are left homotopic, and `g` and `g'` are left homotopic,
then `h` and `h'` are left homotopic.
-/
@[no_expose]
noncomputable def Edge.CompStruct.unique
    {f f' : Edge x₀ x₁} {g g' : Edge x₁ x₂} {h h' : Edge x₀ x₂}
    (s : CompStruct f g h) (s' : CompStruct f' g' h')
    (hf : HomotopyL f f') (hg : HomotopyL g g') : HomotopyL h h' :=
  assoc s (compId g) (assoc (compId f) hg.homotopyR (assoc' hf (idComp g') s'))

/--
Given `CompStruct f g h` and `CompStruct f' g' h'` with the same vertices and edges such
that `f` ≃ `f'` and `g` ≃ `g'`, then the long diagonal edges `h` and `h'` are also homotopic.
-/
lemma Edge.CompStruct.comp_unique {f f' : Edge x₀ x₁} {g g' : Edge x₁ x₂} {h h' : Edge x₀ x₂}
    (s : CompStruct f g h) (s' : CompStruct f' g' h')
    (hf : HomotopicL f f') (hg : HomotopicL g g') : HomotopicL h h' :=
  ⟨Edge.CompStruct.unique s s' hf.some hg.some⟩

/--
Given two consecutive edges `f`, `g`  in a 2-truncated quasicategory, nonconstructively choose
an edge that is the diagonal of a 2-simplex with spine given by `f` and `g`. The `CompStruct`
witnessing this property is given by `Edge.compStruct`.
-/
@[no_expose]
noncomputable def Edge.comp (f : Edge x₀ x₁) (g : Edge x₁ x₂) : Edge x₀ x₂ :=
  (Quasicategory₂.fill21 f g).some.1

/--
See `Edge.comp`
-/
@[no_expose]
noncomputable def Edge.compStruct (f : Edge x₀ x₁) (g : Edge x₁ x₂) : CompStruct f g (f.comp g) :=
  (Quasicategory₂.fill21 f g).some.2

variable (X) in
/--
The homotopy category of a 2-truncated quasicategory `X` has as objects the vertices of `X`
-/
structure HomotopyCategory₂ where
  /-- An object of the homotopy category is a vertex of `X`. -/
  pt : X _⦋0⦌₂

/--
Left homotopy is an equivalence relation on the edges of `X`.
Remark: We could have equivalently chosen right homotopy, as shown by `homotopicL_iff_homotopicR`.
-/
instance instSetoidEdge (x y : X _⦋0⦌₂) : Setoid (Edge x y) where
  r := HomotopicL
  iseqv := ⟨fun _ ↦ HomotopicL.refl, HomotopicL.symm, HomotopicL.trans⟩

namespace HomotopyCategory₂

/--
The morphisms between two vertices `x`, `y` in `HomotopyCategory₂ X` are homotopy classes
of edges between `x` and `y`.
-/
def Hom (x y : HomotopyCategory₂ X) := Quotient (instSetoidEdge x.pt y.pt)

/--
Composition of morphisms in `HomotopyCategory₂ X` is given by lifting the edge
chosen by `composeEdges`.
-/
noncomputable
instance : CategoryStruct (HomotopyCategory₂ X) where
  Hom x y := Hom x y
  id x := Quotient.mk' (Edge.id x.pt)
  comp := Quotient.lift₂ (fun f g ↦ ⟦comp f g⟧)
    (fun _ _ _ _ hf hg ↦ Quotient.sound
      (Edge.CompStruct.comp_unique (compStruct _ _) (compStruct _ _) hf hg))

omit [X.Quasicategory₂] in
/--
The function `HomotopyCategory₂.mk` taking a vertex of `A` and sending it to the corresponding
object of `HomotopyCategory₂ A` is surjective.
-/
lemma mk_surjective : Function.Surjective (mk : X _⦋0⦌₂ → _) :=
  fun ⟨x⟩ ↦ ⟨x, rfl⟩

/--
Any edge in the 2-truncated simplicial set `X` defines a morphism in the homotopy category
by taking its equivalence class.
-/
def homMk (f : Edge x₀ x₁) : mk x₀ ⟶ mk x₁ := ⟦f⟧

/--
Every morphism in the homotopy category `HomotopyCategory₂ X` is the equivalence class of
an edge of `A`.
-/
lemma homMk_surjective : Function.Surjective (homMk : Edge x₀ x₁ → _) := Quotient.mk_surjective

lemma homMk_eq_iff_homotopicL {f g : Edge x₀ x₁} :
    homMk f = homMk g ↔ HomotopicL f g :=
  ⟨Quotient.exact, fun h ↦ Quotient.sound h⟩

lemma homMk_eq_iff_homotopicR {f g : Edge x₀ x₁} :
    homMk f = homMk g ↔ HomotopicR f g := by
  rw [homMk_eq_iff_homotopicL, homotopicL_iff_homotopicR]

/--
The trivial (degenerate) edge at a vertex `x` is a representative for the
identity morphism `x ⟶ x`.
-/
@[simp]
lemma homMk_id (x : HomotopyCategory₂ X) : homMk (Edge.id x.pt) = 𝟙 x := rfl

end HomotopyCategory₂

open HomotopyCategory₂

/--
Left homotopic edges represent the same morphism in the homotopy category.
-/
lemma HomotopicL.congr_homotopyCategory₂HomMk {f g : Edge x₀ x₁} (h : HomotopicL f g) :
    homMk f = homMk g := Quotient.sound h


/--
Right homotopic edges represent the same morphism in the homotopy category.
-/
lemma HomotopicR.congr_homotopyCategory₂HomMk {f g : Edge x₀ x₁} (h : HomotopicR f g) :
    homMk f = homMk g := Quotient.sound h.homotopicL

/--
A `CompStruct f g h` is a witness for the fact that the morphisms represented by
`f` and `g` compose to the morphism represented by `h`.
-/
lemma Edge.CompStruct.homotopyCategory₂_fac {f : Edge x₀ x₁} {g : Edge x₁ x₂} {h : Edge x₀ x₂}
    (s : CompStruct f g h) : homMk f ≫ homMk g = homMk h :=
  (comp_unique (compStruct _ _) s .refl .refl).congr_homotopyCategory₂HomMk

set_option backward.isDefEq.respectTransparency false in
/--
If we have a factorization `homMk f ≫ homMk g = homMk h`, this is the choice
of a structure `CompStruct f g h`.
-/
noncomputable def Edge.CompStruct.ofHomotopyCategory₂Fac
    {f : Edge x₀ x₁} {g : Edge x₁ x₂} {h : Edge x₀ x₂}
    (fac : homMk f ≫ homMk g = homMk h) : CompStruct f g h := by
  dsimp [homMk, CategoryStruct.comp] at fac
  rw [Quotient.eq_iff_equiv] at fac
  exact (Quasicategory₂.fill32 (compStruct f g) (compId g) fac.some).some

/--
Given edges `f`, `g` and `h` of a `2`-truncated quasicategory,
there exists a structure `CompStruct f g h` iff
`homMk f ≫ homMk g = homMk h` holds in the homotopy category.
-/
lemma Edge.CompStruct.nonempty_iff {f : Edge x₀ x₁} {g : Edge x₁ x₂} {h : Edge x₀ x₂} :
    Nonempty (CompStruct f g h) ↔ homMk f ≫ homMk g = homMk h :=
  ⟨fun ⟨h⟩ ↦ h.homotopyCategory₂_fac, fun h ↦ ⟨.ofHomotopyCategory₂Fac h⟩⟩

noncomputable
instance : Category (HomotopyCategory₂ X) where
  id_comp := by
    rintro _ _ ⟨f⟩
    exact (idComp _).homotopyCategory₂_fac
  comp_id := by
    rintro _ _ ⟨f⟩
    exact (compId _).homotopyCategory₂_fac
  assoc := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact (assoc (compStruct f g) (compStruct g h) (compStruct _ _)).homotopyCategory₂_fac

namespace HomotopyCategory₂

variable {D : Type*} [Category D]

section

variable (obj : X _⦋0⦌₂ → D) (map : ∀ {x y : X _⦋0⦌₂}, Edge x y → (obj x ⟶ obj y))
  (map_id : ∀ (x : X _⦋0⦌₂), map (.id x) = 𝟙 (obj x))
  (map_comp : ∀ {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂},
    Edge.CompStruct e₀₁ e₁₂ e₀₂ → map e₀₁ ≫ map e₁₂ = map e₀₂)

/-- Auxiliary definition for `SSet.Truncated.HomotopyCategory₂.desc`. -/
@[no_expose]
def descMap {x y : HomotopyCategory₂ X} (f : x ⟶ y) : obj x.pt ⟶ obj y.pt :=
  Quot.lift map (fun _ _ ⟨h⟩ ↦ by simpa [map_id] using map_comp h) f

@[simp]
lemma descMap_homMk {x y : X _⦋0⦌₂} (e : Edge x y) :
    descMap obj map map_id map_comp (homMk e) = map e := by rfl

/-- Constructor for functors from `SSet.Truncated.HomotopyCategory₂`. -/
@[implicit_reducible]
def desc : HomotopyCategory₂ X ⥤ D where
  obj x := obj x.pt
  map := descMap obj map map_id map_comp
  map_id x := by exact map_id x.pt
  map_comp {x y z} f g := by
    obtain ⟨f, rfl⟩ := homMk_surjective f
    obtain ⟨g, rfl⟩ := homMk_surjective g
    simp [(compStruct f g).homotopyCategory₂_fac, ← map_comp (compStruct f g)]

@[simp]
lemma desc_map_homMk {x y : X _⦋0⦌₂} (e : Edge x y) :
    (desc obj map map_id map_comp).map (homMk e) = map e := by rfl

end

lemma functor_ext {F G : HomotopyCategory₂ X ⥤ D}
    (h₁ : ∀ (x : X _⦋0⦌₂), F.obj (mk x) = G.obj (mk x) := by cat_disch)
    (h₂ : ∀ {x y : X _⦋0⦌₂} (e : Edge x y),
      F.map (homMk e) = eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToHom (h₁ y).symm := by cat_disch) :
    F = G :=
  CategoryTheory.Functor.ext (fun _ ↦ h₁ _) (fun ⟨x⟩ ⟨y⟩ f ↦ by
    obtain ⟨e, rfl⟩ := homMk_surjective f
    exact h₂ e)

end HomotopyCategory₂

end homotopy_category

end SSet.Truncated
