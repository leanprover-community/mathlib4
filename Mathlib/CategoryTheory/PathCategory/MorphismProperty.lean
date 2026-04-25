/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Properties of morphisms in a path category.

We provide a formulation of induction principles for morphisms in a path category in terms of
`MorphismProperty`. This file is separate from `Mathlib/CategoryTheory/PathCategory/Basic.lean` in
order to reduce transitive imports.

We also define a morpism property `W.paths : MorphismProperty (Paths C)` for any
`W : MorphismProperty C`, consisting of all paths in `C` that consist only of morphisms in `W`. -/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory.Paths

section
variable (V : Type u₁) [Quiver.{v₁} V]

/-- A reformulation of `CategoryTheory.Paths.induction` in terms of `MorphismProperty`. -/
lemma morphismProperty_eq_top
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p → P (p ≫ (of V).map q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction (fun f ↦ P f) id comp _

/-- A reformulation of `CategoryTheory.Paths.induction'` in terms of `MorphismProperty`. -/
lemma morphismProperty_eq_top'
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : u ⟶ v) (q : (of V).obj v ⟶ (of V).obj w), P q → P ((of V).map p ≫ q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction' (fun f ↦ P f) id comp _

lemma morphismProperty_eq_top_of_isMultiplicative (P : MorphismProperty (Paths V))
    [P.IsMultiplicative]
    (hP : ∀ {u v : V} (p : u ⟶ v), P ((of V).map p)) : P = ⊤ :=
  morphismProperty_eq_top _ _ (P.id_mem _) (fun _ q hp ↦ P.comp_mem _ _ hp (hP q))
end
section

variable {C : Type*} [Category* C] {V : Type u₁} [Quiver.{v₁} V]

/-- A natural transformation between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
@[simps]
def liftNatTrans {F G : Paths V ⥤ C} (α_app : (v : V) → (F.obj v ⟶ G.obj v))
    (α_nat : {X Y : V} → (f : X ⟶ Y) →
      F.map (Quiver.Hom.toPath f) ≫ α_app Y = α_app X ≫ G.map (Quiver.Hom.toPath f)) : F ⟶ G where
  app := α_app
  naturality := by
    apply MorphismProperty.of_eq_top
      (P := MorphismProperty.naturalityProperty (F₁ := F) α_app)
    exact morphismProperty_eq_top_of_isMultiplicative _ _ α_nat

/-- A natural isomorphism between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
@[simps!]
def liftNatIso {C} [Category* C] {F G : Paths V ⥤ C} (α_app : (v : V) → (F.obj v ≅ G.obj v))
    (α_nat : {X Y : V} → (f : X ⟶ Y) →
      F.map (Quiver.Hom.toPath f) ≫ (α_app Y).hom = (α_app X).hom ≫ G.map (Quiver.Hom.toPath f)) :
    F ≅ G :=
  NatIso.ofComponents α_app (fun f ↦ (liftNatTrans (fun v ↦ (α_app v).hom) α_nat).naturality f)

end

end CategoryTheory.Paths

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C]

open Quiver

/-- For any morphism property `W` on `C`, `W.paths` is the morphism property on `Paths C`
containing all paths of morphisms in `W`. -/
def paths (W : MorphismProperty C) : MorphismProperty (Paths C) :=
  fun _ _ p ↦ p.rec True fun _ f P ↦ P ∧ W f

@[simp]
lemma nil_mem_paths {W : MorphismProperty C} {X : C} : W.paths (.nil (a := X)) := trivial

lemma cons_mem_paths {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z}
    (hp : W.paths p) (hf : W f) : W.paths (p.cons f) :=
  ⟨hp, hf⟩

@[simp]
lemma cons_mem_paths_iff {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {f : Y ⟶ Z} :
    W.paths (p.cons f) ↔ W.paths p ∧ W f :=
  Iff.rfl

lemma toPath_mem_paths {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} (hf : W f) :
    W.paths f.toPath :=
  ⟨trivial, hf⟩

@[simp]
lemma toPath_mem_paths_iff {W : MorphismProperty C} {X Y : C} {f : X ⟶ Y} :
    W.paths f.toPath ↔ W f :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨trivial, h⟩⟩

@[simp]
lemma comp_mem_paths_iff {W : MorphismProperty C} {X Y Z : C} {p : Path X Y} {q : Path Y Z} :
    W.paths (p.comp q) ↔ W.paths p ∧ W.paths q := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hp, hq⟩ ↦ ?_⟩
  · induction q with
    | nil => simpa using h
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact h' h.1
  · induction q with
    | nil => simp
    | cons q' f h' =>
      rw [Path.comp_cons] at h
      exact ⟨h' h.1, h.2⟩
  · induction q with
    | nil => exact hp
    | cons q q' h => exact ⟨h ⟨hp, hq.1⟩ hq.1, hq.2⟩

instance (W : MorphismProperty C) : W.paths.IsMultiplicative where
  id_mem _ := nil_mem_paths
  comp_mem _ _ hf hg := W.comp_mem_paths_iff.2 ⟨hf, hg⟩

/-- If `W` and `W'` are morphism properties on `C` such that `W ≤ W'`, then `W.paths ≤ W'.paths`. -/
@[gcongr]
lemma monotone_paths : Monotone (paths (C := C)) :=
  fun _ _ h _ _ p ↦ p.rec (fun _ ↦ trivial) (fun _ _ hp' hp ↦ ⟨hp' hp.1, h _ hp.2⟩)

lemma composePath_mem_of_id_mem (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C}
    {p : Path X Y} (hp : W.paths p) (h : W (𝟙 X)) : W (composePath p) := by
  revert hp
  exact p.rec (by simpa) fun p f hp hp' ↦ W.comp_mem _ _ (hp hp'.1) hp'.2

lemma composePath_mem_of_length_pos (W : MorphismProperty C) [W.IsStableUnderComposition] {X Y : C}
    {p : Path X Y} (hp : W.paths p) (h : 0 < p.length) : W (composePath p) := by
  revert hp h
  refine p.rec (by simp) fun p f hp hp' hp'' ↦ ?_
  cases p
  · simpa [paths] using hp'
  · refine W.comp_mem _ _ (hp hp'.1 (by simp)) hp'.2

lemma composePath_mem (W : MorphismProperty C) [W.IsMultiplicative] {X Y : C}
    {p : Path X Y} (hp : W.paths p) : W (composePath p) :=
  W.composePath_mem_of_id_mem hp <| W.id_mem X

lemma paths_le_inverseImage (W : MorphismProperty C) [W.IsMultiplicative] :
    W.paths ≤ W.inverseImage (pathComposition C) :=
  fun _ _ _ ↦ W.composePath_mem

instance (W : MorphismProperty C) : IsMultiplicative (W.paths.strictMap (pathComposition C)) where
  id_mem X := W.paths.map_mem_strictMap (pathComposition C) _ (W.paths.id_mem X)
  comp_mem := fun _ _ ⟨hp⟩ ⟨hq⟩ ↦ by
    simpa using W.paths.map_mem_strictMap (pathComposition C) _ <| W.paths.comp_mem _ _ hp hq

lemma multiplicativeClosure_eq_strictMap_paths (W : MorphismProperty C) :
    W.multiplicativeClosure = W.paths.strictMap (pathComposition C) := by
  refine le_antisymm ?_ fun _ _ _ ⟨h⟩ ↦ ?_
  · refine (W.multiplicativeClosure_le_iff _).2 fun X Y f hf ↦ ?_
    simpa using W.paths.map_mem_strictMap (pathComposition C) f.toPath (by simpa)
  · exact composePath_mem _ <| monotone_paths W.le_multiplicativeClosure _ h

end CategoryTheory.MorphismProperty
