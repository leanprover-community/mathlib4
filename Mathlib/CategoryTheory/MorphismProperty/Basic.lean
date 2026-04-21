/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-property is defined

* `RespectsLeft P Q`: `P` respects the property `Q` on the left if `P f → P (i ≫ f)` where
  `i` satisfies `Q`.
* `RespectsRight P Q`: `P` respects the property `Q` on the right if `P f → P (f ≫ i)` where
  `i` satisfies `Q`.
* `Respects`: `P` respects `Q` if `P` respects `Q` both on the left and on the right.

-/

@[expose] public section



universe w v v' u u'

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory

/-- A `MorphismProperty C` is a class of morphisms between objects in `C`. -/
def MorphismProperty (C : Type u) [CategoryStruct.{v} C] :=
  ∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

namespace MorphismProperty

section

variable (C : Type u) [CategoryStruct.{v} C]

instance : CompleteBooleanAlgebra (MorphismProperty C) where
  le P₁ P₂ := ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P₁ f → P₂ f
  __ := (inferInstance : CompleteBooleanAlgebra (∀ ⦃X Y : C⦄ (_ : X ⟶ Y), Prop))

lemma le_def {P Q : MorphismProperty C} :
    P ≤ Q ↔ ∀ {X Y : C} (f : X ⟶ Y), P f → Q f := Iff.rfl

instance : Inhabited (MorphismProperty C) :=
  ⟨⊤⟩

lemma top_eq : (⊤ : MorphismProperty C) = fun _ _ _ => True := rfl

variable {C}

@[ext]
lemma ext (W W' : MorphismProperty C) (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) :
    W = W' := by
  funext X Y f
  rw [h]

@[simp]
lemma top_apply {X Y : C} (f : X ⟶ Y) : (⊤ : MorphismProperty C) f := by
  simp only [top_eq]

lemma of_eq_top {P : MorphismProperty C} (h : P = ⊤) {X Y : C} (f : X ⟶ Y) : P f := by
  simp [h]

@[simp]
lemma sSup_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) :
    sSup S f ↔ ∃ (W : S), W.1 f := by
  dsimp [sSup, iSup]
  constructor
  · rintro ⟨_, ⟨⟨_, ⟨⟨_, ⟨_, h⟩, rfl⟩, rfl⟩⟩, rfl⟩, hf⟩
    exact ⟨⟨_, h⟩, hf⟩
  · rintro ⟨⟨W, hW⟩, hf⟩
    exact ⟨_, ⟨⟨_, ⟨_, ⟨⟨W, hW⟩, rfl⟩⟩, rfl⟩, rfl⟩, hf⟩

@[simp]
lemma iSup_iff {ι : Sort*} (W : ι → MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    iSup W f ↔ ∃ i, W i f := by
  apply (sSup_iff (Set.range W) f).trans
  constructor
  · rintro ⟨⟨_, i, rfl⟩, hf⟩
    exact ⟨i, hf⟩
  · rintro ⟨i, hf⟩
    exact ⟨⟨_, i, rfl⟩, hf⟩

/-- The morphism property in `Cᵒᵖ` associated to a morphism property in `C` -/
@[simp]
def op (P : MorphismProperty C) : MorphismProperty Cᵒᵖ := fun _ _ f => P f.unop

/-- The morphism property in `C` associated to a morphism property in `Cᵒᵖ` -/
@[simp]
def unop (P : MorphismProperty Cᵒᵖ) : MorphismProperty C := fun _ _ f => P f.op

theorem unop_op (P : MorphismProperty C) : P.op.unop = P :=
  rfl

theorem op_unop (P : MorphismProperty Cᵒᵖ) : P.unop.op = P :=
  rfl

end

section

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]

/-- The inverse image of a `MorphismProperty D` by a functor `C ⥤ D` -/
def inverseImage (P : MorphismProperty D) (F : C ⥤ D) : MorphismProperty C := fun _ _ f =>
  P (F.map f)

@[simp]
lemma inverseImage_iff (P : MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    P.inverseImage F f ↔ P (F.map f) := by rfl

@[simp]
lemma op_inverseImage (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).op = P.op.inverseImage F.op := rfl

/-- The (strict) image of a `MorphismProperty C` by a functor `C ⥤ D` -/
inductive strictMap (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D where
  | map {X Y : C} {f : X ⟶ Y} (hf : P f) : strictMap _ _ (F.map f)

lemma map_mem_strictMap (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.strictMap F) (F.map f) := ⟨hf⟩

/-- The image (up to isomorphisms) of a `MorphismProperty C` by a functor `C ⥤ D` -/
def map (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D := fun _ _ f =>
  ∃ (X' Y' : C) (f' : X' ⟶ Y') (_ : P f'), Nonempty (Arrow.mk (F.map f') ≅ Arrow.mk f)

lemma map_mem_map (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.map F) (F.map f) := ⟨X, Y, f, hf, ⟨Iso.refl _⟩⟩

lemma monotone_map (F : C ⥤ D) :
    Monotone (map · F) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

@[simp]
lemma map_top_eq_top_of_essSurj_of_full (F : C ⥤ D) [F.EssSurj] [F.Full] :
    (⊤ : MorphismProperty C).map F = ⊤ := by
  rw [eq_top_iff]
  intro X Y f _
  refine ⟨F.objPreimage X, F.objPreimage Y, F.preimage ?_, ⟨⟨⟩, ⟨?_⟩⟩⟩
  · exact (Functor.objObjPreimageIso F X).hom ≫ f ≫ (Functor.objObjPreimageIso F Y).inv
  · exact Arrow.isoMk' _ _ (Functor.objObjPreimageIso F X) (Functor.objObjPreimageIso F Y)
      (by simp)

section

variable (P : MorphismProperty C)

/-- The set in `Set (Arrow C)` which corresponds to `P : MorphismProperty C`. -/
def toSet : Set (Arrow C) := setOf (fun f ↦ P f.hom)

lemma mem_toSet_iff (f : Arrow C) : f ∈ P.toSet ↔ P f.hom := Iff.rfl

lemma toSet_iSup {ι : Type*} (W : ι → MorphismProperty C) :
    (⨆ i, W i).toSet = ⋃ i, (W i).toSet := by
  ext
  simp [mem_toSet_iff]

lemma toSet_max (W₁ W₂ : MorphismProperty C) :
    (W₁ ⊔ W₂).toSet = W₁.toSet ∪ W₂.toSet := rfl

/-- The family of morphisms indexed by `P.toSet` which corresponds
to `P : MorphismProperty C`, see `MorphismProperty.ofHoms_homFamily`. -/
def homFamily (f : P.toSet) : f.1.left ⟶ f.1.right := f.1.hom

lemma homFamily_apply (f : P.toSet) : P.homFamily f = f.1.hom := rfl

@[simp]
lemma homFamily_arrow_mk {X Y : C} (f : X ⟶ Y) (hf : P f) :
    P.homFamily ⟨Arrow.mk f, hf⟩ = f := rfl

@[simp]
lemma arrow_mk_mem_toSet_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f ∈ P.toSet ↔ P f := Iff.rfl

lemma of_eq {X Y : C} {f : X ⟶ Y} (hf : P f)
    {X' Y' : C} {f' : X' ⟶ Y'}
    (hX : X = X') (hY : Y = Y') (h : f' = eqToHom hX.symm ≫ f ≫ eqToHom hY) :
    P f' := by
  rw [← P.arrow_mk_mem_toSet_iff] at hf ⊢
  rwa [(Arrow.mk_eq_mk_iff f' f).2 ⟨hX.symm, hY.symm, h⟩]

end

/-- The class of morphisms given by a family of morphisms `f i : X i ⟶ Y i`. -/
inductive ofHoms {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) : MorphismProperty C
  | mk (i : ι) : ofHoms f (f i)

lemma ofHoms_iff {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) :
    ofHoms f g ↔ ∃ i, Arrow.mk g = Arrow.mk (f i) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, h⟩
    rw [← (ofHoms f).arrow_mk_mem_toSet_iff, h, arrow_mk_mem_toSet_iff]
    constructor

@[simp]
lemma ofHoms_homFamily (P : MorphismProperty C) : ofHoms P.homFamily = P := by
  ext _ _ f
  constructor
  · intro hf
    rw [ofHoms_iff] at hf
    obtain ⟨⟨f, hf⟩, ⟨_, _⟩⟩ := hf
    exact hf
  · intro hf
    exact ⟨(⟨f, hf⟩ : P.toSet)⟩

end

section

variable {C : Type u} [CategoryStruct.{v} C]

/-- A morphism property `P` satisfies `P.RespectsRight Q` if it is stable under post-composition
with morphisms satisfying `Q`, i.e. whenever `P` holds for `f` and `Q` holds for `i` then `P`
holds for `f ≫ i`. -/
class RespectsRight (P Q : MorphismProperty C) : Prop where
  postcomp {X Y Z : C} (i : Y ⟶ Z) (hi : Q i) (f : X ⟶ Y) (hf : P f) : P (f ≫ i)

/-- A morphism property `P` satisfies `P.RespectsLeft Q` if it is stable under
pre-composition with morphisms satisfying `Q`, i.e. whenever `P` holds for `f`
and `Q` holds for `i` then `P` holds for `i ≫ f`. -/
class RespectsLeft (P Q : MorphismProperty C) : Prop where
  precomp {X Y Z : C} (i : X ⟶ Y) (hi : Q i) (f : Y ⟶ Z) (hf : P f) : P (i ≫ f)

/-- A morphism property `P` satisfies `P.Respects Q` if it is stable under composition on the
left and right by morphisms satisfying `Q`. -/
class Respects (P Q : MorphismProperty C) : Prop extends P.RespectsLeft Q, P.RespectsRight Q where

instance (P Q : MorphismProperty C) [P.RespectsLeft Q] [P.RespectsRight Q] : P.Respects Q where

instance (P Q : MorphismProperty C) [P.RespectsLeft Q] : P.op.RespectsRight Q.op where
  postcomp i hi f hf := RespectsLeft.precomp (Q := Q) i.unop hi f.unop hf

instance (P Q : MorphismProperty C) [P.RespectsRight Q] : P.op.RespectsLeft Q.op where
  precomp i hi f hf := RespectsRight.postcomp (Q := Q) i.unop hi f.unop hf

instance RespectsLeft.inf (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsLeft Q]
    [P₂.RespectsLeft Q] : (P₁ ⊓ P₂).RespectsLeft Q where
  precomp i hi f hf := ⟨precomp i hi f hf.left, precomp i hi f hf.right⟩

instance RespectsRight.inf (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsRight Q]
    [P₂.RespectsRight Q] : (P₁ ⊓ P₂).RespectsRight Q where
  postcomp i hi f hf := ⟨postcomp i hi f hf.left, postcomp i hi f hf.right⟩

end

section

variable (C : Type u) [Category.{v} C]

/-- The `MorphismProperty C` satisfied by isomorphisms in `C`. -/
abbrev isomorphisms : MorphismProperty C := fun _ _ f => IsIso f

/-- The `MorphismProperty C` satisfied by monomorphisms in `C`. -/
abbrev monomorphisms : MorphismProperty C := fun _ _ f => Mono f

/-- The `MorphismProperty C` satisfied by epimorphisms in `C`. -/
abbrev epimorphisms : MorphismProperty C := fun _ _ f => Epi f

@[simp]
lemma op_isomorphisms : (isomorphisms C).op = isomorphisms Cᵒᵖ := by
  ext
  apply isIso_unop_iff

section

variable {C}

/-- `P` respects isomorphisms, if it respects the morphism property `isomorphisms C`, i.e.
it is stable under pre- and postcomposition with isomorphisms. -/
abbrev RespectsIso (P : MorphismProperty C) : Prop := P.Respects (isomorphisms C)

instance inf (P Q : MorphismProperty C) [P.RespectsIso] [Q.RespectsIso] : (P ⊓ Q).RespectsIso where

lemma RespectsIso.mk (P : MorphismProperty C)
    (hprecomp : ∀ {X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z) (_ : P f), P (e.hom ≫ f))
    (hpostcomp : ∀ {X Y Z : C} (e : Y ≅ Z) (f : X ⟶ Y) (_ : P f), P (f ≫ e.hom)) :
    P.RespectsIso where
  precomp e (_ : IsIso e) f hf := hprecomp (asIso e) f hf
  postcomp e (_ : IsIso e) f hf := hpostcomp (asIso e) f hf

lemma RespectsIso.precomp (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : X ⟶ Y)
    [IsIso e] (f : Y ⟶ Z) (hf : P f) : P (e ≫ f) :=
  RespectsLeft.precomp (Q := isomorphisms C) e ‹IsIso e› f hf

instance : RespectsIso (⊤ : MorphismProperty C) where
  precomp _ _ _ _ := trivial
  postcomp _ _ _ _ := trivial

lemma RespectsIso.postcomp (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : Y ⟶ Z)
    [IsIso e] (f : X ⟶ Y) (hf : P f) : P (f ≫ e) :=
  RespectsRight.postcomp (Q := isomorphisms C) e ‹IsIso e› f hf

instance RespectsIso.op (P : MorphismProperty C) [RespectsIso P] : RespectsIso P.op where
  precomp e (_ : IsIso e) f hf := postcomp P e.unop f.unop hf
  postcomp e (_ : IsIso e) f hf := precomp P e.unop f.unop hf

instance RespectsIso.unop (P : MorphismProperty Cᵒᵖ) [RespectsIso P] : RespectsIso P.unop where
  precomp e (_ : IsIso e) f hf := postcomp P e.op f.op hf
  postcomp e (_ : IsIso e) f hf := precomp P e.op f.op hf

/-- The closure by isomorphisms of a `MorphismProperty` -/
def isoClosure (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => ∃ (Y₁ Y₂ : C) (f' : Y₁ ⟶ Y₂) (_ : P f'), Nonempty (Arrow.mk f' ≅ Arrow.mk f)

lemma le_isoClosure (P : MorphismProperty C) : P ≤ P.isoClosure :=
  fun _ _ f hf => ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩

set_option backward.isDefEq.respectTransparency false in
instance isoClosure_respectsIso (P : MorphismProperty C) :
    RespectsIso P.isoClosure where
  precomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left ≪≫ asIso (inv e)) (asIso iso.hom.right) (by simp)⟩⟩
  postcomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left) (asIso iso.hom.right ≪≫ asIso e) (by simp)⟩⟩

lemma monotone_isoClosure : Monotone (isoClosure (C := C)) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

theorem cancel_left_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun h => by simpa using RespectsIso.precomp P (inv f) (f ≫ g) h, RespectsIso.precomp P f g⟩

theorem cancel_right_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun h => by simpa using RespectsIso.postcomp P (inv g) (f ≫ g) h, RespectsIso.postcomp P g f⟩

lemma comma_iso_iff (P : MorphismProperty C) [P.RespectsIso]
    {A B : Type*} [Category* A] [Category* B]
    {L : A ⥤ C} {R : B ⥤ C} {f g : Comma L R} (e : f ≅ g) :
    P f.hom ↔ P g.hom := by
  simp [← Comma.inv_left_hom_right e.hom, cancel_left_of_respectsIso, cancel_right_of_respectsIso]

theorem arrow_iso_iff (P : MorphismProperty C) [RespectsIso P] {f g : Arrow C}
    (e : f ≅ g) : P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

theorem arrow_mk_iso_iff (P : MorphismProperty C) [RespectsIso P] {W X Y Z : C}
    {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g :=
  P.arrow_iso_iff e

set_option backward.isDefEq.respectTransparency false in
theorem RespectsIso.of_respects_arrow_iso (P : MorphismProperty C)
    (hP : ∀ (f g : Arrow C) (_ : f ≅ g) (_ : P f.hom), P g.hom) : RespectsIso P where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (e ≫ f)) (Arrow.isoMk (asIso (inv e)) (Iso.refl _) ?_) hf
    simp
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (f ≫ e)) (Arrow.isoMk (Iso.refl _) (asIso e) ?_) hf
    simp

lemma isoClosure_eq_iff (P : MorphismProperty C) :
    P.isoClosure = P ↔ P.RespectsIso := by
  refine ⟨(· ▸ P.isoClosure_respectsIso), fun hP ↦ le_antisymm ?_ (P.le_isoClosure)⟩
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact (P.arrow_mk_iso_iff e).1 hf'

lemma isoClosure_eq_self (P : MorphismProperty C) [P.RespectsIso] :
    P.isoClosure = P := by rwa [isoClosure_eq_iff]

@[simp]
lemma isoClosure_isoClosure (P : MorphismProperty C) :
    P.isoClosure.isoClosure = P.isoClosure :=
  P.isoClosure.isoClosure_eq_self

lemma isoClosure_le_iff (P Q : MorphismProperty C) [Q.RespectsIso] :
    P.isoClosure ≤ Q ↔ P ≤ Q := by
  constructor
  · exact P.le_isoClosure.trans
  · intro h
    exact (monotone_isoClosure h).trans (by rw [Q.isoClosure_eq_self])

section

variable {D : Type*} [Category* D]

instance map_respectsIso (P : MorphismProperty C) (F : C ⥤ D) :
    (P.map F).RespectsIso := by
  apply RespectsIso.of_respects_arrow_iso
  intro f g e ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨e' ≪≫ e⟩⟩

lemma map_le_iff (P : MorphismProperty C) {F : C ⥤ D} (Q : MorphismProperty D)
    [RespectsIso Q] :
    P.map F ≤ Q ↔ P ≤ Q.inverseImage F := by
  constructor
  · intro h X Y f hf
    exact h (F.map f) (map_mem_map P F f hf)
  · intro h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact (Q.arrow_mk_iso_iff e).1 (h _ hf')

@[simp]
lemma map_isoClosure (P : MorphismProperty C) (F : C ⥤ D) :
    P.isoClosure.map F = P.map F := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨_, _, f', hf', ⟨F.mapArrow.mapIso e⟩⟩
  · exact monotone_map _ (le_isoClosure P)

lemma map_id_eq_isoClosure (P : MorphismProperty C) :
    P.map (𝟭 _) = P.isoClosure := rfl

lemma map_id (P : MorphismProperty C) [RespectsIso P] :
    P.map (𝟭 _) = P := by
  rw [map_id_eq_isoClosure, P.isoClosure_eq_self]

@[simp]
lemma map_map (P : MorphismProperty C) (F : C ⥤ D) {E : Type*} [Category* E] (G : D ⥤ E) :
    (P.map F).map G = P.map (F ⋙ G) := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨X', Y', f', hf', ⟨G.mapArrow.mapIso e⟩⟩
  · rw [map_le_iff]
    intro X Y f hf
    exact map_mem_map _ _ _ (map_mem_map _ _ _ hf)

instance RespectsIso.inverseImage (P : MorphismProperty D) [RespectsIso P] (F : C ⥤ D) :
    RespectsIso (P.inverseImage F) where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_left_of_respectsIso] using hf
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_right_of_respectsIso] using hf

lemma map_eq_of_iso (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    P.map F = P.map G := by
  revert F G e
  suffices ∀ {F G : C ⥤ D} (_ : F ≅ G), P.map F ≤ P.map G from
    fun F G e => le_antisymm (this e) (this e.symm)
  intro F G e X Y f ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨((Functor.mapArrowFunctor _ _).mapIso e.symm).app (Arrow.mk f') ≪≫ e'⟩⟩

lemma map_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).map F ≤ P.isoClosure :=
  fun _ _ _ ⟨_, _, f, hf, ⟨e⟩⟩ => ⟨_, _, F.map f, hf, ⟨e⟩⟩

lemma inverseImage_equivalence_inverse_eq_map_functor
    (P : MorphismProperty D) [RespectsIso P] (E : C ≌ D) :
    P.inverseImage E.functor = P.map E.inverse := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨_, _, _, hf, ⟨?_⟩⟩
    exact ((Functor.mapArrowFunctor _ _).mapIso E.unitIso.symm).app (Arrow.mk f)
  · rw [map_le_iff]
    intro X Y f hf
    exact (P.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))).2 hf

lemma inverseImage_equivalence_functor_eq_map_inverse
    (Q : MorphismProperty C) [RespectsIso Q] (E : C ≌ D) :
    Q.inverseImage E.inverse = Q.map E.functor :=
  inverseImage_equivalence_inverse_eq_map_functor Q E.symm

lemma map_inverseImage_eq_of_isEquivalence
    (P : MorphismProperty D) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.inverseImage F).map F = P := by
  erw [P.inverseImage_equivalence_inverse_eq_map_functor F.asEquivalence, map_map,
    P.map_eq_of_iso F.asEquivalence.counitIso, map_id]

lemma inverseImage_map_eq_of_isEquivalence
    (P : MorphismProperty C) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.map F).inverseImage F = P := by
  erw [((P.map F).inverseImage_equivalence_inverse_eq_map_functor (F.asEquivalence)), map_map,
    P.map_eq_of_iso F.asEquivalence.unitIso.symm, map_id]

end

end

section

variable {C}
variable {X Y : C} (f : X ⟶ Y)

@[simp]
theorem isomorphisms.iff : (isomorphisms C) f ↔ IsIso f := by rfl

@[simp]
theorem monomorphisms.iff : (monomorphisms C) f ↔ Mono f := by rfl

@[simp]
theorem epimorphisms.iff : (epimorphisms C) f ↔ Epi f := by rfl

theorem isomorphisms.infer_property [hf : IsIso f] : (isomorphisms C) f :=
  hf

theorem monomorphisms.infer_property [hf : Mono f] : (monomorphisms C) f :=
  hf

theorem epimorphisms.infer_property [hf : Epi f] : (epimorphisms C) f :=
  hf

end

@[deprecated "Use `op_isomorphisms _` instead." (since := "2026-01-18")]
lemma isomorphisms_op : (isomorphisms C).op = isomorphisms Cᵒᵖ := op_isomorphisms _

instance RespectsIso.monomorphisms : RespectsIso (monomorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp

instance RespectsIso.epimorphisms : RespectsIso (epimorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp

instance RespectsIso.isomorphisms : RespectsIso (isomorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      exact IsIso.comp_isIso

end

/-- If `W₁` and `W₂` are morphism properties on two categories `C₁` and `C₂`,
this is the induced morphism property on `C₁ × C₂`. -/
def prod {C₁ C₂ : Type*} [CategoryStruct C₁] [CategoryStruct C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) :
    MorphismProperty (C₁ × C₂) :=
  fun _ _ f => W₁ f.1 ∧ W₂ f.2

/-- If `W j` are morphism properties on categories `C j` for all `j`, this is the
induced morphism property on the category `∀ j, C j`. -/
def pi {J : Type w} {C : J → Type u} [∀ j, Category.{v} (C j)]
    (W : ∀ j, MorphismProperty (C j)) : MorphismProperty (∀ j, C j) :=
  fun _ _ f => ∀ j, (W j) (f j)

variable {C} [Category.{v} C]

/-- The morphism property on `J ⥤ C` which is defined objectwise
from `W : MorphismProperty C`. -/
def functorCategory (W : MorphismProperty C) (J : Type*) [Category* J] :
    MorphismProperty (J ⥤ C) :=
  fun _ _ f => ∀ (j : J), W (f.app j)

/-- Given `W : MorphismProperty C`, this is the morphism property on `Arrow C` of morphisms
whose left and right parts are in `W`. -/
def arrow (W : MorphismProperty C) :
    MorphismProperty (Arrow C) :=
  fun _ _ f => W f.left ∧ W f.right

end MorphismProperty

namespace NatTrans

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]

lemma isIso_app_iff_of_iso {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    IsIso (α.app X) ↔ IsIso (α.app Y) :=
  (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (by simp))

end NatTrans

end CategoryTheory
