/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.MorphismProperty.HasCardinalLT
public import Mathlib.CategoryTheory.ObjectProperty.HasCardinalLT
public import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
public import Mathlib.CategoryTheory.Products.Unitor

/-!
# `κ`-filtered categories and `κ`-directed poset

In this file, we shall formalize the proof by Deligne (SGA 4 I 8.1.6) that for
any (small) filtered category `J`, there exists a final functor `F : α ⥤ J`
where `α` is a directed partially ordered set (TODO).
The construction applies more generally to `κ`-filtered categories and
`κ`-directed posets (TODO).

Note: the argument by Deligne is reproduced (without reference) in the book
by Adámek and Rosický (theorem 1.5), but with a mistake:
the construction by Deligne involves considering diagrams
(see `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.DiagramWithUniqueTerminal`)
which are not necessarily *subcategories* (the class of morphisms `W` does not
have to be multiplicative.)

## References
* [Alexander Grothendieck and Jean-Louis Verdier, *Exposé I : Préfaisceaux*,
  SGA 4 I 8.1.6][sga-4-tome-1]
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe u v w

namespace CategoryTheory

namespace IsCardinalFiltered

namespace exists_cardinal_directed

variable (J : Type w) [SmallCategory J] (κ : Cardinal.{w})

/-!
Let `J` is a `κ`-filtered category. In order to construct a cofinal functor `α ⥤ J`
with a `κ`-directed poset `α`, we first consider the case where there is no
object `m : J` such that for any object `j : J`, there exists a map `j ⟶ m`.
Under this assumption (`hJ`), the partially ordered type `DiagramWithUniqueTerminal J κ`
of `κ`-bounded diagrams with a unique terminal object in `J` shall be a possible
choice for `α`.
-/

/-- If `κ` is a cardinal, this structure contains the data of a `κ`-bounded diagram
in a category `J`. -/
@[ext]
structure Diagram where
  /-- the morphisms which belongs to the diagram -/
  W : MorphismProperty J
  /-- the objects in the diagram -/
  P : ObjectProperty J
  src {i j : J} {f : i ⟶ j} : W f → P i
  tgt {i j : J} {f : i ⟶ j} : W f → P j
  hW : W.HasCardinalLT κ
  hP : P.HasCardinalLT κ

namespace Diagram

variable {J κ}

/-- Given a `κ`-bounded diagram `D` in a category `J`, an object `e : J`
is terminal if `𝟙 e` belongs to `D` and for any object `j` of `D`,
there is a unique morphism `j ⟶ e` in `D`, such that these unique morphisms
are compatible with precomposition with morphisms in `D`. -/
structure IsTerminal (D : Diagram J κ) (e : J) where
  prop_id : D.W (𝟙 e)
  /-- the unique map to the terminal object in the diagram -/
  lift {j : J} (hj : D.P j) : j ⟶ e
  hlift {j : J} (hj : D.P j) : D.W (lift hj)
  uniq {j : J} (hj : D.P j) {φ : j ⟶ e} (hφ : D.W φ) : lift hj = φ
  comm {i j : J} (f : i ⟶ j) (hf : D.W f) : f ≫ lift (D.tgt hf) = lift (D.src hf)

namespace IsTerminal

attribute [reassoc] IsTerminal.comm

variable {D : Diagram J κ} {e : J}

lemma prop (h : D.IsTerminal e) : D.P e := D.src (h.prop_id)

@[simp]
lemma lift_self (h : D.IsTerminal e) : h.lift h.prop = 𝟙 e := h.uniq _ h.prop_id

instance : Subsingleton (D.IsTerminal e) where
  allEq h₁ h₂ := by
    have : @h₁.lift = @h₂.lift := by
      ext j hj
      exact h₁.uniq hj (h₂.hlift hj)
    cases h₁
    cases h₂
    aesop

/-- Constructor for `Diagram.IsTerminal` for which no data is provided,
but only its existence. -/
noncomputable def ofExistsUnique (prop_id : D.W (𝟙 e))
    (h₁ : ∀ ⦃j : J⦄ (_ : D.P j), ∃ (lift : j ⟶ e), D.W lift)
    (h₂ : ∀ ⦃j : J⦄ (_ : D.P j) (l₁ l₂ : j ⟶ e), D.W l₁ → D.W l₂ → l₁ = l₂)
    (h₃ : ∀ ⦃i j : J⦄ (f : i ⟶ j) (_ : D.W f), ∃ (li : i ⟶ e) (lj : j ⟶ e),
      D.W li ∧ D.W lj ∧ f ≫ lj = li) :
    D.IsTerminal e where
  prop_id := prop_id
  lift hj := (h₁ hj).choose
  hlift hj := (h₁ hj).choose_spec
  uniq hj φ hφ := h₂ hj (h₁ hj).choose φ (h₁ hj).choose_spec hφ
  comm _ hf := by
    obtain ⟨li, lj, hli, hlj, fac⟩ := h₃ _ hf
    rw [h₂ (D.src hf) _ li (h₁ (D.src hf)).choose_spec hli,
      h₂ (D.tgt hf) _ lj (h₁ (D.tgt hf)).choose_spec hlj, fac]

end IsTerminal

end Diagram

/-- If `κ` is a cardinal, this structure contains the data of a `κ`-bounded diagram
with a unique terminal object in a category `J`. -/
structure DiagramWithUniqueTerminal extends Diagram J κ where
  /-- the terminal object -/
  top : J
  /-- `top` is terminal -/
  isTerminal : toDiagram.IsTerminal top
  uniq_terminal (j : J) (hj : toDiagram.IsTerminal j) : j = top

@[ext]
lemma DiagramWithUniqueTerminal.ext {D₁ D₂ : DiagramWithUniqueTerminal J κ}
    (hW : D₁.W = D₂.W) (hP : D₁.P = D₂.P) : D₁ = D₂ := by
  obtain ⟨D₁, top, h₁, h₁'⟩ := D₁
  obtain ⟨D₂, top', h₂, h₂'⟩ := D₂
  obtain rfl : D₁ = D₂ := by aesop
  obtain rfl : top = top' := h₂' _ h₁
  obtain rfl : h₁ = h₂ := by subsingleton
  rfl

instance : PartialOrder (DiagramWithUniqueTerminal J κ) where
  le D₁ D₂ := D₁.W ≤ D₂.W ∧ D₁.P ≤ D₂.P
  le_refl _ := ⟨by rfl, by rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := by
    ext : 1
    · exact le_antisymm h₁.1 h₂.1
    · exact le_antisymm h₁.2 h₂.2

section

variable {J κ}

/-- Auxiliary definition for `functor`. -/
def functorMap {D₁ D₂ : DiagramWithUniqueTerminal J κ} (h : D₁ ≤ D₂) : D₁.top ⟶ D₂.top :=
  D₂.isTerminal.lift (h.2 _ D₁.isTerminal.prop)

@[simp]
lemma functorMap_id (D : DiagramWithUniqueTerminal J κ) : functorMap (le_refl D) = 𝟙 D.top := by
  simp [functorMap]

@[reassoc (attr := simp)]
lemma functorMap_comp {D₁ D₂ D₃ : DiagramWithUniqueTerminal J κ} (h₁₂ : D₁ ≤ D₂) (h₂₃ : D₂ ≤ D₃) :
    functorMap h₁₂ ≫ functorMap h₂₃ = functorMap (h₁₂.trans h₂₃) :=
  D₃.isTerminal.comm _ (h₂₃.1 _ (D₂.isTerminal.hlift _))

end

/-- The functor which sends a `κ`-bounded diagram with a unique terminal object to
its terminal object. -/
@[simps]
def functor : DiagramWithUniqueTerminal J κ ⥤ J where
  obj D := D.top
  map h := functorMap (leOfHom h)

variable [Fact κ.IsRegular]

variable {J κ} in
/-- The diagram containing a single object (and its identity morphism). -/
@[simps]
def Diagram.single (j : J) : Diagram J κ where
  W := .ofHoms (fun (_ : Unit) ↦ 𝟙 j)
  P := .ofObj (fun (_ : Unit) ↦ j)
  src := by rintro _ _ _ ⟨⟩; exact ⟨⟨⟩⟩
  tgt := by rintro _ _ _ ⟨⟩; exact ⟨⟨⟩⟩
  hW :=
    (hasCardinalLT_of_finite _ κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
        (fun (_ : Unit) ↦ ⟨Arrow.mk (𝟙 j), ⟨⟨⟩⟩⟩) (by
      rintro ⟨f, hf⟩
      refine ⟨⟨⟩, ?_⟩
      ext
      exact ((MorphismProperty.ofHoms_iff _ _).1
        ((MorphismProperty.arrow_mk_mem_toSet_iff _ _).1 hf)).choose_spec.symm)
  hP :=
    (hasCardinalLT_of_finite _ κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
      (fun (_ : Unit) ↦ ⟨j, by simp⟩) (fun ⟨k, hk⟩ ↦ ⟨⟨⟩, by aesop⟩)

instance (j : J) : Finite (Subtype (Diagram.single (κ := κ) j).P) :=
  Finite.of_surjective (fun (_ : Unit) ↦ ⟨j, by simp⟩)
    (by rintro ⟨_, ⟨⟩⟩; exact ⟨⟨⟩, rfl⟩)

variable {J κ} in
/-- The diagram with a unique terminal object containing a single object
(and its identity morphism). -/
noncomputable def DiagramWithUniqueTerminal.single (j : J) :
    DiagramWithUniqueTerminal J κ where
  toDiagram := .single j
  top := j
  isTerminal := by
    refine .ofExistsUnique ⟨⟨⟩⟩ (fun _ h ↦ ?_) (fun _ h₁ _ _ h₂ h₃ ↦ ? _) (fun _ _ _ h ↦ ?_)
    · simp only [Diagram.single_P, ObjectProperty.singleton_iff] at h
      subst h
      exact ⟨𝟙 _, ⟨⟨⟩⟩⟩
    · simp only [Diagram.single_P, ObjectProperty.singleton_iff] at h₁
      subst h₁
      obtain ⟨⟨⟩⟩ := h₂
      obtain ⟨⟨⟩⟩ := h₃
      simp
    · obtain ⟨⟨⟩⟩ := h
      exact ⟨𝟙 _, 𝟙 _, ⟨⟨⟩⟩, ⟨⟨⟩⟩, by simp⟩
  uniq_terminal := by rintro _ ⟨⟨⟩⟩; rfl

variable {J κ} in
/-- The union of a `κ`-bounded family of `κ`-bounded diagrams. -/
@[simps]
def Diagram.iSup {ι : Type*} (D : ι → Diagram J κ) (hι : HasCardinalLT ι κ) :
    Diagram J κ where
  W := ⨆ (i : ι), (D i).W
  P := ⨆ (i : ι), (D i).P
  src hf := by
    simp only [MorphismProperty.iSup_iff, iSup_apply, iSup_Prop_eq] at hf ⊢
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, (D i).src hi⟩
  tgt hf := by
    simp only [MorphismProperty.iSup_iff, iSup_apply, iSup_Prop_eq] at hf ⊢
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, (D i).tgt hi⟩
  hW := .iSup (fun i ↦ (D i).hW) hι
  hP := .iSup (fun i ↦ (D i).hP) hι

variable {J κ} in
/-- The union of two `κ`-bounded diagrams. -/
@[simps]
def Diagram.sup (D₁ D₂ : Diagram J κ) :
    Diagram J κ where
  W := D₁.W ⊔ D₂.W
  P := D₁.P ⊔ D₂.P
  src := by
    rintro _ _ _ (h | h)
    · exact Or.inl (D₁.src h)
    · exact Or.inr (D₂.src h)
  tgt := by
    rintro _ _ _ (h | h)
    · exact Or.inl (D₁.tgt h)
    · exact Or.inr (D₂.tgt h)
  hW := .sup D₁.hW D₂.hW (Cardinal.IsRegular.aleph0_le Fact.out)
  hP := .sup D₁.hP D₂.hP (Cardinal.IsRegular.aleph0_le Fact.out)

end exists_cardinal_directed

end IsCardinalFiltered

end CategoryTheory
