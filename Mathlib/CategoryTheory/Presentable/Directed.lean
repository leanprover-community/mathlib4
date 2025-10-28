/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Products.Unitor
import Mathlib.Data.Finite.Sigma

/-!
# `κ`-filtered categories and `κ`-directed poset

In this file, we formalize the proof by Deligne (SGA 4 I 8.1.6) that for
any (small) filtered category `J`, there exists a final functor `F : α ⥤ J`
where `α` is a directed partially ordered set (`IsFiltered.exists_directed`).
The construction applies more generally to `κ`-filtered categories and
`κ`-directed posets (`IsCardinalFiltered.exists_cardinal_directed`).

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

universe u v w

lemma CategoryTheory.MorphismProperty.toSet_iSup {C : Type*} [Category C]
    {ι : Type*} (W : ι → MorphismProperty C) :
    (⨆ i , W i).toSet = ⋃ i, (W i).toSet := by
  ext
  simp [MorphismProperty.toSet]

lemma CategoryTheory.MorphismProperty.toSet_max {C : Type*} [Category C]
    (W₁ W₂ : MorphismProperty C) :
    (W₁ ⊔ W₂).toSet = W₁.toSet ∪ W₂.toSet := rfl

section

open CategoryTheory Limits

lemma hasCardinalLT_toSet_morphismPropertyOfHoms {C : Type*} [Category C]
    {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i) {κ : Cardinal}
    (h : HasCardinalLT ι κ) : HasCardinalLT (MorphismProperty.ofHoms f).toSet κ :=
  h.of_surjective (fun i ↦ ⟨Arrow.mk (f i), ⟨i⟩⟩) (by
    rintro ⟨f, hf⟩
    rw [MorphismProperty.mem_toSet_iff, MorphismProperty.ofHoms_iff] at hf
    obtain ⟨i, hf⟩ := hf
    obtain rfl : f = _ := hf
    exact ⟨i, rfl⟩)

lemma hasCardinalLT_subtype_objectPropertyOfObj {C : Type*} [Category C]
    {ι : Type*} (X : ι → C) {κ : Cardinal}
    (h : HasCardinalLT ι κ) : HasCardinalLT (Subtype (ObjectProperty.ofObj X)) κ :=
  h.of_surjective (fun i ↦ ⟨X i, by simp⟩) (by rintro ⟨_, ⟨i⟩⟩; exact ⟨i, rfl⟩)

end

namespace CategoryTheory

open Limits

namespace IsCardinalFiltered

instance prod (J₁ J₂ : Type*) [Category J₁] [Category J₂]
    (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalFiltered J₁ κ] [IsCardinalFiltered J₂ κ] :
    IsCardinalFiltered (J₁ × J₂) κ where
  nonempty_cocone {C _} F hC := ⟨by
    let c₁ := cocone (F ⋙ Prod.fst _ _) hC
    let c₂ := cocone (F ⋙ Prod.snd _ _) hC
    exact
      { pt := (c₁.pt, c₂.pt)
        ι.app i := (c₁.ι.app i, c₂.ι.app i)
        ι.naturality i j f := by
          ext
          · simpa using c₁.w f
          · simpa using c₂.w f}⟩

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
  hW : HasCardinalLT W.toSet κ
  hP : HasCardinalLT (Subtype P) κ

namespace Diagram

variable {J κ}

/-- Given a `κ`-bounded diagram `D` in a category `J`, an object `e : J`
is terminal if for any object `j` of `D`, there is a unique morphism `j ⟶ e` in `D`,
that these unique morphisms are compatible with precomposition with morphims in `D`,
and that `𝟙 e` belongs to `D`. -/
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
  hW := by
    rw [MorphismProperty.toSet_iSup]
    exact hasCardinalLT_iUnion _ hι (fun i ↦ (D i).hW)
  hP := hasCardinalLT_subtype_iSup _ hι (fun i ↦ (D i).hP)

variable {J κ} in
/-- The union of two `κ`-bounded diagrams. -/
@[simps]
def Diagram.max (D₁ D₂ : Diagram J κ) :
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
  hW := hasCardinalLT_union (Cardinal.IsRegular.aleph0_le Fact.out) D₁.hW D₂.hW
  hP := hasCardinalLT_union (Cardinal.IsRegular.aleph0_le Fact.out) D₁.hP D₂.hP

variable [IsCardinalFiltered J κ]
  (hJ : ∀ (e : J), ∃ (m : J) (_ : e ⟶ m), IsEmpty (m ⟶ e))

include hJ

lemma isCardinalFiltered_aux
    {ι : Type w} (D : ι → DiagramWithUniqueTerminal J κ) (hι : HasCardinalLT ι κ) :
    ∃ (m : J) (u : ∀ i, (D i).top ⟶ m), (∀ (i : ι), IsEmpty (m ⟶ (D i).top)) ∧
      ∀ (i₁ i₂ : ι) (j : J) (hj₁ : (D i₁).P j) (hj₂ : (D i₂).P j),
        (D i₁).isTerminal.lift hj₁ ≫ u i₁ = (D i₂).isTerminal.lift hj₂ ≫ u i₂ := by
  choose m₀ t₀ hm₀ using fun i ↦ hJ (D i).top
  let m₁ := IsCardinalFiltered.max m₀ hι
  let t₁ (i : ι) : m₀ i ⟶ m₁ := IsCardinalFiltered.toMax m₀ hι i
  let u (i : ι) : (D i).top ⟶ m₁ := t₀ i ≫ t₁ i
  let S := { x : ι × ι × J // (D x.1).P x.2.2 ∧ (D x.2.1).P x.2.2 }
  let shape : MultispanShape.{w, w} :=
    { L := { x : ι × ι × J // (D x.1).P x.2.2 ∧ (D x.2.1).P x.2.2 }
      R := PUnit
      fst _ := ⟨⟩
      snd _ := ⟨⟩ }
  let index : MultispanIndex shape J :=
    { left x := x.1.2.2
      right _ := m₁
      fst x := (D x.1.1).isTerminal.lift x.2.1 ≫ u x.1.1
      snd x := (D x.1.2.1).isTerminal.lift x.2.2 ≫ u x.1.2.1 }
  have hκ : Cardinal.aleph0 ≤ κ := Cardinal.IsRegular.aleph0_le Fact.out
  have hL : HasCardinalLT shape.L κ := by
    have : HasCardinalLT (ι × (Σ (i : ι), Subtype (D i).P)) κ :=
      hasCardinalLT_prod hκ hι (hasCardinalLT_sigma _ _ hι (fun i ↦ (D i).hP))
    refine this.of_injective (fun ⟨⟨i₁, i₂, j⟩, h₁, h₂⟩ ↦ ⟨i₁, i₂, ⟨j, h₂⟩⟩) ?_
    rintro ⟨⟨i₁, i₂, j⟩, _, _⟩ ⟨⟨i₁', i₂', j'⟩, _, _⟩ h
    rw [Prod.ext_iff, Sigma.ext_iff] at h
    dsimp at h
    obtain rfl : i₁ = i₁' := h.1
    obtain rfl : i₂ = i₂' := h.2.1
    obtain rfl : j = j' := by simpa using h
    rfl
  have hR : HasCardinalLT shape.R κ := hasCardinalLT_of_finite _ _ hκ
  have hshape : HasCardinalLT (Arrow (WalkingMultispan shape)) κ := by
    rw [hasCardinalLT_iff_of_equiv (WalkingMultispan.arrowEquiv shape),
      hasCardinalLT_sum_iff _ _ _ hκ, hasCardinalLT_sum_iff _ _ _ hκ,
      hasCardinalLT_iff_of_equiv (WalkingMultispan.equiv shape),
      hasCardinalLT_sum_iff _ _ _ hκ]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> assumption
  let c : Multicofork _ := IsCardinalFiltered.cocone index.multispan hshape
  exact ⟨c.pt, fun i ↦ u i ≫ c.π ⟨⟩,
    fun i ↦ ⟨fun hi ↦ (hm₀ i).false (t₁ i ≫ c.π ⟨⟩ ≫ hi)⟩,
    fun i₁ i₂ j h₁ h₂ ↦ by simpa [index, shape] using c.condition ⟨⟨i₁, i₂, j⟩, h₁, h₂⟩⟩

lemma isCardinalFiltered : IsCardinalFiltered (DiagramWithUniqueTerminal J κ) κ :=
  isCardinalFiltered_preorder _ _ (fun ι D hι ↦ by
    have hκ : Cardinal.aleph0 ≤ κ := Cardinal.IsRegular.aleph0_le Fact.out
    simp only [← hasCardinalLT_iff_cardinal_mk_lt] at hι
    obtain ⟨m, u, hm₀, hm⟩ := isCardinalFiltered_aux J κ hJ D hι
    let φ (x : (Σ (i : ι), (Subtype (D i).P))) : x.2.1 ⟶ m :=
      (D x.1).isTerminal.lift x.2.2 ≫ u x.1
    have hD {i : ι} : ¬ (D i).P m := fun hi ↦ (hm₀ i).false ((D i).isTerminal.lift hi)
    let D₀ := Diagram.iSup (fun i ↦ (D i).toDiagram) hι
    let D₁ := D₀.max (.single m)
    let D₂ : Diagram J κ :=
      { W := D₁.W ⊔ .ofHoms φ
        P := D₁.P
        src := by
          simp only [Diagram.max_W, Diagram.iSup_W, Diagram.single_W, Diagram.max_P, Pi.sup_apply,
            Diagram.iSup_P, iSup_apply, iSup_Prop_eq, Diagram.single_P,
            ObjectProperty.singleton_iff, sup_Prop_eq, D₁, D₀]
          rintro _ _ _ ((hf | ⟨⟨⟩⟩) | ⟨i, j, hj⟩)
          · simp only [MorphismProperty.iSup_iff] at hf
            obtain ⟨i, hf⟩ := hf
            exact Or.inl ⟨i, (D i).src hf⟩
          · exact Or.inr rfl
          · exact Or.inl ⟨i, hj⟩
        tgt := by
          simp only [Diagram.max_W, Diagram.iSup_W, Diagram.single_W, Diagram.max_P, Pi.sup_apply,
            Diagram.iSup_P, iSup_apply, iSup_Prop_eq, Diagram.single_P,
            ObjectProperty.singleton_iff, sup_Prop_eq, D₁, D₀]
          rintro _ _ _ ((hf | ⟨⟨⟩⟩) | ⟨i, j, hj⟩)
          · simp only [MorphismProperty.iSup_iff] at hf
            obtain ⟨i, hf⟩ := hf
            exact Or.inl ⟨i, (D i).tgt hf⟩
          · exact Or.inr rfl
          · exact Or.inr rfl
        hW := by
          rw [MorphismProperty.toSet_max]
          exact hasCardinalLT_union hκ D₁.hW
            (hasCardinalLT_toSet_morphismPropertyOfHoms _
              (hasCardinalLT_sigma _ _ hι (fun i ↦ (D i).hP)))
        hP := hasCardinalLT_subtype_max hκ
                (hasCardinalLT_subtype_iSup _ hι (fun i ↦ (D i).hP))
                (hasCardinalLT_of_finite _ _ hκ) }
    have hD₂ {f : m ⟶ m} (hf : D₂.W f) : f = 𝟙 _ := by
      simp only [Diagram.max_W, Diagram.iSup_W, Diagram.single_W, D₁, D₀, D₂] at hf
      obtain ((hf | ⟨⟨⟩⟩) | hf) := hf
      · simp only [MorphismProperty.iSup_iff] at hf
        obtain ⟨i, hi⟩ := hf
        exact (hD ((D i).src hi)).elim
      · rfl
      · rw [MorphismProperty.ofHoms_iff] at hf
        obtain ⟨⟨i, j, hj⟩, hi⟩ := hf
        obtain rfl : m = j := congr_arg Arrow.leftFunc.obj hi
        exact (hD hj).elim
    let he : D₂.IsTerminal m := by
      have H {i : ι} {j : J} (hj : (D i).P j) {f : j ⟶ m} (hf : D₂.W f) :
          f = φ ⟨i, ⟨_, hj⟩⟩ := by
        simp only [Diagram.max_W, Diagram.iSup_W, Diagram.single_W, D₁, D₀, D₂] at hf
        obtain ((hf | ⟨⟨⟩⟩) | ⟨⟨i', j, hj'⟩⟩) := hf
        · simp only [MorphismProperty.iSup_iff] at hf
          obtain ⟨i, hf⟩ := hf
          exact (hD ((D i).tgt hf)).elim
        · exact (hD hj).elim
        · apply hm
      refine .ofExistsUnique ?_ ?_ ?_ ?_
      · exact Or.inl (Or.inr ⟨⟨⟩⟩)
      · simp only [Diagram.max_P, Pi.sup_apply, Diagram.iSup_P, iSup_apply, iSup_Prop_eq,
          Diagram.single_P, ObjectProperty.singleton_iff, sup_Prop_eq, Diagram.max_W,
          Diagram.iSup_W, Diagram.single_W, D₁, D₀, D₂]
        rintro j (⟨i, hi⟩ | rfl)
        · exact ⟨φ ⟨i, _, hi⟩, Or.inr (.mk _)⟩
        · exact ⟨𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩)⟩
      · intro j hj l₁ l₂ hl₁ hl₂
        simp only [Diagram.max_P, Pi.sup_apply, Diagram.iSup_P, iSup_apply, iSup_Prop_eq,
          Diagram.single_P, ObjectProperty.singleton_iff, sup_Prop_eq, D₁, D₀, D₂] at hj
        obtain (⟨i, hj⟩ | rfl) := hj
        · obtain rfl := H hj hl₁
          obtain rfl := H hj hl₂
          rfl
        · rw [hD₂ hl₁, hD₂ hl₂]
      · rintro j k f ((hf | ⟨⟨⟩⟩) | ⟨⟨i, j, hj⟩⟩)
        · simp only [Diagram.iSup_W, MorphismProperty.iSup_iff, D₀] at hf
          obtain ⟨i, hf⟩ := hf
          exact ⟨φ ⟨i, j, (D i).src hf⟩, φ ⟨i, k, (D i).tgt hf⟩, Or.inr ⟨_⟩, Or.inr ⟨_⟩,
            by simp [φ, (D i).isTerminal.comm_assoc _ hf]⟩
        · exact ⟨𝟙 _, 𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩), Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩
        · exact ⟨φ ⟨i, j, hj⟩, 𝟙 _, Or.inr ⟨_⟩, Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩
    let D₂' : DiagramWithUniqueTerminal J κ :=
      { toDiagram := D₂
        top := _
        isTerminal := he
        uniq_terminal j hj := by
          have := hj.prop
          simp only [Diagram.max_P, Pi.sup_apply, Diagram.iSup_P, iSup_apply, iSup_Prop_eq,
            Diagram.single_P, ObjectProperty.singleton_iff, sup_Prop_eq, D₁, D₀, D₂] at this
          obtain (⟨i, hi⟩ | rfl) := this
          · exfalso
            exact (hm₀ i).false (hj.lift (by simp [D₂, D₁]) ≫ (D i).isTerminal.lift hi)
          · rfl }
    refine ⟨D₂', fun i ↦ ⟨?_, ?_⟩⟩
    · exact le_trans (le_trans (le_trans (by rfl) (le_iSup _ i)) le_sup_left) le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ i)) le_sup_left)

lemma final_functor : (functor J κ).Final := by
  have hκ : Cardinal.aleph0 ≤ κ := Cardinal.IsRegular.aleph0_le Fact.out
  have := isCardinalFiltered J κ hJ
  have := isFiltered_of_isCardinalFiltered J κ
  have := isFiltered_of_isCardinalFiltered (DiagramWithUniqueTerminal J κ) κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun j ↦ ⟨.single j, ⟨𝟙 _⟩⟩, fun {j D} (f₁ f₂ : j ⟶ D.top) ↦ ?_⟩
  obtain ⟨m₀, t, hm₀⟩ := hJ D.top
  obtain ⟨m₁, u, hu⟩ : ∃ (m₁ : J) (u : m₀ ⟶ m₁), f₁ ≫ t ≫ u = f₂ ≫ t ≫ u :=
    ⟨_, IsFiltered.coeqHom (f₁ ≫ t) (f₂ ≫ t),
      by simpa using IsFiltered.coeq_condition (f₁ ≫ t) (f₂ ≫ t)⟩
  have h₁ : ¬ (D.P m₁) := fun h₁ ↦ hm₀.false (u ≫ D.isTerminal.lift h₁)
  let φ (x : Subtype D.P) : x.1 ⟶ m₁ := D.isTerminal.lift x.2 ≫ t ≫ u
  let D₀ := D.toDiagram.max (.single m₁)
  let D₁ : Diagram J κ :=
    { W := D₀.W ⊔ .ofHoms φ
      P := D₀.P
      src := by
        rintro i j f (hf | ⟨⟨j, hj⟩⟩)
        · exact D₀.src hf
        · exact Or.inl hj
      tgt := by
        rintro i j f (hf | ⟨⟨j, hj⟩⟩)
        · exact D₀.tgt hf
        · exact Or.inr ⟨⟨⟩⟩
      hW :=
        hasCardinalLT_union hκ
          (hasCardinalLT_union hκ D.hW
            (hasCardinalLT_toSet_morphismPropertyOfHoms _
            (hasCardinalLT_of_finite _ _ hκ)))
          (hasCardinalLT_toSet_morphismPropertyOfHoms _ D.hP)
      hP :=
        hasCardinalLT_union hκ D.hP
          (hasCardinalLT_subtype_objectPropertyOfObj _
            (hasCardinalLT_of_finite _ _ hκ)) }
  have h₂ {j : J} (hj : D.P j) {f : j ⟶ m₁} (hf : D₁.W f) :
      f = φ ⟨_, hj⟩ := by
    obtain ((hf | ⟨⟨⟩⟩) | ⟨⟨⟩⟩) := hf
    · exact (h₁ (D.tgt hf)).elim
    · exact (h₁ hj).elim
    · rfl
  have h₃ {f : m₁ ⟶ m₁} (hf : D₁.W f) : f = 𝟙 _ := by
    obtain ((hf | ⟨⟨⟩⟩) | hf) := hf
    · exact (h₁ (D.src hf)).elim
    · rfl
    · rw [MorphismProperty.ofHoms_iff] at hf
      obtain ⟨⟨j, hj⟩, hf⟩ := hf
      obtain rfl : m₁ = j := congr_arg Arrow.leftFunc.obj hf
      exact (h₁ hj).elim
  let hm₁ : D₁.IsTerminal m₁ :=
    .ofExistsUnique (Or.inl (Or.inr ⟨⟨⟩⟩)) (by
        rintro j (hj | ⟨⟨⟨⟩⟩⟩)
        · exact ⟨φ ⟨_, hj⟩, Or.inr ⟨_⟩⟩
        · exact ⟨𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩)⟩) (by
        rintro j (hj | ⟨⟨⟨⟩⟩⟩) l₁ l₂ hl₁ hl₂
        · obtain rfl := h₂ hj hl₁
          obtain rfl := h₂ hj hl₂
          rfl
        · rw [h₃ hl₁, h₃ hl₂]) (by
      rintro j k f ((hf | ⟨⟨⟩⟩) | ⟨⟨j, hj⟩⟩)
      · exact ⟨φ ⟨_, D.src hf⟩, φ ⟨_, D.tgt hf⟩,
          Or.inr ⟨_⟩, Or.inr ⟨_⟩, D.isTerminal.comm_assoc _ hf _⟩
      · exact ⟨𝟙 _, 𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩), Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩
      · exact ⟨φ ⟨_, hj⟩, 𝟙 _, Or.inr ⟨_⟩, Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩)
  have lift_eq (j : J) (hj : D.P j) : hm₁.lift (Or.inl hj) = φ ⟨_, hj⟩ :=
    hm₁.uniq _ (Or.inr ⟨_⟩)
  let D₁' : DiagramWithUniqueTerminal J κ :=
    { toDiagram := D₁
      top := m₁
      isTerminal := hm₁
      uniq_terminal j hj := by
        obtain (hj' | ⟨⟨⟩⟩) := hj.prop
        · exact hm₀.elim (u ≫ hj.lift (Or.inr ⟨⟨⟩⟩) ≫ D.isTerminal.lift hj')
        · rfl}
  exact ⟨D₁', homOfLE ⟨le_sup_left.trans le_sup_left, le_sup_left⟩,
    by simpa [functorMap, D₁', lift_eq _ D.isTerminal.prop, φ]⟩

lemma aux :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α κ)
      (F : α ⥤ J), F.Final :=
  ⟨DiagramWithUniqueTerminal J κ, _, isCardinalFiltered J κ hJ,
    functor J κ, final_functor J κ hJ⟩

end exists_cardinal_directed


/-!
The previous lemma `IsCardinalFiltered.exists_cardinal_directed.aux`
is the particular case of the main lemma
`IsCardinalFiltered.exists_cardinal_directed` below in the particular
case the `κ`-filtered category `J` has no object `m : J` such that for any
object `j : J`, there exists a map `j ⟶ m`.

The general case is obtained by applying the previous result to
the cartesian product `J × κ.ord.toType`.
-/

@[stacks 0032]
lemma exists_cardinal_directed (J : Type w) [SmallCategory J] (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalFiltered J κ] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α κ)
      (F : α ⥤ J), F.Final := by
  have := isFiltered_of_isCardinalFiltered κ.ord.toType κ
  obtain ⟨α, _, _, F, _⟩ :=
    exists_cardinal_directed.aux (J × κ.ord.toType) κ (fun ⟨j, x⟩ ↦
      ⟨⟨j, Order.succ x⟩, (𝟙 _, homOfLE (Order.le_succ x)), ⟨fun ⟨_, f⟩ ↦ by
        have : NoMaxOrder κ.ord.toType :=
          Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
        exact not_isMax _ (Order.max_of_succ_le (leOfHom f))⟩⟩)
  exact ⟨_, _, inferInstance, F ⋙ Prod.fst _ _, inferInstance⟩

end IsCardinalFiltered

lemma IsFiltered.isDirected (α : Type w) [PartialOrder α] [IsFiltered α] :
    IsDirected α (· ≤ ·) where
  directed i j := ⟨max i j, leOfHom (leftToMax i j), leOfHom (rightToMax i j)⟩

attribute [local instance] Cardinal.fact_isRegular_aleph0 in
@[stacks 0032]
lemma IsFiltered.exists_directed
    (J : Type w) [SmallCategory J] [IsFiltered J] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (F : α ⥤ J), F.Final := by
  have := (isCardinalFiltered_aleph0_iff.{w} J).2 inferInstance
  obtain ⟨α, _, _, F, _⟩ := IsCardinalFiltered.exists_cardinal_directed J .aleph0
  have : IsFiltered α := by rwa [← isCardinalFiltered_aleph0_iff.{w}]
  exact ⟨α, _, IsFiltered.isDirected _, nonempty, F, inferInstance⟩

end CategoryTheory
