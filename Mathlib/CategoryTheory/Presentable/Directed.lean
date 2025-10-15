/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# `κ`-filtered categories and `κ`-directed poset

-/

universe w

lemma hasCardinalLT_of_finite
    (X : Type*) [Finite X] (κ : Cardinal) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT X κ :=
  .of_le (by rwa [hasCardinalLT_aleph0_iff]) hκ

lemma hasCardinalLT_punit (κ : Cardinal) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT PUnit κ :=
  hasCardinalLT_of_finite _ _ hκ

namespace CategoryTheory

namespace IsCardinalFiltered

variable (J : Type w) [SmallCategory J] (κ : Cardinal.{w})

namespace ExistsDirected

@[ext]
structure PreDiagram where
  W : MorphismProperty J
  P : ObjectProperty J
  src {i j : J} {f : i ⟶ j} : W f → P i
  tgt {i j : J} {f : i ⟶ j} : W f → P j
  hW : HasCardinalLT W.toSet κ
  hP : HasCardinalLT (Subtype P) κ

namespace PreDiagram

variable {J κ}

structure Terminal (D : PreDiagram J κ) (e : J) where
  prop_id : D.W (𝟙 e)
  lift {j : J} (hj : D.P j) : j ⟶ e
  hlift {j : J} (hj : D.P j) : D.W (lift hj)
  uniq {j : J} (hj : D.P j) {φ : j ⟶ e} (hφ : D.W φ) : lift hj = φ
  comm {i j : J} (f : i ⟶ j) (hf : D.W f) : f ≫ lift (D.tgt hf) = lift (D.src hf)

namespace Terminal

attribute [reassoc] Terminal.comm

variable {D : PreDiagram J κ} {e : J}

lemma prop (h : D.Terminal e) : D.P e := D.src (h.prop_id)

@[simp]
lemma lift_self (h : D.Terminal e) : h.lift h.prop = 𝟙 e := h.uniq _ h.prop_id

instance : Subsingleton (D.Terminal e) where
  allEq h₁ h₂ := by
    have : @h₁.lift = @h₂.lift := by
      ext j hj
      exact h₁.uniq hj (h₂.hlift hj)
    cases h₁
    cases h₂
    aesop

noncomputable def ofExistsUnique (prop_id : D.W (𝟙 e))
    (h₁ : ∀ ⦃j : J⦄ (_ : D.P j), ∃ (lift : j ⟶ e), D.W lift)
    (h₂ : ∀ ⦃j : J⦄ (_ : D.P j) (l₁ l₂ : j ⟶ e), D.W l₁ → D.W l₂ → l₁ = l₂)
    (h₃ : ∀ ⦃i j : J⦄ (f : i ⟶ j) (_ : D.W f), ∃ (li : i ⟶ e) (lj : j ⟶ e),
      D.W li ∧ D.W lj ∧ f ≫ lj = li) :
    D.Terminal e where
  prop_id := prop_id
  lift hj := (h₁ hj).choose
  hlift hj := (h₁ hj).choose_spec
  uniq hj φ hφ := h₂ hj (h₁ hj).choose φ (h₁ hj).choose_spec hφ
  comm _ hf := by
    obtain ⟨li, lj, hli, hlj, fac⟩ := h₃ _ hf
    rw [h₂ (D.src hf) _ li (h₁ (D.src hf)).choose_spec hli,
      h₂ (D.tgt hf) _ lj (h₁ (D.tgt hf)).choose_spec hlj, fac]

end Terminal

end PreDiagram

structure Diagram extends PreDiagram J κ where
  e : J
  terminal : toPreDiagram.Terminal e
  uniq_terminal (j : J) (hj : toPreDiagram.Terminal j) : j = e

@[ext]
lemma Diagram.ext {D₁ D₂ : Diagram J κ} (hW : D₁.W = D₂.W) (hP : D₁.P = D₂.P) : D₁ = D₂ := by
  obtain ⟨D₁, e, h₁, h₁'⟩ := D₁
  obtain ⟨D₂, e', h₂, h₂'⟩ := D₂
  obtain rfl : D₁ = D₂ := by aesop
  obtain rfl : e = e' := h₂' _ h₁
  obtain rfl : h₁ = h₂ := by subsingleton
  rfl

instance : PartialOrder (Diagram J κ) where
  le D₁ D₂ := D₁.W ≤ D₂.W ∧ D₁.P ≤ D₂.P
  le_refl _ := ⟨by rfl, by rfl⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩
  le_antisymm _ _ h₁ h₂ := by
    ext : 1
    · exact le_antisymm h₁.1 h₂.1
    · exact le_antisymm h₁.2 h₂.2

section

variable {J κ}

def functorMap {D₁ D₂ : Diagram J κ} (h : D₁ ≤ D₂) : D₁.e ⟶ D₂.e :=
  D₂.terminal.lift (h.2 _ D₁.terminal.prop)

@[simp]
lemma functorMap_id (D : Diagram J κ) : functorMap (le_refl D) = 𝟙 D.e := by
  simp [functorMap]

@[reassoc (attr := simp)]
lemma functorMap_comp {D₁ D₂ D₃ : Diagram J κ} (h₁₂ : D₁ ≤ D₂) (h₂₃ : D₂ ≤ D₃) :
    functorMap h₁₂ ≫ functorMap h₂₃ = functorMap (h₁₂.trans h₂₃) :=
  D₃.terminal.comm _ (h₂₃.1 _ (D₂.terminal.hlift _))

end

@[simps]
def functor : Diagram J κ ⥤ J where
  obj D := D.e
  map h := functorMap (leOfHom h)

variable [Fact κ.IsRegular]

variable {J κ} in
@[simps]
def PreDiagram.single (j : J) : PreDiagram J κ where
  W := .ofHoms (fun (_ : Unit) ↦ 𝟙 j)
  P := .ofObj (fun (_ : Unit) ↦ j)
  src := by rintro _ _ _ ⟨⟩; exact ⟨⟨⟩⟩
  tgt := by rintro _ _ _ ⟨⟩; exact ⟨⟨⟩⟩
  hW :=
    (hasCardinalLT_punit κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
        (f := fun (_ : Unit) ↦ ⟨Arrow.mk (𝟙 j), ⟨⟨⟩⟩⟩) (by
      rintro ⟨f, hf⟩
      refine ⟨⟨⟩, ?_⟩
      ext
      exact ((MorphismProperty.ofHoms_iff _ _).1
        ((MorphismProperty.arrow_mk_mem_toSet_iff _ _).1 hf)).choose_spec.symm)
  hP :=
    (hasCardinalLT_punit κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
      (f := fun (_ : Unit) ↦ ⟨j, by simp⟩) (fun ⟨k, hk⟩ ↦ ⟨⟨⟩, by aesop⟩)

variable {J κ} in
def Diagram.single (j : J) : Diagram J κ where
  toPreDiagram := .single j
  e := j
  terminal :=
    { prop_id := ⟨⟨⟩⟩
      lift := by rintro j hj; simp at hj; subst hj; exact 𝟙 _
      hlift := by rintro j hj; simp at hj; subst hj; exact ⟨⟨⟩⟩
      uniq := by rintro j hj φ hφ; simp at hj; subst hj; obtain ⟨⟨⟩⟩ := hφ; simp
      comm := by rintro _ _ f hf; obtain ⟨⟨⟩⟩ := hf; simp }
  uniq_terminal := by rintro _ ⟨⟨⟩⟩; rfl

variable {J κ} in
@[simps]
def PreDiagram.iSup {ι : Type*} (D : ι → PreDiagram J κ) (hι : HasCardinalLT ι κ) :
    PreDiagram J κ where
  W := ⨆ (i : ι), (D i).W
  P := ⨆ (i : ι), (D i).P
  src hf := by
    simp at hf ⊢
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, (D i).src hi⟩
  tgt hf := by
    simp at hf ⊢
    obtain ⟨i, hi⟩ := hf
    exact ⟨i, (D i).tgt hi⟩
  hW := by
    sorry
  hP := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    sorry

variable {J κ} in
@[simps]
def PreDiagram.max (D₁ D₂ : PreDiagram J κ) :
    PreDiagram J κ where
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
  hW := sorry
  hP := sorry

variable [IsCardinalFiltered J κ]
  (hJ : ∀ (e : J), ∃ (m : J) (_ : e ⟶ m), IsEmpty (m ⟶ e))

include hJ in
lemma isCardinalFiltered : IsCardinalFiltered (Diagram J κ) κ :=
  isCardinalFiltered_preorder _ _ (fun ι D hι ↦ by
    simp only [← hasCardinalLT_iff_cardinal_mk_lt] at hι
    choose m₀ t₀ hm₀ using fun i ↦ hJ (D i).e
    let m₁ := IsCardinalFiltered.max m₀ hι
    let t₁ (i : ι) : m₀ i ⟶ m₁ := IsCardinalFiltered.toMax m₀ hι i
    let u (i : ι) : (D i).e ⟶ m₁ := t₀ i ≫ t₁ i
    obtain ⟨m₂, t₂, hm₂⟩ : ∃ (m₂ : J) (t₂ : m₁ ⟶ m₂),
      ∀ (i₁ i₂ : ι) (j : J) (hj₁ : (D i₁).P j) (hj₂ : (D i₂).P j),
        (D i₁).terminal.lift hj₁ ≫ u i₁ ≫ t₂ = (D i₂).terminal.lift hj₂ ≫ u i₂ ≫ t₂ := by
      sorry
    let φ (x : (Σ (i : ι), (Subtype (D i).P))) : x.2.1 ⟶ m₂ :=
      (D x.1).terminal.lift x.2.2 ≫ u x.1 ≫ t₂
    let D₀ := PreDiagram.iSup (fun i ↦ (D i).toPreDiagram) hι
    have hD₀ {i : ι} : ¬ (D i).P m₂ := fun hi ↦
      (hm₀ i).false (t₁ _ ≫ t₂ ≫ (D i).terminal.lift hi)
    let D₁ := D₀.max (.single m₂)
    let D₂ : PreDiagram J κ :=
      { W := D₁.W ⊔ .ofHoms φ
        P := D₁.P
        src := by
          simp [D₁, D₀]
          rintro _ _ _ ((hf | ⟨⟨⟩⟩) | ⟨i, j, hj⟩)
          · simp at hf
            obtain ⟨i, hf⟩ := hf
            exact Or.inl ⟨i, (D i).src hf⟩
          · exact Or.inr rfl
          · exact Or.inl ⟨i, hj⟩
        tgt := by
          simp [D₁, D₀]
          rintro _ _ _ ((hf | ⟨⟨⟩⟩) | ⟨i, j, hj⟩)
          · simp at hf
            obtain ⟨i, hf⟩ := hf
            exact Or.inl ⟨i, (D i).tgt hf⟩
          · exact Or.inr rfl
          · exact Or.inr rfl
        hW := sorry
        hP := sorry }
    have hD₂ {f : m₂ ⟶ m₂} (hf : D₂.W f) : f = 𝟙 _ := by
      simp [D₂, D₁, D₀] at hf
      obtain ((hf | ⟨⟨⟩⟩) | hf) := hf
      · simp at hf
        obtain ⟨i, hi⟩ := hf
        exact (hD₀ ((D i).src hi)).elim
      · rfl
      · rw [MorphismProperty.ofHoms_iff] at hf
        obtain ⟨⟨i, j, hj⟩, hi⟩ := hf
        obtain rfl : m₂ = j := congr_arg Arrow.leftFunc.obj hi
        exact (hD₀ hj).elim
    let he : D₂.Terminal m₂ := by
      have H {i : ι} {j : J} (hj : (D i).P j) {f : j ⟶ m₂} (hf : D₂.W f) :
          f = φ ⟨i, ⟨_, hj⟩⟩ := by
        simp [D₂, D₁, D₀] at hf
        obtain ((hf | ⟨⟨⟩⟩) | ⟨⟨i', j, hj'⟩⟩) := hf
        · simp at hf
          obtain ⟨i, hf⟩ := hf
          exact (hD₀ ((D i).tgt hf)).elim
        · exact (hD₀ hj).elim
        · apply hm₂
      refine .ofExistsUnique ?_ ?_ ?_ ?_
      · exact Or.inl (Or.inr ⟨⟨⟩⟩)
      · simp [D₂, D₁, D₀]
        rintro j (⟨i, hi⟩ | rfl)
        · exact ⟨φ ⟨i, _, hi⟩, Or.inr (.mk _)⟩
        · exact ⟨𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩)⟩
      · intro j hj l₁ l₂ hl₁ hl₂
        simp [D₂, D₁, D₀] at hj
        obtain (⟨i, hj⟩ | rfl) := hj
        · obtain rfl := H hj hl₁
          obtain rfl := H hj hl₂
          rfl
        · rw [hD₂ hl₁, hD₂ hl₂]
      · sorry
    let D₂' : Diagram J κ :=
      { toPreDiagram := D₂
        e := _
        terminal := he
        uniq_terminal j hj := by
          have := hj.prop
          simp [D₂, D₁, D₀] at this
          obtain (⟨i, hi⟩ | rfl) := this
          · exfalso
            exact (hm₀ i).false (t₁ _ ≫ t₂ ≫ hj.lift
              (by simp [D₂, D₁]) ≫ (D i).terminal.lift hi)
          · rfl }
    refine ⟨D₂', fun i ↦ ⟨?_, ?_⟩⟩
    · exact le_trans (le_trans (le_trans (by rfl) (le_iSup _ i))
        le_sup_left) le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ i)) le_sup_left)

end ExistsDirected

lemma exists_cardinal_directed [Fact κ.IsRegular] [IsCardinalFiltered J κ] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α κ)
      (F : α ⥤ J), F.Final := sorry

end IsCardinalFiltered

end CategoryTheory
