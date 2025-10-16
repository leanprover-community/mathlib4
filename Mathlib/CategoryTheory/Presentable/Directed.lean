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
(see `CategoryTheory.IsCardinalFiltered.exists_cardinal_directed.Diagram`)
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

lemma hasCardinalLT_of_finite
    (X : Type*) [Finite X] (κ : Cardinal) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT X κ :=
  .of_le (by rwa [hasCardinalLT_aleph0_iff]) hκ

lemma hasCardinalLT_punit (κ : Cardinal) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT PUnit κ :=
  hasCardinalLT_of_finite _ _ hκ

lemma Cardinal.mk_surjective :
    Function.Surjective (Cardinal.mk : Type w → Cardinal) := by
  rintro ⟨_⟩; exact ⟨_, rfl⟩

lemma hasCardinalLT_sigma' {ι : Type w} (α : ι → Type w) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hα : ∀ i, HasCardinalLT (α i) κ) :
    HasCardinalLT (Σ i, α i) κ := by
  have hκ : Cardinal.aleph0 ≤ κ := Cardinal.IsRegular.aleph0_le Fact.out
  obtain hκ | rfl := hκ.lt_or_eq
  · obtain ⟨κ₀, h₁, h₂, h₃, h₄⟩ : ∃ (κ₀ : Cardinal), Cardinal.aleph0 ≤ κ₀ ∧ κ₀ < κ ∧
      Cardinal.mk ι ≤ κ₀ ∧ ∀ i, Cardinal.mk (α i) ≤ κ₀ := sorry
    obtain ⟨X, rfl⟩ := κ₀.mk_surjective
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    obtain ⟨φ⟩ := h₃
    let ψ (i : ι) : α i ↪ X := (h₄ i).some
    refine lt_of_le_of_lt ?_ h₂
    trans Cardinal.mk (X × X)
    · refine ⟨⟨fun ⟨i, a⟩ ↦ ⟨φ i, ψ i a⟩, fun ⟨i, a⟩ ⟨j, b⟩ h ↦ ?_⟩⟩
      rw [Prod.ext_iff] at h
      obtain rfl : i = j := φ.injective h.1
      obtain rfl : a = b := (ψ i).injective h.2
      rfl
    · rw [← Cardinal.mul_def]
      exact (Cardinal.mul_le_max_of_aleph0_le_left h₁).trans (by simp)
  · simp only [hasCardinalLT_aleph0_iff] at hι hα ⊢
    infer_instance

@[simp]
lemma hasCardinalLT_lift_iff (X : Type v) (κ : Cardinal.{w}) :
    HasCardinalLT X (Cardinal.lift.{u} κ) ↔ HasCardinalLT X κ := by
  simp [HasCardinalLT, ← (Cardinal.lift_strictMono.{max v w, max u}).lt_iff_lt]

@[simp]
lemma hasCardinalLT_ulift_iff (X : Type v) (κ : Cardinal.{w}) :
    HasCardinalLT (ULift.{u} X) κ ↔ HasCardinalLT X κ :=
  hasCardinalLT_iff_of_equiv Equiv.ulift κ

lemma Cardinal.IsRegular.lift {κ : Cardinal.{w}} (hκ : κ.IsRegular) :
    (Cardinal.lift.{u} κ).IsRegular := by
  obtain ⟨h₁, h₂⟩ := hκ
  constructor
  · simpa
  · rwa [← Cardinal.lift_ord, ← Ordinal.lift_cof, lift_le]

lemma hasCardinalLT_sigma {ι : Type u} (α : ι → Type v) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hα : ∀ i, HasCardinalLT (α i) κ) :
    HasCardinalLT (Σ i, α i) κ := by
  let ι' : Type max u v w := ULift.{max v w} ι
  let α' (i : ι') : Type max u v w := ULift.{max u w} (α (ULift.down i))
  let κ' : Cardinal.{max u v w} := Cardinal.lift.{max u v} κ
  have : Fact κ'.IsRegular := ⟨Cardinal.IsRegular.lift Fact.out⟩
  have := hasCardinalLT_sigma' α' κ'
    (by rwa [hasCardinalLT_lift_iff, hasCardinalLT_ulift_iff]) (fun i ↦ by
      rw [hasCardinalLT_lift_iff, hasCardinalLT_ulift_iff]
      exact hα _)
  rw [hasCardinalLT_lift_iff] at this
  exact this.of_surjective (fun ⟨i, a⟩ ↦ ⟨ULift.down i, ULift.down a⟩)
    (fun ⟨i, a⟩ ↦ ⟨⟨ULift.up i, ULift.up a⟩, rfl⟩)

lemma hasCardinalLT_subtype_iSup
    {ι : Type*} {X : Type*} (P : ι → X → Prop) {κ : Cardinal} [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hP : ∀ i, HasCardinalLT (Subtype (P i)) κ) :
    HasCardinalLT (Subtype (⨆ i, P i)) κ :=
  (hasCardinalLT_sigma (fun i ↦ Subtype (P i)) κ hι hP).of_surjective
    (fun ⟨i, x, hx⟩ ↦ ⟨x, by simp only [iSup_apply, iSup_Prop_eq]; exact ⟨i, hx⟩⟩) (by
    rintro ⟨_, h⟩
    simp only [iSup_apply, iSup_Prop_eq] at h
    obtain ⟨i, hi⟩ := h
    exact ⟨⟨i, _, hi⟩, rfl⟩)

lemma hasCardinalLT_iUnion
    {ι : Type*} {X : Type*} (S : ι → Set X) {κ : Cardinal} [Fact κ.IsRegular]
    (hι : HasCardinalLT ι κ) (hS : ∀ i, HasCardinalLT (S i) κ) :
    HasCardinalLT (⋃ i, S i) κ := by
  convert hasCardinalLT_subtype_iSup S hι hS using 2
  ext x
  change _ ↔ ((⨆ i, S i) : X → Prop ) x
  aesop

lemma hasCardinalLT_subtype_max
    {X : Type*} {P₁ P₂ : X → Prop} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (h₁ : HasCardinalLT (Subtype P₁) κ) (h₂ : HasCardinalLT (Subtype P₂) κ) :
    HasCardinalLT (Subtype (P₁ ⊔ P₂)) κ := by
  have : HasCardinalLT (Subtype P₁ ⊕ Subtype P₂) κ := by
    rw [hasCardinalLT_sum_iff _ _ _ hκ]
    exact ⟨h₁, h₂⟩
  refine this.of_surjective (Sum.elim (fun x ↦ ⟨x.1, Or.inl x.2⟩)
    (fun x ↦ ⟨x.1, Or.inr x.2⟩)) ?_
  rintro ⟨x, hx | hx⟩
  · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩

lemma hasCardinalLT_union
    {X : Type*} {S₁ S₂ : Set X} {κ : Cardinal} [Fact κ.IsRegular]
    (h₁ : HasCardinalLT S₁ κ) (h₂ : HasCardinalLT S₂ κ) :
    HasCardinalLT (S₁ ∪ S₂ : Set _) κ :=
  hasCardinalLT_subtype_max (Cardinal.IsRegular.aleph0_le Fact.out) h₁ h₂

lemma hasCardinalLT_prod {T₁ T₂ : Type*} {κ : Cardinal} [Fact κ.IsRegular]
    (h₁ : HasCardinalLT T₁ κ) (h₂ : HasCardinalLT T₂ κ) :
    HasCardinalLT (T₁ × T₂) κ :=
  (hasCardinalLT_sigma (fun (t : T₁) ↦ T₂) κ h₁ (fun _ ↦ h₂)).of_surjective
    (fun ⟨t₁, t₂⟩ ↦ (t₁, t₂)) (by rintro ⟨t₁, t₂⟩; exact ⟨⟨t₁, t₂⟩, rfl⟩)

section

open CategoryTheory Limits

lemma hasCardinalLT_toSet_morphismPropertyOfHoms {C : Type*} [Category C]
    {ι : Type*} {X Y : ι → C} (f : ∀ i, X i ⟶ Y i)
    {κ : Cardinal}
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

lemma hasCardinalLT_arrow_walkingMultispan {h : MultispanShape} {κ : Cardinal}
    [Fact κ.IsRegular]
    (h₁ : HasCardinalLT h.L κ) (h₂ : HasCardinalLT h.R κ) :
    HasCardinalLT (Arrow (WalkingMultispan h)) κ := by
  let T := WalkingMultispan h ⊕ h.L ⊕ h.L
  have hT₀ : HasCardinalLT (WalkingMultispan h) κ := by
    have : HasCardinalLT (h.L ⊕ h.R) κ := by
      rw [hasCardinalLT_sum_iff _ _ _ (Cardinal.IsRegular.aleph0_le Fact.out)]
      exact ⟨h₁, h₂⟩
    refine this.of_surjective (Sum.elim WalkingMultispan.left WalkingMultispan.right) ?_
    rintro (x | y)
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr y, rfl⟩
  have hT : HasCardinalLT T κ := by
    rw [hasCardinalLT_sum_iff _ _ _ (Cardinal.IsRegular.aleph0_le Fact.out),
      hasCardinalLT_sum_iff _ _ _ (Cardinal.IsRegular.aleph0_le Fact.out)]
    exact ⟨hT₀, h₁, h₁⟩
  refine hT.of_surjective (fun t ↦ match t with
    | Sum.inl x => Arrow.mk (𝟙 x)
    | Sum.inr (Sum.inl z) => Arrow.mk (WalkingMultispan.Hom.fst z)
    | Sum.inr (Sum.inr z) => Arrow.mk (WalkingMultispan.Hom.snd z)) ?_
  intro f
  obtain ⟨x, y, f, rfl⟩ := f.mk_surjective
  obtain (_ | z | z) := f
  · exact ⟨Sum.inl x, rfl⟩
  · exact ⟨Sum.inr (Sum.inl z), rfl⟩
  · exact ⟨Sum.inr (Sum.inr z), rfl⟩

end

namespace CategoryTheory

open Limits

namespace Functor.Final

variable {C D : Type*} [Category C] [Category D]

instance [IsFiltered D] : (Prod.fst C D).Final := by
  let F : D ⥤ Discrete PUnit.{1} := (Functor.const _).obj (Discrete.mk .unit)
  have hF : F.Final := Functor.final_of_isFiltered_of_pUnit _
  change (Functor.prod (𝟭 C) F ⋙ (prod.rightUnitorEquivalence.{0} C).functor).Final
  infer_instance

end Functor.Final

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

variable (J : Type w) [SmallCategory J] (κ : Cardinal.{w})

namespace exists_cardinal_directed

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
        (fun (_ : Unit) ↦ ⟨Arrow.mk (𝟙 j), ⟨⟨⟩⟩⟩) (by
      rintro ⟨f, hf⟩
      refine ⟨⟨⟩, ?_⟩
      ext
      exact ((MorphismProperty.ofHoms_iff _ _).1
        ((MorphismProperty.arrow_mk_mem_toSet_iff _ _).1 hf)).choose_spec.symm)
  hP :=
    (hasCardinalLT_punit κ (Cardinal.IsRegular.aleph0_le Fact.out)).of_surjective
      (fun (_ : Unit) ↦ ⟨j, by simp⟩) (fun ⟨k, hk⟩ ↦ ⟨⟨⟩, by aesop⟩)

instance (j : J) : Finite (Subtype (PreDiagram.single (κ := κ) j).P) :=
  Finite.of_surjective (fun (_ : Unit) ↦ ⟨j, by simp⟩)
    (by rintro ⟨_, ⟨⟩⟩; exact ⟨⟨⟩, rfl⟩)

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
    rw [MorphismProperty.toSet_iSup]
    exact hasCardinalLT_iUnion _ hι (fun i ↦ (D i).hW)
  hP := hasCardinalLT_subtype_iSup _ hι (fun i ↦ (D i).hP)

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
  hW := hasCardinalLT_union D₁.hW D₂.hW
  hP := hasCardinalLT_union D₁.hP D₂.hP

variable [IsCardinalFiltered J κ]
  (hJ : ∀ (e : J), ∃ (m : J) (_ : e ⟶ m), IsEmpty (m ⟶ e))

include hJ

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
      let S := { x : ι × ι × J // (D x.1).P x.2.2 ∧ (D x.2.1).P x.2.2 }
      let shape : MultispanShape.{w, w} :=
        { L := { x : ι × ι × J // (D x.1).P x.2.2 ∧ (D x.2.1).P x.2.2 }
          R := PUnit
          fst _ := ⟨⟩
          snd _ := ⟨⟩ }
      let index : MultispanIndex shape J :=
        { left x := x.1.2.2
          right _ := m₁
          fst x := (D x.1.1).terminal.lift x.2.1 ≫ u x.1.1
          snd x := (D x.1.2.1).terminal.lift x.2.2 ≫ u x.1.2.1 }
      have hshape : HasCardinalLT (Arrow (WalkingMultispan shape)) κ := by
        refine hasCardinalLT_arrow_walkingMultispan ?_
          (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
        let T := Σ (i : ι), Subtype (D i).P
        have hT : HasCardinalLT (ι × T) κ :=
          hasCardinalLT_prod hι (hasCardinalLT_sigma _ _ hι (fun i ↦ (D i).hP))
        refine hT.of_injective (fun ⟨⟨i₁, i₂, j⟩, h₁, h₂⟩ ↦ ⟨i₁, i₂, ⟨j, h₂⟩⟩) ?_
        rintro ⟨⟨i₁, i₂, j⟩, _, _⟩ ⟨⟨i₁', i₂', j'⟩, _, _⟩ h
        rw [Prod.ext_iff, Sigma.ext_iff] at h
        dsimp at h
        obtain rfl : i₁ = i₁' := h.1
        obtain rfl : i₂ = i₂' := h.2.1
        obtain rfl : j = j' := by simpa using h
        rfl
      let c : Multicofork _ := IsCardinalFiltered.cocone index.multispan hshape
      exact ⟨c.pt, c.π ⟨⟩, fun i₁ i₂ j h₁ h₂ ↦ by
        simpa [index, shape] using c.condition ⟨⟨i₁, i₂, j⟩, h₁, h₂⟩⟩
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
        hW := by
          rw [MorphismProperty.toSet_max]
          exact hasCardinalLT_union D₁.hW
            (hasCardinalLT_toSet_morphismPropertyOfHoms _
              (hasCardinalLT_sigma _ _ hι (fun i ↦ (D i).hP)))
        hP := hasCardinalLT_subtype_max (Cardinal.IsRegular.aleph0_le Fact.out)
                (hasCardinalLT_subtype_iSup _ hι (fun i ↦ (D i).hP))
                (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
            }
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
      · rintro j k f ((hf | ⟨⟨⟩⟩) | ⟨⟨i, j, hj⟩⟩)
        · simp [D₀] at hf
          obtain ⟨i, hf⟩ := hf
          exact ⟨φ ⟨i, j, (D i).src hf⟩, φ ⟨i, k, (D i).tgt hf⟩, Or.inr ⟨_⟩, Or.inr ⟨_⟩,
            by simp [φ, (D i).terminal.comm_assoc _ hf]⟩
        · exact ⟨𝟙 _, 𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩), Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩
        · exact ⟨φ ⟨i, j, hj⟩, 𝟙 _, Or.inr ⟨_⟩, Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩
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

lemma final_functor : (functor J κ).Final := by
  have := isCardinalFiltered J κ hJ
  have := isFiltered_of_isCardinalFiltered J κ
  have := isFiltered_of_isCardinalFiltered (Diagram J κ) κ
  rw [Functor.final_iff_of_isFiltered]
  refine ⟨fun j ↦ ⟨.single j, ⟨𝟙 _⟩⟩, fun {j D} (f₁ f₂ : j ⟶ D.e) ↦ ?_⟩
  obtain ⟨m₀, t, hm₀⟩ := hJ D.e
  obtain ⟨m₁, u, hu⟩ : ∃ (m₁ : J) (u : m₀ ⟶ m₁), f₁ ≫ t ≫ u = f₂ ≫ t ≫ u :=
    ⟨_, IsFiltered.coeqHom (f₁ ≫ t) (f₂ ≫ t),
      by simpa using IsFiltered.coeq_condition (f₁ ≫ t) (f₂ ≫ t)⟩
  have h₁ : ¬ (D.P m₁) := fun h₁ ↦ hm₀.false (u ≫ D.terminal.lift h₁)
  let φ (x : Subtype D.P) : x.1 ⟶ m₁ := D.terminal.lift x.2 ≫ t ≫ u
  let D₀ := D.toPreDiagram.max (.single m₁)
  let D₁ : PreDiagram J κ :=
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
        hasCardinalLT_union
          (hasCardinalLT_union D.hW
            (hasCardinalLT_toSet_morphismPropertyOfHoms _
            (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))))
          (hasCardinalLT_toSet_morphismPropertyOfHoms _ D.hP)
      hP :=
        hasCardinalLT_union D.hP
          (hasCardinalLT_subtype_objectPropertyOfObj _
            ((hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)))) }
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
  let hm₁ : D₁.Terminal m₁ :=
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
          Or.inr ⟨_⟩, Or.inr ⟨_⟩, D.terminal.comm_assoc _ hf _⟩
      · exact ⟨𝟙 _, 𝟙 _, Or.inl (Or.inr ⟨⟨⟩⟩), Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩
      · exact ⟨φ ⟨_, hj⟩, 𝟙 _, Or.inr ⟨_⟩, Or.inl (Or.inr ⟨⟨⟩⟩), by simp⟩)
  have lift_eq (j : J) (hj : D.P j) : hm₁.lift (Or.inl hj) = φ ⟨_, hj⟩ :=
    hm₁.uniq _ (Or.inr ⟨_⟩)
  let D₁' : Diagram J κ :=
    { toPreDiagram := D₁
      e := m₁
      terminal := hm₁
      uniq_terminal j hj := by
        obtain (hj' | ⟨⟨⟩⟩) := hj.prop
        · exact hm₀.elim (u ≫ hj.lift (Or.inr ⟨⟨⟩⟩) ≫ D.terminal.lift hj')
        · rfl}
  exact ⟨D₁', homOfLE ⟨le_sup_left.trans le_sup_left, le_sup_left⟩,
    by simpa [functorMap, D₁', lift_eq _ D.terminal.prop, φ]⟩

lemma aux :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α κ)
      (F : α ⥤ J), F.Final :=
  ⟨_, _, isCardinalFiltered J κ hJ, functor J κ, final_functor J κ hJ⟩

end exists_cardinal_directed

lemma exists_cardinal_directed [Fact κ.IsRegular] [IsCardinalFiltered J κ] :
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
lemma IsFiltered.exists_directed
    (J : Type w) [SmallCategory J] [IsFiltered J] :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (F : α ⥤ J), F.Final := by
  have := (isCardinalFiltered_aleph0_iff.{w} J).2 inferInstance
  obtain ⟨α, _, _, F, _⟩ := IsCardinalFiltered.exists_cardinal_directed J .aleph0
  have : IsFiltered α := by rwa [← isCardinalFiltered_aleph0_iff.{w}]
  exact ⟨α, _, IsFiltered.isDirected _, nonempty, F, inferInstance⟩

end CategoryTheory
