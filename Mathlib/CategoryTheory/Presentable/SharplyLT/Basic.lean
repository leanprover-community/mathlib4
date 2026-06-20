/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.Presentable.CardinalDirectedPoset
public import Mathlib.CategoryTheory.Presentable.Dense
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.Order.TransfiniteIteration

/-!
# Sharply smaller regular cardinals

-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace Cardinal

variable {κ₁ κ₂ : Cardinal.{w}} [Fact κ₁.IsRegular] [Fact κ₂.IsRegular]

variable (κ₁ κ₂) in
structure SharplyLT : Prop where
  lt : κ₁ < κ₂
  isCardinalAccessible_cardinalDirectedPoset :
    IsCardinalAccessibleCategory (CardinalFilteredPoset κ₁) κ₂

namespace SharplyLT

lemma le (h : SharplyLT κ₁ κ₂) : κ₁ ≤ κ₂ := h.lt.le

set_option backward.defeqAttrib.useBackward true in
open CardinalFilteredPoset in
lemma exists_cofinal_of_isCardinalAccessibleCategory_cardinalFilteredPoset
    (h : κ₁ ≤ κ₂) [IsCardinalAccessibleCategory (CardinalFilteredPoset κ₁) κ₂]
    {X : Type w} (hX : HasCardinalLT X κ₂) :
    ∃ (A : Set (SetCardinalLT κ₁ X)), HasCardinalLT A κ₂ ∧ IsCofinal A := by
  obtain ⟨J, _, _, ⟨p⟩⟩ := (isCardinalFilteredGenerator_isCardinalPresentable
    (CardinalFilteredPoset κ₁) κ₂).exists_colimitsOfShape (setCardinalLT κ₁ X)
  have : IsCardinalFiltered J κ₁ := .of_le _ h
  have hp (j : J) : HasCardinalLT (p.diag.obj j).obj κ₂ := by
    rw [← CardinalFilteredPoset.isCardinalPresentable_iff _ h]
    exact p.prop_diag_obj j
  choose j y hy using fun x ↦ Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CardinalFilteredPoset κ₁)) p.isColimit)
    (SetCardinalLT.singleton κ₁ x)
  dsimp at y hy
  let j' := IsCardinalFiltered.max j hX
  let y' (x : X) : (p.diag.obj j').obj :=
    p.diag.map (IsCardinalFiltered.toMax j hX x) (y x)
  have hy' (x : X) : p.ι.app j' (y' x) = SetCardinalLT.singleton κ₁ x := by
    rw [← hy, ← p.w (IsCardinalFiltered.toMax j hX x)]
    rfl
  refine ⟨Set.range (p.ι.app j'), (hp j').of_surjective _
    (Set.rangeFactorization_surjective (f := p.ι.app j')), fun ⟨B, hB⟩ ↦ ?_⟩
  let j'' := IsCardinalFiltered.max (fun b ↦ y' b.val) hB
  refine ⟨_, ⟨j'', rfl⟩, fun b hb ↦ ?_⟩
  have : y' b ≤ j'' := (leOfHom (IsCardinalFiltered.toMax (fun b ↦ y' b.val) hB ⟨b, hb⟩) :)
  refine (p.ι.app j').hom.hom.monotone this ?_
  convert Set.mem_singleton b
  exact Subtype.ext_iff.1 (hy' b)

section

open CardinalFilteredPoset

namespace existsIsCardinalFilteredSetOfExistsCofinal

variable (h₀ : κ₁ < κ₂)
  {X : Type w} [PartialOrder X]
  (Y : ∀ (B : Set X) (_ : HasCardinalLT B κ₂), Set (SetCardinalLT κ₁ B))
  (hY : ∀ (B : Set X) (hB : HasCardinalLT B κ₂), HasCardinalLT (Y B hB) κ₂)
  (hY' : ∀ (B : Set X) (hB : HasCardinalLT B κ₂), IsCofinal (Y B hB))
  (m : ∀ (B : Set X) (hB : HasCardinalLT B κ₂) (C : SetCardinalLT κ₁ B),
    C ∈ Y B hB → X)
  (hm : ∀ (B : Set X) (hB : HasCardinalLT B κ₂) (C : SetCardinalLT κ₁ B)
    (hC : C ∈ Y B hB) (b : B), b ∈ C.val → b ≤ m B hB C hC)
  (A : Set X) (hA : HasCardinalLT A κ₂)

def φ₀ (B : Set X) (hB : HasCardinalLT B κ₂) : Set X :=
    ⋃ (C : Y B hB), Subtype.val '' C.val.val ∪ {m B hB _ C.prop}

omit [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] in
include hY' hm in
lemma hφ₀ (B : Set X) (hB : HasCardinalLT B κ₂) {T : Type w} (f : T → B)
    (hT : HasCardinalLT T κ₁) :
    ∃ (a : φ₀ Y m B hB), ∀ (t : T), f t ≤ a.val := by
  let C₀ : SetCardinalLT κ₁ B :=
    ⟨Set.range f, hT.of_surjective _ Set.rangeFactorization_surjective⟩
  obtain ⟨C, hC, hC'⟩ := hY' B hB C₀
  exact ⟨⟨m B hB C hC, Set.subset_iUnion _ ⟨C, hC⟩ (Or.inr (by simp))⟩,
    fun t ↦ hm B hB C hC (f t) (hC' (by simp [C₀]))⟩

open Classical in
def φ (B : Set X) : Set X :=
  if hB : HasCardinalLT B κ₂ then φ₀ Y m B hB else B

omit [Fact κ₁.IsRegular] [Fact κ₂.IsRegular] [PartialOrder X] in
lemma φ_eq (B : Set X) (hB : HasCardinalLT B κ₂) :
  φ Y m B = φ₀ Y m B hB := dif_pos hB

include hY' in
omit [Fact κ₂.IsRegular] [PartialOrder X] in
lemma le_φ (B : Set X) : B ≤ φ Y m B := by
  dsimp [φ]
  split_ifs with hB
  · intro b hb
    obtain ⟨C, hC, hC'⟩ := hY' B hB ⟨{⟨b, hb⟩},
      hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out)⟩
    refine Set.subset_iUnion _ ⟨C, hC⟩ (Or.inl ?_)
    simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    refine ⟨hb, @hC' ⟨b, hb⟩ (by simp)⟩
  · simp

variable (κ₁) in
noncomputable abbrev orderBot : OrderBot κ₁.ord.ToType :=
  have : Nonempty κ₁.ord.ToType := by
    rw [Ordinal.nonempty_toType_iff, ne_eq, ord_eq_zero]
    exact IsRegular.ne_zero Fact.out
  WellFoundedLT.toOrderBot _

include h₀ hA hY in
omit [PartialOrder X] in
lemma hasCardinalLT_transfiniteIterate_φ (j : κ₁.ord.ToType) :
    HasCardinalLT (transfiniteIterate (φ Y m) j A :) κ₂ := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    letI := orderBot κ₁
    simpa [hj.eq_bot]
  | succ j hj hj' =>
    have hκ₂ : κ₂.IsRegular := Fact.out
    rw [transfiniteIterate_succ _ _ _ hj, φ_eq _ _ _ hj']
    refine hasCardinalLT_iUnion _ (hY _ _)
      (fun ⟨C, hC⟩ ↦ hasCardinalLT_union hκ₂.aleph0_le ?_
        (hasCardinalLT_of_finite _ _ hκ₂.aleph0_le))
    refine (C.prop.of_le h₀.le).of_injective (fun ⟨c, hc⟩ ↦ ?_)
      (fun c₁ c₂ hc ↦ ?_)
    · simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hc
      exact ⟨⟨c, hc.choose⟩, hc.choose_spec⟩
    · simpa only [Subtype.ext_iff] using hc
  | isSuccLimit j hj hj' =>
    rw [transfiniteIterate_limit _ _ _ hj, Set.iSup_eq_iUnion]
    refine hasCardinalLT_iUnion _
      (HasCardinalLT.of_injective ?_ _ Subtype.val_injective) (fun ⟨k, hk⟩ ↦ hj' _ hk)
    simpa [hasCardinalLT_iff_cardinal_mk_lt]

include hY' in
omit [Fact κ₂.IsRegular] [PartialOrder X] in
lemma monotone_transfiniteIterate_φ :
    Monotone (fun (j : κ₁.ord.ToType) ↦ transfiniteIterate (φ Y m) j A) :=
  letI := orderBot κ₁
  monotone_transfiniteIterate _ _ (le_φ _ hY' _)

omit [PartialOrder X] [Fact κ₂.IsRegular] in
lemma subset_iUnion : A ⊆ ⋃ (j : κ₁.ord.ToType), transfiniteIterate (φ Y m) j A := by
  letI := orderBot κ₁
  exact subset_trans (by simp) (Set.subset_iUnion _ ⊥)

include h₀ hY hY' hm hA in
lemma isCardinalFiltered_iUnion :
    IsCardinalFiltered (⋃ (j : κ₁.ord.ToType), transfiniteIterate (φ Y m) j A) κ₁ := by
  suffices ∀ ⦃K : Type w⦄ (j : κ₁.ord.ToType) (f : K → (transfiniteIterate (φ Y m) j A : Set _))
      (hK : HasCardinalLT K κ₁),
      ∃ (x : (transfiniteIterate (φ Y m) (Order.succ j) A : Set _)),
          ∀ (k : K), (f k).val ≤ x.val by
    refine isCardinalFiltered_preorder _ _ (fun K f hK ↦ ?_)
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have (k : K) : ∃ (j : κ₁.ord.ToType), (f k).val ∈ transfiniteIterate (φ Y m) j A := by
      simpa only [Set.mem_iUnion] using (f k).prop
    choose a ha using this
    obtain ⟨⟨z, hz⟩, hz'⟩ := this (IsCardinalFiltered.max a hK) (fun k ↦
      ⟨(f k).val, monotone_transfiniteIterate_φ Y hY' m A
          (leOfHom (IsCardinalFiltered.toMax a hK k)) (ha k)⟩) hK
    exact ⟨⟨z, Set.subset_iUnion _ _ hz⟩, hz'⟩
  intro K j f hK
  have := hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A
  obtain ⟨⟨x, hx⟩, hx'⟩ := hφ₀ Y hY' m hm _
    (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA _) f hK
  refine ⟨⟨x, ?_⟩, hx'⟩
  have : NoMaxOrder κ₁.ord.ToType := noMaxOrder (IsRegular.aleph0_le Fact.out)
  rwa [transfiniteIterate_succ _ _ _ (not_isMax j),
    φ_eq _ _ _ (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA _)]

end existsIsCardinalFilteredSetOfExistsCofinal

open existsIsCardinalFilteredSetOfExistsCofinal in
lemma exists_isCardinalFiltered_set_of_exists_cofinal (h₀ : κ₁ < κ₂)
    (h : ∀ (X : Type w) (_ : HasCardinalLT X κ₂),
    ∃ (A : Set (SetCardinalLT κ₁ X)), HasCardinalLT A κ₂ ∧ IsCofinal A)
    {X : Type w} [PartialOrder X] [IsCardinalFiltered X κ₁]
    (A : Set X) (hA : HasCardinalLT A κ₂) :
    ∃ (B : Set X), A ⊆ B ∧ IsCardinalFiltered B κ₁ ∧ HasCardinalLT B κ₂ := by
  choose Y hY hY' using fun (B : Set X) hB ↦ h B hB
  have hY'' (B : Set X) (hB : HasCardinalLT B κ₂)
      (C : SetCardinalLT κ₁ B) (hC : C ∈ Y B hB) :
    ∃ (m : X), ∀ (b : B), b ∈ C.val → b ≤ m :=
      ⟨IsCardinalFiltered.max (fun (c : C.val) ↦ c.val.val) C.prop,
        fun b hb ↦ leOfHom (IsCardinalFiltered.toMax
          (fun (c : C.val) ↦ c.val.val) C.prop ⟨_, hb⟩)⟩
  choose m hm using hY''
  exact ⟨_, subset_iUnion Y m A,
    isCardinalFiltered_iUnion h₀ Y hY hY' m hm A hA,
    hasCardinalLT_iUnion _ (by simpa [hasCardinalLT_iff_cardinal_mk_lt])
      (hasCardinalLT_transfiniteIterate_φ h₀ Y hY m A hA)⟩

end

section

variable (hκ : κ₁ < κ₂)
  (hκ' : ∀ {X : Type w} [PartialOrder X] [IsCardinalFiltered X κ₁]
    (A : Set X) (_ : HasCardinalLT A κ₂),
    ∃ (B : Set X), A ⊆ B ∧ IsCardinalFiltered B κ₁ ∧ HasCardinalLT B κ₂)

variable (κ₁ κ₂) in
def IsCardinalFilteredAndHasCardinalLT
    (J : Type w) [PartialOrder J] (A : Set J) : Prop :=
  IsCardinalFiltered A κ₁ ∧ HasCardinalLT A κ₂

namespace IsCardinalFilteredAndHasCardinalLT

variable (κ₁ κ₂) {C : Type u} [Category.{v} C] {X : C}
  {J : Type w} [PartialOrder J]
  (p : (isCardinalPresentable C κ₁).ColimitOfShape J X)

variable [IsCardinalAccessibleCategory C κ₁]

instance (A : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)) :
    HasColimit ((Subtype.mono_coe A.val).functor ⋙ p.diag) := by
  have : IsCardinalFiltered (Subtype A.val) κ₁ := A.prop.1
  infer_instance

abbrev singleton (j : J) : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J) :=
  ⟨{j}, by
    letI : OrderTop ({j} : Set J) :=
      { top := ⟨j, by simp⟩
        le_top := by simp }
    exact isCardinalFiltered_of_hasTerminal _ _,
    hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out)⟩

abbrev pair {j j' : J} (h : j ≤ j') :
    Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J) :=
  ⟨{j, j'}, by
    letI : OrderTop ({j, j'} : Set J) :=
      { top := ⟨j', by simp⟩
        le_top := by aesop }
    apply isCardinalFiltered_of_hasTerminal,
    hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out)⟩

lemma le_pair {j j' : J} (h : j ≤ j') :
    singleton κ₁ κ₂ j ≤ pair κ₁ κ₂ h := by
  rw [Subtype.mk_le_mk]
  simp

lemma le_pair' {j j' : J} (h : j ≤ j') :
    singleton κ₁ κ₂ j' ≤ pair κ₁ κ₂ h := by
  rw [Subtype.mk_le_mk]
  simp

noncomputable abbrev colimit
    (A : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)) : C :=
    Limits.colimit ((Subtype.mono_coe A.val).functor ⋙ p.diag)

noncomputable abbrev colimit.ι
    (A : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)) (a : J) (ha : a ∈ A.val) :
    p.diag.obj a ⟶ colimit κ₁ κ₂ p A :=
  Limits.colimit.ι ((Subtype.mono_coe A.val).functor ⋙ p.diag) ⟨a, ha⟩

omit [Fact κ₂.IsRegular] in
@[reassoc (attr := simp)]
lemma colimit.w (A : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J))
    {a b : J} (hab : a ≤ b) (ha : a ∈ A.val) (hb : b ∈ A.val) :
    p.diag.map (homOfLE hab) ≫ colimit.ι κ₁ κ₂ p A b hb = colimit.ι κ₁ κ₂ p A a ha :=
  Limits.colimit.w ((Subtype.mono_coe A.val).functor ⋙ p.diag)
    (j := ⟨a, ha⟩) (j' := ⟨b, hb⟩) (homOfLE hab)

set_option backward.defeqAttrib.useBackward true in
noncomputable def colimit.map
    {A₁ A₂ : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)} (hA : A₁ ≤ A₂) :
    colimit κ₁ κ₂ p A₁ ⟶ colimit κ₁ κ₂ p A₂ :=
  colimit.desc _ (Cocone.mk _
    { app j := colimit.ι κ₁ κ₂ p A₂ j.val (hA j.prop)
      naturality j₁ j₂ f := by
        simpa using! colimit.w κ₁ κ₂ p A₂ (leOfHom f) (hA j₁.prop) (hA j₂.prop) })

omit [Fact κ₂.IsRegular] in
@[reassoc (attr := simp)]
lemma colimit.ι_map {A₁ A₂ : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)}
    (hA : A₁ ≤ A₂) (j : J) (hj : j ∈ A₁.val) :
    colimit.ι κ₁ κ₂ p A₁ j hj ≫ colimit.map κ₁ κ₂ p hA = colimit.ι κ₁ κ₂ p A₂ j (hA hj) :=
  colimit.ι_desc ..

omit [Fact κ₂.IsRegular] in
@[ext]
lemma colimit.hom_ext
    {A : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)} {T : C}
    {φ₁ φ₂ : colimit κ₁ κ₂ p A ⟶ T}
    (h : ∀ (j : J) (hj : j ∈ A.val), colimit.ι κ₁ κ₂ p A j hj ≫ φ₁ =
      colimit.ι κ₁ κ₂ p A j hj ≫ φ₂) :
    φ₁ = φ₂ := by
  ext
  apply h

set_option backward.defeqAttrib.useBackward true in
noncomputable def colimit.π
    (A : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)) : colimit κ₁ κ₂ p A ⟶ X :=
  colimit.desc _ (Cocone.mk _
    { app a := by exact p.ι.app a
      naturality _ _ _ := by simpa using p.ι.naturality _ })

omit [Fact κ₂.IsRegular] in
@[reassoc (attr := simp)]
lemma colimit.ι_π
    (A : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)) (a : J) (ha : a ∈ A.val) :
    colimit.ι κ₁ κ₂ p A a ha ≫ colimit.π κ₁ κ₂ p A = p.ι.app a :=
  colimit.ι_desc ..

omit [Fact κ₂.IsRegular] in
@[reassoc (attr := simp)]
lemma colimit.map_π {A₁ A₂ : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)} (hA : A₁ ≤ A₂) :
    colimit.map κ₁ κ₂ p hA ≫ colimit.π κ₁ κ₂ p A₂ = colimit.π κ₁ κ₂ p A₁ := by
  ext
  simp

@[simps]
noncomputable def functor :
    Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J) ⥤ C where
  obj A := colimit κ₁ κ₂ p A
  map f := colimit.map κ₁ κ₂ p f.le
  map_id _ := by ext; simp
  map_comp f g := by ext; simp

set_option backward.defeqAttrib.useBackward true in
@[simps]
noncomputable def cocone : Cocone (functor κ₁ κ₂  p) where
  pt := X
  ι.app j := colimit.π κ₁ κ₂ p j

namespace isColimit

variable {κ₁ κ₂ p} (s : Cocone (functor κ₁ κ₂ p))

set_option backward.defeqAttrib.useBackward true in
@[simps]
noncomputable def coconeDesc : Cocone p.diag where
  pt := s.pt
  ι.app j := colimit.ι _ _ _ _ _ (by simp) ≫ s.ι.app (singleton κ₁ κ₂ j)
  ι.naturality j j' f := by
    simpa [← s.w (homOfLE (le_pair κ₁ κ₂ (leOfHom f))),
        ← s.w (homOfLE (le_pair' κ₁ κ₂ (leOfHom f)))]
      using! colimit.w_assoc ..

noncomputable def desc : X ⟶ s.pt := p.isColimit.desc (coconeDesc s)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma fac (j : J) :
    dsimp% p.ι.app j ≫ desc s =
      colimit.ι _ _ _ _ _ (by simp) ≫ s.ι.app (singleton κ₁ κ₂ j) :=
  p.isColimit.fac (coconeDesc s) j

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma fac' (A : Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)) :
    colimit.π κ₁ κ₂ p A ≫ desc s = s.ι.app A := by
  ext j hj
  let φ : singleton κ₁ κ₂ j ⟶ A := homOfLE (by
    rw [Subtype.mk_le_mk]
    simpa)
  simp [colimit.ι_π_assoc, fac, ← s.w φ]

end isColimit

open isColimit in
set_option backward.defeqAttrib.useBackward true in
noncomputable def isColimit : IsColimit (cocone κ₁ κ₂ p) where
  desc s := desc s
  fac s A := fac' s A
  uniq s m hm :=
    p.isColimit.hom_ext (fun j ↦ by simp [fac s j, ← hm])

variable {κ₁ κ₂} in
include hκ' in
lemma isCardinalFiltered_subtype [IsCardinalFiltered J κ₁] :
    IsCardinalFiltered (Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J)) κ₂ :=
  isCardinalFiltered_preorder _ _ (fun K f hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    obtain ⟨B, hB₁, hB₂, hB₃⟩ := hκ' (⋃ (k : K), (f k).val)
      (hasCardinalLT_iUnion _ hK (fun k ↦ (f k).prop.2))
    exact ⟨⟨B, hB₂, hB₃⟩, fun k ↦ (Set.subset_iUnion _ k).trans hB₁⟩)

end IsCardinalFilteredAndHasCardinalLT

variable (C : Type u) [Category.{v} C]

variable (κ₁ κ₂) in
abbrev generator : ObjectProperty C :=
  (isCardinalPresentable C κ₁).colimitsCardinalClosure κ₂

include hκ in
lemma generator_le_isCardinalPresentable [LocallySmall.{w} C] :
    generator κ₁ κ₂ C ≤ isCardinalPresentable C κ₂ :=
  ObjectProperty.colimitsCardinalClosure_le _ _
    (fun _ _ hJ ↦ isClosedUnderColimitsOfShape_isCardinalPresentable C hJ)
    (isCardinalPresentable_monotone _ hκ.le)

open IsCardinalFilteredAndHasCardinalLT in
include hκ hκ' in
lemma isCardinalFilteredGenerator
    [IsCardinalAccessibleCategory C κ₁] :
    (generator κ₁ κ₂ C).IsCardinalFilteredGenerator κ₂ where
  le_isCardinalPresentable := generator_le_isCardinalPresentable hκ C
  exists_colimitsOfShape X := by
    have hκ₁ := isCardinalFilteredGenerator_isCardinalPresentable C κ₁
    obtain ⟨J, _, _, ⟨p⟩⟩ :
        ∃ (J : Type w) (_ : PartialOrder J) (_ : IsCardinalFiltered J κ₁),
      Nonempty ((isCardinalPresentable C κ₁).ColimitOfShape J X) := by
        obtain ⟨J₀, _, _, ⟨p₀⟩⟩ := hκ₁.exists_colimitsOfShape X
        obtain ⟨J, _, _, F, _⟩ := IsCardinalFiltered.exists_cardinal_directed J₀ κ₁
        exact ⟨_, _, inferInstance, ⟨p₀.reindex F⟩⟩
    refine ⟨Subtype (IsCardinalFilteredAndHasCardinalLT κ₁ κ₂ J), inferInstance,
      isCardinalFiltered_subtype hκ',
      ⟨{ diag := _, ι := _, isColimit := isColimit κ₁ κ₂ p, prop_diag_obj A := ?_ }⟩⟩
    have : (generator κ₁ κ₂ C).IsClosedUnderColimitsOfShape (Subtype A.val) := by
      apply ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
      rw [hasCardinalLT_arrow_iff_of_isThin _ _ (IsRegular.aleph0_le Fact.out)]
      exact A.prop.2
    exact ObjectProperty.prop_colimit _ _
      (fun ⟨a, ha⟩ ↦ ObjectProperty.le_colimitsCardinalClosure _ _ _
        (p.prop_diag_obj a))

include hκ hκ' in
lemma isCardinalAccessibleCategory'
    (C : Type u) [Category.{v} C] [IsCardinalAccessibleCategory C κ₁] :
    IsCardinalAccessibleCategory C κ₂ where
  toHasCardinalFilteredColimits := .of_le C hκ.le
  exists_generator := ⟨_, inferInstance, isCardinalFilteredGenerator hκ hκ' C⟩

end

lemma tfae (h : κ₁ < κ₂) :
    List.TFAE [SharplyLT κ₁ κ₂,
      IsCardinalAccessibleCategory (CardinalFilteredPoset κ₁) κ₂,
      ∀ (C : Type (w + 1)) [Category.{w} C] [IsCardinalAccessibleCategory C κ₁],
        IsCardinalAccessibleCategory C κ₂,
      ∀ (X : Type w) (_ : HasCardinalLT X κ₂),
        ∃ (A : Set (CardinalFilteredPoset.SetCardinalLT κ₁ X)), HasCardinalLT A κ₂ ∧ IsCofinal A,
      ∀ ⦃X : Type w⦄ [PartialOrder X] [IsCardinalFiltered X κ₁] (A : Set X)
          (_ : HasCardinalLT A κ₂),
        ∃ (B : Set X), A ⊆ B ∧ IsCardinalFiltered B κ₁ ∧ HasCardinalLT B κ₂] := by
  tfae_have 1 ↔ 2 :=
    ⟨fun h ↦ h.isCardinalAccessible_cardinalDirectedPoset, fun _ ↦ ⟨h, inferInstance⟩⟩
  tfae_have 3 → 2 := fun h' ↦ h' _
  tfae_have 2 → 4 := fun _ X hX ↦
    exists_cofinal_of_isCardinalAccessibleCategory_cardinalFilteredPoset h.le hX
  tfae_have 4 → 5 := fun h' X _ _ A hA ↦
    exists_isCardinalFiltered_set_of_exists_cofinal h h' _ hA
  tfae_have 5 → 3 := fun h' C _ _ ↦ isCardinalAccessibleCategory' h (fun A hA ↦ h' A hA) C
  tfae_finish

lemma exists_cofinal (h : SharplyLT κ₁ κ₂)
    {X : Type w} (hX : HasCardinalLT X κ₂) :
    ∃ (A : Set (CardinalFilteredPoset.SetCardinalLT κ₁ X)),
      HasCardinalLT A κ₂ ∧ IsCofinal A := by
  have := (tfae h.lt).out 1 3
  exact this.1 h.isCardinalAccessible_cardinalDirectedPoset X hX

lemma of_exists_cofinal (h₀ : κ₁ < κ₂)
    (h : ∀ (X : Type w) (_ : HasCardinalLT X κ₂),
      ∃ (A : Set (CardinalFilteredPoset.SetCardinalLT κ₁ X)),
      HasCardinalLT A κ₂ ∧ IsCofinal A) :
    SharplyLT κ₁ κ₂ :=
  ((tfae h₀).out 3 0).1 h

lemma exists_isCardinalFiltered_set (h : SharplyLT κ₁ κ₂)
    {X : Type w} [PartialOrder X] [IsCardinalFiltered X κ₁]
    (A : Set X) (hA : HasCardinalLT A κ₂) :
    ∃ (B : Set X), A ⊆ B ∧ IsCardinalFiltered B κ₁ ∧ HasCardinalLT B κ₂ := by
  have := (tfae h.lt).out 1 4
  exact this.1 h.isCardinalAccessible_cardinalDirectedPoset A hA

lemma isCardinalAccessibleCategory (h : SharplyLT κ₁ κ₂)
    (C : Type u) [Category.{v} C] [IsCardinalAccessibleCategory C κ₁] :
    IsCardinalAccessibleCategory C κ₂ :=
  isCardinalAccessibleCategory' h.lt h.exists_isCardinalFiltered_set C

lemma trans (h₁₂ : SharplyLT κ₁ κ₂) {κ₃ : Cardinal.{w}} [Fact κ₃.IsRegular]
    (h₂₃ : SharplyLT κ₂ κ₃) :
    SharplyLT κ₁ κ₃ where
  lt := h₁₂.lt.trans h₂₃.lt
  isCardinalAccessible_cardinalDirectedPoset := by
    have := h₁₂.isCardinalAccessible_cardinalDirectedPoset
    exact h₂₃.isCardinalAccessibleCategory _

end SharplyLT

end Cardinal
