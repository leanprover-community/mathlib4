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

open CardinalFilteredPoset Classical in
lemma exists_isCardinalFiltered_set_of_exists_cofinal (h₀ : κ₁ < κ₂)
    (h : ∀ (X : Type w) (_ : HasCardinalLT X κ₂),
    ∃ (A : Set (SetCardinalLT κ₁ X)), HasCardinalLT A κ₂ ∧ IsCofinal A)
    {X : Type w} [PartialOrder X] [IsCardinalFiltered X κ₁]
    (A : Set X) (hA : HasCardinalLT A κ₂) :
    ∃ (B : Set X), A ⊆ B ∧ IsCardinalFiltered B κ₁ ∧ HasCardinalLT B κ₂ := by
  have hκ₁ : κ₁.IsRegular := Fact.out
  have hκ₂ : κ₂.IsRegular := Fact.out
  have : NoMaxOrder κ₁.ord.ToType := noMaxOrder (hκ₁.aleph0_le)
  choose Y hY hY' using fun (B : Set X) hB ↦ h B hB
  have hY'' (B : Set X) (hB : HasCardinalLT B κ₂)
      (C : SetCardinalLT κ₁ B) (hC : C ∈ Y B hB) :
    ∃ (m : X), ∀ (b : B), b ∈ C.val → b ≤ m :=
      ⟨IsCardinalFiltered.max (fun (c : C.val) ↦ c.val.val) C.prop,
        fun b hb ↦ leOfHom (IsCardinalFiltered.toMax
          (fun (c : C.val) ↦ c.val.val) C.prop ⟨_, hb⟩)⟩
  choose m hm using hY''
  let φ₀ (B : Set X) (hB : HasCardinalLT B κ₂) : Set X :=
    ⋃ (C : Y B hB), Subtype.val '' C.val.val ∪ {m B hB _ C.prop}
  have hφ₀ (B : Set X) (hB : HasCardinalLT B κ₂) {T : Type w} (f : T → B)
      (hT : HasCardinalLT T κ₁) :
    ∃ (m : φ₀ B hB), ∀ (t : T), f t ≤ m.val := by
      let C₀ : SetCardinalLT κ₁ B :=
        ⟨Set.range f, hT.of_surjective _ Set.rangeFactorization_surjective⟩
      obtain ⟨C, hC, hC'⟩ := hY' B hB C₀
      exact ⟨⟨m B hB C hC, Set.subset_iUnion _ ⟨C, hC⟩ (Or.inr (by simp))⟩,
        fun t ↦ hm B hB C hC (f t) (hC' (by simp [C₀]))⟩
  let φ (B : Set X) : Set X :=
    if hB : HasCardinalLT B κ₂ then φ₀ B hB else B
  have φ_eq (B : Set X) (hB : HasCardinalLT B κ₂) : φ B = φ₀ B hB := dif_pos hB
  have hφ (B : Set X) : B ≤ φ B := by
    dsimp [φ]
    split_ifs with hB
    · intro b hb
      obtain ⟨C, hC, hC'⟩ := hY' B hB ⟨{⟨b, hb⟩}, hasCardinalLT_of_finite _ _ hκ₁.aleph0_le⟩
      refine Set.subset_iUnion _ ⟨C, hC⟩ (Or.inl ?_)
      simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      refine ⟨hb, @hC' ⟨b, hb⟩ (by simp)⟩
    · simp
  let : Nonempty κ₁.ord.ToType := by
    rw [Ordinal.nonempty_toType_iff, ne_eq, ord_eq_zero]
    exact IsRegular.ne_zero Fact.out
  let : OrderBot κ₁.ord.ToType := WellFoundedLT.toOrderBot _
  let s (j : κ₁.ord.ToType) : Set X := transfiniteIterate φ j A
  have hs : Monotone s := monotone_transfiniteIterate _ _ hφ
  have hs' (j) : HasCardinalLT (s j) κ₂ := by
    induction j using SuccOrder.limitRecOn with
    | isMin j hj => simpa [hj.eq_bot, s]
    | succ j hj hj' =>
      dsimp [s]
      rw [transfiniteIterate_succ _ _ _ hj, φ_eq _ hj']
      refine hasCardinalLT_iUnion _ (hY _ _)
        (fun ⟨C, hC⟩ ↦ hasCardinalLT_union hκ₂.aleph0_le ?_
          (hasCardinalLT_of_finite _ _ hκ₂.aleph0_le))
      refine (C.prop.of_le h₀.le).of_injective (fun ⟨c, hc⟩ ↦ ?_)
        (fun c₁ c₂ hc ↦ ?_)
      · simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hc
        exact ⟨⟨c, hc.choose⟩, hc.choose_spec⟩
      · simpa only [Subtype.ext_iff] using hc
    | isSuccLimit j hj hj' =>
      dsimp [s]
      rw [transfiniteIterate_limit _ _ _ hj, Set.iSup_eq_iUnion]
      refine hasCardinalLT_iUnion _
        (HasCardinalLT.of_injective ?_ _ Subtype.val_injective) (fun ⟨k, hk⟩ ↦ hj' _ hk)
      simpa [hasCardinalLT_iff_cardinal_mk_lt]
  refine ⟨⋃ j, s j, ?_, ?_, ?_⟩
  · exact subset_trans (by simp [s]) (Set.subset_iUnion _ ⊥)
  · suffices ∀ ⦃K : Type w⦄ (j : κ₁.ord.ToType) (f : K → s j) (hK : HasCardinalLT K κ₁),
        ∃ (x : s (Order.succ j)), ∀ (k : K), (f k).val ≤ x.val by
      refine isCardinalFiltered_preorder _ _ (fun K f hK ↦ ?_)
      rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
      have (k : K) : ∃ (j : κ₁.ord.ToType), (f k).val ∈ s j := by
        simpa only [Set.mem_iUnion] using (f k).prop
      choose a ha using this
      obtain ⟨⟨z, hz⟩, hz'⟩ := this (IsCardinalFiltered.max a hK) (fun k ↦
        ⟨(f k).val, hs (leOfHom (IsCardinalFiltered.toMax a hK k)) (ha k)⟩) hK
      exact ⟨⟨z, Set.subset_iUnion _ _ hz⟩, hz'⟩
    intro K j f hK
    obtain ⟨⟨x, hx⟩, hx'⟩ := hφ₀ _ (hs' _) f hK
    refine ⟨⟨x, ?_⟩, hx'⟩
    dsimp [s]
    rwa [transfiniteIterate_succ _ _ _ (not_isMax j), φ_eq _ (hs' _)]
  · exact hasCardinalLT_iUnion _ (by simpa [hasCardinalLT_iff_cardinal_mk_lt]) hs'

section

variable (hκ : κ₁ < κ₂)
  (hκ' : ∀ {X : Type w} [PartialOrder X] [IsCardinalFiltered X κ₁]
    (A : Set X) (_ : HasCardinalLT A κ₂),
    ∃ (B : Set X), A ⊆ B ∧ IsCardinalFiltered B κ₁ ∧ HasCardinalLT B κ₂)

namespace isCardinalAccessible

variable (κ₁ κ₂)

abbrev generator (C : Type u) [Category.{v} C] :
    ObjectProperty C :=
  (isCardinalPresentable C κ₁).colimitsCardinalClosure κ₂

variable (C : Type u) [Category.{v} C]

variable {κ₁ κ₂} in
include hκ in
lemma generator_le_isCardinalPresentable [LocallySmall.{w} C] :
    generator κ₁ κ₂ C ≤ isCardinalPresentable C κ₂ :=
  ObjectProperty.colimitsCardinalClosure_le _ _
    (fun _ _ hJ ↦ isClosedUnderColimitsOfShape_isCardinalPresentable C hJ)
    (isCardinalPresentable_monotone _ hκ.le)

variable [IsCardinalAccessibleCategory C κ₁]

def prop (J : Type w) [PartialOrder J] (A : Set J) : Prop :=
  IsCardinalFiltered A κ₁ ∧ HasCardinalLT A κ₂

variable {C} {X : C} {J : Type w} [PartialOrder J]
  (p : (isCardinalPresentable C κ₁).ColimitOfShape J X)

instance (A : Subtype (prop κ₁ κ₂ J)) :
    HasColimit ((Subtype.mono_coe A.val).functor ⋙ p.diag) := by
  have : IsCardinalFiltered (Subtype A.val) κ₁ := A.prop.1
  infer_instance

abbrev singleton (j : J) : Subtype (prop κ₁ κ₂ J) :=
  ⟨{j}, by
    letI : OrderTop ({j} : Set J) :=
      { top := ⟨j, by simp⟩
        le_top := by simp }
    exact isCardinalFiltered_of_hasTerminal _ _,
    hasCardinalLT_of_finite _ _ (IsRegular.aleph0_le Fact.out)⟩

abbrev pair {j j' : J} (h : j ≤ j') : Subtype (prop κ₁ κ₂ J) :=
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

noncomputable abbrev colimit (A : Subtype (prop κ₁ κ₂ J)) : C :=
    Limits.colimit ((Subtype.mono_coe A.val).functor ⋙ p.diag)

noncomputable abbrev colimit.ι (A : Subtype (prop κ₁ κ₂ J)) (a : J) (ha : a ∈ A.val) :
    p.diag.obj a ⟶ colimit κ₁ κ₂ p A :=
  Limits.colimit.ι ((Subtype.mono_coe A.val).functor ⋙ p.diag) ⟨a, ha⟩

omit [Fact κ₂.IsRegular] in
@[reassoc (attr := simp)]
lemma colimit.w (A : Subtype (prop κ₁ κ₂ J)) {a b : J} (hab : a ≤ b) (ha : a ∈ A.val)
    (hb : b ∈ A.val) :
    p.diag.map (homOfLE hab) ≫ colimit.ι κ₁ κ₂ p A b hb = colimit.ι κ₁ κ₂ p A a ha :=
  Limits.colimit.w ((Subtype.mono_coe A.val).functor ⋙ p.diag)
    (j := ⟨a, ha⟩) (j' := ⟨b, hb⟩) (homOfLE hab)

noncomputable def colimit.map {A₁ A₂ : Subtype (prop κ₁ κ₂ J)} (hA : A₁ ≤ A₂) :
    colimit κ₁ κ₂ p A₁ ⟶ colimit κ₁ κ₂ p A₂ :=
  colimit.desc _ (Cocone.mk _
    { app j := colimit.ι κ₁ κ₂ p A₂ j.val (hA j.prop)
      naturality j₁ j₂ f := by
        simpa using colimit.w κ₁ κ₂ p A₂ (leOfHom f) (hA j₁.prop) (hA j₂.prop) })

omit [Fact κ₂.IsRegular] in
@[reassoc (attr := simp)]
lemma colimit.ι_map {A₁ A₂ : Subtype (prop κ₁ κ₂ J)} (hA : A₁ ≤ A₂) (j : J) (hj : j ∈ A₁.val) :
    colimit.ι κ₁ κ₂ p A₁ j hj ≫ colimit.map κ₁ κ₂ p hA = colimit.ι κ₁ κ₂ p A₂ j (hA hj) :=
  colimit.ι_desc ..

omit [Fact κ₂.IsRegular] in
@[ext]
lemma colimit.hom_ext {A : Subtype (prop κ₁ κ₂ J)} {T : C} {φ₁ φ₂ : colimit κ₁ κ₂ p A ⟶ T}
    (h : ∀ (j : J) (hj : j ∈ A.val), colimit.ι κ₁ κ₂ p A j hj ≫ φ₁ =
      colimit.ι κ₁ κ₂ p A j hj ≫ φ₂) :
    φ₁ = φ₂ := by
  ext
  apply h

noncomputable def colimit.π (A : Subtype (prop κ₁ κ₂ J)) : colimit κ₁ κ₂ p A ⟶ X :=
  colimit.desc _ (Cocone.mk _
    { app a := by exact p.ι.app a
      naturality _ _ _ := by simpa using p.ι.naturality _ })

omit [Fact κ₂.IsRegular] in
@[reassoc (attr := simp)]
lemma colimit.ι_π (A : Subtype (prop κ₁ κ₂ J)) (a : J) (ha : a ∈ A.val) :
    colimit.ι κ₁ κ₂ p A a ha ≫ colimit.π κ₁ κ₂ p A = p.ι.app a :=
  colimit.ι_desc ..

omit [Fact κ₂.IsRegular] in
@[reassoc (attr := simp)]
lemma colimit.map_π {A₁ A₂ : Subtype (prop κ₁ κ₂ J)} (hA : A₁ ≤ A₂) :
    colimit.map κ₁ κ₂ p hA ≫ colimit.π κ₁ κ₂ p A₂ = colimit.π κ₁ κ₂ p A₁ := by
  ext
  simp

@[simps]
noncomputable def functor : Subtype (prop κ₁ κ₂ J) ⥤ C where
  obj A := colimit κ₁ κ₂ p A
  map f := colimit.map κ₁ κ₂ p f.le
  map_id _ := by ext; simp
  map_comp f g := by ext; simp

@[simps]
noncomputable def cocone : Cocone (functor κ₁ κ₂  p) where
  pt := X
  ι.app j := colimit.π κ₁ κ₂ p j

section

namespace isColimit

variable {κ₁ κ₂ p} (s : Cocone (functor κ₁ κ₂ p))

@[simps]
noncomputable def coconeDesc : Cocone p.diag where
  pt := s.pt
  ι.app j := colimit.ι _ _ _ _ _ (by simp) ≫ s.ι.app (singleton κ₁ κ₂ j)
  ι.naturality j j' f := by
    simpa [← s.w (homOfLE (le_pair κ₁ κ₂ (leOfHom f))),
        ← s.w (homOfLE (le_pair' κ₁ κ₂ (leOfHom f)))]
      using colimit.w_assoc ..

noncomputable def desc : X ⟶ s.pt := p.isColimit.desc (coconeDesc s)

@[reassoc (attr := simp)]
lemma fac (j : J) :
    dsimp% p.ι.app j ≫ desc s =
      colimit.ι _ _ _ _ _ (by simp) ≫ s.ι.app (singleton κ₁ κ₂ j) :=
  p.isColimit.fac (coconeDesc s) j

@[reassoc]
lemma fac' (A : Subtype (prop κ₁ κ₂ J)) :
    colimit.π κ₁ κ₂ p A ≫ desc s = s.ι.app A := by
  ext j hj
  let φ : singleton κ₁ κ₂ j ⟶ A := homOfLE (by
    rw [Subtype.mk_le_mk]
    simpa)
  simp [colimit.ι_π_assoc, fac, ← s.w φ]

end isColimit

open isColimit in
noncomputable def isColimit : IsColimit (cocone κ₁ κ₂ p) where
  desc s := desc s
  fac s A := fac' s A
  uniq s m hm :=
    p.isColimit.hom_ext (fun j ↦ by simp [fac s j, ← hm])

end

variable {κ₁ κ₂} in
include hκ' in
lemma isCardinalFiltered_subtype_prop [IsCardinalFiltered J κ₁] :
    IsCardinalFiltered (Subtype (prop κ₁ κ₂ J)) κ₂ :=
  isCardinalFiltered_preorder _ _ (fun K f hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    obtain ⟨B, hB₁, hB₂, hB₃⟩ := hκ' (⋃ (k : K), (f k).val)
      (hasCardinalLT_iUnion _ hK (fun k ↦ (f k).prop.2))
    exact ⟨⟨B, hB₂, hB₃⟩, fun k ↦ (Set.subset_iUnion _ k).trans hB₁⟩)

variable {κ₁ κ₂} (C) in
include hκ hκ' in
lemma isCardinalFilteredGenerator :
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
    refine ⟨Subtype (prop κ₁ κ₂ J), inferInstance, isCardinalFiltered_subtype_prop hκ',
      ⟨{ diag := _, ι := _, isColimit := isColimit κ₁ κ₂ p, prop_diag_obj A := ?_ }⟩⟩
    have : (generator κ₁ κ₂ C).IsClosedUnderColimitsOfShape (Subtype A.val) := by
      apply ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
      rw [hasCardinalLT_arrow_iff_of_isThin _ _ (IsRegular.aleph0_le Fact.out)]
      exact A.prop.2
    exact ObjectProperty.prop_colimit _ _
      (fun ⟨a, ha⟩ ↦ ObjectProperty.le_colimitsCardinalClosure _ _ _
        (p.prop_diag_obj a))

end isCardinalAccessible

include hκ hκ' in
open isCardinalAccessible in
lemma isCardinalAccessible'
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
  tfae_have 5 → 3 := fun h' C _ _ ↦ isCardinalAccessible' h (fun A hA ↦ h' A hA) C
  tfae_finish

lemma exists_cofinal (h : SharplyLT κ₁ κ₂)
    {X : Type w} (hX : HasCardinalLT X κ₂) :
    ∃ (A : Set (CardinalFilteredPoset.SetCardinalLT κ₁ X)),
      HasCardinalLT A κ₂ ∧ IsCofinal A := by
  have := (tfae h.lt).out 1 3
  exact this.1 h.isCardinalAccessible_cardinalDirectedPoset X hX

lemma exists_isCardinalFiltered_set (h : SharplyLT κ₁ κ₂)
    {X : Type w} [PartialOrder X] [IsCardinalFiltered X κ₁]
    (A : Set X) (hA : HasCardinalLT A κ₂) :
    ∃ (B : Set X), A ⊆ B ∧ IsCardinalFiltered B κ₁ ∧ HasCardinalLT B κ₂ := by
  have := (tfae h.lt).out 1 4
  exact this.1 h.isCardinalAccessible_cardinalDirectedPoset A hA

lemma isCardinalAccessible (h : SharplyLT κ₁ κ₂)
    (C : Type u) [Category.{v} C] [IsCardinalAccessibleCategory C κ₁] :
    IsCardinalAccessibleCategory C κ₂ :=
  isCardinalAccessible' h.lt h.exists_isCardinalFiltered_set C

lemma trans (h₁₂ : SharplyLT κ₁ κ₂) {κ₃ : Cardinal.{w}} [Fact κ₃.IsRegular]
    (h₂₃ : SharplyLT κ₂ κ₃) :
    SharplyLT κ₁ κ₃ where
  lt := h₁₂.lt.trans h₂₃.lt
  isCardinalAccessible_cardinalDirectedPoset := by
    have := h₁₂.isCardinalAccessible_cardinalDirectedPoset
    exact h₂₃.isCardinalAccessible _

end SharplyLT

end Cardinal
