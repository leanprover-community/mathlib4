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
      refine (C.prop.of_le h₀.le).of_injective (fun ⟨c, hc⟩ ↦ ⟨⟨c, ?_⟩, ?_⟩)
        (fun c₁ c₂ hc ↦ ?_)
      · simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hc
        exact hc.choose
      · simp only [Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hc
        exact hc.choose_spec
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

namespace SharplyLT

lemma le (h : SharplyLT κ₁ κ₂) : κ₁ ≤ κ₂ := h.lt.le

section

/-- Whan `k₁` is sharply smaller than `κ₂`, and `C` is a `κ₁`-accessible category, this
is a property of objects which allows to show that `C` is a `κ₂`-accessible category.
This property is defined as the closure of `κ₁`-presentable objects under
colimits of shape `J` for categories `J` such that `Arrow J` is of cardinality `< κ₂`. -/
abbrev generator (_ : SharplyLT κ₁ κ₂) (C : Type u) [Category.{v} C] :
    ObjectProperty C :=
  (isCardinalPresentable C κ₁).colimitsCardinalClosure κ₂

variable (h : SharplyLT κ₁ κ₂) (C : Type u) [Category.{v} C]

lemma generator_le_isCardinalPresentable [LocallySmall.{w} C] :
    h.generator C ≤ isCardinalPresentable C κ₂ :=
  ObjectProperty.colimitsCardinalClosure_le _ _
    (fun _ _ hJ ↦ isClosedUnderColimitsOfShape_isCardinalPresentable C hJ)
    (isCardinalPresentable_monotone _ h.le)

variable [IsCardinalAccessibleCategory C κ₁]

namespace isCardinalFilteredGenerator

def prop (_ : SharplyLT κ₁ κ₂) (J : Type w) [PartialOrder J] (A : Set J) : Prop :=
  IsCardinalFiltered (Subtype A) κ₁ ∧ HasCardinalLT (Subtype A) κ₂

variable {h} {C} {X : C} {J : Type w} [PartialOrder J]
  (p : (isCardinalPresentable C κ₁).ColimitOfShape J X)

instance (A : Subtype (prop h J)) :
    HasColimit ((Subtype.mono_coe A.val).functor ⋙ p.diag) := by
  have := A.prop.1
  infer_instance

noncomputable abbrev colimit (A : Subtype (prop h J)) : C :=
    Limits.colimit ((Subtype.mono_coe A.val).functor ⋙ p.diag)

noncomputable abbrev colimit.ι (A : Subtype (prop h J)) (a : J) (ha : a ∈ A.val) :
    p.diag.obj a ⟶ colimit p A :=
  Limits.colimit.ι ((Subtype.mono_coe A.val).functor ⋙ p.diag) ⟨a, ha⟩

@[reassoc (attr := simp)]
lemma colimit.w (A : Subtype (prop h J)) {a b : J} (hab : a ≤ b) (ha : a ∈ A.val)
    (hb : b ∈ A.val) :
    p.diag.map (homOfLE hab) ≫ colimit.ι p A b hb = colimit.ι p A a ha :=
  Limits.colimit.w ((Subtype.mono_coe A.val).functor ⋙ p.diag)
    (j := ⟨a, ha⟩) (j' := ⟨b, hb⟩) (homOfLE hab)

noncomputable def colimit.map {A₁ A₂ : Subtype (prop h J)} (hA : A₁ ≤ A₂) :
    colimit p A₁ ⟶ colimit p A₂ :=
  colimit.desc _ (Cocone.mk _
    { app j := colimit.ι p A₂ j.val (hA j.prop)
      naturality j₁ j₂ f := by
        simpa using colimit.w p A₂ (leOfHom f) (hA j₁.prop) (hA j₂.prop) })

@[reassoc (attr := simp)]
lemma colimit.ι_map {A₁ A₂ : Subtype (prop h J)} (hA : A₁ ≤ A₂) (j : J) (hj : j ∈ A₁.val) :
    colimit.ι p A₁ j hj ≫ colimit.map p hA = colimit.ι p A₂ j (hA hj) :=
  colimit.ι_desc ..

@[ext high]
lemma colimit.hom_ext {A : Subtype (prop h J)} {T : C} {φ₁ φ₂ : colimit p A ⟶ T}
    (h : ∀ (j : J) (hj : j ∈ A.val), colimit.ι p A j hj ≫ φ₁ = colimit.ι p A j hj ≫ φ₂) :
    φ₁ = φ₂ := by
  ext
  apply h

noncomputable def colimit.π (A : Subtype (prop h J)) : colimit p A ⟶ X :=
  colimit.desc _ (Cocone.mk _
    { app a := by exact p.ι.app a
      naturality _ _ _ := by simpa using p.ι.naturality _ })

@[reassoc (attr := simp)]
lemma colimit.ι_π (A : Subtype (prop h J)) (a : J) (ha : a ∈ A.val) :
    colimit.ι p A a ha ≫ colimit.π p A = p.ι.app a :=
  colimit.ι_desc ..

@[reassoc (attr := simp)]
lemma colimit.map_π {A₁ A₂ : Subtype (prop h J)} (hA : A₁ ≤ A₂) :
    colimit.map p hA ≫ colimit.π p A₂ = colimit.π p A₁ := by
  ext
  simp

variable (h) in
@[simps]
noncomputable def functor : Subtype (prop h J) ⥤ C where
  obj A := colimit p A
  map f := colimit.map p f.le
  map_id _ := by ext; simp
  map_comp f g := by ext; simp

variable (h) in
@[simps]
noncomputable def cocone : Cocone (functor h p) where
  pt := X
  ι.app j := colimit.π p j

variable (h) in
def isColimit [IsCardinalFiltered J κ₁] : IsColimit (cocone h p) := sorry

instance [IsCardinalFiltered J κ₁] : IsCardinalFiltered (Subtype (prop h J)) κ₂ := by
  sorry

end isCardinalFilteredGenerator

open isCardinalFilteredGenerator in
lemma isCardinalFilteredGenerator :
    (h.generator C).IsCardinalFilteredGenerator κ₂ where
  le_isCardinalPresentable := h.generator_le_isCardinalPresentable C
  exists_colimitsOfShape X := by
    have hκ₁ := isCardinalFilteredGenerator_isCardinalPresentable C κ₁
    obtain ⟨J, _, _, ⟨p⟩⟩ :
        ∃ (J : Type w) (_ : PartialOrder J) (_ : IsCardinalFiltered J κ₁),
      Nonempty ((isCardinalPresentable C κ₁).ColimitOfShape J X) := by
        obtain ⟨J₀, _, _, ⟨p₀⟩⟩ := hκ₁.exists_colimitsOfShape X
        obtain ⟨J, _, _, F, _⟩ := IsCardinalFiltered.exists_cardinal_directed J₀ κ₁
        exact ⟨_, _, inferInstance, ⟨p₀.reindex F⟩⟩
    refine ⟨Subtype (prop h J), inferInstance, inferInstance,
      ⟨{ diag := _, ι := _, isColimit := isColimit h p, prop_diag_obj A := ?_ }⟩⟩
    have : (h.generator C).IsClosedUnderColimitsOfShape (Subtype A.val) := by
      apply ObjectProperty.isClosedUnderColimitsOfShape_colimitsCardinalClosure
      have := A.prop.2
      sorry
    exact ObjectProperty.prop_colimit _ _
      (fun ⟨a, ha⟩ ↦ ObjectProperty.le_colimitsCardinalClosure _ _ _
        (p.prop_diag_obj a))

end

lemma isCardinalAccessible (h : SharplyLT κ₁ κ₂)
    (C : Type u) [Category.{v} C] [IsCardinalAccessibleCategory C κ₁] :
    IsCardinalAccessibleCategory C κ₂ where
  toHasCardinalFilteredColimits := .of_le C h.le
  exists_generator :=
    ⟨_, inferInstance, h.isCardinalFilteredGenerator C⟩

lemma trans (h₁₂ : SharplyLT κ₁ κ₂) {κ₃ : Cardinal.{w}} [Fact κ₃.IsRegular]
    (h₂₃ : SharplyLT κ₂ κ₃) :
    SharplyLT κ₁ κ₃ where
  lt := h₁₂.lt.trans h₂₃.lt
  isCardinalAccessible_cardinalDirectedPoset := by
    have := h₁₂.isCardinalAccessible_cardinalDirectedPoset
    exact h₂₃.isCardinalAccessible _

end SharplyLT

end Cardinal
