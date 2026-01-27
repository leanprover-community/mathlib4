module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Presentable.StrongGenerator

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits Functor

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

lemma nonempty_of_isCardinalFiltered {J : Type*} [Category* J] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (hJ : IsCardinalFiltered J κ) : Nonempty J := by
  obtain ⟨c⟩ := hJ.1 (Functor.empty _) <| hasCardinalLT_of_finite _ _
    (Cardinal.IsRegular.aleph0_le Fact.out)
  exact ⟨c.pt⟩

instance (F : C ⥤ D) (G : D ⥤ E) [IsAccessible.{w} F] [IsAccessible.{w} G] :
    IsAccessible.{w} (F ⋙ G) where
  exists_cardinal := by
    obtain ⟨κF, _, hF⟩ := IsAccessible.exists_cardinal (F := F)
    obtain ⟨κG, _, hG⟩ := IsAccessible.exists_cardinal (F := G)
    have h₁ : κF ≤ κF ⊔ κG := by simp
    have h₂ : κG ≤ κF ⊔ κG := by simp
    have : Fact <| (κF ⊔ κG).IsRegular := ⟨iteInduction (fun a ↦ Fact.out) (fun a ↦ Fact.out)⟩
    replace hF := isCardinalAccessible_of_le F h₁
    replace hG := isCardinalAccessible_of_le G h₂
    exact ⟨κF ⊔ κG, inferInstance, inferInstance⟩

lemma isCardinalAccessibleCategory_for_arbitrarily_large_cardinals
    {κ κ' : Cardinal.{w}} [Fact κ.IsRegular] [Fact κ'.IsRegular] [IsCardinalAccessibleCategory C κ]
    (h : κ ≤ κ') : ∃ (κ'' : Cardinal.{w}) (_ : Fact κ''.IsRegular), κ' ≤ κ'' ∧
      IsCardinalAccessibleCategory C κ'' := by
  sorry

-- #20267 contains WIP on this
instance (L : C ⥤ E) (R : D ⥤ E) (κ : Cardinal.{w}) [Fact κ.IsRegular] [IsCardinalAccessible L κ]
    [IsCardinalAccessible R κ] [IsCardinalAccessibleCategory C κ]
    [IsCardinalAccessibleCategory D κ] : IsCardinalAccessibleCategory (Comma L R) κ where
  toHasCardinalFilteredGenerator := sorry
  hasColimitsOfShape J _ _ := by
    have := preservesColimitsOfShape_of_isCardinalAccessible L κ J
    infer_instance

instance (L : C ⥤ E) (R : D ⥤ E) [IsAccessible.{w} L] [IsAccessible.{w} R] :
    IsAccessibleCategory.{w} (Comma L R) := by
  have : IsAccessibleCategory.{w} C := sorry
  have : IsAccessibleCategory.{w} D := sorry
  obtain ⟨κC, _, _⟩ := IsAccessibleCategory.exists_cardinal (C := C)
  obtain ⟨κD, _, _⟩ := IsAccessibleCategory.exists_cardinal (C := D)
  obtain ⟨κL, _, _⟩ := IsAccessible.exists_cardinal (F := L)
  obtain ⟨κR, _, _⟩ := IsAccessible.exists_cardinal (F := R)
  let κ' := κC ⊔ κD ⊔ κL ⊔ κR
  have hC : κC ≤ κ' := by simp [κ']
  have hD : κD ≤ κ' := by simp [κ']
  have hL : κL ≤ κ' := by simp [κ']
  have hR : κR ≤ κ' := by simp [κ']
  have : Fact κ'.IsRegular := ⟨iteInduction (fun a ↦ Fact.out) (fun a ↦
    iteInduction (fun a ↦ Fact.out) (fun a ↦ iteInduction (fun a ↦ Fact.out) (fun a ↦ Fact.out)))⟩
  obtain ⟨κ₁, _, _⟩ := isCardinalAccessibleCategory_for_arbitrarily_large_cardinals (C := C) hC
  obtain ⟨κ₂, _, _⟩ := isCardinalAccessibleCategory_for_arbitrarily_large_cardinals (C := D) hD
  -- `isCardinalAccessibleCategory_for_arbitrarily_large_cardinals` is not enough, need
  -- to simultaneously obtain a `κ` that works for `C`, `D`, `L` and `R`. This is possible e.g. by
  -- Adamek-Rosicky 2.11-2.13.
  let κ : Cardinal.{w} := sorry
  have : Fact κ.IsRegular := sorry
  have hhC : IsCardinalAccessibleCategory.{w} C κ := sorry
  have hhD : IsCardinalAccessibleCategory.{w} D κ := sorry
  have hhL : IsCardinalAccessible.{w} L κ := sorry
  have hhR : IsCardinalAccessible.{w} R κ := sorry
  refine ⟨κ, inferInstance, inferInstance⟩

instance (L : C ⥤ E) (R : D ⥤ E) [IsAccessible.{w} L] [IsAccessible.{w} R] :
    IsAccessible.{w} (Comma.fst L R) := sorry

instance (L : C ⥤ E) (R : D ⥤ E) [IsAccessible.{w} L] [IsAccessible.{w} R] :
    IsAccessible.{w} (Comma.snd L R) := sorry

lemma solutionSetCondition_of_isAccessible (R : C ⥤ D) [IsAccessible.{w} R] :
    SolutionSetCondition.{w} R := by
  intro A
  let CA : D ⥤ D := (Functor.const _).obj A
  have : IsAccessible.{w} CA := by
    dsimp [CA]
    obtain ⟨κ, _, this⟩ := IsAccessible.exists_cardinal (F := R)
    refine ⟨κ, inferInstance, ⟨fun J _ hJ ↦ ?_⟩⟩
    let j := (nonempty_of_isCardinalFiltered κ hJ).some
    exact ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨{
      desc s := s.ι.app j
      fac s j' := by
        rw [isCardinalFiltered_iff] at hJ
        obtain ⟨k, hk⟩ := @hJ.1 ({j, j'} : Set J) Subtype.val
          (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
        have hj := s.ι.naturality (hk ⟨j, by simp⟩).some
        have hj' := s.ι.naturality (hk ⟨j', by simp⟩).some
        simp_all
      uniq s m h := by simpa using h j }⟩⟩⟩
  have : IsAccessibleCategory.{w} <| Comma CA R := inferInstance
  obtain ⟨κ, _, this⟩ := this
  have h₁ := this.1
  have _ := this.2
  obtain ⟨P, _, hP⟩ := h₁
  obtain ⟨Q, _, _, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  obtain ⟨_, hP⟩ := hP
  have : IsAccessible.{w} (Comma.snd CA R) := inferInstance
  refine ⟨Shrink <| Subtype Q, fun b ↦ (equivShrink _ |>.symm b).val.right,
    fun b ↦ (equivShrink _ |>.symm b).val.hom, ?_⟩
  intro X h
  obtain ⟨J, _, hJ, ⟨⟨⟨diag, ι, hc⟩, hx⟩⟩⟩ := hP (Comma.mk (R.obj X) _ h)
  let j := (nonempty_of_isCardinalFiltered κ hJ).some
  have : P (diag.obj j) := hx j
  have := hPQ _ this
  obtain ⟨x, qx, ⟨ix⟩⟩ := this
  refine ⟨equivShrink _ ⟨x, qx⟩, eqToHom (by simp) ≫ ix.inv.right ≫ (ι.app _).right, ?_⟩
  simp [← Category.assoc, eqToHom_map, ← CommaMorphism.w, CA]

private lemma aux {C : Type u₁} {D : Type u₂} [Category.{w} C] [Category.{w} D]
    (R : C ⥤ D) [IsLocallyPresentable.{w} C] [IsLocallyPresentable.{w} D]
    [IsAccessible.{w} R] [PreservesLimitsOfSize.{w, w} R]
    [HasLimits C] : R.IsRightAdjoint := by
  refine isRightAdjoint_of_preservesLimits_of_solutionSetCondition _ fun A ↦ ?_
  obtain ⟨κ₁, _, ⟨h⟩⟩ := IsAccessible.exists_cardinal (F := R)
  obtain ⟨κ₀₁, _, h₁⟩ := IsLocallyPresentable.exists_cardinal (C := C)
  obtain ⟨κ₀₂, _, h₂⟩ := IsLocallyPresentable.exists_cardinal (C := D)
  obtain ⟨κ₀, _, hC, hD⟩ : ∃ (κ₀ : Cardinal.{w}) (_ : Fact κ₀.IsRegular),
      IsCardinalLocallyPresentable C κ₀ ∧ IsCardinalLocallyPresentable D κ₀ := by
    have : Fact (κ₀₁ ⊔ κ₀₂).IsRegular := ⟨iteInduction (fun a ↦ Fact.out) (fun a ↦ Fact.out)⟩
    have h₀₁ : κ₀₁ ≤ κ₀₁ ⊔ κ₀₂ := by simp
    have h₀₂ : κ₀₂ ≤ κ₀₁ ⊔ κ₀₂ := by simp
    refine ⟨κ₀₁ ⊔ κ₀₂, inferInstance, .of_le _ h₀₁, .of_le _ h₀₂⟩
  obtain ⟨P, _, ⟨le, h⟩⟩ := hD.1
  obtain ⟨J, _, cf, ⟨⟨⟨diag, ι, hc⟩, hx⟩⟩⟩ := h A
  obtain ⟨κ', hκ', lt⟩ := HasCardinalLT.exists_regular_cardinal (Arrow J)
  obtain ⟨κ, _, h₀, h₁, ⟨_⟩⟩ : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), κ₀ ≤ κ ∧ κ₁ ≤ κ ∧
      isCardinalPresentable D κ A := by
    have : Fact (κ₀ ⊔ κ₁ ⊔ κ').IsRegular :=
      ⟨iteInduction (fun a ↦ hκ') (fun a ↦ iteInduction (fun a ↦ Fact.out) (fun a ↦ Fact.out))⟩
    have hκ₀ : κ₀ ≤ κ₀ ⊔ κ₁ ⊔ κ' := by simp
    have hκ₁ : κ₁ ≤ κ₀ ⊔ κ₁ ⊔ κ' := by simp
    have (k : J) : IsCardinalPresentable (diag.obj k) (κ₀ ⊔ κ₁ ⊔ κ') := by
      have := le _ (hx k)
      dsimp [isCardinalPresentable] at this
      apply isCardinalPresentable_of_le _ hκ₀
    exact ⟨κ₀ ⊔ κ₁ ⊔ κ', inferInstance, hκ₀, hκ₁,
      isCardinalPresentable_of_isColimit _ hc _ (lt.of_le (by simp))⟩
  obtain ⟨P, _, ⟨_, h⟩⟩ := (IsCardinalLocallyPresentable.of_le C h₀).1
  obtain ⟨Q, _, _, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  refine ⟨(X : Shrink (Subtype Q)) × (A ⟶ R.obj ((equivShrink (Subtype Q)).symm X).val),
    fun X ↦ ((equivShrink _).symm X.fst).val, fun X ↦ X.snd, fun X f ↦ ?_⟩
  obtain ⟨J, _, _, ⟨⟨⟨diag, ι, hc⟩, hx⟩⟩⟩ := h X
  have : IsCardinalFiltered J κ₁ := IsCardinalFiltered.of_le J h₁
  replace hc := isColimitOfPreserves (coyoneda.obj ⟨A⟩) (isColimitOfPreserves R hc)
  obtain ⟨j, hj, w⟩ := Types.jointly_surjective_of_isColimit hc f
  obtain ⟨d, hd, ⟨i⟩⟩ := hPQ _ (hx j)
  exact ⟨⟨equivShrink _ ⟨d, hd⟩, hj ≫ R.map i.hom ≫ R.map (eqToHom (by simp))⟩,
    eqToHom (by simp) ≫ i.inv ≫ ι.app _, by simp [← w]⟩

instance {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (R : C ⥤ D) [IsLocallyPresentable.{w} C] [IsLocallyPresentable.{w} D]
    [IsAccessible.{w} R] [PreservesLimitsOfSize.{w, w} R]
    [HasLimitsOfSize.{w, w} C] : R.IsRightAdjoint := by
  obtain ⟨κC, _, h₁⟩ := IsLocallyPresentable.exists_cardinal (C := C)
  obtain ⟨κD, _, h₂⟩ := IsLocallyPresentable.exists_cardinal (C := D)
  obtain ⟨κR, _, h₃⟩ := IsAccessible.exists_cardinal (F := R)
  let R' := (ShrinkHoms.equivalence.{w} C).symm.functor ⋙ R ⋙ (ShrinkHoms.equivalence.{w} D).functor
  have : IsLocallyPresentable.{w} (ShrinkHoms C) :=
    ⟨κC, inferInstance, (ShrinkHoms.equivalence.{w} C).isCardinalLocallyPresentable _⟩
  have : IsLocallyPresentable.{w} (ShrinkHoms D) :=
    ⟨κD, inferInstance, (ShrinkHoms.equivalence.{w} D).isCardinalLocallyPresentable _⟩
  have : IsAccessible.{w} R' := ⟨κR, inferInstance, inferInstance⟩
  have : HasLimits (ShrinkHoms C) :=
    has_limits_of_equivalence (ShrinkHoms.equivalence.{w} C).inverse
  have : IsRightAdjoint R' := by apply aux
  let i : R ≅ (ShrinkHoms.equivalence.{w} C).functor ⋙ R' ⋙
      (ShrinkHoms.equivalence.{w} D).inverse :=
    .isoCompInverse <| .isoInverseComp (.refl _ : _ ≅ R')
  exact isRightAdjoint_of_iso i.symm

end CategoryTheory.Adjunction
