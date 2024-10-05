import Mathlib.CategoryTheory.Triangulated.Filtered.ForgetHalf

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

namespace FilteredTriangulated

variable {C : Type _} [Category C] [HasZeroObject C]  [Preadditive C] [HasShift C (ℤ × ℤ)]
  [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C] [IsTriangulated C]

variable [∀ (X : C) (n : ℤ), Decidable (IsZero ((Gr'' n).obj X))]

noncomputable def HalfForgetObj (X : C) : hP.Core' := by
  by_cases IsLE X 0
  · exact (existence_omega X).choose
  · exact 0

noncomputable def IdToHalfForgetApp (X : C) : X ⟶ (HalfForgetObj X).1 := by
  dsimp [HalfForgetObj]
  by_cases h : IsLE X 0
  · simp only [h, ↓reduceDIte]
    exact (existence_omega X).choose_spec.choose
  · simp only [h, ↓reduceDIte]
    exact 0

lemma HalfForgetObj_prop (X : C) [IsLE X 0] (Y : C) [IsGE Y 0] :
    Function.Bijective (fun (f : (HalfForgetObj X).1 ⟶ Y) ↦ (IdToHalfForgetApp X) ≫ f) := by
  dsimp [HalfForgetObj, IdToHalfForgetApp]
  have h : IsLE X 0 := inferInstance
  simp only [h, ↓reduceDIte, congrArg_cast_hom_right, assoc]
  refine Function.Bijective.comp ?_ (IsIso.comp_left_bijective _)
  exact (existence_omega X).choose_spec.choose_spec Y inferInstance

noncomputable def HalfForgetMap {X Y : C} (f : X ⟶ Y) : HalfForgetObj X ⟶ HalfForgetObj Y := by
  by_cases IsLE X 0
  · by_cases IsLE Y 0
    · exact ((HalfForgetObj_prop X (HalfForgetObj Y).1).2 (f ≫ IdToHalfForgetApp Y)).choose
    · exact 0
  · exact  0

@[simp]
lemma HalfForgetMap_prop {X Y : C} (f : X ⟶ Y) [IsLE X 0] [IsLE Y 0] :
    IdToHalfForgetApp X ≫ HalfForgetMap f = f ≫ IdToHalfForgetApp Y := by
  dsimp [HalfForgetMap]
  have hX : IsLE X 0 := inferInstance
  have hY : IsLE Y 0 := inferInstance
  simp only [hX, ↓reduceDIte, hY, ↓reduceIte]
  exact ((HalfForgetObj_prop X (HalfForgetObj Y).1).2 (f ≫ IdToHalfForgetApp Y)).choose_spec

lemma HalfForgetMapId {X : C} : HalfForgetMap (𝟙 X) = 𝟙 (HalfForgetObj X) := by
  by_cases h : IsLE X 0
  · apply (HalfForgetObj_prop X (HalfForgetObj X).1).1
    simp only
    rw [HalfForgetMap_prop (𝟙 X), id_comp]; erw [comp_id]
  · simp only [HalfForgetObj, h, HalfForgetMap, ↓reduceDIte]
    have : IsZero (HalfForgetObj X) := by
      simp only [HalfForgetObj, h, ↓reduceDIte]
      exact Limits.isZero_zero _
    exact (Limits.IsZero.eq_zero_of_src this _).symm

lemma HalfForgetMapComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsLE Y 0] :
    HalfForgetMap (f ≫ g) = HalfForgetMap f ≫ HalfForgetMap g := by
  have hY : IsLE Y 0 := inferInstance
  by_cases hX : IsLE X 0
  · by_cases hZ : IsLE Z 0
    · apply (HalfForgetObj_prop X (HalfForgetObj Z).1).1
      simp only
      rw [HalfForgetMap_prop (f ≫ g)]
      conv_rhs => erw [← assoc]; rw [HalfForgetMap_prop f, assoc, HalfForgetMap_prop g, ← assoc]
    · simp only [HalfForgetObj, hX, hZ, HalfForgetMap, ↓reduceDIte, hY, comp_zero]
  · simp only [HalfForgetObj, hX, HalfForgetMap, ↓reduceDIte, hY, dite_eq_ite, zero_comp]

lemma HalfForgetMapComp' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hZ : ¬ (IsLE Z 0)) :
    HalfForgetMap (f ≫ g) = HalfForgetMap f ≫ HalfForgetMap g := by
  simp only [HalfForgetMap, hZ, ↓reduceDIte, dite_eq_ite, ite_self, comp_zero]

/- We construct `Forget X` as the colimit of `HalfForget X⟪n⟫` as `n` varies over `ℤ` (seen
as a poset category), with the transition maps given by `power_of_alpha`.-/

@[simp]
noncomputable def ForgetInductiveSystem_aux (X : C) : ℤ ⥤ C where
  obj a := (@shiftFunctor C _ _ _ Shift₂ a).obj X
  map := by
    intro a b f
    exact power_of_alpha X a b (b - a).natAbs
      (by rw [← Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom f)), add_sub_cancel])
  map_id a := by
    simp only [id_eq, eq_mpr_eq_cast, sub_self, Int.natAbs_zero]
    rw [power_of_alpha_zero', Iso.refl_hom]
  map_comp := by
    intro a b c f g
    simp only [id_eq, eq_mpr_eq_cast]
    have hab : (b - a).natAbs = b - a :=
      (Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom f))).symm
    have hbc : (c - b).natAbs = c - b :=
      (Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom g))).symm
    have hac : (c - a).natAbs = c - a :=
      (Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom (f ≫ g)))).symm
    rw [power_of_alpha_change_exponent X (c - a).natAbs ((b - a).natAbs + (c - b).natAbs)
      (by rw [← Nat.cast_inj (R := ℤ), Nat.cast_add, hab, hbc, hac, sub_add_sub_cancel'])
      a c (by rw [hac, add_sub_cancel])]
    exact (power_of_alpha_assoc X a b c (b - a).natAbs (c - b).natAbs
      (by rw [hab, add_sub_cancel]) (by rw [hbc, add_sub_cancel])).symm

lemma ForgetInductiveSystem_aux_prop (X : C) (a : ℤ) [IsLE X a] {b c : Set.Iic (-a)}
    (u : b ⟶ c) (Y : C) [IsGE Y 0] : Function.Bijective
    (fun (f : (ForgetInductiveSystem_aux X).obj c ⟶ Y) ↦
    ((ForgetInductiveSystem_aux X).map u ≫ f)) := by
  have : IsLE X (a + b.1 - b.1) := by rw [add_sub_cancel_right]; infer_instance
  have : IsGE Y (a + b.1 + ↑(c.1 - b.1).natAbs) := by
    rw [← Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom u)), add_assoc, add_sub_cancel]
    refine isGE_of_GE Y _ 0 ?_
    have := Set.mem_Iic.mp c.2; linarith
  refine adj_left_extended X Y b.1 c.1 (a + b) (c.1 - b.1).natAbs
    (by rw [← Int.eq_natAbs_of_zero_le (sub_nonneg.mpr (leOfHom u)), add_sub_cancel])

noncomputable def ForgetInductiveSystem (X : C) : ℤ ⥤ hP.Core' where
  obj a := HalfForgetObj ((ForgetInductiveSystem_aux X).obj a)
  map f := HalfForgetMap ((ForgetInductiveSystem_aux X).map f)
  map_id a := by
    simp only
    rw [Functor.map_id, HalfForgetMapId]
  map_comp := by
    intro a b c f g
    simp only
    rw [Functor.map_comp]
    by_cases h : IsLE X (-b)
    · have : IsLE ((ForgetInductiveSystem_aux X).obj b) 0 := by
        dsimp [ForgetInductiveSystem_aux]
        exact isLE_shift X (-b) b 0 (by linarith)
      exact HalfForgetMapComp ((ForgetInductiveSystem_aux X).map f)
        ((ForgetInductiveSystem_aux X).map g)
    · have : ¬ IsLE ((ForgetInductiveSystem_aux X).obj c) 0 := by
        dsimp [ForgetInductiveSystem_aux]
        intro habs
        have : IsLE X (-c) := isLE_of_shift X (-c) c 0 (by linarith)
        have : IsLE X (-b ) := isLE_of_LE X (- c) (- b) (by have := leOfHom g; linarith)
        exact h this
      exact HalfForgetMapComp' ((ForgetInductiveSystem_aux X).map f)
        ((ForgetInductiveSystem_aux X).map g) this

lemma ForgetInductiveSystem_prop (X : C) (a : ℤ) [IsLE X a] {b c : Set.Iic (-a)}
    (u : b ⟶ c) (Y : C) [IsGE Y 0] : Function.Bijective
    (fun (f : ((ForgetInductiveSystem X).obj c).1 ⟶ Y) ↦
    ((fullSubcategoryInclusion _).map ((ForgetInductiveSystem X).map u) ≫ f)) := by
  simp only [ForgetInductiveSystem, fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map]
  have : IsLE ((ForgetInductiveSystem_aux X).obj b.1) 0 := by
    simp only [ForgetInductiveSystem_aux]
    have : IsLE X (-b.1) := isLE_of_LE X a (-b) (by have := Set.mem_Iic.mp b.2; linarith)
    refine isLE_shift X (-b) b.1 0 (by linarith)
  have : IsLE ((ForgetInductiveSystem_aux X).obj c.1) 0 := by
    simp only [ForgetInductiveSystem_aux]
    have : IsLE X (-c.1) := isLE_of_LE X a (-c) (by have := Set.mem_Iic.mp c.2; linarith)
    refine isLE_shift X (-c) c.1 0 (by linarith)
  rw [← Function.Bijective.of_comp_iff'
    (HalfForgetObj_prop ((ForgetInductiveSystem_aux X).obj b) Y) _]
  have heq : (fun (f : (HalfForgetObj ((ForgetInductiveSystem_aux X).obj b.1)).obj ⟶ Y) ↦
      IdToHalfForgetApp ((ForgetInductiveSystem_aux X).obj b.1) ≫ f) ∘
      (fun f ↦ HalfForgetMap ((ForgetInductiveSystem_aux X).map u) ≫ f) =
      (fun (f : (ForgetInductiveSystem_aux X).obj c ⟶ Y) ↦
      ((ForgetInductiveSystem_aux X).map u ≫ f)) ∘
      (fun (f : (HalfForgetObj ((ForgetInductiveSystem_aux X).obj c.1)).obj ⟶ Y) ↦
      IdToHalfForgetApp ((ForgetInductiveSystem_aux X).obj c.1) ≫ f) := by
    ext g
    simp only [Function.comp_apply]
    conv_lhs => rw [← assoc, HalfForgetMap_prop, assoc]
  rw [heq]
  apply Function.Bijective.comp
  · exact ForgetInductiveSystem_aux_prop X a u Y
  · exact HalfForgetObj_prop ((ForgetInductiveSystem_aux X).obj c) Y

lemma ForgetInductiveSystem_iso_of_le (X : C) (a : ℤ) [IsLE X a] {b c : Set.Iic (-a)}
    (u : b ⟶ c) : IsIso ((ForgetInductiveSystem X).map u) := by
  apply IsIso.mk
  have bij := ForgetInductiveSystem_prop X a u ((ForgetInductiveSystem X).obj b).1
  obtain ⟨f, hf⟩ := bij.2 (𝟙 ((ForgetInductiveSystem X).obj b))
  use f
  constructor
  · exact hf
  · have bij' := ForgetInductiveSystem_prop X a u ((ForgetInductiveSystem X).obj c).1
    apply bij'.1
    simp only [fullSubcategoryInclusion.obj, fullSubcategoryInclusion.map] at hf ⊢
    conv_lhs => erw [← assoc]; rw [hf]; erw [id_comp]
    erw [comp_id]

noncomputable abbrev ForgetInductiveSystemMap {X Y : C} (f : X ⟶ Y) (a : ℤ) :
    (ForgetInductiveSystem X).obj a ⟶ (ForgetInductiveSystem Y).obj a :=
  HalfForgetMap ((@shiftFunctor C _ _ _ Shift₂ a).map f)

lemma ForgetInductiveSystemMap_naturality {X Y : C} (f : X ⟶ Y) {a b : ℤ} (u : a ⟶ b)
    [IsLE X (-b)] [IsLE Y (-b)] :
    (ForgetInductiveSystem X).map u ≫ ForgetInductiveSystemMap f b =
    ForgetInductiveSystemMap f a ≫ (ForgetInductiveSystem Y).map u := by
  dsimp [ForgetInductiveSystem, ForgetInductiveSystemMap]
  have : IsLE ((@shiftFunctor C _ _ _ Shift₂ b).obj X) 0 := isLE_shift X (-b) b 0 (by linarith)
  have : IsLE ((@shiftFunctor C _ _ _ Shift₂ a).obj Y) 0 := by
    have := isLE_shift Y (-b) a (a - b) (by linarith)
    exact isLE_of_LE _ (a - b) 0 (by have := leOfHom u; linarith)
  conv_lhs => rw [← HalfForgetMapComp]
  conv_rhs => rw [← HalfForgetMapComp]
  rw [power_of_alpha_naturality f]

lemma ForgetInductiveSystemMap_naturality' {X Y : C} (f : X ⟶ Y) (a : ℤ) [IsLE X a] [IsLE Y a]
    {b c : Set.Iic (-a)} (u : b ⟶ c) :
    (ForgetInductiveSystem X).map u ≫ ForgetInductiveSystemMap f c.1 =
    ForgetInductiveSystemMap f b.1 ≫ (ForgetInductiveSystem Y).map u := by
  have : IsLE X (- c.1) := isLE_of_LE X a (-c) (by have := Set.mem_Iic.mp c.2; linarith)
  have : IsLE Y (- c.1) := isLE_of_LE Y a (-c) (by have := Set.mem_Iic.mp c.2; linarith)
  exact ForgetInductiveSystemMap_naturality f u

lemma ForgetInductiveSystem_hasLimit (X : C) : HasLimit (ForgetInductiveSystem X) := by
  set a := (hP.LE_exhaustive X).choose
  have : IsLE X a := {le := (hP.LE_exhaustive X).choose_spec}
  exact HasLimit_of_transition_eventually_iso
    (ForgetInductiveSystem X) (a := -a) (fun _ _ u ↦ ForgetInductiveSystem_iso_of_le X a u)

/- The definition of the functor `Forget`.-/

@[simp]
noncomputable def ForgetObj (X : C) : hP.Core' := by
  have := ForgetInductiveSystem_hasLimit X
  exact Limits.limit (ForgetInductiveSystem X)

@[simp]
noncomputable def ForgetMap {X Y : C} (f : X ⟶ Y) : ForgetObj X ⟶ ForgetObj Y := by
  have := ForgetInductiveSystem_hasLimit X
  have := ForgetInductiveSystem_hasLimit Y
  set a := (hP.LE_exhaustive X).choose
  have : IsLE X a := {le := (hP.LE_exhaustive X).choose_spec}
  set b := (hP.LE_exhaustive Y).choose
  have : IsLE Y b := {le := (hP.LE_exhaustive Y).choose_spec}
  refine Hom_of_almost_NatTrans _ _ (ForgetInductiveSystemMap f) ?_
  use -max a b
  have : IsLE X (max a b) := isLE_of_LE X a (max a b) (le_max_left _ _)
  have : IsLE Y (max a b) := isLE_of_LE Y b (max a b) (le_max_right _ _)
  exact (fun _ _ u ↦ ForgetInductiveSystemMap_naturality' f (max a b) u)

noncomputable def Forget : C ⥤ hP.Core' where
  obj X := ForgetObj X
  map f := ForgetMap f
  map_id X := by
    have := ForgetInductiveSystem_hasLimit X
    refine Hom_of_almost_NatTrans_id _ _ ?_
    use 0
    simp only [ForgetInductiveSystemMap, ForgetInductiveSystem_aux, Functor.map_id, Subtype.forall,
      Set.mem_Iic]
    exact fun _ _ ↦ HalfForgetMapId
  map_comp := by
    intro X Y Z f g
    have := ForgetInductiveSystem_hasLimit X
    have := ForgetInductiveSystem_hasLimit Y
    have := ForgetInductiveSystem_hasLimit Z
    simp only [ForgetObj, ForgetMap]
    rw [Hom_of_almost_NatTrans_comp]
    set a := (hP.LE_exhaustive Y).choose
    have : IsLE Y a := {le := (hP.LE_exhaustive Y).choose_spec}
    use (-a)
    simp only [ForgetInductiveSystemMap, ForgetInductiveSystem_aux, Functor.map_comp]
    intro b
    have : IsLE ((@shiftFunctor C _ _ _ Shift₂ b.1).obj Y) 0 := by
      have : IsLE Y (-b.1) := isLE_of_LE Y a (-b.1) (by have := Set.mem_Iic.mp b.2; linarith)
      exact isLE_shift Y (-b.1) b 0 (by linarith)
    rw [HalfForgetMapComp]

-- TODO:
-- (1) `Forget` is a triangulated functor.
-- (2) If `X` is `≤ 0`, then `Hom(Forget(X),Y) = Hom(X,Y)` for every `Y ≥ 0`. (In particular,
-- the restriction of `Forget` to `C(≤ 0)` is left adjoint to the inclusion.)
-- (3) If `X` is `≥ 0`, then `Hom(Y,Forget(X)) = Hom(Y,X)` for every `Y ≤ 0`. (In particular,
-- the restriction of `Forget` to `C(≥ 0)` is right adjoint to the inclusion.)
-- (just redo the whole construction dually, and prove isomorphism of functors?)
-- (4) `Hom(X,Y) = Hom(Forget(X),Forget(X))` is `X ≤ 0` and `Y ≥ 0`. (Should follow fron (2) and (3).)
-- (5) `Forget(α)` is an isomorphism (`α : X ⟶ X⟪1⟫`). In fact `Forget` sends all
-- `power_of_alpha` to isomorphisms.

end FilteredTriangulated

end Triangulated

end CategoryTheory
