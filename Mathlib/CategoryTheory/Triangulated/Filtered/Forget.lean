import Mathlib.CategoryTheory.Triangulated.Filtered.Basic
import Mathlib.CategoryTheory.Triangulated.Filtered.TruncationProp
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Data.Int.ConditionallyCompleteOrder

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

variable {C : Type _} [Category C] [HasZeroObject C]  [Preadditive C] [HasShift C (ℤ × ℤ)]
  [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C] [IsTriangulated C]

namespace FilteredTriangulated

/- Commutation of the truncation functors with the second shift.-/

@[simp]
noncomputable def truncLE_shift_hom_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    (truncLE n').obj ((@shiftFunctor C _ _ _ Shift₂ a).obj X) ⟶
    (@shiftFunctor C _ _ _ Shift₂ a).obj ((truncLE n).obj X) := by
  have := isLE_shift ((truncLE n).obj X) n a n' h
  exact descTruncLE ((@shiftFunctor C _ _ _ Shift₂ a).map ((truncLEπ n).app X)) n'

lemma truncLE_shift_hom_naturality {X Y : C} (f : X ⟶ Y) (n a n' : ℤ) (h : a + n = n') :
    (truncLE n').map ((@shiftFunctor C _ _ _ Shift₂ a).map f) ≫
    truncLE_shift_hom_app Y n a n' h = truncLE_shift_hom_app X n a n' h ≫
    (@shiftFunctor C _ _ _ Shift₂ a).map ((truncLE n).map f) := by
  have := isLE_shift ((truncLE n).obj Y) n a n' h
  apply from_truncLE_obj_ext
  simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, truncLE_shift_hom_app,
    π_descTruncLE_assoc]
  conv_lhs => rw [← assoc, ← (truncLEπ n').naturality, Functor.id_map, assoc, π_descTruncLE]
  rw [← Functor.map_comp, ← Functor.map_comp, ← (truncLEπ n).naturality, Functor.id_map]

noncomputable def truncLE_shift_inv_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    (@shiftFunctor C _ _ _ Shift₂ a).obj ((truncLE n).obj X) ⟶
    (truncLE n').obj ((@shiftFunctor C _ _ _ Shift₂ a).obj X) := by
  refine (@shiftFunctor C _ _ _ Shift₂ a).map ?_ ≫ (@shiftNegShift C _ _ _ Shift₂ _ a).hom
  have := isLE_shift ((truncLE n').obj ((@shiftFunctor C _ _ _ Shift₂ a).obj X)) n' (-a) n
    (by linarith)
  exact descTruncLE ((@shiftShiftNeg C _ _ _ Shift₂ X a).inv ≫
    (@shiftFunctor C _ _ _ Shift₂ (-a)).map ((truncLEπ n').app _)) n

@[simp]
lemma π_truncLE_shift_inv_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    (@shiftFunctor C _ _ _ Shift₂ a).map ((truncLEπ n).app X) ≫
    (truncLE_shift_inv_app X n a n' h) =
    (truncLEπ n').app ((@shiftFunctor C _ _ _ Shift₂ a).obj X) := by
  dsimp [truncLE_shift_inv_app]
  conv_lhs => rw [← assoc, ← Functor.map_comp, π_descTruncLE, Functor.map_comp]
  have heq : (@shiftFunctor C _ _ _ Shift₂ a).map ((@shiftFunctorCompIsoId C _ _ _ Shift₂
      a (-a) (add_neg_self a)).inv.app X) = (@shiftNegShift C _ _ _ Shift₂ _ a).inv := by
    simp only [Functor.id_obj, Functor.comp_obj, Iso.app_inv, shiftEquiv'_inverse,
      shiftEquiv'_functor, shiftEquiv'_counitIso]
    rw [@shift_shiftFunctorCompIsoId_inv_app]
  rw [heq, assoc]
  simp only [Functor.id_obj, Iso.app_inv, shiftEquiv'_inverse, shiftEquiv'_functor,
    shiftEquiv'_counitIso]
  have := (@shiftFunctorCompIsoId C _ _ _ Shift₂ (-a) a (by linarith)).hom.naturality
    ((truncLEπ n').app ((@shiftFunctor C _ _ _ Shift₂ a).obj X))
  simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map, Functor.id_map] at this
  rw [this]
  simp only [Iso.inv_hom_id_app_assoc]

@[simp]
lemma truncLE_shift_hom_inv_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    truncLE_shift_hom_app X n a n' h ≫ truncLE_shift_inv_app X n a n' h = 𝟙 _ := by
  apply from_truncLE_obj_ext
  simp only [Functor.id_obj, truncLE_shift_hom_app, π_descTruncLE_assoc, π_truncLE_shift_inv_app,
    comp_id]

@[simp]
lemma truncLE_shift_inv_hom_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    truncLE_shift_inv_app X n a n' h ≫ truncLE_shift_hom_app X n a n' h = 𝟙 _ := by
  set f := truncLE_shift_inv_app X n a n' h ≫ truncLE_shift_hom_app X n a n' h
  suffices h : (@shiftFunctor C _ _ _ Shift₂ a).map ((truncLEπ n).app X) ≫ f =
      (@shiftFunctor C _ _ _ Shift₂ a).map ((truncLEπ n).app X) ≫ 𝟙 _ by
    conv_rhs at h => rw [← Functor.map_id, ← Functor.map_comp]
    obtain ⟨g, hg⟩ := Functor.Full.map_surjective (F := @shiftFunctor C _ _ _ Shift₂ a) f
    rw [← hg, ← Functor.map_comp] at h
    have := from_truncLE_obj_ext _ _ _ _ (Functor.Faithful.map_injective
      (F := @shiftFunctor C _ _ _ Shift₂ a) h)
    rw [this] at hg
    rw [← hg, Functor.map_id]
  simp only [Functor.id_obj, truncLE_shift_hom_app, comp_id, f]
  conv_lhs => rw [← assoc, π_truncLE_shift_inv_app, π_descTruncLE]

noncomputable def truncLE_shift (n a n' : ℤ) (h : a + n = n') :
    @shiftFunctor C _ _ _ Shift₂ a ⋙ truncLE n'
    ≅ truncLE n ⋙ @shiftFunctor C _ _ _ Shift₂ a :=
  NatIso.ofComponents
    (fun X ↦ {hom := truncLE_shift_hom_app X n a n' h
              inv := truncLE_shift_inv_app X n a n' h
              hom_inv_id := truncLE_shift_hom_inv_app X n a n' h
              inv_hom_id := truncLE_shift_inv_hom_app X n a n' h})
    (fun f ↦ truncLE_shift_hom_naturality f n a n' h)

@[simp]
lemma π_truncLE_shift_hom (n a n' : ℤ) (h : a + n = n') :
    whiskerLeft (@shiftFunctor C _ _ _ Shift₂ a) (truncLEπ n') ≫ (truncLE_shift n a n' h).hom =
    whiskerRight (truncLEπ n) (@shiftFunctor C _ _ _ Shift₂ a) := by
  ext X
  simp only [Functor.comp_obj, Functor.id_obj, truncLE_shift, truncLE_shift_hom_app,
    NatTrans.comp_app, whiskerLeft_app, NatIso.ofComponents_hom_app, π_descTruncLE,
    whiskerRight_app]

@[simp]
lemma π_truncLE_shift_inv (n a n' : ℤ) (h : a + n = n') :
    whiskerRight (truncLEπ n) (@shiftFunctor C _ _ _ Shift₂ a) ≫ (truncLE_shift n a n' h).inv =
    whiskerLeft (@shiftFunctor C _ _ _ Shift₂ a) (truncLEπ n') := by
  ext X
  simp only [Functor.comp_obj, Functor.id_obj, truncLE_shift, truncLE_shift_hom_app,
    NatTrans.comp_app, whiskerRight_app, NatIso.ofComponents_inv_app, π_truncLE_shift_inv_app,
    whiskerLeft_app]

@[simp]
lemma truncLE_shift_zero (n : ℤ):
    truncLE_shift n 0 n (by linarith) =
    @Functor.CommShift.isoZero C C _ _ (truncLE n) ℤ _ Shift₂ Shift₂ := by
  ext X
  have : IsLE ((truncLE n ⋙ @shiftFunctor C _ _ _ Shift₂ 0).obj X) n :=
    isLE_shift _ n 0 n (by linarith)
  apply from_truncLE_obj_ext
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app]
  conv_rhs => rw [← assoc, ← (truncLEπ n).naturality, Functor.id_map, ← NatTrans.comp_app]
  have := π_truncLE_shift_hom n 0 n (by linarith) (C := C)
  apply_fun (fun f ↦ f.app X) at this
  rw [NatTrans.comp_app, whiskerLeft_app] at this
  rw [this]
  simp only [whiskerRight_app, Functor.id_obj, NatTrans.comp_app, assoc]
  rw [← cancel_mono (f := (@shiftFunctorZero C ℤ _ _ Shift₂).hom.app _)]
  simp only [Functor.id_obj, NatTrans.naturality, Functor.id_map, assoc, Iso.inv_hom_id_app,
    comp_id]

@[simp]
lemma truncLE_shift_add' (n n' n'' a b c : ℤ) (h : a + n = n') (h' : b + n' = n'')
    (h₀ : a + b = c) :
    truncLE_shift n c n'' (by linarith) = isoWhiskerRight (@shiftFunctorAdd' C _ _ _
    Shift₂ a b c h₀) (truncLE n'') ≪≫ isoWhiskerLeft (@shiftFunctor C _ _ _ Shift₂ a)
    (truncLE_shift n' b n'' h') ≪≫ isoWhiskerRight (truncLE_shift n a n' h)
    (@shiftFunctor C _ _ _ Shift₂ b) ≪≫ isoWhiskerLeft (truncLE n)
    (@shiftFunctorAdd' C _ _ _ Shift₂ a b c h₀).symm := sorry

@[simp]
lemma truncLE_shift_add (n n' n'' a b : ℤ) (h : a + n = n') (h' : b + n' = n'') :
    truncLE_shift n (a + b) n'' (by linarith) = isoWhiskerRight (@shiftFunctorAdd C _ _ _
    Shift₂ a b) (truncLE n'') ≪≫ isoWhiskerLeft (@shiftFunctor C _ _ _ Shift₂ a)
    (truncLE_shift n' b n'' h') ≪≫ isoWhiskerRight (truncLE_shift n a n' h)
    (@shiftFunctor C _ _ _ Shift₂ b) ≪≫ isoWhiskerLeft (truncLE n)
    (@shiftFunctorAdd C _ _ _ Shift₂ a b).symm := by
  simp only [← shiftFunctorAdd'_eq_shiftFunctorAdd]
  exact truncLE_shift_add' n n' n'' a b (a + b) h h' rfl

@[simp]
noncomputable def truncGE_shift_hom_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    (@shiftFunctor C _ _ _ Shift₂ a).obj ((truncGE n).obj X) ⟶
    (truncGE n').obj ((@shiftFunctor C _ _ _ Shift₂ a).obj X) := by
  have := isGE_shift ((truncGE n).obj X) n a n' h
  exact hP.liftTruncGE ((@shiftFunctor C _ _ _ Shift₂ a).map ((truncGEι n).app X)) n'

lemma truncGE_shift_hom_naturality {X Y : C} (f : X ⟶ Y) (n a n' : ℤ) (h : a + n = n') :
    (@shiftFunctor C _ _ _ Shift₂ a).map ((truncGE n).map f) ≫ truncGE_shift_hom_app Y n a n' h
    = truncGE_shift_hom_app X n a n' h ≫
    (truncGE n').map ((@shiftFunctor C _ _ _ Shift₂ a).map f) := by
  have := isGE_shift ((truncGE n).obj X) n a n' h
  apply to_truncGE_obj_ext
  simp only [Functor.id_obj, truncGE_shift_hom_app, assoc, liftTruncGE_ι, NatTrans.naturality,
    Functor.id_map, liftTruncGE_ι_assoc]
  conv_lhs => rw [← Functor.map_comp, (truncGEι n).naturality]
  simp only [Functor.id_obj, Functor.id_map, Functor.map_comp]

noncomputable def truncGE_shift_inv_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    (truncGE n').obj ((@shiftFunctor C _ _ _ Shift₂ a).obj X) ⟶
    (@shiftFunctor C _ _ _ Shift₂ a).obj ((truncGE n).obj X) := by
  refine (@shiftNegShift C _ _ _ Shift₂ _ a).inv ≫ (@shiftFunctor C _ _ _ Shift₂ a).map ?_
  have := isGE_shift ((truncGE n').obj ((@shiftFunctor C _ _ _ Shift₂ a).obj X)) n' (-a) n
    (by linarith)
  exact liftTruncGE ((@shiftFunctor C _ _ _ Shift₂ (-a)).map ((truncGEι n').app _) ≫
    (@shiftShiftNeg C _ _ _ Shift₂ X a).hom) n


@[simp]
lemma truncGE_shift_inv_app_ι (X : C) (n a n' : ℤ) (h : a + n = n') :
    (truncGE_shift_inv_app X n a n' h) ≫
    (@shiftFunctor C _ _ _ Shift₂ a).map ((truncGEι n).app X) =
    (truncGEι n').app ((@shiftFunctor C _ _ _ Shift₂ a).obj X) := by
  dsimp [truncGE_shift_inv_app]
  conv_lhs => rw [assoc, ← Functor.map_comp, liftTruncGE_ι, Functor.map_comp]
  have heq : (@shiftFunctor C _ _ _ Shift₂ a).map ((@shiftFunctorCompIsoId C _ _ _ Shift₂
      a (-a) (add_neg_self _)).hom.app X) = (@shiftFunctorCompIsoId C _ _ _ Shift₂
      (-a) a (by linarith)).hom.app _ := by
    simp only [Functor.comp_obj, Functor.id_obj]
    rw [@shift_shiftFunctorCompIsoId_hom_app]
  rw [heq]
  have := (@shiftFunctorCompIsoId C _ _ _ Shift₂ (-a) a (by linarith)).hom.naturality
    ((truncGEι n').app ((@shiftFunctor C _ _ _ Shift₂ a).obj X))
  simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map] at this
  rw [this]
  simp only [Iso.inv_hom_id_app_assoc]

@[simp]
lemma truncGE_shift_hom_inv_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    truncGE_shift_hom_app X n a n' h ≫ truncGE_shift_inv_app X n a n' h = 𝟙 _ := by
  set f := truncGE_shift_hom_app X n a n' h ≫ truncGE_shift_inv_app X n a n' h
  suffices h : f ≫ (@shiftFunctor C _ _ _ Shift₂ a).map ((truncGEι n).app X) =
      𝟙 _ ≫ (@shiftFunctor C _ _ _ Shift₂ a).map ((truncGEι n).app X) by
    conv_rhs at h => rw [← Functor.map_id, ← Functor.map_comp]
    obtain ⟨g, hg⟩ := Functor.Full.map_surjective (F := @shiftFunctor C _ _ _ Shift₂ a) f
    rw [← hg, ← Functor.map_comp] at h
    have := to_truncGE_obj_ext _ _ _ _
      (Functor.Faithful.map_injective (F := @shiftFunctor C _ _ _ Shift₂ a) h)
    rw [this] at hg
    rw [← hg, Functor.map_id]
  simp only [Functor.id_obj, truncGE_shift_hom_app, assoc, truncGE_shift_inv_app_ι,
    liftTruncGE_ι, id_comp, f]

@[simp]
lemma truncGE_shift_inv_hom_app (X : C) (n a n' : ℤ) (h : a + n = n') :
    truncGE_shift_inv_app X n a n' h ≫ truncGE_shift_hom_app X n a n' h = 𝟙 _ := by
  apply to_truncGE_obj_ext
  simp only [Functor.id_obj, truncGE_shift_hom_app, assoc, liftTruncGE_ι,
    truncGE_shift_inv_app_ι, id_comp]

noncomputable def truncGE_shift (n a n' : ℤ) (h : a + n = n') :
    truncGE n ⋙ @shiftFunctor C _ _ _ Shift₂ a ≅
    @shiftFunctor C _ _ _ Shift₂ a ⋙ truncGE n' :=
  NatIso.ofComponents
    (fun X ↦ {hom := truncGE_shift_hom_app X n a n' h
              inv := truncGE_shift_inv_app X n a n' h
              hom_inv_id := truncGE_shift_hom_inv_app X n a n' h
              inv_hom_id := truncGE_shift_inv_hom_app X n a n' h})
    (fun f ↦ truncGE_shift_hom_naturality f n a n' h)

@[simp]
lemma truncGE_shift_hom_ι (n a n' : ℤ) (h : a + n = n') :
    (truncGE_shift n a n' h).hom ≫ whiskerLeft (@shiftFunctor C _ _ _ Shift₂ a) (truncGEι n') =
    whiskerRight (truncGEι n) (@shiftFunctor C _ _ _ Shift₂ a) := by
  ext X
  simp only [Functor.comp_obj, Functor.id_obj, truncGE_shift, truncGE_shift_hom_app,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, whiskerLeft_app, liftTruncGE_ι,
    whiskerRight_app]

@[simp]
lemma truncGE_shift_inv_ι (n a n' : ℤ) (h : a + n = n') :
    (truncGE_shift n a n' h).inv ≫ whiskerRight (truncGEι n) (@shiftFunctor C _ _ _ Shift₂ a) =
    whiskerLeft (@shiftFunctor C _ _ _ Shift₂ a) (truncGEι n') := by
  ext X
  simp only [Functor.comp_obj, Functor.id_obj, truncGE_shift, truncGE_shift_hom_app,
    NatTrans.comp_app, NatIso.ofComponents_inv_app, whiskerRight_app, truncGE_shift_inv_app_ι,
    whiskerLeft_app]

noncomputable def truncGELE_shift (n₁ n₂ a n₁' n₂' : ℤ) (h₁ : a + n₁ = n₁') (h₂ : a + n₂ = n₂') :
    @shiftFunctor C _ _ _ Shift₂ a ⋙ truncGELE n₁' n₂' ≅
    truncGELE n₁ n₂ ⋙ @shiftFunctor C _ _ _ Shift₂ a :=
  isoWhiskerRight (truncLE_shift n₂ a n₂' h₂) (truncGE n₁') ≪≫
    isoWhiskerLeft (truncLE n₂) (truncGE_shift n₁ a n₁' h₁).symm

noncomputable def Gr_shift (n a n' : ℤ) (h : a + n = n') :
    @shiftFunctor C _ _ _ Shift₂ a ⋙ Gr'' n' ≅ Gr'' n :=
  isoWhiskerRight (truncGELE_shift n n a n' n' h h) (@shiftFunctor C _ _ _ Shift₂ (-n')) ≪≫
  isoWhiskerLeft (truncGELE n n) (@shiftFunctorAdd' C _ _ _ Shift₂ a (-n') (-n)
  (by linarith)).symm

/- More on the `Gr` functors.-/

lemma isLE_of_big_enough (X : C) : ∃ (n : ℤ), IsLE X n := by
  obtain ⟨n, hn⟩ := hP.LE_exhaustive X
  exact ⟨n, {le := hn}⟩

lemma isGE_of_small_enough (X : C) : ∃ (n : ℤ), IsGE X n := by
  obtain ⟨n, hn⟩ := hP.GE_exhaustive X
  exact ⟨n, {ge := hn}⟩

lemma Gr_zero_of_isLE (X : C) (n : ℤ) [IsLE X n] (m : ℤ) (hm : n < m) :
    IsZero ((Gr'' m).obj X) := by
  dsimp [Gr'']
  refine Limits.IsZero.of_iso ?_ (Functor.mapIso _ ((truncLEGEIsoGELE m m).app X).symm)
  dsimp [truncLEGE]
  have : IsZero ((truncGE m).obj X) := by
    have : IsLE X (m - 1) := isLE_of_LE X n (m - 1) (by linarith [hm])
    exact isZero_truncGE_obj_of_isLE (m - 1) m (by linarith) X
  rw [IsZero.iff_id_eq_zero] at this ⊢
  rw [← Functor.map_id, ← Functor.map_id, this, Functor.map_zero, Functor.map_zero]

lemma Gr_zero_of_isGE (X : C) (n : ℤ) [IsGE X n] (m : ℤ) (hm : m < n) :
    IsZero ((Gr'' m).obj X) := by
  dsimp [Gr'', truncGELE]
  have : IsZero ((truncLE m).obj X) := by
    have : IsGE X (m + 1) := isGE_of_GE X (m + 1) n (by linarith [hm])
    exact isZero_truncLE_obj_of_isGE m (m + 1) (by linarith) X
  rw [IsZero.iff_id_eq_zero] at this ⊢
  rw [← Functor.map_id, ← Functor.map_id, this, Functor.map_zero, Functor.map_zero]

lemma isLE_of_isLE_and_Gr_zero (X : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [IsLE X n₁]
    (hX : IsZero ((Gr'' n₁).obj X)) : IsLE X n₀ := by
  rw [isLE_iff_isIso_truncLTπ_app n₀ n₁ h]
  have hz : IsZero ((truncGELE n₁ n₁).obj X) := by
    dsimp [Gr''] at hX
    refine Limits.IsZero.of_iso ?_ (@shiftNegShift _ _ _ _ Shift₂
      ((truncGELE n₁ n₁).obj X) n₁).symm
    rw [IsZero.iff_id_eq_zero] at hX ⊢
    rw [← Functor.map_id, hX, Functor.map_zero]
  have hz' : IsZero (((truncGELE n₁ n₁).obj X)⟦(1 : ℤ)⟧) := by
    rw [IsZero.iff_id_eq_zero] at hz ⊢; rw [← Functor.map_id, hz, Functor.map_zero]
  set φ := Triangle.homMk (Triangle.mk (0 : 0 ⟶ X) (CategoryTheory.CategoryStruct.id X) 0)
    ((triangleGELELTLE n₁ n₁ (le_refl _)).obj X) 0 ((truncLEπ n₁).app X)
    ((truncLTπ n₁).app X) (by simp)
    (by simp only [Triangle.mk_obj₂, triangleGELELTLE_obj_obj₃, Triangle.mk_obj₃,
      Triangle.mk_mor₂, id_comp, triangleGELELTLE_obj_obj₂, triangleGELELTLE_obj_mor₂]
        exact (natTransTruncLTOfGE_π_app (n₁ + 1) n₁ (by linarith) X).symm)
    (Limits.IsTerminal.hom_ext (Limits.IsZero.isTerminal hz') _ _)
  refine isIso₃_of_isIso₁₂ φ (contractible_distinguished₁ X) (triangleGELELTLE_distinguished n₁
    n₁ (le_refl _) X) ?_ ((isLE_iff_isIso_truncLEπ_app n₁ X).mp inferInstance)
  exact Limits.isIso_of_isTerminal Limits.HasZeroObject.zeroIsTerminal
    (Limits.IsZero.isTerminal hz) _

lemma isGE_of_isGE_and_Gr_zero (X : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) [IsGE X n₀]
    (hX : IsZero ((Gr'' n₀).obj X)) : IsGE X n₁ := by
  rw [isGE_iff_isIso_truncGEι_app]
  have hz : IsZero ((truncLTGE n₀ n₁).obj X) := by
    refine IsZero.of_iso ?_ ((truncLTGEIsoGELT n₀ n₁).app X)
    have heq : n₁ = n₀ + 1 := by linarith
    rw [heq]
    dsimp [Gr''] at hX
    refine Limits.IsZero.of_iso ?_ (@shiftNegShift _ _ _ _ Shift₂
      ((truncGELE n₀ n₀).obj X) n₀).symm
    rw [IsZero.iff_id_eq_zero] at hX ⊢
    rw [← Functor.map_id, hX, Functor.map_zero]
  set φ := Triangle.homMk ((triangleGEGELTGE n₀ n₁ (by linarith)).obj X)
    (contractibleTriangle X) ((truncGEι n₁).app X) ((truncGEι n₀).app X) 0 (by simp) (by simp)
    (Limits.IsInitial.hom_ext (Limits.IsZero.isInitial hz) _ _)
  refine isIso₁_of_isIso₂₃ φ (triangleGEGELTGE_distinguished n₀ n₁ (by linarith) X)
    (contractible_distinguished X) ?_ ?_
  exact (isGE_iff_isIso_truncGEι_app n₀ X).mp inferInstance
  exact Limits.isIso_of_isTerminal (Limits.IsZero.isTerminal hz)
    Limits.HasZeroObject.zeroIsTerminal _

lemma isLE_of_Gr_zero (X : C) (n : ℤ) (hn : ∀ (m : ℤ), n < m → IsZero ((Gr'' m).obj X)) :
    IsLE X n := by
  obtain ⟨N, hN⟩ := isLE_of_big_enough X
  by_cases h : n ≤ N
  · set P := fun (r : ℤ) ↦ n ≤ r → IsLE X r
    have := Int.le_induction_down (P := P) (m := N) (fun _ ↦ hN)
      (fun r _ h₂ hr ↦ by
         have : IsLE X r := h₂ (by linarith)
         refine isLE_of_isLE_and_Gr_zero X (r - 1) r (by linarith) (hn r (by linarith)))
    exact this n h (le_refl _)
  · exact isLE_of_LE X N n (by linarith)

lemma isGE_of_Gr_zero (X : C) (n : ℤ) (hn : ∀ (m : ℤ), m < n → IsZero ((Gr'' m).obj X)) :
    IsGE X n := by
  obtain ⟨N, hN⟩ := isGE_of_small_enough X
  by_cases h : N ≤ n
  · set P := fun (r : ℤ) ↦ r ≤ n → IsGE X r
    have := Int.le_induction (P := P) (m := N) (fun _ ↦ hN)
      (fun r _ h₂  hr ↦ by
        have : IsGE X r := h₂ (by linarith)
        exact isGE_of_isGE_and_Gr_zero X r (r + 1) rfl (hn r (by linarith)))
    exact this n h (le_refl _)
  · exact isGE_of_GE X n N (by linarith)

lemma isZero_of_Gr_zero (X : C) (hX : ∀ (n : ℤ), IsZero ((Gr'' n).obj X)) : IsZero X := by
  have := (isGE_iff_isIso_truncGEι_app 0 X).mp (isGE_of_Gr_zero X 0 (fun n _ ↦ hX n))
  refine IsZero.of_iso ?_ (asIso ((truncGEι 0).app X)).symm
  rw [← isLE_iff_isZero_truncGE_obj (-1) 0 (by linarith)]
  exact isLE_of_Gr_zero X (-1) (fun n _ ↦ hX n)

lemma Gr_ι_isIso_of_GE (X : C) (n m : ℤ) (h : n ≤ m) :
    IsIso ((Gr'' m).map ((truncGEι n).app X)) := by
  have := (Gr'' m).map_distinguished _ (triangleGELT_distinguished n X)
  erw [← Triangle.isZero₃_iff_isIso₁ _ this]
  simp only [Functor.mapTriangle_obj, triangleGELT_obj_obj₁, triangleGELT_obj_obj₂,
    triangleGELT_obj_obj₃, triangleGELT_obj_mor₁, triangleGELT_obj_mor₂, triangleGELT_obj_mor₃,
    Triangle.mk_obj₃]
  exact Gr_zero_of_isLE ((truncLT n).obj X) (n - 1) m (by linarith)

lemma Gr_π_isIso_of_LE (X : C) (n m : ℤ) (h : m ≤ n) :
    IsIso ((Gr'' m).map ((truncLEπ n).app X)) := by
  have := (Gr'' m).map_distinguished _ (triangleGELT_distinguished (n + 1) X)
  erw [← Triangle.isZero₁_iff_isIso₂ _ this]
  simp only [Functor.mapTriangle_obj, triangleGELT_obj_obj₁, triangleGELT_obj_obj₂,
    triangleGELT_obj_obj₃, triangleGELT_obj_mor₁, triangleGELT_obj_mor₂, triangleGELT_obj_mor₃,
    Triangle.mk_obj₁]
  exact Gr_zero_of_isGE ((truncGE (n + 1)).obj X) (n + 1) m (by linarith)

variable [∀ (X : C) (n : ℤ), Decidable (IsZero ((Gr'' n).obj X))]

/- Support of an object `X` of `C`. That's the set of integers `n` such that `Gr'' n X` is nonzero,
and it is finite.-/

lemma bounded_above (X : C) : ∃ (n : ℤ), ∀ (m : ℤ), n < m → IsZero ((Gr'' m).obj X) := by
  obtain ⟨r, hr⟩ := isLE_of_big_enough X
  existsi r
  intro m hm
  exact Gr_zero_of_isLE X r m hm

lemma bounded_below (X : C) : ∃ (n : ℤ), ∀ (m : ℤ), m < n → IsZero ((Gr'' m).obj X) := by
  obtain ⟨r, hr⟩ := isGE_of_small_enough X
  existsi r
  intro m hm
  exact Gr_zero_of_isGE X r m hm

lemma support_finite (X : C) : Set.Finite {n | ¬ (IsZero ((Gr'' n).obj X))} := by
  suffices sub : ∃ n m, {n | ¬ (IsZero ((Gr'' n).obj X))} ⊆ Set.Icc n m by
    obtain ⟨n, m, h⟩ := sub
    exact Set.Finite.subset (Set.finite_Icc n m) h
  obtain ⟨m, hm⟩ := bounded_above X
  obtain ⟨n, hn⟩ := bounded_below X
  existsi n, m
  intro r
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  contrapose!
  intro hr
  by_cases h : r < n
  · exact hn r h
  · dsimp [Gr'']
    rw [lt_iff_not_le, not_not] at h
    exact hm r (hr h)

noncomputable def support (X : C) := Set.Finite.toFinset (support_finite X)

lemma support_def (X : C) (n : ℤ) : n ∈ support X ↔ ¬ (IsZero ((Gr'' n).obj X)) := by
  simp only [support, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

lemma support_def' (X : C) (n : ℤ) : n ∉ support X ↔ IsZero ((Gr'' n).obj X) := by
  rw [support_def]; simp only [Decidable.not_not]

lemma isLE_iff_support_bounded_above (X : C) (n : ℤ) :
    IsLE X n ↔ (support X).toSet ⊆ Set.Iic n := by
  constructor
  · intro hX m
    simp only [Finset.mem_coe, Set.mem_Iic]
    contrapose!
    rw [support_def']
    exact Gr_zero_of_isLE X n m
  · intro hX
    refine isLE_of_Gr_zero X n (fun m hm ↦ ?_)
    rw [← support_def']
    intro habs
    have := hX habs
    simp only [Set.mem_Iic] at this
    linarith

lemma isGE_iff_support_bounded_below (X : C) (n : ℤ) :
    IsGE X n ↔ (support X).toSet ⊆ Set.Ici n := by
  constructor
  · intro hX r
    simp only [Finset.mem_coe, Set.mem_Ici]
    contrapose!
    rw [support_def']
    exact Gr_zero_of_isGE X n r
  · intro hX
    refine isGE_of_Gr_zero X n (fun m hm ↦ ?_)
    rw [← support_def']
    intro habs
    have := hX habs
    simp only [Set.mem_Ici] at this
    linarith

lemma isZero_iff_empty_support (X : C) : IsZero X ↔ support X = ∅ := by
  constructor
  · intro h
    ext n
    simp only [Finset.not_mem_empty, iff_false]
    rw [support_def']
    rw [IsZero.iff_id_eq_zero] at h ⊢
    rw [← Functor.map_id, h, Functor.map_zero]
  · intro hX
    refine isZero_of_Gr_zero X (fun n ↦ ?_)
    rw [← support_def', hX]
    simp only [Finset.not_mem_empty, not_false_eq_true]

lemma isCore_iff_support_sub_0 (X : C) : tCore.P X ↔ support X ⊆ {0} := by
  rw [mem_tCore_iff, isGE_iff_support_bounded_below, isLE_iff_support_bounded_above,
    ← Set.subset_inter_iff]
  constructor
  · intro h a ha
    simp only [Finset.mem_singleton]
    have := h ha
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici] at this
    exact le_antisymm this.1 this.2
  · intro h
    rw [Finset.subset_singleton_iff'] at h
    intro a ha
    rw [h a ha]
    simp only [Set.mem_inter_iff, Set.mem_Iic, le_refl, Set.mem_Ici, and_self]

lemma shift_isCore_iff_support_sub_singleton (X : C) (n : ℤ) :
    tCore.P ((@shiftFunctor C _ _ _ Shift₂ (-n)).obj X) ↔ support X ⊆ {n} := by
  rw [isCore_iff_support_sub_0]
  constructor
  · intro h a ha
    rw [support_def] at ha
    rw [Iso.isZero_iff ((Gr_shift a (-n) (a - n) (by linarith)).symm.app X),
      Functor.comp_obj, ← support_def] at ha
    have := h ha
    rw [Finset.mem_singleton, Int.sub_eq_zero] at this
    rw [this, Finset.mem_singleton]
  · intro h a ha
    rw [support_def] at ha
    erw [Iso.isZero_iff ((Gr_shift (C := C) (a + n) (-n) a (by linarith)).app X)] at ha
    rw [← support_def] at ha
    have := h ha
    rw [Finset.mem_singleton] at this
    have : a = 0 := by linarith
    rw [this, Finset.mem_singleton]

lemma support_truncLE (X : C) (n : ℤ) :
    support ((truncLE n).obj X) = (support X).filter (fun a ↦ a ≤ n) := by
  ext a
  simp only [support_def, Finset.mem_filter]
  by_cases h : a ≤ n
  · simp only [h, and_true]
    have := Gr_π_isIso_of_LE X n a h
    rw [← (asIso ((Gr'' a).map ((truncLEπ n).app X))).isZero_iff]
    rfl
  · simp only [h, and_false, iff_false, Decidable.not_not]
    exact Gr_zero_of_isLE ((truncLE n).obj X) n a (by linarith)

lemma support_truncGE (X : C) (n : ℤ) :
    support ((truncGE n).obj X) = (support X).filter (fun a ↦ n ≤ a) := by
  ext a
  simp only [support_def, Finset.mem_filter]
  by_cases h : n ≤ a
  · simp only [h, and_true]
    have := Gr_ι_isIso_of_GE X n a h
    rw [(asIso ((Gr'' a).map ((truncGEι n).app X))).isZero_iff]
    rfl
  · simp only [h, and_false, iff_false, Decidable.not_not]
    exact Gr_zero_of_isGE ((truncGE n).obj X) n a (by linarith)

/- The functor forgetting filtrations on the subcategory of objects `X` such that `IsLE X 0`.-/

/- First we do the case where the support is a singleton.-/

/-- The morphism "`αⁿ`"" from `X` to `X⟪n⟫`, if `n` is a natural number.-/
noncomputable def power_of_alpha (X : C) (n : ℕ) :
    X ⟶ (@shiftFunctor C _ _ _ Shift₂ (n : ℤ)).obj X := by
  induction' n with n fn
  · exact ((@shiftFunctorZero C ℤ _ _ Shift₂).symm.app X).hom
  · exact fn ≫ α.app _ ≫ ((@shiftFunctorAdd' C _ _ _ Shift₂ n 1 ↑(n + 1) rfl).symm.app X).hom

/-- The morphism "`αⁿ` from `X⟪m⟫` to `X⟪m+n⟫`, if `m` is an integer and `n` is a natural number.-/
noncomputable def power_of_alpha' (X : C) (m : ℤ) (n : ℕ) :
    (@shiftFunctor C _ _ _ Shift₂ m).obj X ⟶ (@shiftFunctor C _ _ _ Shift₂ (m + n)).obj X := by
  induction' n with n fn
  · exact ((@shiftFunctorZero C ℤ _ _ Shift₂).symm.app ((@shiftFunctor C _ _ _ Shift₂ m).obj X)≪≫
      (@shiftFunctorAdd C _ _ _ Shift₂ m 0).symm.app X).hom
  · refine fn ≫ ?_
    refine ?_ ≫ ((@shiftFunctorAdd' C _ _ _ Shift₂ (m + n) 1 (m + ↑(n + 1))
      (by simp only [Nat.cast_add, Nat.cast_one]; linarith)).symm.app X).hom
    exact hP.α.app _

@[simp]
lemma power_of_alpha_zero (X : C) : power_of_alpha X 0 = (shiftFunctorZero C ℤ).inv.app X := by
  dsimp [power_of_alpha]; rfl

@[simp]
lemma power_of_alpha_plus_one (X : C) (n : ℕ) :
    power_of_alpha X (n + 1) = power_of_alpha X n ≫ α.app _ ≫
    ((@shiftFunctorAdd' C _ _ _ Shift₂ n 1 ↑(n + 1) rfl).symm.app X).hom := by
  dsimp [power_of_alpha]

lemma adj_left_shift (X Y : C) (p q : ℤ) (hpq : p + 1 ≤ q) [IsLE X p] [IsGE Y q] :
    Function.Bijective (fun (f : (@shiftFunctor C _ _ _ Shift₂ 1).obj X ⟶ Y) ↦ α.app X ≫ f) := by
  set e : ((@shiftFunctor C _ _ _ Shift₂ 1).obj X ⟶ Y) → ((@shiftFunctor C _ _ _ Shift₂ 1).obj
      ((@shiftFunctor C _ _ _ Shift₂ (-p)).obj X) ⟶ (@shiftFunctor C _ _ _ Shift₂ (-p)).obj Y) :=
    Function.comp (CategoryStruct.comp (@shiftComm C _ _ _ Shift₂ _ _ _).hom)
    (@shiftFunctor C _ _ _ Shift₂ (-p)).map
  

lemma adj_left_extended (n : ℕ) : ∀ (X Y : C) (m : ℤ) [IsLE X m] [IsGE Y (m + n)],
    Function.Bijective
    (fun (f : (@shiftFunctor C _ _ _ Shift₂ n).obj X ⟶ Y) ↦ (power_of_alpha X n ≫ f)) := by
  induction' n with n fn
  · intro X Y m _ _
    simp only [Int.Nat.cast_ofNat_Int, power_of_alpha_zero]
    exact IsIso.comp_left_bijective _
  · intro X Y m _ _
    simp only [power_of_alpha_plus_one, Functor.comp_obj, Iso.app_hom, Iso.symm_hom, assoc]
    refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ ?_)
    · have : IsGE Y (m + n) := isGE_of_GE Y (m + n) (m + ↑(n + 1)) (by simp only [Nat.cast_add,
      Nat.cast_one, add_le_add_iff_left, le_add_iff_nonneg_right, zero_le_one])
      exact fn X Y m
    · have : IsLE ((@shiftFunctor C _ _ _ Shift₂ n).obj X) (m + ↑n) := by
        exact isLE_shift X m n (m + n) (by linarith)
      exact adj_left_shift _ _ (m + n) (m + ↑(n + 1))
        (by simp only [Nat.cast_add, Nat.cast_one]; linarith)
    · exact IsIso.comp_left_bijective _

/- Then the general case, by induction on the size of the support.-/

lemma existence_omega_aux (n : ℕ) : ∀ (X : C) [IsLE X 0], Finset.card (support X) = n →
    ∃ (Y : hP.Core') (s : X ⟶ Y.1),
    ∀ (Z : C), IsGE Z 0 → IsIso ((preadditiveYoneda.obj Z).map (Quiver.Hom.op s)) := by
  refine Nat.strongRec ?_ n
  intro n hn X _ hX
  by_cases h : n = 0
  · existsi 0, 0
    intro Z hZ
    have  h₁: IsZero ((preadditiveYoneda.obj Z).obj (Opposite.op (FullSubcategory.obj
        (0 : hP.Core')))) := by
      simp only [preadditiveYoneda_obj, Functor.comp_obj, preadditiveYonedaObj_obj,
        ModuleCat.forget₂_obj]
      refine @AddCommGrp.isZero_of_subsingleton _ (Subsingleton.intro ?_)
      simp only [AddCommGrp.coe_of]
      change ∀ (a b : (FullSubcategory.obj (0 : hP.Core') ⟶ Z)), a = b
      intro f g
      have h₀ : IsZero (FullSubcategory.obj (0 : hP.Core')) := by
        have : IsZero (0 : hP.Core') := isZero_zero _
        rw [IsZero.iff_id_eq_zero] at this ⊢
        exact this
      rw [Limits.IsZero.eq_zero_of_src h₀ f, Limits.IsZero.eq_zero_of_src h₀ g]
    have h₂: IsZero ((preadditiveYoneda.obj Z).obj (Opposite.op X)) := by
      simp only [preadditiveYoneda_obj, Functor.comp_obj, preadditiveYonedaObj_obj,
        ModuleCat.forget₂_obj]
      have h₀ : IsZero X := by
        rw [isZero_iff_empty_support, ← Finset.card_eq_zero, ← h]
        exact hX
      refine @AddCommGrp.isZero_of_subsingleton _ (Subsingleton.intro ?_)
      simp only [AddCommGrp.coe_of]
      change ∀ (a b : (X ⟶ Z)), a = b
      intro f g
      rw [Limits.IsZero.eq_zero_of_src h₀ f, Limits.IsZero.eq_zero_of_src h₀ g]
    exact Limits.isIso_of_isInitial h₁.isInitial h₂.isInitial _
  · set b := sSup (support X).toSet
    sorry

  #exit


lemma existence_omega (X : C) [IsLE X 0] : ∃ (Y : hP.Core') (s : X ⟶ Y.1),
    ∀ (Z : C), IsGE Z 0 → Function.Bijective (fun (f : Y.1 ⟶ Z) ↦ s ≫ f) := sorry


end FilteredTriangulated

end Triangulated

end CategoryTheory
