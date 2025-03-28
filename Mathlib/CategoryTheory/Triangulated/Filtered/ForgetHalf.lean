import Mathlib.CategoryTheory.Triangulated.Filtered.Basic
import Mathlib.CategoryTheory.Triangulated.Filtered.TruncationProp
import Mathlib.Data.Int.Interval
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

variable {C : Type _} [Category C] [HasZeroObject C]  [Preadditive C] [HasShift C (ℤ × ℤ)]
  [∀ p : ℤ × ℤ, Functor.Additive (CategoryTheory.shiftFunctor C p)]
  [hC : Pretriangulated C] [hP : FilteredTriangulated C] [IsTriangulated C]

attribute [local instance] endofunctorMonoidalCategory

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

lemma Gr_π_isIso_of_LT (X : C) (n m : ℤ) (h : m < n) :
    IsIso ((Gr'' m).map ((truncLTπ n).app X)) := by
  have := (Gr'' m).map_distinguished _ (triangleGELT_distinguished n X)
  erw [← Triangle.isZero₁_iff_isIso₂ _ this]
  simp only [Functor.mapTriangle_obj, triangleGELT_obj_obj₁, triangleGELT_obj_obj₂,
    triangleGELT_obj_obj₃, triangleGELT_obj_mor₁, triangleGELT_obj_mor₂, triangleGELT_obj_mor₃,
    Triangle.mk_obj₁]
  exact Gr_zero_of_isGE ((truncGE n).obj X) n m h

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

lemma support_shift (X : C) (a b n : ℤ) (hab : a + n = b) :
    a ∈ support X ↔ b ∈ support ((@shiftFunctor C _ _ _ Shift₂ n).obj X) := by
  rw [support_def, support_def,
    Iso.isZero_iff ((hP.Gr_shift a n b (by linarith [hab])).symm.app X), Functor.comp_obj]

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

lemma shift_isCore_iff_support_sub_singleton (X : C) (n n' : ℤ) (hnn' : n + n' = 0) :
    tCore.P ((@shiftFunctor C _ _ _ Shift₂ n').obj X) ↔ support X ⊆ {n} := by
  rw [isCore_iff_support_sub_0]
  constructor
  · intro h a ha
    rw [support_shift X a (a - n) n' (by linarith)] at ha
    have := h ha
    have : a = n := by simp only [Finset.mem_singleton] at this; linarith
    rw [this, Finset.mem_singleton]
  · intro h a ha
    rw [← support_shift X (a + n) a n' (by linarith)] at ha
    have := h ha
    have : a = 0 := by simp only [Finset.mem_singleton, add_left_eq_self] at this; exact this
    rw [this, Finset.mem_singleton]

lemma support_truncLT (X : C) (n : ℤ) :
    support ((truncLT n).obj X) = (support X).filter (fun a ↦ a < n) := by
  ext a
  simp only [support_def, Finset.mem_filter]
  by_cases h : a < n
  · simp only [h, and_true]
    have := Gr_π_isIso_of_LT X n a h
    rw [← (asIso ((Gr'' a).map ((truncLTπ n).app X))).isZero_iff]
    rfl
  · simp only [h, and_false, iff_false, Decidable.not_not]
    exact Gr_zero_of_isLE ((truncLT n).obj X) (n - 1) a (by linarith)

lemma support_truncLE (X : C) (n : ℤ) :
    support ((truncLE n).obj X) = (support X).filter (fun a ↦ a ≤ n) := by
  dsimp [truncLE]; rw [support_truncLT]
  ext a
  simp only [Finset.mem_filter, and_congr_right_iff]
  exact fun _ ↦ Int.lt_add_one_iff

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

/-- The morphism "`αⁿ` from `X⟪a⟫` to `X⟪b⟫`, if `a,b` are integers and `n` is a natural number
such that `a + n = b`.-/
noncomputable def power_of_alpha (X : C) (a b : ℤ) (n : ℕ) (_ : a + n = b) :
    (@shiftFunctor C _ _ _ Shift₂ a).obj X ⟶ (@shiftFunctor C _ _ _ Shift₂ b).obj X := by
  revert X a b
  induction' n with n fn
  · intro X a b hn
    exact ((@shiftFunctorZero C _ _ _ Shift₂).symm.app ((@shiftFunctor C _ _ _ Shift₂ a).obj X) ≪≫
      (@shiftFunctorAdd' C _ _ _ Shift₂ a 0 b hn).symm.app X).hom
  · intro X a b hn
    refine fn X a (a + n) rfl ≫ ?_
    refine ?_ ≫ ((@shiftFunctorAdd' C _ _ _ Shift₂ (a + n) 1 b
      (by rw [← hn]; simp only [Nat.cast_add, Nat.cast_one]; linarith)).symm.app X).hom
    exact hP.α.app _

lemma power_of_alpha_zero (X : C) (a b : ℤ) (hab : a = b) :
    power_of_alpha X a b 0 (by rw [hab, Nat.cast_zero, add_zero]) = eqToHom (by rw [hab]) := by
  dsimp [power_of_alpha, shiftFunctorAdd']
  rw [@shiftFunctorAdd_add_zero_inv_app C _ _ _ Shift₂]
  simp only [Functor.id_obj, add_zero, eqToHom_naturality, eqToHom_app, assoc,
    eqToHom_naturality_assoc, Iso.inv_hom_id_app_assoc, eqToHom_trans]

lemma power_of_alpha_zero' (X : C) (a : ℤ) :
    power_of_alpha X a a 0 (by simp only [Nat.cast_zero, add_zero]) = (Iso.refl _).hom := by
  dsimp [power_of_alpha]
  rw [shiftFunctorAdd'_add_zero]
  simp only [Iso.trans_inv, isoWhiskerLeft_inv, Iso.symm_inv, NatTrans.comp_app, Functor.comp_obj,
    Functor.id_obj, whiskerLeft_app, Functor.rightUnitor_hom_app, comp_id, Iso.inv_hom_id_app]

lemma power_of_alpha_change_exponent (X : C) (n m : ℕ) (hnm : n = m) (a b : ℤ) (hn : a + n = b) :
    power_of_alpha X a b n hn = power_of_alpha X a b m (by rw [← hnm, hn]) := by
  simp_rw [hnm]

lemma power_of_alpha_eqToHom (n : ℕ) : ∀ (X : C) (a b a' b' : ℤ) (hn : a + n = b)
    (hn' : a' + n = b') (ha : a = a') (hb : b = b'),
    power_of_alpha X a b n hn = eqToHom (by rw [ha]) ≫ power_of_alpha X a' b' n hn' ≫
    eqToHom (by rw [hb]) := by
  induction' n with n hind
  · intro X a b a' b' hn hn' ha hb
    rw [power_of_alpha_zero X a b (by rw [← hn, Nat.cast_zero, add_zero]),
      power_of_alpha_zero X a' b' (by rw [← hn', Nat.cast_zero, add_zero])]
    simp only [eqToHom_trans]
  · intro X a b a' b' hn hn' ha hb
    change power_of_alpha X a (a + n) n rfl ≫ hP.α.app _ ≫
      ((@shiftFunctorAdd' C _ _ _ Shift₂ (a + n) 1 b
      (by rw [← hn]; simp only [Nat.cast_add, Nat.cast_one]; linarith)).symm.app X).hom
      = _ ≫ (power_of_alpha X a' (a' + n) n rfl ≫ hP.α.app _ ≫
      ((@shiftFunctorAdd' C _ _ _ Shift₂ (a' + n) 1 b'
      (by rw [← hn']; simp only [Nat.cast_add, Nat.cast_one]; linarith)).symm.app X).hom) ≫ _
    rw [hind X a (a + n) a' (a' + n) rfl rfl ha (by rw [ha])]
    rw [@shiftFunctorAdd'_symm_eqToIso C _ _ _ Shift₂ (a + n) 1 b (a' + n) 1 b'
      (by rw [← hn, add_assoc, Nat.cast_add, Nat.cast_one])
      (by rw [← hn', add_assoc, Nat.cast_add, Nat.cast_one]) (by rw [ha]) rfl]
    simp only [Functor.comp_obj, NatIso.trans_app, Iso.trans_hom, Iso.app_hom, eqToIso.hom,
      eqToHom_app, Iso.symm_hom, assoc]
    congr 2
    have := α.naturality (eqToHom (by rw [ha]) : (@shiftFunctor C _ _ _ Shift₂ (a' + n)).obj X ⟶
      (@shiftFunctor C _ _ _ Shift₂ (a + n)).obj X)
    simp only [Functor.id_obj, Functor.id_map] at this
    conv_lhs => rw [← assoc, this, eqToHom_map]
    simp only [assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp]

lemma power_of_alpha_plus_one (X : C) (n : ℕ) (a b c : ℤ) (hn : a + n = b) (h : a + (n + 1) = c) :
    power_of_alpha X a c (n + 1) h = power_of_alpha X a b n hn ≫ α.app _ ≫
    ((@shiftFunctorAdd' C _ _ _ Shift₂ b 1 c (by rw [← hn, ← h, add_assoc])).symm.app X).hom := by
  conv_lhs => rw [power_of_alpha]
  change power_of_alpha X a (a + n) n rfl ≫ hP.α.app ((@shiftFunctor C _ _ _ Shift₂ (a + n)).obj X)
    ≫ ((@shiftFunctorAdd' C _ _ _ Shift₂ (a + n) 1 c (by rw [← h, add_assoc])).symm.app X).hom  = _
  have heq : power_of_alpha X a (a + n) n rfl = power_of_alpha X a b n hn ≫ eqToHom
      (by rw [hn]) := by
    rw [power_of_alpha_eqToHom n X a (a + n) a b rfl hn rfl hn]
    simp only [eqToHom_refl, id_comp]
  rw [heq]
  simp only [Functor.comp_obj, Iso.app_hom, Iso.symm_hom, assoc]
  congr 1
  have := hP.α.naturality (X := (@shiftFunctor C _ _ _ Shift₂ b).obj X)
    (Y := (@shiftFunctor C _ _ _ Shift₂ (a + ↑n)).obj X) (eqToHom (by rw [hn]))
  simp only [Functor.id_obj, Functor.id_map] at this
  rw [← assoc, this, assoc]
  congr 1
  rw [eqToHom_map]
  have := @shiftFunctorAdd'_symm_eqToIso C _ _ _ Shift₂ (a + n) 1 c b 1 c (by rw [← h, add_assoc])
    (by rw [← hn, ← h, add_assoc]) hn rfl
  apply_fun (fun T ↦ T.hom.app X) at this
  simp only [Functor.comp_obj, Iso.symm_hom, eqToIso_refl, Iso.trans_refl, Iso.trans_hom,
    eqToIso.hom, NatTrans.comp_app, eqToHom_app] at this
  rw [this]
  simp

lemma power_of_alpha_naturality {X Y : C} (f : X ⟶ Y) (a b : ℤ) (n : ℕ) (hn : a + n = b) :
    (@shiftFunctor C _ _ _ Shift₂ a).map f ≫ power_of_alpha Y a b n hn =
    power_of_alpha X a b n hn ≫ (@shiftFunctor C _ _ _ Shift₂ b).map f := by
  revert X Y f a b
  induction' n with n hind
  · intro X Y f a b hn
    have hab : a = b := by rw [← hn, Nat.cast_zero, add_zero]
    rw [power_of_alpha_zero X a b hab, power_of_alpha_zero Y a b hab,
      eqToHom_naturality (fun (a : ℤ) ↦ (@shiftFunctor C _ _ _ Shift₂ a).map f) hab]
  · intro X Y f a b hn
    rw [power_of_alpha_plus_one X n a (a + n) b rfl (by rw [← hn, Nat.cast_add, Nat.cast_one])]
    rw [power_of_alpha_plus_one Y n a (a + n) b rfl (by rw [← hn, Nat.cast_add, Nat.cast_one])]
    conv_lhs => rw [← assoc, hind f a (a + n) rfl]
    have := α.naturality ((@shiftFunctor C _ _ _ Shift₂ (a + n)).map f)
    simp only [Functor.id_obj, Functor.id_map] at this
    slice_lhs 2 3 => rw [this]
    have := (@shiftFunctorAdd' C _ _ _ Shift₂ (a + n) 1 b
      (by rw [← hn, Nat.cast_add, Nat.cast_one, add_assoc])).inv.naturality f
    simp only [Functor.comp_obj, Functor.comp_map] at this
    simp only [Functor.comp_obj, Iso.app_hom, Iso.symm_hom, assoc]
    rw [this]

lemma power_of_alpha_assoc (X : C) (a b c : ℤ) (n m : ℕ) (hn : a + n = b) (hm : b + m = c) :
    power_of_alpha X a b n hn ≫ power_of_alpha X b c m hm =
    power_of_alpha X a c (n + m) (by rw [← hm, ← hn, Nat.cast_add, add_assoc]) := by
  revert n X a b c
  induction' m with m hind
  · intro X a b c n hn hm
    have heq : c = b := by rw [← hm, Nat.cast_zero, add_zero]
    rw [power_of_alpha_zero _ _ _ heq.symm]
    simp only [add_zero]
    rw [power_of_alpha_eqToHom n X a c a b (by rw [heq, hn]) hn rfl heq]
    simp only [eqToHom_refl, id_comp]
  · intro X a b c n hn hm
    rw [power_of_alpha_plus_one X m b (b + m) c rfl hm, ← assoc, hind X a b (b + m) n hn rfl]
    have : n + (m + 1) = (n + m) + 1 := by rw [add_assoc]
    simp_rw [this]
    rw [power_of_alpha_plus_one X (n + m) a (b + m) c (by rw [← hn, Nat.cast_add, add_assoc])
      (by rw [← hm, ← hn, Nat.cast_add, Nat.cast_add, Nat.cast_one, add_assoc, add_assoc])]

/-- The morphism "`αⁿ`"" from `X` to `X⟪n⟫`, if `n` is a natural number.-/
noncomputable def power_of_alpha' (X : C) (n : ℕ) :
    X ⟶ (@shiftFunctor C _ _ _ Shift₂ (n : ℤ)).obj X :=
  (@shiftFunctorZero C _ _ _ Shift₂).inv.app X ≫ power_of_alpha X 0 n n (by rw [zero_add])

@[simp]
lemma power_of_alpha'_zero (X : C) : power_of_alpha' X 0 = (shiftFunctorZero C ℤ).inv.app X := by
  dsimp [power_of_alpha']
  rw [power_of_alpha_zero']
  simp only [Iso.refl_hom, comp_id]
  rfl

@[simp]
lemma power_of_alpha'_plus_one (X : C) (n : ℕ) :
    power_of_alpha' X (n + 1) = power_of_alpha' X n ≫ α.app _ ≫
    ((@shiftFunctorAdd' C _ _ _ Shift₂ n 1 ↑(n + 1) rfl).symm.app X).hom := by
  dsimp [power_of_alpha']
  rw [power_of_alpha_plus_one X n 0 n ↑(n + 1) (by rw [zero_add])]
  simp only [Functor.comp_obj, Iso.app_hom, Iso.symm_hom, assoc]
/-  dsimp [power_of_alpha']-/

lemma adj_left_shift (X Y : C) (p q : ℤ) (hpq : p + 1 ≤ q) [IsLE X p] [IsGE Y q] :
    Function.Bijective (fun (f : (@shiftFunctor C _ _ _ Shift₂ 1).obj X ⟶ Y) ↦ α.app X ≫ f) := by
  set s₁ := fun (f : (@shiftFunctor C _ _ _ Shift₂ 1).obj X ⟶ Y) ↦ α.app X ≫ f
  set s₂ := fun (f : (@shiftFunctor C _ _ _ Shift₂ 1).obj
      ((@shiftFunctor C _ _ _ Shift₂ (-p)).obj X) ⟶ (@shiftFunctor C _ _ _ Shift₂ (-p)).obj Y) ↦
      α.app _ ≫ f
  set e : ((@shiftFunctor C _ _ _ Shift₂ 1).obj X ⟶ Y) → ((@shiftFunctor C _ _ _ Shift₂ 1).obj
      ((@shiftFunctor C _ _ _ Shift₂ (-p)).obj X) ⟶ (@shiftFunctor C _ _ _ Shift₂ (-p)).obj Y) :=
    Function.comp (CategoryStruct.comp (@shiftComm C _ _ _ Shift₂ _ _ _).hom)
    (@shiftFunctor C _ _ _ Shift₂ (-p)).map
  have he : Function.Bijective e := by
    apply Function.Bijective.comp
    · have heq : CategoryStruct.comp (@shiftComm C _ _ _ Shift₂ X (-p) 1).hom =
          (Iso.homFromEquiv (Z := (@shiftFunctor C _ _ _ Shift₂ (-p)).obj Y)
          (@shiftComm C _ _ _ Shift₂ X (-p) 1).symm).toFun := by
        ext f
        simp only [Iso.app_hom, shiftComm_symm, Equiv.toFun_as_coe, Iso.homFromEquiv_apply,
          Iso.app_inv]
        conv_rhs => rw [← shiftFunctorComm_symm, Iso.symm_inv]
      rw [heq]
      exact Equiv.bijective _
    · exact ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩
  set e' : (X ⟶ Y) → (((@shiftFunctor C _ _ _ Shift₂ (-p)).obj X) ⟶ (@shiftFunctor C _ _ _ Shift₂
      (-p)).obj Y) := (@shiftFunctor C _ _ _ Shift₂ (-p)).map
  have he' : Function.Bijective e' := ⟨Functor.Faithful.map_injective, Functor.Full.map_surjective⟩
  have hcomm : e' ∘ s₁ = s₂ ∘ e := by
    ext f
    simp only [Functor.id_obj, Function.comp_apply, Functor.map_comp, Iso.app_hom, e', s₁, s₂, e]
    rw [← assoc, α_vs_second_shift (-p) X]
  rw [← Function.Bijective.of_comp_iff' he', hcomm]
  refine Function.Bijective.comp (hP.adj_left ?_ ?_) he
  · exact hP.GE_shift (p + 1) _ _ (by linarith) _ (GE_antitone hpq _ (mem_of_isGE Y q))
  · exact hP.LE_shift p _ _ (by linarith) _ (mem_of_isLE _ _)

lemma adj_left_extended (X Y : C) (a b m : ℤ) (n : ℕ) (hn : a + n = b) [IsLE X (m - a)]
    [IsGE Y (m + n)] : Function.Bijective
    (fun (f : (@shiftFunctor C _ _ _ Shift₂ b).obj X ⟶ Y) ↦ (power_of_alpha X a b n hn ≫ f)) := by
  revert X Y a b m
  induction' n with n hind
  · intro X Y a b m hn _ _
    rw [power_of_alpha_zero X a b (by rw [← hn, Nat.cast_zero, add_zero])]
    exact IsIso.comp_left_bijective _
  · intro X Y a b m hn _ _
    rw [power_of_alpha_plus_one X n a (a + n) b rfl (by rw [← hn, Nat.cast_add, Nat.cast_one])]
    simp only [Functor.comp_obj, Iso.app_hom, Iso.symm_hom, assoc]
    refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ (IsIso.comp_left_bijective _))
    · have : IsGE Y (m + n) := isGE_of_GE Y (m + n) (m + ↑(n + 1)) (by simp only [Nat.cast_add,
      Nat.cast_one, add_le_add_iff_left, le_add_iff_nonneg_right, zero_le_one])
      exact hind X Y a (a + n) m rfl
    · have : IsLE ((@shiftFunctor C _ _ _ Shift₂ (a + n)).obj X) (m + ↑n) := by
        exact isLE_shift X (m - a) (a + n) (m + n) (by linarith)
      exact adj_left_shift _ _ (m + n) (m + ↑(n + 1))
        (by simp only [Nat.cast_add, Nat.cast_one]; linarith)

lemma adj_left_extended' (X Y : C) (m : ℤ) (n : ℕ) [IsLE X m] [IsGE Y (m + n)] :
    Function.Bijective
    (fun (f : (@shiftFunctor C _ _ _ Shift₂ n).obj X ⟶ Y) ↦ (power_of_alpha' X n ≫ f)) := by
  dsimp [power_of_alpha']; simp only [assoc]
  have : IsLE X (m - 0) := isLE_of_LE X m (m - 0) (by simp only [sub_zero, le_refl])
  exact Function.Bijective.comp (IsIso.comp_left_bijective _)
    (adj_left_extended X Y 0 n m n (by rw [zero_add]))

/- Lemmas about omega and shifting.-/

lemma shift_omega_mono {X Y : C} (f : X ⟶ Y) (n m : ℤ) (hf : ∀ (Z : C) (hZ : IsGE Z n),
    Mono ((preadditiveYoneda.obj Z).map f.op)) : ∀ (Z : C) (hZ : IsGE Z n),
    Mono ((preadditiveYoneda.obj Z).map (f⟦m⟧').op) := by
  intro Z hZ
  set e := shiftNegShift Z m
  have hf := hf (Z⟦-m⟧) inferInstance
  rw [AddCommGrp.mono_iff_ker_eq_bot, AddSubgroup.eq_bot_iff_forall] at hf ⊢
  intro g hg
  change f⟦m⟧' ≫ g = 0 at hg
  rw [← cancel_mono e.inv, zero_comp] at hg ⊢
  rw [assoc] at hg
  obtain ⟨g', hg'⟩ := Functor.Full.map_surjective (F := shiftFunctor C m) (g ≫ e.inv)
  rw [← hg'] at hg ⊢
  rw [← Functor.map_comp] at hg
  have heq : (0 : X ⟶ Z⟦-m⟧)⟦m⟧' = 0 := by rw [Functor.map_zero]
  rw [← heq] at hg
  rw [hf g' (Functor.Faithful.map_injective (F := shiftFunctor C m) hg), Functor.map_zero]

lemma shift_omega_epi {X Y : C} (f : X ⟶ Y) (n m : ℤ) (hf : ∀ (Z : C) (hZ : IsGE Z n),
    Epi ((preadditiveYoneda.obj Z).map f.op)) : ∀ (Z : C) (hZ : IsGE Z n),
    Epi ((preadditiveYoneda.obj Z).map (f⟦m⟧').op) := by
  intro Z hZ
  set e := shiftNegShift Z m
  have hf := hf (Z⟦-m⟧) inferInstance
  rw [AddCommGrp.epi_iff_range_eq_top, AddSubgroup.eq_top_iff'] at hf ⊢
  intro g
  change X⟦m⟧ ⟶ Z at g
  rw [AddMonoidHom.mem_range]
  obtain ⟨g', hg'⟩ := AddMonoidHom.mem_range.mp (hf ((shiftShiftNeg X m).inv ≫ g⟦-m⟧'))
  change f ≫ g' = _ at hg'
  existsi g'⟦m⟧' ≫ (shiftNegShift Z m).hom
  change f⟦m⟧' ≫ g'⟦m⟧' ≫ _ = _
  rw [← assoc, ← Functor.map_comp, hg', Functor.map_comp]
  have := shift_equiv_triangle m X
  rw [← cancel_mono (shiftNegShift ((shiftFunctor C m).obj X) m).inv, id_comp, assoc,
    Iso.hom_inv_id, comp_id] at this
  rw [this]
  erw [← (shiftEquiv C m).counitIso.inv.naturality g]
  simp only [Functor.id_obj, shiftEquiv'_inverse, shiftEquiv'_functor, Functor.comp_obj,
    Functor.id_map, shiftEquiv'_counitIso, Iso.app_hom, assoc, Iso.inv_hom_id_app, comp_id]

/- The functor forgetting filtrations on the subcategory of objects `X` such that `IsLE X 0`.-/

/- First we do the case where the support is a singleton.-/

lemma existence_omega_support_singleton (X : C) [IsLE X 0] (hsupp : Finset.card (support X) = 1) :
    ∃ (Y : hP.Core') (s : X ⟶ Y.1),
    ∀ (Z : C), IsGE Z 0 → IsIso ((preadditiveYoneda.obj Z).map (Quiver.Hom.op s)) := by
  obtain ⟨n, hsupp⟩ := Finset.card_eq_one.mp hsupp
  have hn : n ≤ 0 := by
    have := (isLE_iff_support_bounded_above X 0).mp inferInstance
    have h : n ∈ support X := by rw [hsupp, Finset.mem_singleton]
    exact Set.mem_Iic.mp (this h)
  have hn : n = - ↑n.natAbs := by rw [Int.ofNat_natAbs_of_nonpos hn, neg_neg]
  existsi ⟨(@shiftFunctor C _ _ _ Shift₂ n.natAbs).obj X, ?_⟩, power_of_alpha' X n.natAbs
  · rw [shift_isCore_iff_support_sub_singleton X n n.natAbs (by linarith), hsupp]
  · intro Z _
    have : IsLE X n := by
      rw [isLE_iff_support_bounded_above X n, hsupp]
      simp only [Finset.coe_singleton, Set.singleton_subset_iff, Set.mem_Iic, le_refl]
    have : IsGE Z (n + n.natAbs) := by
      rw [hn]; simp only [Int.natCast_natAbs, Int.natAbs_neg, abs_abs, add_left_neg]
      infer_instance
    set f : ((@shiftFunctor C _ _ _ Shift₂ ↑n.natAbs).obj X ⟶ Z) →+ (X ⟶ Z) :=
      {
       toFun := fun f ↦ power_of_alpha' X n.natAbs ≫ f,
       map_zero' := by simp only [comp_zero]
       map_add' := fun _ _ ↦ by simp only [comp_add]
      }
    set e := AddEquiv.ofBijective f (adj_left_extended' X Z n n.natAbs)
    simp only [preadditiveYoneda_obj, Int.reduceNeg, Int.rawCast, Int.cast_id, Nat.rawCast,
      Nat.cast_id, Int.Nat.cast_ofNat_Int, Int.reduceAdd, Int.ofNat_eq_coe, eq_mp_eq_cast, id_eq,
      eq_mpr_eq_cast, Functor.comp_obj, preadditiveYonedaObj_obj, ModuleCat.forget₂_obj,
      Functor.comp_map, preadditiveYonedaObj_map, Quiver.Hom.unop_op, ModuleCat.forget₂_map]
    change IsIso (AddCommGrp.ofHom e.toAddMonoidHom)
    apply IsIso.mk
    existsi (AddCommGrp.ofHom e.symm.toAddMonoidHom)
    constructor
    · ext a
      change e.symm.toFun (e.toFun a) = a
      simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.toEquiv_symm, Equiv.toFun_as_coe,
        EquivLike.coe_coe, EquivLike.coe_symm_apply_apply]
    · ext a
      change e.toFun (e.symm.toFun a) = a
      simp only [AddEquiv.toEquiv_eq_coe, AddEquiv.toEquiv_symm, Equiv.toFun_as_coe,
        AddEquiv.coe_toEquiv_symm, EquivLike.coe_coe, AddEquiv.apply_symm_apply]

/- Then the general case, by induction on the size of the support.-/

open CategoryTheory.Pretriangulated.Opposite

noncomputable abbrev triangle_to_yoneda_comp_arrows₄ (Z : C) {X₁ X₂ X₃ : C} (u : X₁ ⟶ X₂)
    (v : X₂ ⟶ X₃) (w : X₃ ⟶ X₁⟦(1 : ℤ)⟧) : ComposableArrows AddCommGrp 4 :=
  ComposableArrows.mk₄ (((preadditiveYoneda.obj Z).map w.op)) (((preadditiveYoneda.obj Z).map v.op))
  (((preadditiveYoneda.obj Z).map u.op)) ((preadditiveYoneda.obj Z).map (-w⟦(-1 : ℤ)⟧' ≫
  (shiftEquiv C (1 : ℤ)).unitIso.inv.app _).op)

noncomputable abbrev triangle_to_yoneda_comp_arrows₄_hom (Z : C) {X₁ X₂ X₃ X'₁ X'₂ X'₃: C}
    (u : X₁ ⟶ X₂) (v : X₂ ⟶ X₃) (w : X₃ ⟶ X₁⟦(1 : ℤ)⟧) (u' : X'₁ ⟶ X'₂) (v' : X'₂ ⟶ X'₃)
    (w' : X'₃ ⟶ X'₁⟦(1 : ℤ)⟧) (f : Triangle.mk u' v' w' ⟶ Triangle.mk u v w) :
    triangle_to_yoneda_comp_arrows₄ Z u v w ⟶ triangle_to_yoneda_comp_arrows₄ Z u' v' w' := by
    refine ComposableArrows.homMk ?_ ?_
    · intro i
      match i with
      | 0 => exact (preadditiveYoneda.obj Z).map (f.hom₁⟦(1 : ℤ)⟧').op
      | 1 => exact (preadditiveYoneda.obj Z).map f.hom₃.op
      | 2 => exact (preadditiveYoneda.obj Z).map f.hom₂.op
      | 3 => exact (preadditiveYoneda.obj Z).map f.hom₁.op
      | 4 => refine (preadditiveYoneda.obj Z).map (f.hom₃⟦-1⟧').op
    · intro i _
      match i with
      | 0 => change (preadditiveYoneda.obj Z).map w.op ≫ (preadditiveYoneda.obj Z).map
                 f.hom₃.op = (preadditiveYoneda.obj Z).map ((shiftFunctor C 1).map f.hom₁).op ≫
                 (preadditiveYoneda.obj Z).map w'.op
             rw [← Functor.map_comp, ← Functor.map_comp]
             congr 1
             change (f.hom₃ ≫ w).op = _
             erw [← f.comm₃]; rfl
      | 1 => change (preadditiveYoneda.obj Z).map v.op ≫ (preadditiveYoneda.obj Z).map
                 f.hom₂.op = (preadditiveYoneda.obj Z).map f.hom₃.op ≫
                 (preadditiveYoneda.obj Z).map v'.op
             rw [← Functor.map_comp, ← Functor.map_comp]
             congr 1
             change (f.hom₂ ≫ v).op = _
             erw [← f.comm₂]
             rfl
      | 2 => change (preadditiveYoneda.obj Z).map u.op ≫ (preadditiveYoneda.obj Z).map f.hom₁.op
                 = (preadditiveYoneda.obj Z).map f.hom₂.op ≫ (preadditiveYoneda.obj Z).map u'.op
             rw [← Functor.map_comp, ← Functor.map_comp]
             congr 1
             change (f.hom₁ ≫ u).op = _
             erw [← f.comm₁]
             rfl
      | 3 => change (preadditiveYoneda.obj Z).map (-(shiftFunctor C (-1)).map w ≫
                 (shiftEquiv C 1).unitIso.inv.app X₁).op ≫ (preadditiveYoneda.obj Z).map
                 ((shiftFunctor C (-1)).map f.hom₃).op = (preadditiveYoneda.obj Z).map f.hom₁.op ≫
                 (preadditiveYoneda.obj Z).map (-(shiftFunctor C (-1)).map w' ≫
                 (shiftEquiv C 1).unitIso.inv.app X'₁).op
             rw [← Functor.map_comp, ← Functor.map_comp]
             congr 1
             change (f.hom₃⟦-1⟧' ≫ (- w⟦-1⟧' ≫ (shiftEquiv C 1).unitIso.inv.app X₁)).op = _
             conv_lhs => rw [Preadditive.comp_neg, ← assoc, ← Functor.map_comp]; erw [← f.comm₃]
             change _ = ((-(shiftFunctor C (-1)).map w' ≫ (shiftEquiv C 1).unitIso.inv.app
                 X'₁) ≫ f.hom₁).op
             congr 1
             conv_rhs => rw [Preadditive.neg_comp, assoc]
                         erw [← (shiftEquiv C (1 : ℤ)).unitIso.inv.naturality f.hom₁]
             simp only [Int.reduceNeg, Triangle.mk_obj₃, Functor.id_obj, Triangle.mk_obj₁,
               Triangle.mk_mor₃, Functor.map_comp, shiftEquiv'_functor, shiftEquiv'_inverse,
               shiftEquiv'_unitIso, Iso.symm_inv, assoc, Functor.comp_obj, Functor.comp_map]

lemma triangle_to_yoneda_comp_arrows₄_exact_of_distinguished (Z : C) {X₁ X₂ X₃ : C} (u : X₁ ⟶ X₂)
    (v : X₂ ⟶ X₃) (w : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
    (dT : Triangle.mk u v w ∈ Pretriangulated.distinguishedTriangles) :
    (triangle_to_yoneda_comp_arrows₄ Z u v w).Exact := by
  refine {zero := fun i _ ↦ ?_, exact := fun i _ ↦ ?_}
  · match i with
    | 0 => change ((preadditiveYoneda.obj Z).map w.op) ≫ ((preadditiveYoneda.obj Z).map
                 v.op) = 0
           rw [← Functor.map_comp]
           change (preadditiveYoneda.obj Z).map (v ≫ w).op = 0
           have : v ≫ w = 0 := Pretriangulated.comp_distTriang_mor_zero₂₃ _ dT
           rw [this]
           erw [Functor.map_zero]
    | 1 => change ((preadditiveYoneda.obj Z).map v.op) ≫ ((preadditiveYoneda.obj Z).map
                 u.op) = 0
           rw [← Functor.map_comp]
           change (preadditiveYoneda.obj Z).map (u ≫ v).op = 0
           have : u ≫ v = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ dT
           rw [this]
           erw [Functor.map_zero]
    | 2 => change ((preadditiveYoneda.obj Z).map u.op) ≫ ((preadditiveYoneda.obj Z).map
                 ((-(w⟦-1⟧') ≫ (shiftEquiv C 1).unitIso.inv.app X₁)).op) = 0
           rw [← Functor.map_comp]
           change (preadditiveYoneda.obj Z).map ((-(w⟦-1⟧') ≫
                 (shiftEquiv C 1).unitIso.inv.app X₁) ≫ u).op = 0
           have : (-(w⟦-1⟧') ≫ (shiftEquiv C 1).unitIso.inv.app X₁) ≫ u = 0 :=
                 Pretriangulated.comp_distTriang_mor_zero₁₂ _
                 (Pretriangulated.inv_rot_of_distTriang _ dT)
           rw [this]
           erw [Functor.map_zero]
  · match i with
    | 0 => rw [Pretriangulated.rotate_distinguished_triangle] at dT
           have dT' : (triangleOpEquivalence C).functor.obj (Opposite.op (Triangle.mk v w
               (-u⟦1⟧'))) ∈ Opposite.distinguishedTriangles C := by
             rw [Opposite.mem_distinguishedTriangles_iff']
             existsi (Triangle.mk v w (-u⟦1⟧')), dT
             exact Nonempty.intro (Iso.refl _)
           exact Functor.IsHomological.exact (F := preadditiveYoneda.obj Z) _ dT'
    | 1 => have dT' : (triangleOpEquivalence C).functor.obj (Opposite.op (Triangle.mk u v w)) ∈
               Opposite.distinguishedTriangles C := by
             rw [Opposite.mem_distinguishedTriangles_iff']
             existsi (Triangle.mk u v w), dT
             exact Nonempty.intro (Iso.refl _)
           exact Functor.IsHomological.exact (F := preadditiveYoneda.obj Z) _ dT'
    | 2 => set T'₂ := (triangleOpEquivalence C).functor.obj (Opposite.op (Triangle.mk
                 (-w⟦(-1 : ℤ)⟧' ≫ (shiftEquiv C (1 : ℤ)).unitIso.inv.app _) u (v ≫
                 (shiftEquiv C (1 : ℤ)).counitIso.inv.app _ )))
           have dT' : ((triangleOpEquivalence C).functor.obj (Opposite.op (Triangle.mk
               (-w⟦(-1 : ℤ)⟧' ≫ (shiftEquiv C (1 : ℤ)).unitIso.inv.app _) u (v ≫ (shiftEquiv C
               (1 : ℤ)).counitIso.inv.app _ )))) ∈ Opposite.distinguishedTriangles C := by
             rw [Opposite.mem_distinguishedTriangles_iff']
             existsi (Triangle.mk (-w⟦(-1 : ℤ)⟧' ≫ (shiftEquiv C (1 : ℤ)).unitIso.inv.app _)
                   u (v ≫ (shiftEquiv C (1 : ℤ)).counitIso.inv.app _ )),
                   Pretriangulated.inv_rot_of_distTriang _ dT
             exact Nonempty.intro (Iso.refl _)
           exact Functor.IsHomological.exact (F := preadditiveYoneda.obj Z) _ dT'

lemma existence_omega_aux (n : ℕ) : ∀ (X : C) [IsLE X 0], Finset.card (support X) = n →
    ∃ (Y : hP.Core') (s : X ⟶ Y.1),
    ∀ (Z : C), IsGE Z 0 → IsIso ((preadditiveYoneda.obj Z).map (Quiver.Hom.op s)) := by
  refine Nat.strongRec ?_ n
  intro n hn X _ hX
  by_cases h : n = 0
  · existsi 0, 0
    intro Z _
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
    set T := (triangleGELT b).obj X
    set dT := triangleGELT_distinguished b X
    have hb : b ∈ support X := by
      dsimp [b]; rw [← Finset.mem_coe]
      apply Set.Nonempty.csSup_mem
      · rw [← hX, ← ne_eq, Finset.card_ne_zero, ← Finset.coe_nonempty] at h
        exact h
      · exact Finset.finite_toSet _
    have : b ≤ 0 := by
      apply csSup_le (Finset.coe_nonempty.mp ⟨b, hb⟩)
      have : IsLE X 0 := inferInstance
      rw [isLE_iff_support_bounded_above] at this
      exact fun _ hn ↦ Set.mem_Iic.mp (this hn)
    have : IsLE T.obj₃ 0 := by
      have : IsLE T.obj₃ (b - 1) := by dsimp [T]; infer_instance
      exact isLE_of_LE _ (b - 1) 0 (by linarith)
    have : IsLE T.obj₁ 0 := by
      have : IsLE T.obj₂ 0 := by dsimp [T]; infer_instance
      exact LE_ext₁ _ dT 0
    have h₁ : Finset.card (support T.obj₁) = 1 := by
      dsimp [T]
      rw [support_truncGE, Finset.card_eq_one]
      existsi b
      rw [Finset.eq_singleton_iff_unique_mem]
      simp only [Finset.mem_filter, le_refl, and_true, and_imp]
      constructor
      · exact hb
      · exact fun _ hn hbn ↦ le_antisymm (le_csSup (Finset.bddAbove _) hn) hbn
    have h₃ : Finset.card (support T.obj₃) < n := by
      have heq : support T.obj₃ = Finset.erase (support X) b := by
        ext n
        simp only [Finset.mem_erase, ne_eq]
        dsimp [T]; rw [support_truncLT, Finset.mem_filter]
        constructor
        · exact fun h ↦ ⟨ne_of_lt h.2, h.1⟩
        · intro h
          rw [and_iff_right h.2, lt_iff_le_and_ne, ne_eq, and_iff_left h.1]
          exact le_csSup (Finset.bddAbove _) (Finset.mem_coe.mpr h.2)
      rw [heq, ← hX]
      exact Finset.card_erase_lt_of_mem hb
    obtain ⟨Y₁, s₁, hY₁⟩ := existence_omega_support_singleton T.obj₁ h₁
    obtain ⟨Y₃, s₃, hY₃⟩ := hn _ h₃ T.obj₃ rfl
    have : IsLE Y₁.1 0 := {le := Y₁.2.1}
    have : IsLE Y₃.1 0 := {le := Y₃.2.1}
    have : IsGE Y₁.1 0 := {ge := Y₁.2.2}
    have : IsGE Y₃.1 0 := {ge := Y₃.2.2}
    have := hY₃ (Y₁.1⟦(1 : ℤ)⟧) inferInstance
    set w : Y₃.obj ⟶ Y₁.obj⟦(1 : ℤ)⟧ := inv (((preadditiveYoneda.obj (Y₁.obj⟦(1 : ℤ)⟧)).map s₃.op))
      (T.mor₃ ≫ s₁⟦1⟧') with hwdef
    have hw : s₃ ≫ w = T.mor₃ ≫ s₁⟦1⟧' := by
      change ((preadditiveYoneda.obj ((shiftFunctor C 1).obj Y₁.obj)).map s₃.op) w = _
      rw [hwdef]
      change (_ ≫ ((preadditiveYoneda.obj ((shiftFunctor C 1).obj Y₁.obj)).map s₃.op)) _ = _
      rw [IsIso.inv_hom_id]
      simp only [preadditiveYoneda_obj, Functor.comp_obj, preadditiveYonedaObj_obj,
        ModuleCat.forget₂_obj, AddCommGrp.coe_of, AddCommGrp.coe_id', id_eq]
    obtain ⟨Y₂, u, v, dT'⟩ := distinguished_cocone_triangle₂ w
    obtain ⟨s₂, hu, hv⟩ := complete_distinguished_triangle_morphism₂ _ _ dT dT' s₁ s₃ hw.symm
    have hY₂ : tCore.P Y₂ := by
      constructor
      · refine (@LE_ext₂ C _ _ _ _ _ _ _ _ dT' 0 ?_ ?_).le
        simp only [Triangle.mk_obj₁]; infer_instance
        simp only [Triangle.mk_obj₃]; infer_instance
      · refine (@GE_ext₂ C _ _ _ _ _ _ _ _ dT' 0 ?_ ?_).ge
        simp only [Triangle.mk_obj₁]; infer_instance
        simp only [Triangle.mk_obj₃]; infer_instance
    existsi ⟨Y₂, hY₂⟩, s₂
    intro Z hZ
    refine Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (R₁ := triangle_to_yoneda_comp_arrows₄ Z
      u v w) (R₂ := triangle_to_yoneda_comp_arrows₄ Z T.mor₁ T.mor₂ T.mor₃)
      (triangle_to_yoneda_comp_arrows₄_exact_of_distinguished Z u v w dT')
      (triangle_to_yoneda_comp_arrows₄_exact_of_distinguished Z T.mor₁ T.mor₂ T.mor₃ dT)
      (triangle_to_yoneda_comp_arrows₄_hom Z u v w T.mor₁ T.mor₂ T.mor₃
      (Triangle.homMk T (Triangle.mk u v w) s₁ s₂ s₃ hu hv hw.symm)) ?_ ?_ ?_ ?_
    · exact shift_omega_epi s₁ 0 1 (fun Z hZ ↦ @IsIso.epi_of_iso _ _ _ _ _ (hY₁ Z hZ)) Z hZ
    · exact hY₃ Z hZ
    · exact hY₁ Z hZ
    · exact shift_omega_mono s₃ 0 (-1) (fun Z hZ ↦ @IsIso.mono_of_iso _ _ _ _ _ (hY₃ Z hZ)) Z hZ

lemma existence_omega (X : C) [IsLE X 0] : ∃ (Y : hP.Core') (s : X ⟶ Y.1),
    ∀ (Z : C), IsGE Z 0 → Function.Bijective (fun (f : Y.1 ⟶ Z) ↦ s ≫ f) := by
  obtain ⟨Y, s, h⟩ := existence_omega_aux (Finset.card (support X)) X rfl
  use Y, s
  intro Z hZ
  have := h Z hZ
  rw [← isIso_iff_bijective]
  exact (forget AddCommGrp).map_isIso ((preadditiveYoneda.obj Z).map s.op)

end FilteredTriangulated

end Triangulated

end CategoryTheory
