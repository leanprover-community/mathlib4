import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Shift.ShiftSequence
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Shift.Predicate

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

attribute [local instance] endofunctorMonoidalCategory

variable {C D : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
  [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

variable (C)

structure FilteredTriangulated where
  s : MonoidalFunctor (Discrete ℤ) (C ⥤ C)
  s_commshift : ∀ (n : ℤ), (s.obj {as := n}).CommShift ℤ
  s_triang : ∀ (n : ℤ), (s.obj {as := n}).IsTriangulated
  α : 𝟭 C ⟶ s.obj {as := 1}
  LE : ℤ → Triangulated.Subcategory C
  GE : ℤ → Triangulated.Subcategory C
  LE_closedUnderIsomorphisms : ∀ (n : ℤ), ClosedUnderIsomorphisms (LE n).P
  GE_closedUnderIsomorphisms : ∀ (n : ℤ), ClosedUnderIsomorphisms (GE n).P
  LE_zero_le : (LE 0).P ≤ (LE 1).P
  GE_one_le : (GE 1).P ≤ (GE 0).P
  LE_shift : ∀ (n a n' : ℤ), a + n = n' → ∀ (X : C), (LE n).P X → (LE n').P
    ((s.obj {as := a}).obj X)
  GE_shift : ∀ (n a n' : ℤ), a + n = n' → ∀ (X : C), (GE n).P X → (GE n').P
    ((s.obj {as := a}).obj X)
  zero' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (GE 1).P X → (LE 0).P Y → f = 0
  adj_left : ∀ ⦃X Y : C⦄, (GE 1).P X → (LE 0).P Y → Function.Bijective
    (fun (f : (s.obj {as := 1}).obj Y ⟶ X) ↦ (α.app Y ≫ f : Y ⟶ X))
  adj_right : ∀ ⦃X Y : C⦄, (GE 1).P X → (LE 0).P Y → Function.Bijective
    (fun (f : Y ⟶ X) ↦ (f ≫ α.app X: Y ⟶ (s.obj {as := 1}).obj X))
  LE_exhaustive : ∀ (X : C), ∃ (n : ℤ), (LE n).P X
  GE_exhaustive : ∀ (X : C), ∃ (n : ℤ), (GE n).P X
  α_s : ∀ (X : C), (s.obj {as := 1}).map (α.app X) = α.app ((s.obj {as := 1}).obj X)
  exists_triangle_one_zero : ∀ (X : C), ∃ (A : C) (B : C) (_ : (GE 1).P A) (_ : (LE 0).P B)
    (f : A ⟶ X) (g : X ⟶ B) (h : B ⟶ A⟦1⟧),
    Triangle.mk f g h ∈ distinguishedTriangles

namespace FilteredTriangulated

attribute [instance] LE_closedUnderIsomorphisms GE_closedUnderIsomorphisms

variable {C}
variable (F : FilteredTriangulated C)

lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : (F.GE n₁).P X) (_ : (F.LE n₀).P Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := F.exists_triangle_one_zero ((F.s.obj {as := -n₀}).obj A)
  let T := (@Functor.mapTriangle _ _ _ _ _ _ (F.s.obj {as := n₀}) (F.s_commshift n₀)).obj
    (Triangle.mk f g h)
  let e := (@shiftEquiv' C _ _ _ {shift := F.s} (-n₀) n₀ (by rw [add_left_neg])).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine isomorphic_distinguished _ (@Functor.IsTriangulated.map_distinguished _ _ _ _ _ _
      (F.s.obj {as := n₀}) (F.s_commshift n₀) _ _ _ _ _ _ _ _ (F.s_triang n₀) _ mem) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    all_goals dsimp; simp [T]
  exact ⟨_, _, F.GE_shift _ _ _ (by omega) _ hX,
      F.LE_shift _ _ _ (by omega) _ hY, _, _, _, hT'⟩

lemma predicateShift_LE (n n' a : ℤ) (hn' : n = n') :
    (PredicateShift (F.LE n).P a) = (F.LE n').P := by
  ext X
  simp only [PredicateShift, Triangulated.Subcategory.shift_iff, hn']

lemma predicateShift_GE (a n n' : ℤ) (hn' : n = n') :
    (PredicateShift (F.GE n).P a) = (F.GE n').P := by
  ext X
  simp only [PredicateShift, hn', Triangulated.Subcategory.shift_iff]

lemma LE_monotone : Monotone (fun n ↦ (F.LE n).P) := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), (F.LE n).P ≤ (F.LE (n + a)).P
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX =>
    (F.LE_closedUnderIsomorphisms (n + 1)).of_iso ((@shiftEquiv' C _ _ _ {shift := F.s}
    (-n) n (by rw [add_left_neg])).unitIso.symm.app X) (F.LE_shift 1 n (n + 1) rfl _
    (F.LE_zero_le _ (F.LE_shift n (-n) 0 (by rw [add_left_neg]) X hX)))
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n+a))
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

lemma GE_antitone : Antitone (fun n ↦ (F.GE n).P) := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), (F.GE (n + a)).P ≤ (F.GE n).P
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by omega
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX =>
    (F.GE_closedUnderIsomorphisms n).of_iso ((@shiftEquiv' C _ _ _ {shift := F.s}
    (-n) n (by rw [add_left_neg])).unitIso.symm.app X) (F.GE_shift 0 n n (by rw [add_zero]) _
    (F.GE_one_le _ (F.GE_shift (n + 1) (-n) 1 (by rw [neg_add_cancel_left]) X hX)))
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc ]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction' a with a ha
  · exact H_zero
  · exact H_add a 1 _ rfl ha H_one

/-- Given a filtration `F` on a pretriangulated category `C`, the property `F.IsLE X n`
holds if `X : C` is `≤ n` for the filtration. -/
class IsLE (X : C) (n : ℤ) : Prop where
  le : (F.LE n).P X

/-- Given a filtration `F` on a pretriangulated category `C`, the property `F.IsGE X n`
holds if `X : C` is `≥ n` for the filtration. -/
class IsGE (X : C) (n : ℤ) : Prop where
  ge : (F.GE n).P X

lemma mem_of_isLE (X : C) (n : ℤ) [F.IsLE X n] : (F.LE n).P X := IsLE.le

lemma mem_of_isGE (X : C) (n : ℤ) [F.IsGE X n] : (F.GE n).P X := IsGE.ge

-- Should the following be instances or lemmas? Let's make them instances and see what happens.
instance zero_isLE (n : ℤ) : F.IsLE 0 n := {le := (F.LE n).zero}

instance zero_isGE (n : ℤ) : F.IsGE 0 n := {ge := (F.GE n).zero}

instance shift_isLE_of_isLE (X : C) (n a : ℤ) [F.IsLE X n] : F.IsLE (X⟦a⟧) n :=
  {le := (F.LE n).shift X a (F.mem_of_isLE X n)}

instance shift_isGE_of_isGE (X : C) (n a : ℤ) [F.IsGE X n] : F.IsGE (X⟦a⟧) n :=
  {ge := (F.GE n).shift X a (F.mem_of_isGE X n)}

instance LE_ext₁ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [F.IsLE T.obj₂ n]
    [F.IsLE T.obj₃ n] : F.IsLE T.obj₁ n :=
  {le := (F.LE n).ext₁ T hT (F.mem_of_isLE T.obj₂ n) (F.mem_of_isLE T.obj₃ n)}

instance LE_ext₂ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [F.IsLE T.obj₁ n]
    [F.IsLE T.obj₃ n] : F.IsLE T.obj₂ n :=
  {le := (F.LE n).ext₂ T hT (F.mem_of_isLE T.obj₁ n) (F.mem_of_isLE T.obj₃ n)}

instance LE_ext₃ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [F.IsLE T.obj₁ n]
    [F.IsLE T.obj₂ n] : F.IsLE T.obj₃ n :=
  {le := (F.LE n).ext₃ T hT (F.mem_of_isLE T.obj₁ n) (F.mem_of_isLE T.obj₂ n)}

instance GE_ext₁ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [F.IsGE T.obj₂ n]
    [F.IsGE T.obj₃ n] : F.IsGE T.obj₁ n :=
  {ge := (F.GE n).ext₁ T hT (F.mem_of_isGE T.obj₂ n) (F.mem_of_isGE T.obj₃ n)}

instance GE_ext₂ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [F.IsGE T.obj₁ n]
    [F.IsGE T.obj₃ n] : F.IsGE T.obj₂ n :=
  {ge := (F.GE n).ext₂ T hT (F.mem_of_isGE T.obj₁ n) (F.mem_of_isGE T.obj₃ n)}

instance GE_ext₃ (T : Triangle C) (hT : T ∈ distinguishedTriangles) (n : ℤ) [F.IsGE T.obj₁ n]
    [F.IsGE T.obj₂ n] : F.IsGE T.obj₃ n :=
  {ge := (F.GE n).ext₃ T hT (F.mem_of_isGE T.obj₁ n) (F.mem_of_isGE T.obj₂ n)}

lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [F.IsLE X n] : F.IsLE Y n where
  le := mem_of_iso (F.LE n).P e (F.mem_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [F.IsGE X n] : F.IsGE Y n where
  ge := mem_of_iso (F.GE n).P e (F.mem_of_isGE X n)

lemma isLE_of_LE (X : C) (p q : ℤ) (hpq : p ≤ q) [F.IsLE X p] : F.IsLE X q where
  le := LE_monotone F hpq _ (F.mem_of_isLE X p)

lemma isGE_of_GE (X : C) (p q : ℤ) (hpq : p ≤ q) [F.IsGE X q] : F.IsGE X p where
  ge := GE_antitone F hpq _ (F.mem_of_isGE X q)

lemma isLE_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [F.IsLE X n] :
    F.IsLE ((F.s.obj {as := a}).obj X) n' :=
  ⟨F.LE_shift n a n' hn' X (F.mem_of_isLE X n)⟩

lemma isGE_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [F.IsGE X n] :
    F.IsGE ((F.s.obj {as := a}).obj X) n' :=
  ⟨F.GE_shift n a n' hn' X (F.mem_of_isGE X n)⟩

lemma isLE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [F.IsLE ((F.s.obj {as := a}).obj X) n'] :
    F.IsLE X n := by
  have h := F.isLE_shift ((F.s.obj {as := a}).obj X) n' (-a) n (by linarith)
  exact F.isLE_of_iso (show (F.s.obj { as := -a }).obj ((F.s.obj { as := a }).obj X) ≅ X from
  (@shiftEquiv C _ _ _ {shift := F.s} a).unitIso.symm.app X) n

lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n = n') [F.IsGE ((F.s.obj {as := a}).obj X) n'] :
    F.IsGE X n := by
  have h := F.isGE_shift ((F.s.obj {as := a}).obj X) n' (-a) n (by linarith)
  exact F.isGE_of_iso (show (F.s.obj { as := -a }).obj ((F.s.obj { as := a }).obj X) ≅ X from
  (@shiftEquiv C _ _ _ {shift := F.s} a).unitIso.symm.app X) n

lemma isLE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n = n') :
    F.IsLE ((F.s.obj {as := a}).obj X) n' ↔ F.IsLE X n := by
  constructor
  · intro
    exact F.isLE_of_shift X n a n' hn'
  · intro
    exact F.isLE_shift X n a n' hn'

lemma isGE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n = n') :
    F.IsGE ((F.s.obj {as := a}).obj X) n' ↔ F.IsGE X n := by
  constructor
  · intro
    exact F.isGE_of_shift X n a n' hn'
  · intro
    exact F.isGE_shift X n a n' hn'

#exit

lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [F.IsGE X n₁] [F.IsLE Y n₀] : f = 0 := by
  have := F.isLE_shift Y n₀ (-n₀) 0 (by simp only [add_left_neg])
  have := F.isGE_shift X n₁ (-n₀) (n₁-n₀) (by linarith)
  have := F.isGE_of_GE ((F.s.obj {as := -n₀}).obj X) 1 (n₁-n₀) (by linarith)
  apply (@shiftFunctor C _ _ _ {shift := F.s} (-n₀)).map_injective
  simp only [Functor.map_zero]
  apply F.zero'
  · apply F.mem_of_isGE
  · sorry

#exit

  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  · apply t.mem_of_isLE
  · apply t.mem_of_isGE

#exit

lemma zero_of_isLE_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (_ : t.IsLE X n₀) (_ : t.IsGE Y n₁) : f = 0 :=
  t.zero f n₀ n₁ h

lemma isZero (X : C) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    [t.IsLE X n₀] [t.IsGE X n₁] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

def heart (X : C) : Prop := t.LE 0 X ∧ t.GE 0 X

lemma mem_heart_iff (X : C) :
    t.heart X ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨t.mem_of_isLE _ _, t.mem_of_isGE _ _⟩

instance : ClosedUnderIsomorphisms t.heart where
  of_iso {X Y} e hX := by
    rw [mem_heart_iff] at hX ⊢
    have := hX.1
    have := hX.2
    constructor
    · exact t.isLE_of_iso e 0
    · exact t.isGE_of_iso e 0

-- this should be refactored by requiring a type class [t.HasHeart]
-- which would involve a fully faithful functor `H ⥤ C` whose essential image is `t.heart`

abbrev Heart' := FullSubcategory t.heart

abbrev ιHeart' : t.Heart' ⥤ C := fullSubcategoryInclusion _


instance (X : t.Heart') : t.IsLE (t.ιHeart'.obj X) 0 := ⟨X.2.1⟩
instance (X : t.Heart') : t.IsGE (t.ιHeart'.obj X) 0 := ⟨X.2.2⟩
instance (X : t.Heart') : t.IsLE X.1 0 := ⟨X.2.1⟩
instance (X : t.Heart') : t.IsGE X.1 0 := ⟨X.2.2⟩

lemma ιHeart_obj_mem_heart (X : t.Heart') : t.heart (t.ιHeart'.obj X) := X.2

def ιHeartDegree (n : ℤ) : t.Heart' ⥤ C :=
  t.ιHeart' ⋙ shiftFunctor C (-n)

noncomputable def ιHeartDegreeCompShiftIso (n : ℤ) : t.ιHeartDegree n ⋙ shiftFunctor C n ≅ t.ιHeart' :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (shiftFunctorCompIsoId C (-n) n (add_left_neg n)) ≪≫
    Functor.rightUnitor _

class HasHeart where
  H : Type*
  [cat : Category H]
  [preadditive : Preadditive H]
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  fullι : ι.Full := by infer_instance
  faithful_ι : ι.Faithful := by infer_instance
  hι : ι.essImage = setOf t.heart := by simp

def hasHeartFullSubcategory : t.HasHeart where
  H := FullSubcategory t.heart
  ι := fullSubcategoryInclusion t.heart
  hι := by
    ext X
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      refine ClosedUnderIsomorphisms.of_iso (Functor.essImage.getIso h ) ?_
      exact (Functor.essImage.witness h).2
    · intro h
      change (fullSubcategoryInclusion t.heart).obj ⟨X, h⟩ ∈ _
      exact Functor.obj_mem_essImage _ _

variable [ht : t.HasHeart]

def Heart := ht.H

instance : Category t.Heart := ht.cat

def ιHeart : t.Heart ⥤ C := ht.ι

instance : Preadditive t.Heart := ht.preadditive
instance : t.ιHeart.Full := ht.fullι
instance : t.ιHeart.Faithful := ht.faithful_ι
instance : t.ιHeart.Additive := ht.additive_ι

lemma ιHeart_obj_mem (X : t.Heart) : t.heart (t.ιHeart.obj X) := by
  change (t.ιHeart.obj X) ∈ setOf t.heart
  rw [← ht.hι]
  exact t.ιHeart.obj_mem_essImage X

instance (X : t.Heart) : t.IsLE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).1⟩

instance (X : t.Heart) : t.IsGE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).2⟩

lemma mem_essImage_ιHeart_iff (X : C) :
    X ∈ t.ιHeart.essImage ↔ t.heart X := by
  dsimp [ιHeart]
  rw [ht.hι, Set.mem_setOf_eq]

noncomputable def heartMk (X : C) (hX : t.heart X) : t.Heart :=
  Functor.essImage.witness ((t.mem_essImage_ιHeart_iff X).2 hX)

noncomputable def ιHeartObjHeartMkIso (X : C) (hX : t.heart X) :
    t.ιHeart.obj (t.heartMk X hX) ≅ X :=
  Functor.essImage.getIso ((t.mem_essImage_ιHeart_iff X).2 hX)

@[simps obj]
noncomputable def liftHeart {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) :
    D ⥤ t.Heart where
  obj X := t.heartMk (F.obj X) (hF X)
  map {X Y} f := t.ιHeart.preimage ((t.ιHeartObjHeartMkIso _ (hF X)).hom ≫ F.map f ≫
      (t.ιHeartObjHeartMkIso _ (hF Y)).inv)
  map_id X := t.ιHeart.map_injective (by simp)
  map_comp f g := t.ιHeart.map_injective (by simp)

@[simp, reassoc]
lemma ιHeart_map_liftHeart_map {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) {X Y : D} (f : X ⟶ Y) :
    t.ιHeart.map ((t.liftHeart F hF).map f) =
      (t.ιHeartObjHeartMkIso _ (hF X)).hom ≫ F.map f ≫
        (t.ιHeartObjHeartMkIso _ (hF Y)).inv := by
  simp [liftHeart]

noncomputable def liftHeartιHeart {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) :
    t.liftHeart F hF ⋙ t.ιHeart ≅ F :=
  NatIso.ofComponents (fun X => t.ιHeartObjHeartMkIso _ (hF X)) (by aesop_cat)

end TStructure

namespace Subcategory

variable {C}
variable (S : Subcategory C) (t : TStructure C)

class HasInducedTStructure : Prop :=
  exists_triangle_zero_one (A : C) (hA : S.P A) :
    ∃ (X Y : C) (_ : t.LE 0 X) (_ : t.GE 1 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧) (_ : Triangle.mk f g h ∈ distTriang C),
    X ∈ S.ι.essImage ∧ Y ∈ S.ι.essImage

variable [h : S.HasInducedTStructure t]

def tStructure : TStructure S.category where
  LE n X := t.LE n (S.ι.obj X)
  GE n X := t.GE n (S.ι.obj X)
  LE_closedUnderIsomorphisms n := ⟨fun {X Y} e hX => mem_of_iso (t.LE n) (S.ι.mapIso e) hX⟩
  GE_closedUnderIsomorphisms n := ⟨fun {X Y} e hX => mem_of_iso (t.GE n) (S.ι.mapIso e) hX⟩
  LE_shift n a n' h X hX := mem_of_iso (t.LE n') ((S.ι.commShiftIso a).symm.app X)
    (t.LE_shift n a n' h (S.ι.obj X) hX)
  GE_shift n a n' h X hX := mem_of_iso (t.GE n') ((S.ι.commShiftIso a).symm.app X)
    (t.GE_shift n a n' h (S.ι.obj X) hX)
  zero' {X Y} f hX hY := S.ι.map_injective (by
    rw [Functor.map_zero]
    exact t.zero' (S.ι.map f) hX hY)
  LE_zero_le X hX := t.LE_zero_le _ hX
  GE_one_le X hX := t.GE_one_le _ hX
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, ⟨X', ⟨e⟩⟩, ⟨Y', ⟨e'⟩⟩⟩ :=
      h.exists_triangle_zero_one A.1 A.2
    refine' ⟨X', Y', mem_of_iso (t.LE 0) e.symm hX, mem_of_iso (t.GE 1) e'.symm hY,
      S.ι.preimage (e.hom ≫ f), S.ι.preimage (g ≫ e'.inv),
      S.ι.preimage (e'.hom ≫ h ≫ e.inv⟦(1 : ℤ)⟧' ≫ (S.ι.commShiftIso (1 : ℤ)).inv.app X'),
      isomorphic_distinguished _ hT _ _⟩
    refine' Triangle.isoMk _ _ e (Iso.refl _) e' _ _ _
    · dsimp
      simp
    · dsimp
      simp
    · dsimp
      simp only [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
        Category.comp_id, Iso.cancel_iso_hom_left, ← Functor.map_comp, Iso.inv_hom_id,
        Functor.map_id]

@[simp]
lemma mem_tStructure_heart_iff (X : S.category) :
    (S.tStructure t).heart X ↔ t.heart X.1 := by
  rfl

lemma tStructure_isLE_iff (X : S.category) (n : ℤ) :
    (S.tStructure t).IsLE X n ↔ t.IsLE (S.ι.obj X) n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

lemma tStructure_isGE_iff (X : S.category) (n : ℤ) :
    (S.tStructure t).IsGE X n ↔ t.IsGE (S.ι.obj X) n :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

end Subcategory

end Triangulated

end CategoryTheory


end FilteredTriangulated
