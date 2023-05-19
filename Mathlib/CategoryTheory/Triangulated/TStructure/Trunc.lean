import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject

namespace Triangulated

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

namespace TStructure

lemma triangle_map_ext' (a b : ℤ) (hab : a ≤ b) {T T' : Triangle C} (f₁ f₂ : T ⟶ T')
    (hT : T ∈ distTriang C) (hT' : T' ∈ distTriang C)
    (h₀ : T.obj₁ ∈ t.setLE a)
    (h₁' : T'.obj₃ ∈ t.setGE b)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ := by
  suffices ∀ (f : T ⟶ T') (_ : f.hom₂ = 0), f = 0 by
    rw [← sub_eq_zero]
    apply this
    dsimp
    rw [H, sub_self]
  intro f hf
  ext
  . obtain ⟨g, hg⟩ := covariant_yoneda_exact₂ _ (inv_rot_of_dist_triangle _ hT') f.hom₁ (by
      have eq := f.comm₁
      dsimp at eq ⊢
      rw [← eq, hf, comp_zero])
    have hg' : g = 0 := t.zero g a (b+1) (by linarith) h₀
      (t.shift_mem_setGE b (-1) (b+1) (by linarith) _ h₁')
    rw [instAddCommGroupTriangleHom_zero_hom₁, hg, hg', zero_comp]
  . rw [hf, instAddCommGroupTriangleHom_zero_hom₂]
  . obtain ⟨g, hg⟩ := contravariant_yoneda_exact₃ _ hT f.hom₃ (by rw [f.comm₂, hf, zero_comp])
    have hg' : g = 0 := t.zero g (a-1) b (by linarith)
      (t.shift_mem_setLE a 1 (a-1) (by linarith) _ h₀) h₁'
    rw [instAddCommGroupTriangleHom_zero_hom₃, hg, hg', comp_zero]

namespace TruncAux

variable (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (A : C)

noncomputable def triangle : Triangle C :=
  Triangle.mk
    (t.exists_triangle A n₀ n₁ h).choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle A n₀ n₁
      h).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    (t.exists_triangle A n₀ n₁
      h).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose

lemma triangle_distinguished :
    triangle t n₀ n₁ h A ∈ distTriang C :=
  (t.exists_triangle A n₀ n₁
      h).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

lemma triangle_obj₁_mem_setLE :
    (triangle t n₀ n₁ h A).obj₁ ∈ t.setLE n₀ :=
  (t.exists_triangle A n₀ n₁ h).choose_spec.choose_spec.choose

@[simp]
lemma triangle_obj₂ :
    (triangle t n₀ n₁ h A).obj₂ = A := by rfl

lemma triangle_obj₃_mem_setGE :
    (triangle t n₀ n₁ h A).obj₃ ∈ t.setGE n₁ :=
  (t.exists_triangle A n₀ n₁ h).choose_spec.choose_spec.choose_spec.choose

variable {A}
variable {B : C} (φ : A ⟶ B)

lemma triangle_map_ext (f₁ f₂ : triangle t n₀ n₁ h A ⟶ triangle t n₀ n₁ h B)
    (H : f₁.hom₂ = f₂.hom₂) : f₁ = f₂ :=
  triangle_map_ext' t n₀ n₁ (by linarith) _ _
    (triangle_distinguished t n₀ n₁ h A) (triangle_distinguished t n₀ n₁ h B)
    (triangle_obj₁_mem_setLE _ _ _ _ _) (triangle_obj₃_mem_setGE _ _ _ _ _) H

-- TODO: generalize this lemma
lemma triangle_map_exists : ∃ (a : (triangle t n₀ n₁ h A).obj₁ ⟶ (triangle t n₀ n₁ h B).obj₁)
    (c : (triangle t n₀ n₁ h A).obj₃ ⟶ (triangle t n₀ n₁ h B).obj₃)
    (_ : (triangle t n₀ n₁ h A).mor₁ ≫ φ = a ≫ (triangle t n₀ n₁ h B).mor₁)
    (_ : (triangle t n₀ n₁ h A).mor₂ ≫ c = φ ≫ (triangle t n₀ n₁ h B).mor₂),
      (triangle t n₀ n₁ h A).mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ (triangle t n₀ n₁ h B).mor₃ := by
  obtain ⟨a, comm₁⟩  := covariant_yoneda_exact₂ _ (triangle_distinguished t n₀ n₁ h B)
    ((triangle t n₀ n₁ h A).mor₁ ≫ φ) (t.zero _ n₀ n₁ (by linarith)
      (triangle_obj₁_mem_setLE _ _ _ _ _) (triangle_obj₃_mem_setGE _ _ _ _ _))
  obtain ⟨c, ⟨comm₂, comm₃⟩⟩ :=
    complete_distinguished_triangle_morphism _ _ (triangle_distinguished t n₀ n₁ h A)
      (triangle_distinguished t n₀ n₁ h B) a φ comm₁
  exact ⟨a, c, comm₁, comm₂, comm₃⟩

noncomputable def triangle_map : triangle t n₀ n₁ h A ⟶ triangle t n₀ n₁ h B where
  hom₁ := (triangle_map_exists t n₀ n₁ h φ).choose
  hom₂ := φ
  hom₃ := (triangle_map_exists t n₀ n₁ h φ).choose_spec.choose
  comm₁ := (triangle_map_exists t n₀ n₁ h φ).choose_spec.choose_spec.choose
  comm₂ := (triangle_map_exists t n₀ n₁ h φ).choose_spec.choose_spec.choose_spec.choose
  comm₃ := (triangle_map_exists t n₀ n₁ h φ).choose_spec.choose_spec.choose_spec.choose_spec

noncomputable def triangleFunctor : C ⥤ Triangle C where
  obj := triangle t n₀ n₁ h
  map φ := triangle_map t n₀ n₁ h φ
  map_id _ := triangle_map_ext t n₀ n₁ h _ _ rfl
  map_comp _ _ := triangle_map_ext t n₀ n₁ h _ _ rfl

lemma triangleFunctor_obj_distinguished (A : C) :
  (triangleFunctor t n₀ n₁ h).obj A ∈ distTriang C :=
    triangle_distinguished t n₀ n₁ h A

variable (A)

@[simp]
lemma triangleFunctor_obj_obj₂ : ((triangleFunctor t n₀ n₁ h).obj A).obj₂ = A := rfl

variable {A}

@[simp]
lemma triangleFunctor_map_hom₂ : ((triangleFunctor t n₀ n₁ h).map φ).hom₂ = φ := rfl

lemma triangleFunctor_obj_obj₁_mem_setLE :
  ((triangleFunctor t n₀ n₁ h).obj A).obj₁ ∈ t.setLE n₀ :=
    triangle_obj₁_mem_setLE _ _ _ h _

lemma triangleFunctor_obj_obj₃_mem_setGE :
  ((triangleFunctor t n₀ n₁ h).obj A).obj₃ ∈ t.setGE n₁ :=
    triangle_obj₃_mem_setGE _ _ _ h _

noncomputable def congrTriangleFunctor (n₀ n₁ n₀' n₁' : ℤ) (h : n₀ + 1 = n₁) (h' : n₀' + 1 = n₁')
  (eq : n₀ = n₀') :
    triangleFunctor t n₀ n₁ h ≅ triangleFunctor t n₀' n₁' h' := eqToIso (by
  subst eq
  obtain rfl : n₁ = n₁' := by linarith
  rfl)

end TruncAux

class IsLE (X : C) (n : ℤ) : Prop where
  mem : X ∈ t.setLE n

lemma mem_of_isLE (X : C) (n : ℤ) [t.IsLE X n] : X ∈ t.setLE n := IsLE.mem

class IsGE (X : C) (n : ℤ) : Prop where
  mem : X ∈ t.setGE n

lemma mem_of_isGE (X : C) (n : ℤ) [t.IsGE X n] : X ∈ t.setGE n := IsGE.mem

lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsLE X n] : t.IsLE Y n where
  mem := (t.setLE n).mem_of_iso e (t.mem_of_isLE X n)

lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsGE X n] : t.IsGE Y n where
  mem := (t.setGE n).mem_of_iso e (t.mem_of_isGE X n)

lemma isLE_of_LE (X : C) (p q : ℤ) (hpq : p ≤ q) [t.IsLE X p] : t.IsLE X q where
  mem := setLE_monotone t p q hpq (t.mem_of_isLE X p)

lemma isGE_of_GE (X : C) (p q : ℤ) (hpq : p ≤ q) [t.IsGE X q] : t.IsGE X p where
  mem := setGE_antitone t p q hpq (t.mem_of_isGE X q)

noncomputable def truncLE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t n (n+1) rfl ⋙ Triangle.π₁

noncomputable def truncLEι (n : ℤ) : t.truncLE n ⟶ 𝟭 _ :=
  whiskerLeft (TruncAux.triangleFunctor t n (n+1) rfl) Triangle.π₁Toπ₂

noncomputable def truncGE (n : ℤ) : C ⥤ C :=
  TruncAux.triangleFunctor t (n-1) n (by linarith) ⋙ Triangle.π₃

noncomputable def truncGEπ (n : ℤ) : 𝟭 _ ⟶ t.truncGE n  :=
  whiskerLeft (TruncAux.triangleFunctor t (n-1) n (by linarith)) Triangle.π₂Toπ₃

instance (X : C) (n : ℤ) : t.IsLE ((t.truncLE n).obj X) n where
  mem := TruncAux.triangle_obj₁_mem_setLE _ _ _ rfl _

instance (X : C) (n : ℤ) : t.IsGE ((t.truncGE n).obj X) n where
  mem := TruncAux.triangle_obj₃_mem_setGE _ _ _ (by linarith) _

noncomputable def truncδ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
  t.truncGE n₁ ⟶ t.truncLE n₀ ⋙ shiftFunctor C (1 : ℤ) := by
    refine' _ ≫ whiskerLeft (TruncAux.triangleFunctor t n₀ (n₀+1) rfl) Triangle.π₃Toπ₁
    dsimp only [truncGE]
    exact whiskerRight (((TruncAux.congrTriangleFunctor t (n₁ - 1) n₁ n₀ (n₀ + 1)
      (by linarith) rfl (by linarith))).hom) Triangle.π₃

@[simps]
noncomputable def truncTriangle (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : C ⥤ Triangle C where
  obj X := Triangle.mk ((t.truncLEι n₀).app X) ((t.truncGEπ n₁).app X) ((t.truncδ n₀ n₁ h).app X)
  map φ :=
    { hom₁ := (t.truncLE n₀).map φ
      hom₂ := φ
      hom₃ := (t.truncGE n₁).map φ
      comm₂ := by
        dsimp
        erw [← NatTrans.naturality, Functor.id_map] }

set_option maxHeartbeats 400000 in
def truncTriangle_obj_distinguished (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (X : C) :
    (truncTriangle t n₀ n₁ h).obj X ∈ distTriang C := by
  let e := TruncAux.congrTriangleFunctor t (n₁ - 1) n₁ n₀ (n₀ + 1) (by linarith) rfl (by linarith)
  refine' isomorphic_distinguished _ (TruncAux.triangleFunctor_obj_distinguished t (n₁-1) n₁ (by linarith) X) _ _
  refine' Triangle.isoMk _ _ (Triangle.π₁.mapIso (e.app X).symm) (Iso.refl _) (Iso.refl _) _ _ _
  . dsimp [truncLEι]
    rw [comp_id, ← (e.inv.app X).comm₁]
    dsimp [TruncAux.congrTriangleFunctor]
    simp only [eqToHom_app, Triangle.eqToHom_hom₂, eqToHom_refl,
      TruncAux.triangleFunctor_obj_obj₂, comp_id]
  . dsimp [truncGEπ]
    rw [comp_id, id_comp]
  . dsimp
    dsimp only [truncδ]
    simp only [NatTrans.comp_app]
    dsimp only [whiskerRight, whiskerLeft, id, Triangle.π₃, Triangle.π₃Toπ₁]
    rw [id_comp, assoc, (e.inv.app X).comm₃, ← comp_hom₃_assoc,
      e.hom_inv_id_app, id_hom₃, id_comp]

attribute [irreducible] truncLE truncGE truncLEι truncGEπ truncδ

/-lemma isLE_iff_isIso_truncLEι_app (X : C) (n : ℤ) :
    t.IsLE X n ↔ IsIso ((t.truncLEι n).app X) := by
  constructor
  . intro h
    refine' (isIso₁_iff _ (t.truncTriangle_obj_distinguished n (n+1) rfl X)).2 ⟨_, _⟩
    . sorry
    . sorry
  . intro
    exact t.isLE_of_iso (asIso ((truncLEι t n).app X)) n-/

/-def plus : Triangulated.Subcategory C where
  set X := ∃ (n : ℤ), X ∈ t.setGE n
  zero := ⟨0, by sorry⟩
  shift := by
    rintro X n ⟨i, hX⟩
    exact ⟨i - n, t.shift_mem_setGE i n (i - n) (by linarith) X hX⟩
  ext₂ := sorry -/

end TStructure

end Triangulated

end CategoryTheory
