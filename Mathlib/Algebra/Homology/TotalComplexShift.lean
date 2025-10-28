/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Shift
import Mathlib.Algebra.Homology.TotalComplex

/-!
# Behaviour of the total complex with respect to shifts

There are two ways to shift objects in `HomologicalComplex₂ C (up ℤ) (up ℤ)`:
* by shifting the first indices (and changing signs of horizontal differentials),
  which corresponds to the shift by `ℤ` on `CochainComplex (CochainComplex C ℤ) ℤ`.
* by shifting the second indices (and changing signs of vertical differentials).

These two sorts of shift functors shall be abbreviated as
`HomologicalComplex₂.shiftFunctor₁ C x` and
`HomologicalComplex₂.shiftFunctor₂ C y`.

In this file, for any `K : HomologicalComplex₂ C (up ℤ) (up ℤ)`, we define an isomorphism
`K.totalShift₁Iso x : ((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧`
for any `x : ℤ` (which does not involve signs) and an isomorphism
`K.totalShift₂Iso y : ((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧`
for any `y : ℤ` (which is given by the multiplication by `(p * y).negOnePow` on the
summand in bidegree `(p, q)` of `K`).

Depending on the order of the "composition" of the two isomorphisms
`totalShift₁Iso` and `totalShift₂Iso`, we get
two ways to identify `((shiftFunctor₁ C x).obj ((shiftFunctor₂ C y).obj K)).total (up ℤ)`
and `(K.total (up ℤ))⟦x + y⟧`. The lemma `totalShift₁Iso_trans_totalShift₂Iso` shows that
these two compositions of isomorphisms differ by the sign `(x * y).negOnePow`.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape Limits

namespace HomologicalComplex₂

variable (C : Type*) [Category C] [Preadditive C]

/-- The shift on bicomplexes obtained by shifting the first indices (and changing the
sign of differentials). -/
abbrev shiftFunctor₁ (x : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  shiftFunctor _ x

/-- The shift on bicomplexes obtained by shifting the second indices (and changing the
sign of differentials). -/
abbrev shiftFunctor₂ (y : ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (shiftFunctor _ y).mapHomologicalComplex _

variable {C}
variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

/-- The isomorphism `(((shiftFunctor₁ C x).obj K).X a).X b ≅ (K.X a').X b` when `a' = a + x`. -/
def shiftFunctor₁XXIso (a x a' : ℤ) (h : a' = a + x) (b : ℤ) :
    (((shiftFunctor₁ C x).obj K).X a).X b ≅ (K.X a').X b := eqToIso (by subst h; rfl)

/-- The isomorphism `(((shiftFunctor₂ C y).obj K).X a).X b ≅ (K.X a).X b'` when `b' = b + y`. -/
def shiftFunctor₂XXIso (a b y b' : ℤ) (h : b' = b + y) :
    (((shiftFunctor₂ C y).obj K).X a).X b ≅ (K.X a).X b' := eqToIso (by subst h; rfl)

@[simp]
lemma shiftFunctor₁XXIso_refl (a b x : ℤ) :
    K.shiftFunctor₁XXIso a x (a + x) rfl b = Iso.refl _ := rfl

@[simp]
lemma shiftFunctor₂XXIso_refl (a b y : ℤ) :
    K.shiftFunctor₂XXIso a b y (b + y) rfl = Iso.refl _ := rfl

variable (x y : ℤ) [K.HasTotal (up ℤ)]

instance : ((shiftFunctor₁ C x).obj K).HasTotal (up ℤ) := fun n =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) (n + x)) _
    { toFun := fun ⟨⟨a, b⟩, h⟩ => ⟨⟨a + x, b⟩, by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        cutsat⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨(a - x, b), by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        cutsat⟩
      left_inv := by
        rintro ⟨⟨a, b⟩, h⟩
        ext
        · dsimp
          cutsat
        · rfl
      right_inv := by
        intro ⟨⟨a, b⟩, h⟩
        ext
        · dsimp
          cutsat
        · rfl }
    (fun _ => Iso.refl _)

instance : ((shiftFunctor₂ C y).obj K).HasTotal (up ℤ) := fun n =>
  hasCoproduct_of_equiv_of_iso (K.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) (n + y)) _
    { toFun := fun ⟨⟨a, b⟩, h⟩ => ⟨⟨a, b + y⟩, by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        cutsat⟩
      invFun := fun ⟨⟨a, b⟩, h⟩ => ⟨(a, b - y), by
        simp only [Set.mem_preimage, π_def, Set.mem_singleton_iff] at h ⊢
        cutsat⟩
      left_inv _ := by simp
      right_inv _ := by simp }
    (fun _ => Iso.refl _)

instance : ((shiftFunctor₂ C y ⋙ shiftFunctor₁ C x).obj K).HasTotal (up ℤ) := by
  dsimp
  infer_instance

instance : ((shiftFunctor₁ C x ⋙ shiftFunctor₂ C y).obj K).HasTotal (up ℤ) := by
  dsimp
  infer_instance

/-- Auxiliary definition for `totalShift₁Iso`. -/
noncomputable def totalShift₁XIso (n n' : ℤ) (h : n + x = n') :
    (((shiftFunctor₁ C x).obj K).total (up ℤ)).X n ≅ (K.total (up ℤ)).X n' where
  hom := totalDesc _ (fun p q hpq => K.ιTotal (up ℤ) (p + x) q n' (by dsimp at hpq ⊢; omega))
  inv := totalDesc _ (fun p q hpq =>
    (K.XXIsoOfEq _ _ _ (Int.sub_add_cancel p x) rfl).inv ≫
      ((shiftFunctor₁ C x).obj K).ιTotal (up ℤ) (p - x) q n
        (by dsimp at hpq ⊢; omega))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, CochainComplex.shiftFunctor_obj_X', ι_totalDesc, comp_id]
    exact ((shiftFunctor₁ C x).obj K).XXIsoOfEq_inv_ιTotal _ (by omega) rfl _ _
  inv_hom_id := by
    ext
    dsimp
    simp only [ι_totalDesc_assoc, Category.assoc, ι_totalDesc, XXIsoOfEq_inv_ιTotal, comp_id]

@[reassoc]
lemma D₁_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₁ (up ℤ) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₁ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₁_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, ι_D₁,
      ((shiftFunctor₁ C x).obj K).d₁_eq _ rfl _ _ (by dsimp; cutsat),
      K.d₁_eq _ (show p + x + 1 = p + 1 + x by cutsat) _ _ (by dsimp; cutsat)]
    dsimp
    rw [one_smul, Category.assoc, ι_totalDesc, one_smul, Linear.units_smul_comp]
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

@[reassoc]
lemma D₂_totalShift₁XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + x = n₀') (h₁ : n₁ + x = n₁') :
    ((shiftFunctor₁ C x).obj K).D₂ (up ℤ) n₀ n₁ ≫ (K.totalShift₁XIso x n₁ n₁' h₁).hom =
      x.negOnePow • ((K.totalShift₁XIso x n₀ n₀' h₀).hom ≫ K.D₂ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₁XIso]
    rw [ι_D₂_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, ι_D₂,
      ((shiftFunctor₁ C x).obj K).d₂_eq _ _ rfl _ (by dsimp; cutsat),
      K.d₂_eq _ _ rfl _ (by dsimp; cutsat), smul_smul,
      Linear.units_smul_comp, Category.assoc, ι_totalDesc]
    dsimp
    congr 1
    rw [add_comm p, Int.negOnePow_add, ← mul_assoc, Int.units_mul_self, one_mul]
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    grind [up_Rel]

/-- The isomorphism `((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧`
expressing the compatibility of the total complex with the shift on the first indices.
This isomorphism does not involve signs. -/
noncomputable def totalShift₁Iso :
    ((shiftFunctor₁ C x).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦x⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₁XIso x n (n + x) rfl)
    (fun n n' _ => by
      dsimp
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₁XIso_hom x n n' _ _ rfl rfl,
        K.D₂_totalShift₁XIso_hom x n n' _ _ rfl rfl])

@[reassoc]
lemma ι_totalShift₁Iso_hom_f (a b n : ℤ) (h : a + b = n) (a' : ℤ) (ha' : a' = a + x)
    (n' : ℤ) (hn' : n' = n + x) :
    ((shiftFunctor₁ C x).obj K).ιTotal (up ℤ) a b n h ≫ (K.totalShift₁Iso x).hom.f n =
      (K.shiftFunctor₁XXIso a x a' ha' b).hom ≫ K.ιTotal (up ℤ) a' b n' (by dsimp; cutsat) ≫
        (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) x n n' hn').inv := by
  subst ha' hn'
  dsimp [totalShift₁Iso, totalShift₁XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

@[reassoc]
lemma ι_totalShift₁Iso_inv_f (a b n : ℤ) (h : a + b = n) (a' n' : ℤ)
    (ha' : a' + b = n') (hn' : n' = n + x) :
    K.ιTotal (up ℤ) a' b n' ha' ≫
      (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) x n n' hn').inv ≫
        (K.totalShift₁Iso x).inv.f n =
      (K.shiftFunctor₁XXIso a x a' (by cutsat) b).inv ≫
        ((shiftFunctor₁ C x).obj K).ιTotal (up ℤ) a b n h := by
  subst hn'
  obtain rfl : a = a' - x := by cutsat
  dsimp [totalShift₁Iso, totalShift₁XIso, shiftFunctor₁XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

variable {K L} in
@[reassoc]
lemma totalShift₁Iso_hom_naturality [L.HasTotal (up ℤ)] :
    total.map ((shiftFunctor₁ C x).map f) (up ℤ) ≫ (L.totalShift₁Iso x).hom =
      (K.totalShift₁Iso x).hom ≫ (total.map f (up ℤ))⟦x⟧' := by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc, L.ι_totalShift₁Iso_hom_f x i₁ i₂ n h _ rfl _ rfl,
    K.ι_totalShift₁Iso_hom_f_assoc x i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp, id_comp, id_comp, comp_id, ιTotal_map]

/-- Auxiliary definition for `totalShift₂Iso`. -/
noncomputable def totalShift₂XIso (n n' : ℤ) (h : n + y = n') :
    (((shiftFunctor₂ C y).obj K).total (up ℤ)).X n ≅ (K.total (up ℤ)).X n' where
  hom := totalDesc _ (fun p q hpq => (p * y).negOnePow • K.ιTotal (up ℤ) p (q + y) n'
    (by dsimp at hpq ⊢; omega))
  inv := totalDesc _ (fun p q hpq => (p * y).negOnePow •
    (K.XXIsoOfEq _ _ _ rfl (Int.sub_add_cancel q y)).inv ≫
      ((shiftFunctor₂ C y).obj K).ιTotal (up ℤ) p (q - y) n (by dsimp at hpq ⊢; omega))
  hom_inv_id := by
    ext p q h
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, ι_totalDesc, smul_smul,
      Int.units_mul_self, one_smul, comp_id]
    exact ((shiftFunctor₂ C y).obj K).XXIsoOfEq_inv_ιTotal _ rfl (by omega) _ _
  inv_hom_id := by
    ext
    dsimp
    simp only [ι_totalDesc_assoc, Linear.units_smul_comp, Category.assoc, ι_totalDesc,
      Linear.comp_units_smul, XXIsoOfEq_inv_ιTotal, smul_smul, Int.units_mul_self, one_smul,
      comp_id]

@[reassoc]
lemma D₁_totalShift₂XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁') :
    ((shiftFunctor₂ C y).obj K).D₁ (up ℤ) n₀ n₁ ≫ (K.totalShift₂XIso y n₁ n₁' h₁).hom =
      y.negOnePow • ((K.totalShift₂XIso y n₀ n₀' h₀).hom ≫ K.D₁ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₁_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, Linear.units_smul_comp,
      ι_D₁, smul_smul, ((shiftFunctor₂ C y).obj K).d₁_eq _ rfl _ _ (by dsimp; cutsat),
      K.d₁_eq _ rfl _ _ (by dsimp; cutsat)]
    dsimp
    rw [one_smul, one_smul, Category.assoc, ι_totalDesc, Linear.comp_units_smul,
      ← Int.negOnePow_add]
    congr 2
    linarith
  · rw [D₁_shape _ _ _ _ h, zero_comp, D₁_shape, comp_zero, smul_zero]
    grind [up_Rel]

@[reassoc]
lemma D₂_totalShift₂XIso_hom (n₀ n₁ n₀' n₁' : ℤ) (h₀ : n₀ + y = n₀') (h₁ : n₁ + y = n₁') :
    ((shiftFunctor₂ C y).obj K).D₂ (up ℤ) n₀ n₁ ≫ (K.totalShift₂XIso y n₁ n₁' h₁).hom =
      y.negOnePow • ((K.totalShift₂XIso y n₀ n₀' h₀).hom ≫ K.D₂ (up ℤ) n₀' n₁') := by
  by_cases h : (up ℤ).Rel n₀ n₁
  · apply total.hom_ext
    intro p q hpq
    dsimp at h hpq
    dsimp [totalShift₂XIso]
    rw [ι_D₂_assoc, Linear.comp_units_smul, ι_totalDesc_assoc, Linear.units_smul_comp,
      smul_smul, ι_D₂, ((shiftFunctor₂ C y).obj K).d₂_eq _ _ rfl _ (by dsimp; cutsat),
      K.d₂_eq _ _ (show q + y + 1 = q + 1 + y by cutsat) _ (by dsimp; cutsat),
      Linear.units_smul_comp, Category.assoc, smul_smul, ι_totalDesc]
    dsimp
    rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, smul_smul,
      ← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add,
      ← Int.negOnePow_add]
    congr 2
    cutsat
  · rw [D₂_shape _ _ _ _ h, zero_comp, D₂_shape, comp_zero, smul_zero]
    simp_all only [up_Rel]
    grind

/-- The isomorphism `((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧`
expressing the compatibility of the total complex with the shift on the second indices.
This isomorphism involves signs: on the summand in degree `(p, q)` of `K`, it is given by the
multiplication by `(p * y).negOnePow`. -/
noncomputable def totalShift₂Iso :
    ((shiftFunctor₂ C y).obj K).total (up ℤ) ≅ (K.total (up ℤ))⟦y⟧ :=
  HomologicalComplex.Hom.isoOfComponents (fun n => K.totalShift₂XIso y n (n + y) rfl)
    (fun n n' _ => by
      dsimp
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, smul_add,
        Linear.comp_units_smul, K.D₁_totalShift₂XIso_hom y n n' _ _ rfl rfl,
        K.D₂_totalShift₂XIso_hom y n n' _ _ rfl rfl])

@[reassoc]
lemma ι_totalShift₂Iso_hom_f (a b n : ℤ) (h : a + b = n) (b' : ℤ) (hb' : b' = b + y)
    (n' : ℤ) (hn' : n' = n + y) :
    ((shiftFunctor₂ C y).obj K).ιTotal (up ℤ) a b n h ≫ (K.totalShift₂Iso y).hom.f n =
      (a * y).negOnePow • (K.shiftFunctor₂XXIso a b y b' hb').hom ≫
        K.ιTotal (up ℤ) a b' n' (by dsimp; cutsat) ≫
          (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) y n n' hn').inv := by
  subst hb' hn'
  dsimp [totalShift₂Iso, totalShift₂XIso]
  simp only [ι_totalDesc, comp_id, id_comp]

@[reassoc]
lemma ι_totalShift₂Iso_inv_f (a b n : ℤ) (h : a + b = n) (b' n' : ℤ)
    (hb' : a + b' = n') (hn' : n' = n + y) :
    K.ιTotal (up ℤ) a b' n' hb' ≫
      (CochainComplex.shiftFunctorObjXIso (K.total (up ℤ)) y n n' hn').inv ≫
        (K.totalShift₂Iso y).inv.f n =
      (a * y).negOnePow • (K.shiftFunctor₂XXIso a b y b' (by cutsat)).inv ≫
        ((shiftFunctor₂ C y).obj K).ιTotal (up ℤ) a b n h := by
  subst hn'
  obtain rfl : b = b' - y := by cutsat
  dsimp [totalShift₂Iso, totalShift₂XIso, shiftFunctor₂XXIso, XXIsoOfEq]
  simp only [id_comp, ι_totalDesc]

variable {K L} in
@[reassoc]
lemma totalShift₂Iso_hom_naturality [L.HasTotal (up ℤ)] :
    total.map ((shiftFunctor₂ C y).map f) (up ℤ) ≫ (L.totalShift₂Iso y).hom =
      (K.totalShift₂Iso y).hom ≫ (total.map f (up ℤ))⟦y⟧' := by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc, L.ι_totalShift₂Iso_hom_f y i₁ i₂ n h _ rfl _ rfl,
    K.ι_totalShift₂Iso_hom_f_assoc y i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp, id_comp, comp_id, comp_id, Linear.comp_units_smul,
    Linear.units_smul_comp, ιTotal_map]

variable (C) in
/-- The shift functors `shiftFunctor₁ C x` and `shiftFunctor₂ C y` on bicomplexes
with respect to both variables commute. -/
def shiftFunctor₁₂CommIso (x y : ℤ) :
    shiftFunctor₂ C y ⋙ shiftFunctor₁ C x ≅ shiftFunctor₁ C x ⋙ shiftFunctor₂ C y :=
  Iso.refl _

/-- The compatibility isomorphisms of the total complex with the shifts
in both variables "commute" only up to a sign `(x * y).negOnePow`. -/
lemma totalShift₁Iso_trans_totalShift₂Iso :
    ((shiftFunctor₂ C y).obj K).totalShift₁Iso x ≪≫
      (shiftFunctor (CochainComplex C ℤ) x).mapIso (K.totalShift₂Iso y) =
    (x * y).negOnePow • (total.mapIso ((shiftFunctor₁₂CommIso C x y).app K) (up ℤ)) ≪≫
      ((shiftFunctor₁ C x).obj K).totalShift₂Iso y ≪≫
      (shiftFunctor _ y).mapIso (K.totalShift₁Iso x) ≪≫
      (shiftFunctorComm (CochainComplex C ℤ) x y).app _ := by
  ext n n₁ n₂ h
  dsimp at h ⊢
  rw [Linear.comp_units_smul,ι_totalShift₁Iso_hom_f_assoc _ x n₁ n₂ n h _ rfl _ rfl,
    ιTotal_map_assoc, ι_totalShift₂Iso_hom_f_assoc _ y n₁ n₂ n h _ rfl _ rfl,
    Linear.units_smul_comp, Linear.comp_units_smul]
  dsimp [shiftFunctor₁₂CommIso]
  rw [id_comp, id_comp, id_comp, id_comp, comp_id,
    ι_totalShift₂Iso_hom_f _ y (n₁ + x) n₂ (n + x) (by cutsat) _ rfl _ rfl, smul_smul,
    ← Int.negOnePow_add, add_mul, add_comm (x * y)]
  dsimp
  rw [id_comp, comp_id,
    ι_totalShift₁Iso_hom_f_assoc _ x n₁ (n₂ + y) (n + y) (by cutsat) _ rfl (n + x + y) (by cutsat),
    CochainComplex.shiftFunctorComm_hom_app_f]
  dsimp
  rw [Iso.inv_hom_id, comp_id, id_comp]

/-- The compatibility isomorphisms of the total complex with the shifts
in both variables "commute" only up to a sign `(x * y).negOnePow`. -/
@[reassoc]
lemma totalShift₁Iso_hom_totalShift₂Iso_hom :
    (((shiftFunctor₂ C y).obj K).totalShift₁Iso x).hom ≫ (K.totalShift₂Iso y).hom⟦x⟧' =
      (x * y).negOnePow • (total.map ((shiftFunctor₁₂CommIso C x y).hom.app K) (up ℤ) ≫
          (((shiftFunctor₁ C x).obj K).totalShift₂Iso y).hom ≫
          (K.totalShift₁Iso x).hom⟦y⟧' ≫
          (shiftFunctorComm (CochainComplex C ℤ) x y).hom.app _) :=
  congr_arg Iso.hom (totalShift₁Iso_trans_totalShift₂Iso K x y)

end HomologicalComplex₂
