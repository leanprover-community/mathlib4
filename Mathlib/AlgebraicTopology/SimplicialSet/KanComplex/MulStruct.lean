/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Pointed simplices

Given a simplicial set `X`, `n : ℕ` and `x : X _⦋0⦌`, we introduce the
type `X.PtSimplex n x` of morphisms `Δ[n] ⟶ X` which send `∂Δ[n]` to `x`.
We introduce structures `PtSimplex.RelStruct` and `PtSimplex.MulStruct`
which will be used in the definition of homotopy groups of Kan complexes.

-/

@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial Limits

namespace SSet

namespace stdSimplex

lemma face_pair_compl_le₁ {n : ℕ} (i j : Fin (n + 1)) : face {i, j}ᶜ ≤ face {i}ᶜ := by
  simp [face_le_face_iff]

lemma face_pair_compl_le₂ {n : ℕ} (i j : Fin (n + 1)) : face {i, j}ᶜ ≤ face {j}ᶜ := by
  simp [face_le_face_iff]

@[simps! apply]
noncomputable def _root_.Finset.orderIsoOfOrderEmbedding
    {α β : Type*} [Preorder α] [Preorder β] [DecidableEq β] [Fintype α]
    (f : α ↪o β) (S : Finset β) (hS : Finset.image f ⊤ = S) : α ≃o S where
  toEquiv := Equiv.ofBijective (f := fun a ↦ ⟨f a, by simp [← hS]⟩)
    ⟨fun _ _ _ ↦ by aesop, fun _ ↦ by aesop⟩
  map_rel_iff' := by simp

noncomputable def _root_.Fin.orderIsoPairCompl {n : ℕ} (i j : Fin (n + 2)) (h : i < j) :
    Fin n ≃o ({i, j}ᶜ : Finset _) :=
  let φ :=
    (Fin.succAboveOrderEmb (i.castPred (Fin.ne_last_of_lt h))).trans
      (Fin.succAboveOrderEmb j)
  Finset.orderIsoOfOrderEmbedding φ _ (by
    refine Finset.eq_of_subset_of_card_le (fun k hk ↦ ?_) ?_
    · simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at hk
      obtain ⟨k, rfl⟩ := hk
      obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
      dsimp [φ]
      simp only [Finset.compl_insert, Finset.mem_erase, ne_eq, Finset.mem_compl,
        Finset.mem_singleton, Fin.succAbove_ne, not_false_eq_true, and_true]
      grind [Fin.succAbove]
    · rw [Finset.card_image_of_injective _ φ.injective,
        Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
        ← Nat.add_le_add_iff_right (n := Finset.card {i, j}),
        Finset.card_compl_add_card, Finset.card_pair h.ne, Fintype.card_fin])

noncomputable def facePairComplIso {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    Δ[n] ≅ (face {i, j}ᶜ : SSet.{u}) :=
  isoOfRepresentableBy (faceRepresentableBy _ _ (Fin.orderIsoPairCompl i j h))

@[reassoc]
lemma facePairComplIso_hom_ι {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    (facePairComplIso.{u} i j h).hom ≫ (face {i, j}ᶜ).ι =
      stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) ≫ stdSimplex.δ j :=
  rfl

@[reassoc]
lemma facePairComplIso_hom_ι' {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    (facePairComplIso.{u} i j h).hom ≫ (face {i, j}ᶜ).ι =
      stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) ≫ stdSimplex.δ i := by
  rw [facePairComplIso_hom_ι]
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  dsimp
  rw [Fin.pred_succ, stdSimplex.δ_comp_δ (by grind)]

@[reassoc]
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_pred {n : ℕ}
    (i j : Fin (n + 3)) (h : i < j) :
    Subcomplex.homOfLE (face_pair_compl_le₁ i j) ≫
      (faceSingletonComplIso.{u} i).inv =
        (facePairComplIso i j h).inv ≫ stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) := by
  rw [← cancel_mono (faceSingletonComplIso i).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom]
  simp [facePairComplIso_hom_ι']

@[reassoc]
lemma homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_castPred
    {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    Subcomplex.homOfLE (face_pair_compl_le₂ i j) ≫
      (faceSingletonComplIso.{u} j).inv =
        (facePairComplIso i j h).inv ≫
          stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) := by
  rw [← cancel_mono (faceSingletonComplIso j).hom,
    ← cancel_mono (Subcomplex.ι _), ← cancel_epi (facePairComplIso i j h).hom]
  simp [facePairComplIso_hom_ι]

end stdSimplex

namespace horn

variable {X : SSet.{u}} {n : ℕ}

protected def IsCompatible
    {i : Fin (n + 2)} (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet) ⟶ X) : Prop := by
  match n with
  | 0 => exact True
  | n + 1 => exact ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk

@[simp]
lemma isCompatible_iff_true {i : Fin 2} (f : ∀ (j : Fin 2) (_ : j ≠ i), (Δ[0] : SSet) ⟶ X) :
    horn.IsCompatible f ↔ True := Iff.rfl

@[simp]
lemma isCompatible_iff
    {i : Fin (n + 3)} (f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet) ⟶ X) :
    horn.IsCompatible f ↔
    ∀ (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk := Iff.rfl

namespace IsCompatible
variable {X : SSet.{u}} {n : ℕ}

lemma δ_pred_comp {i : Fin (n + 3)} {f : ∀ (j : Fin (n + 3)) (_ : j ≠ i), (Δ[n + 1] : SSet) ⟶ X}
    (hf : horn.IsCompatible f)
    (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i) (hjk : j < k) :
    stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
    stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk :=
  hf j k hj hk hjk

variable {i : Fin (n + 2)} {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet) ⟶ X}

open stdSimplex in
def multicofork (hf : horn.IsCompatible f) :
    Multicofork ((multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
      (Subcomplex.toSSetFunctor)) :=
  Multicofork.ofπ _ X (fun ⟨j, hj⟩ ↦ (stdSimplex.faceSingletonComplIso j).inv ≫ f j hj) (by
    obtain _ | n := n
    · rintro ⟨⟨a, b⟩, hab⟩
      grind
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab : a < b⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha hb
      dsimp
      rw [homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_pred_assoc _ _ hab,
        homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_castPred_assoc _ _ hab,
        hf.δ_pred_comp _ _ _ _ hab])

lemma exists_desc (hf : horn.IsCompatible f) :
    ∃ (φ : (Λ[n + 1, i] : SSet) ⟶ X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), horn.ι i j hj ≫ φ = f j hj :=
  ⟨(horn.isColimit.{u} i).desc hf.multicofork, fun j hj ↦ by
    rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).inv]
    simpa using (horn.isColimit.{u} i).fac hf.multicofork (.right ⟨j, hj⟩)⟩

@[no_expose]
noncomputable def desc (hf : horn.IsCompatible f) :
    (Λ[n + 1, i] : SSet) ⟶ X :=
  hf.exists_desc.choose

@[reassoc (attr := simp)]
lemma ι_desc (hf : horn.IsCompatible f) (j : Fin (n + 2))
    (hj : j ≠ i) :
    horn.ι i j hj ≫ hf.desc = f j hj :=
  hf.exists_desc.choose_spec j hj

open modelCategoryQuillen in
lemma exists_lift (hf : horn.IsCompatible f) {Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
    (b : Δ[n + 1] ⟶ Y)
    (comm : ∀ (j : Fin (n + 2)) (hj : j ≠ i), f j hj ≫ p = stdSimplex.δ j ≫ b) :
    ∃ (φ : Δ[n + 1] ⟶ X),
      (∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj) ∧
      φ ≫ p = b := by
  have sq : CommSq hf.desc Λ[n + 1, i].ι p b :=
    ⟨horn.hom_ext' (fun j hj ↦ by simpa using comm j hj)⟩
  refine ⟨sq.lift, fun j hj ↦ by simp [← ι_ι_assoc i j hj], by simp⟩

lemma exists_lift_of_kanComplex [KanComplex X]
    (hf : horn.IsCompatible f) :
    ∃ (φ : Δ[n + 1] ⟶ X),
      ∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ φ = f j hj := by
  obtain ⟨φ, hφ, _⟩ := hf.exists_lift (terminal.from _) (terminal.from _) (by simp)
  exact ⟨φ, hφ⟩

@[no_expose]
noncomputable def lift [KanComplex X] (hf : horn.IsCompatible f) :
    Δ[n + 1] ⟶ X :=
  hf.exists_lift_of_kanComplex.choose

@[reassoc]
lemma δ_lift [KanComplex X] (hf : horn.IsCompatible f)
    (j : Fin (n + 2)) (hj : j ≠ i := by grind) :
    stdSimplex.δ j ≫ hf.lift = f j hj :=
  hf.exists_lift_of_kanComplex.choose_spec j hj

end IsCompatible

end horn

variable (X : SSet.{u})

/-- Given a simplicial set `X`, `n : ℕ` and `x : X _⦋0⦌`, this is the type
of morphisms `Δ[n] ⟶ X` which are constant with value `x` on the boundary. -/
abbrev PtSimplex (n : ℕ) (x : X _⦋0⦌) : Type u :=
  RelativeMorphism (boundary n) (Subcomplex.ofSimplex x)
    (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)

namespace PtSimplex

variable {X} {n : ℕ} {x : X _⦋0⦌}

@[reassoc]
lemma comp_map_eq_const
    (s : X.PtSimplex n x) {Y : SSet.{u}} (φ : Y ⟶ Δ[n]) [Y.HasDimensionLT n] :
    φ ≫ s.map = const x := by
  refine (Subcomplex.lift φ ?_) ≫= s.comm
  rw [stdSimplex.le_boundary_iff]
  intro h
  have : IsIso (Subcomplex.range φ).ι := by rw [h]; infer_instance
  exact stdSimplex.not_hasDimensionLT n
    ((hasDimensionLT_iff_of_iso (asIso (Subcomplex.range φ).ι) n).mp inferInstance)

@[reassoc (attr := simp)]
lemma δ_map (f : X.PtSimplex (n + 1) x) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ f.map = const x :=
  comp_map_eq_const _ _

/-- For each `i : Fin (n + 1)`, this is a variant of the homotopy relation on
`n`-simplices that are constant on the boundary. Simplices `f` and `g` are related
if they appear respectively as the `i.castSucc` and `i.succ` faces of a
`n + 1`-simplex such that all the other faces are constant. -/
structure RelStruct (f g : X.PtSimplex n x) (i : Fin (n + 1)) where
  /-- A `n + 1`-simplex -/
  map : Δ[n + 1] ⟶ X
  δ_castSucc_map : stdSimplex.δ i.castSucc ≫ map = f.map := by cat_disch
  δ_succ_map : stdSimplex.δ i.succ ≫ map = g.map := by cat_disch
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc) :
    stdSimplex.δ j ≫ map = const x := by cat_disch
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ < j) :
    stdSimplex.δ j ≫ map = const x := by cat_disch

namespace RelStruct

attribute [reassoc (attr := simp)] δ_castSucc_map δ_succ_map
  δ_map_of_lt δ_map_of_gt

/-- `RelStruct` is reflexive. -/
@[simps]
def refl (f : X.PtSimplex n x) (i : Fin (n + 1)) : RelStruct f f i where
  map := stdSimplex.σ i ≫ f.map
  δ_castSucc_map := by rw [CosimplicialObject.δ_comp_σ_self_assoc]
  δ_succ_map := by rw [CosimplicialObject.δ_comp_σ_succ_assoc]
  δ_map_of_lt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_succ_of_ne_zero (by aesop)
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (by grind)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_le_assoc (by grind), δ_map, comp_const]
  δ_map_of_gt j hj := by
    obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by grind)
    obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by aesop)
    obtain _ | n := n
    · fin_cases i
    · rw [stdSimplex.δ_comp_σ_of_gt_assoc (by grind), δ_map, comp_const]

/-- The `RelStruct f' g' i` deduced from `r : RelStruct f g i` when
`f = f'` and `g = g'`. -/
@[simps]
def copy {f g : X.PtSimplex n x} {i : Fin (n + 1)} (r : RelStruct f g i)
    {f' g' : X.PtSimplex n x} (hf : f = f') (hg : g = g') :
    RelStruct f' g' i where
  map := r.map
  δ_castSucc_map := by rw [δ_castSucc_map, hf]
  δ_succ_map := by rw [δ_succ_map, hg]
  δ_map_of_lt j hj := by rw [δ_map_of_lt _ j hj]
  δ_map_of_gt j hj := by rw [δ_map_of_gt _ j hj]

/-- The `RelStruct f g i` deduced from an equality `f = g`. -/
@[simps! map]
def ofEq {f g : X.PtSimplex n x} (h : f = g) (i : Fin (n + 1)) :
    RelStruct f g i :=
  (refl f i).copy rfl h

end RelStruct

/-- For each `i : Fin n`, this structure is a candidate for the relation saying
that `fg` is the product of `f` and `g` in the homotopy group (of a Kan complex).
It is so if `g`, `fg` and `f` are respectively the `i.castSucc.castSucc`,
`i.castSucc.succ` and `i.succ.succ` faces of a `n + 1`-simplex such that
all the other faces are constant. (The multiplication on homotopy groups will be
defined using `i := Fin.last _`, but in general, this structure is useful in
order to obtain properties of `RelStruct`.) -/
structure MulStruct (f g fg : X.PtSimplex n x) (i : Fin n) where
  /-- A `n + 1`-simplex -/
  map : Δ[n + 1] ⟶ X
  δ_castSucc_castSucc_map : stdSimplex.δ (i.castSucc.castSucc) ≫ map = g.map := by cat_disch
  δ_succ_castSucc_map : stdSimplex.δ (i.castSucc.succ) ≫ map = fg.map := by cat_disch
  δ_succ_succ_map : stdSimplex.δ (i.succ.succ) ≫ map = f.map := by cat_disch
  δ_map_of_lt (j : Fin (n + 2)) (hj : j < i.castSucc.castSucc) :
    stdSimplex.δ j ≫ map = const x := by cat_disch
  δ_map_of_gt (j : Fin (n + 2)) (hj : i.succ.succ < j) :
    stdSimplex.δ j ≫ map = const x := by cat_disch

namespace MulStruct

attribute [reassoc (attr := simp)] δ_castSucc_castSucc_map δ_succ_castSucc_map δ_succ_succ_map
  δ_map_of_lt δ_map_of_gt

end MulStruct

/-- If `f` and `g` are in `X.PtSimplex n x`, then `RelStruct f g i.castSucc`
identifies to `MulStruct .const f g i`. -/
@[simps apply_map symm_apply_map]
def relStructCastSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} :
    RelStruct f g i.castSucc ≃ MulStruct .const f g i where
  toFun h :=
    { map := h.map
      δ_map_of_gt j hj := h.δ_map_of_gt j (lt_trans (by simp) hj) }
  invFun h :=
    { map := h.map
      δ_map_of_gt j hj := by
        rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hj
        obtain rfl | hj := hj.eq_or_lt
        · exact h.δ_succ_succ_map
        · exact h.δ_map_of_gt j hj }

/-- If `f` and `g` are in `X.PtSimplex n x`, then `RelStruct f g i.succ`
identifies to `MulStruct g .const f i`. -/
@[simps apply_map symm_apply_map]
def relStructSuccEquivMulStruct {f g : X.PtSimplex n x} {i : Fin n} :
    RelStruct f g i.succ ≃ MulStruct g .const f i where
  toFun h :=
    { map := h.map
      δ_map_of_lt j hj := h.δ_map_of_lt j (lt_trans hj (by simp))
      δ_succ_castSucc_map := by rw [← Fin.castSucc_succ, h.δ_castSucc_map] }
  invFun h :=
    { map := h.map
      δ_map_of_lt j hj := by
        rw [← Fin.succ_castSucc] at hj
        obtain rfl | hj := (Fin.le_castSucc_iff.2 hj).eq_or_lt
        · exact h.δ_castSucc_castSucc_map
        · exact h.δ_map_of_lt j hj }

namespace MulStruct

/-- Given `f : X.PtSimplex n x` and `i : Fin n` (note that this implies `n ≠ 0`),
this is the term in `MulStruct .const f f i` corresponding to
`stdSimplex.σ i.castSucc ≫ f.map`. -/
@[simps! map]
def oneMul (f : X.PtSimplex n x) (i : Fin n) :
    MulStruct .const f f i :=
  relStructCastSuccEquivMulStruct (.refl f i.castSucc)

/-- Given `f : X.PtSimplex n x` and `i : Fin n` (note that this implies `n ≠ 0`),
this is the term in `MulStruct f .const f i` corresponding to
`stdSimplex.σ i.succ ≫ f.map`. -/
@[simps! map]
def mulOne (f : X.PtSimplex n x) (i : Fin n) :
    MulStruct f .const f i :=
  relStructSuccEquivMulStruct (.refl f i.succ)

section

variable {f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f₀₃ : X.PtSimplex n x} {i : Fin n}
  (h₀₂ : MulStruct f₀₁ f₁₂ f₀₂ i) (h₁₃ : MulStruct f₁₂ f₂₃ f₁₃ i)
  (h : MulStruct f₀₁ f₁₃ f₀₃ i)

namespace assocAux

def α (j : Fin (n + 3)) (_ : j ≠ i.castSucc.castSucc.succ := by grind) :
    Δ[n + 1] ⟶ X :=
  if j = i.castSucc.castSucc.castSucc then h₁₃.map else
    if j = i.castSucc.succ.succ then h.map else
      if j = i.succ.succ.succ then h₀₂.map else
        const x

lemma α_of_lt (j : Fin (n + 3)) (hj : j < i.castSucc.castSucc.castSucc := by grind) :
    α h₀₂ h₁₃ h j = const x := by
  dsimp [α]
  rw [if_neg (by grind), if_neg (by grind), if_neg (by grind)]

lemma α_of_gt (j : Fin (n + 3)) (hj : i.succ.succ.succ < j := by grind) :
    α h₀₂ h₁₃ h j = const x := by
  dsimp [α]
  rw [if_neg (by grind), if_neg (by grind), if_neg (by grind)]

@[simp]
lemma α_castSucc_castSucc_castSucc :
    α h₀₂ h₁₃ h i.castSucc.castSucc.castSucc = h₁₃.map := by
  simp [α]

@[simp]
lemma α_castSucc_succ_succ :
    α h₀₂ h₁₃ h (i.castSucc.succ.succ) = h.map := by
  dsimp [α]
  rw [if_neg (by grind), if_pos (by simp)]

@[simp]
lemma α_succ_succ_succ :
    α h₀₂ h₁₃ h i.succ.succ.succ = h₀₂.map := by
  dsimp [α]
  rw [if_neg (by grind), if_neg (by grind), if_pos (by simp)]

lemma isCompatible_α : horn.IsCompatible (fun j hj ↦ α h₀₂ h₁₃ h j hj) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
  simp only [Fin.pred_succ, Fin.castPred_castSucc]
  simp only [Fin.castSucc_lt_succ_iff] at hjk
  by_cases! hj' : j < i.castSucc.castSucc
  · rw [α_of_lt _ _ _ _ (by simpa), comp_const]
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj')
    by_cases! hk : k.succ < i.castSucc.castSucc.castSucc
    · simp [α_of_lt _ _ _ _ hk]
    · obtain hk | hk := hk.eq_or_lt
      · simp only [← hk, α_castSucc_castSucc_castSucc]
        rwa [h₁₃.δ_map_of_lt]
      · simp only [Fin.castSucc_lt_succ_iff] at hk
        obtain rfl | hk := hk.eq_or_lt
        · rw [α_of_lt, comp_const]
        · rw [Fin.castSucc_lt_iff_succ_le] at hk
          · obtain rfl | hk := hk.eq_or_lt
            · rw [α_castSucc_succ_succ, h.δ_map_of_lt _ (by grind)]
            · rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hk
              obtain rfl | hk := hk.eq_or_lt
              · rw [α_succ_succ_succ, h₀₂.δ_map_of_lt _ (by grind)]
              · rw [α_of_gt .., comp_const]
  · obtain rfl | hj' := hj'.eq_or_lt
    · rw [α_castSucc_castSucc_castSucc]
      replace hjk := hjk.lt_of_ne' (by simpa using hk)
      rw [Fin.castSucc_lt_iff_succ_le] at hjk
      obtain rfl | hjk := hjk.eq_or_lt
      · simp
      · rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hjk
        obtain rfl | hjk := hjk.eq_or_lt
        · simp
        · rw [h₁₃.δ_map_of_gt _ hjk, α_of_gt .., comp_const]
    · rw [Fin.castSucc_lt_iff_succ_le] at hj'
      replace hj' := hj'.lt_of_ne (by grind)
      rw [Fin.succ_castSucc, Fin.castSucc_lt_iff_succ_le] at hj'
      obtain rfl | hj' := hj'.eq_or_lt
      · simp only [Fin.castSucc_succ, α_castSucc_succ_succ]
        obtain rfl | hjk := hjk.eq_or_lt
        · simp
        · rw [h.δ_map_of_gt _ hjk, α_of_gt .., comp_const]
      · rw [← Fin.succ_le_castSucc_iff] at hj'
        obtain hj' | hj' := hj'.eq_or_lt
        · simp only [← hj', α_succ_succ_succ]
          rw [h₀₂.δ_map_of_gt _ (by grind), α_of_gt .., comp_const]
        · rw [α_of_gt .., α_of_gt .., comp_const, comp_const]

end assocAux

def assocAux (φ : (Δ[n + 2] : SSet) ⟶ X)
    (hφ : ∀ (j : Fin (n + 3)) (hj : j ≠ i.castSucc.castSucc.succ),
      stdSimplex.δ j ≫ φ = assocAux.α h₀₂ h₁₃ h j hj) :
    MulStruct f₀₂ f₂₃ f₀₃ i where
  map := stdSimplex.δ i.castSucc.castSucc.succ ≫ φ
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_δ_assoc (by simp), hφ _ (by grind)]
    simp
  δ_succ_castSucc_map := by
    rw [dsimp% stdSimplex.δ_comp_δ_self_assoc (i := i.castSucc.succ),
      hφ _ (by grind)]
    simp
  δ_succ_succ_map := by
    rw [← dsimp% stdSimplex.δ_comp_δ_assoc (i := i.castSucc.succ) (by grind),
      hφ _ (by grind)]
    simp
  δ_map_of_lt j hj := by
    rw [stdSimplex.δ_comp_δ_assoc (by grind), hφ _ (by grind),
      assocAux.α_of_lt _ _ _ _ (by grind)]
    simp
  δ_map_of_gt j hj := by
    rw [← dsimp% stdSimplex.δ_comp_δ_assoc (i := i.castSucc.succ) (by grind),
      hφ _ (by grind), assocAux.α_of_gt _ _ _ _ (by grind)]
    simp

variable [KanComplex X]

noncomputable def assoc : MulStruct f₀₂ f₂₃ f₀₃ i :=
  assocAux h₀₂ h₁₃ h (assocAux.isCompatible_α h₀₂ h₁₃ h).lift
    (fun j hj ↦ (assocAux.isCompatible_α h₀₂ h₁₃ h).δ_lift j hj)

end

end MulStruct

end PtSimplex

end SSet
