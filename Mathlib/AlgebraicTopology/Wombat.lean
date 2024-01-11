/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.AlgebraicTopology.ForMathlib
import Mathlib.AlgebraicTopology.Quasicategory

/-!
# Kan complexes and quasicategories

-/

universe v u

open CategoryTheory Simplicial Opposite

namespace SSet

@[simps]
def horn.δ {n : ℕ} (i j : Fin (n+2)) (h : j ≠ i) : Λ[n+1, i] _[n] := by
  refine ⟨SimplexCategory.δ j, ?_⟩
  simpa only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.δ, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe, Set.union_singleton, ne_eq,
    ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_insert_iff, Set.mem_range,
    Fin.succAboveEmb_apply, Fin.exists_succAbove_eq_iff, forall_true_left, not_forall, not_or,
    not_not, exists_eq_right]


section nerve

variable {C : Type} [inst : Category C]

-- TODO: move
/-- A constructor for `n`-simplices of the nerve of a category,
by specifying `n+1` objects and a morphism between each of the `n` pairs of adjecent objects. -/
noncomputable
def nerve.mk (n : ℕ)
    (obj : Fin (n+1) → C) (mor : ∀ (i : Fin n), obj i.castSucc ⟶ obj i.succ) :
    (nerve C).obj (op [n]) :=
  ComposableArrows.mkOfObjOfMapSucc obj mor

def nerve.δ_mk_mor (n : ℕ)
    (obj : Fin (n+2) → C) (mor : ∀ (i : Fin (n+1)), obj i.castSucc ⟶ obj i.succ)
    (j : Fin (n+2)) (k : Fin n) :
    obj (Fin.succAbove j k.castSucc) ⟶ obj (Fin.succAbove j k.succ) :=
  if hkj : k.val + 1 < j.val
  then by
    refine eqToHom (congrArg _ ?_) ≫ mor k.castSucc ≫ eqToHom (congrArg _ ?_)
    · have : k.val < j.val := by linarith only [hkj]
      simp [Fin.succAbove, this]
    · ext; simp [Fin.succAbove, hkj]
  else if hkj' : k.val + 1 = j.val
  then by
    refine eqToHom (congrArg _ ?_) ≫ mor k.castSucc ≫ mor k.succ ≫ eqToHom (congrArg _ ?_)
    · simp [Fin.succAbove, hkj'.symm]
    · simp [Fin.succAbove, hkj'.symm]
  else by
    refine eqToHom (congrArg _ ?_) ≫ mor k.succ ≫ eqToHom (congrArg _ ?_)
    · have : ¬ k.val < j.val := by omega
      ext; simp [Fin.succAbove, this]
    · have : ¬ k.val + 1 < j.val := by omega
      ext; simp [Fin.succAbove, this]

lemma nerve.δ_mk (n : ℕ)
    (obj : Fin (n+2) → C) (mor : ∀ (i : Fin (n+1)), obj i.castSucc ⟶ obj i.succ)
    (j : Fin (n+2)) :
    (nerve C).δ j (nerve.mk (n+1) obj mor) =
      nerve.mk n (obj ∘ Fin.succAbove j) (nerve.δ_mk_mor n obj mor j) :=
  ComposableArrows.ext (fun _ ↦ rfl) <| by
  dsimp [SimplicialObject.δ, mk, nerve, unop_op, Monotone.functor]
  simp only [Category.comp_id, Category.id_comp]
  intro i hi
  symm
  rw [← ComposableArrows.map'_def _ i (i+1) (by omega) (by omega),
      ComposableArrows.mkOfObjOfMapSucc_map_succ (hi := hi)]
  dsimp only [δ_mk_mor]
  by_cases hij : i + 1 < j
  · simp only [hij, unop_op, SimplexCategory.len_mk, Fin.castSucc_mk, Fin.succ_mk, dite_true]
    have aux := (ComposableArrows.mkOfObjOfMapSucc obj mor).map'_def i (i+1) (by omega) (by omega)
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mor i (by omega)] at aux
    have := (ComposableArrows.mkOfObjOfMapSucc obj mor).map_eqToHom
    rw [← this, ← this, aux, ← Functor.map_comp, ← Functor.map_comp]
    rfl
    · have : i < j.val := by linarith only [hij]
      simp [Fin.succAbove, this]
    · ext; simp [Fin.succAbove, hij]
  rw [dif_neg hij]
  by_cases hij' : i + 1 = j
  · simp only [hij', unop_op, SimplexCategory.len_mk, Fin.castSucc_mk, Fin.succ_mk, dite_true]
    have aux1 := (ComposableArrows.mkOfObjOfMapSucc obj mor).map'_def i (i+1) (by omega) (by omega)
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mor i (by omega)] at aux1
    have aux2 := (ComposableArrows.mkOfObjOfMapSucc obj mor).map'_def (i+1) (i+2) (by omega) (by omega)
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mor (i+1) (by omega)] at aux2
    have := (ComposableArrows.mkOfObjOfMapSucc obj mor).map_eqToHom
    rw [← this, ← this, aux1, aux2, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    rfl
    · simp [Fin.succAbove, hij'.symm]
    · simp [Fin.succAbove, hij'.symm]
  rw [dif_neg hij']
  · simp only [unop_op, SimplexCategory.len_mk, Fin.castSucc_mk, Fin.succ_mk, dite_true]
    have aux := (ComposableArrows.mkOfObjOfMapSucc obj mor).map'_def (i+1) (i+2) (by omega) (by omega)
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ obj mor (i+1) (by omega)] at aux
    have := (ComposableArrows.mkOfObjOfMapSucc obj mor).map_eqToHom
    rw [← this, ← this, aux, ← Functor.map_comp, ← Functor.map_comp]
    rfl
    · have : ¬ i < j.val := by omega
      ext; simp [Fin.succAbove, this]
    · have : ¬ i + 1 < j.val := by omega
      ext; simp [Fin.succAbove, this]

-- TODO: move
def nerve.arrow (f : (nerve C) _[1]) : f.obj (0 : Fin 2) ⟶ f.obj (1 : Fin 2) :=
  f.map' 0 1 zero_le_one le_rfl

open SimplexCategory in
lemma nerve.horn_app_obj (n : ℕ) (i : Fin (n+3)) (σ : Λ[n+2, i] ⟶ nerve C)
    (m : SimplexCategoryᵒᵖ) (f : Λ[n+2, i].obj m) (k : Fin (m.unop.len + 1)) :
    (σ.app m f).obj k = (σ.app (op [0]) (horn.const _ i (f.1.toOrderHom k) _)).obj 0 := by
  let φ : ([0] : SimplexCategory) ⟶ m.unop :=
    Hom.mk ⟨Function.const _ k, fun _ _ _ ↦ le_rfl⟩
  have := σ.naturality φ.op
  rw [Function.funext_iff] at this
  specialize this f
  exact (congrArg (fun F ↦ F.obj 0) this).symm


def horn.edge'' {n m : ℕ} {i : Fin (n+4)}
    (f : Λ[n+3, i] _[m]) (a b : Fin (m+1)) (h : a ≤ b) :
    Λ[n+3, i] _[1] :=
  edge₃ _ i (f.1.toOrderHom a) (f.1.toOrderHom b) (f.1.toOrderHom.monotone h) <| by
  simp only [le_add_iff_nonneg_left, zero_le]

def horn.edge' {n m : ℕ} {i : Fin (n+4)}
    (f : Λ[n+3, i] _[m]) (k : ℕ) (hk : k + 1 ≤ m) :
    Λ[n+3, i] _[1] :=
  edge'' f ⟨k, by omega⟩ ⟨k+1, by omega⟩ <| by simp [Fin.le_iff_val_le_val]

lemma morphism_heq {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (hX : X₁ = X₂) (hY : Y₁ = Y₂) (H : f₁ = eqToHom hX ≫ f₂ ≫ eqToHom hY.symm) :
    HEq f₁ f₂ := by
  subst hX hY
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at H
  exact heq_of_eq H

lemma nerve.arrow_app_congr (n : ℕ) (i : Fin (n+3)) (σ : Λ[n+2, i] ⟶ nerve C)
  (f g : Λ[n+2, i] _[1]) (h : f = g) :
  arrow (σ.app (op [1]) f) =
    eqToHom (by rw [h]) ≫
    arrow (σ.app (op [1]) g)
    ≫ eqToHom (by rw [h]) := by
  subst h; simp

open SimplexCategory in
lemma nerve.horn_app_map (n : ℕ) (i : Fin (n+4)) (σ : Λ[n+3, i] ⟶ nerve C)
    (m : ℕ) (f : Λ[n+3, i] _[m]) (a b : ℕ) (hab : a ≤ b) (hbm : b ≤ m) :
    (σ.app (op [m]) f).map' a b hab hbm =
      eqToHom (by rw [nerve.horn_app_obj, eq_comm, nerve.horn_app_obj]; rfl) ≫
      nerve.arrow (σ.app (op [1])
        (horn.edge'' f
          ⟨a, Nat.lt_add_one_iff.mpr <| hab.trans hbm⟩
          ⟨b, Nat.lt_add_one_iff.mpr <| hbm⟩
          <| Fin.mk_le_mk.mpr hab))
      ≫ eqToHom (by rw [nerve.horn_app_obj, eq_comm, nerve.horn_app_obj]; rfl) := by
  let φ : ([1] : SimplexCategory) ⟶ [m] :=
    Hom.mk ⟨![⟨a, by omega⟩, ⟨b, by omega⟩], ?mono⟩
  case mono =>
    rw [Fin.monotone_iff_le_succ]
    simpa [Fin.forall_fin_one, Fin.le_iff_val_le_val]
  have := σ.naturality φ.op
  rw [Function.funext_iff] at this
  specialize this f
  have := congr_arg_heq arrow this
  apply eq_of_heq
  refine this.symm.trans ?_; clear this; clear this
  apply morphism_heq
  case hX =>
    rw [nerve.horn_app_obj, types_comp, Function.comp_apply, nerve.horn_app_obj]
    rfl
  case hY =>
    rw [nerve.horn_app_obj, types_comp, Function.comp_apply, nerve.horn_app_obj]
    rfl
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, types_comp, Function.comp_apply]
  dsimp only [horn.edge', horn]
  simp only [ne_eq, smallCategory_comp, Hom.comp, len_mk, unop_op, Int.ofNat_eq_coe,
    Int.Nat.cast_ofNat_Int, id_eq, Fin.castSucc_zero, Matrix.cons_val_zero, eq_mpr_eq_cast,
    Quiver.Hom.unop_op, Hom.toOrderHom_mk]
  dsimp [OrderHom.comp]
  apply arrow_app_congr
  apply Subtype.ext
  apply Hom.ext
  ext j
  dsimp at j ⊢
  fin_cases j <;> rfl

end nerve

namespace filler

variable {C : Type} [Category C]
variable {n : ℕ} {i : Fin (n+3)} (σ₀ : Λ[n+2, i] ⟶ nerve C)
variable (h₀ : 0 < i) (hₙ : i < Fin.last (n+2))

private
def obj : Fin (n+3) → C :=
  fun j ↦ (σ₀.app (op [0]) (horn.const n i j _)).obj 0

private
def mor (j : Fin (n+2)) : obj σ₀ j.castSucc ⟶ obj σ₀ j.succ := by
  refine eqToHom ?_
    ≫ (nerve.arrow (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ j)))
    ≫ eqToHom ?_
  all_goals rw [nerve.horn_app_obj _ _ _ (op [1])]; rfl

end filler

section

variable {C : Type} [Category C]
variable {n : ℕ} {i : Fin (n+3)} (σ₀ : Λ[n+2, i] ⟶ nerve C)
variable (h₀ : 0 < i) (hₙ : i < Fin.last (n+2))

noncomputable
def filler : (nerve C) _[n+2] :=
  nerve.mk _ (filler.obj σ₀) (filler.mor σ₀ h₀ hₙ)

open SimplexCategory in
lemma filler_spec_zero ⦃i : Fin 3⦄ (σ₀ : Λ[2, i] ⟶ nerve C)
    (h₀ : 0 < i) (hₙ : i < Fin.last 2) (j : Fin 3) (hj : j ≠ i) :
    (nerve C).δ j (filler σ₀ h₀ hₙ) = σ₀.app (op [1]) (horn.δ i j hj) := by
  rw [filler, nerve.δ_mk]
  dsimp only [nerve.mk]
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · symm; apply nerve.horn_app_obj
  · symm; apply nerve.horn_app_obj
  dsimp only [ComposableArrows.hom]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ 0 zero_lt_one]
  obtain rfl : i = 1 := by
    fin_cases i <;> simp at h₀ hₙ
    · rfl
    · exact (lt_irrefl _ hₙ).elim
  dsimp only [nerve.δ_mk_mor]
  simp only [ne_eq, Fin.ext_iff, Fin.val_one, @eq_comm ℕ _ 1] at hj
  simp only [unop_op, SimplexCategory.len_mk, ComposableArrows.mkOfObjOfMapSucc_obj, Fin.zero_eta,
    Function.comp_apply, Fin.mk_one, zero_add, Nat.zero_eq, Fin.castSucc_zero, Fin.succ_zero_eq_one,
    hj, Fin.succ_one_eq_two, Fin.castSucc_one, dite_false, ComposableArrows.map']
  split <;> rename_i hj'
  · obtain rfl : j = 2 := by fin_cases j <;> simp at hj hj'; rfl
    rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; symm; apply nerve.horn_app_obj
    swap; apply nerve.horn_app_obj
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    apply nerve.arrow_app_congr
    apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, standardSimplex.edge, horn.edge, horn.δ, δ, Fin.succAbove] at b ⊢
    fin_cases b <;> simp
  · obtain rfl : j = 0 := by fin_cases j <;> simp at hj hj'; rfl
    rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; symm; apply nerve.horn_app_obj
    swap; apply nerve.horn_app_obj
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    apply nerve.arrow_app_congr
    apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, standardSimplex.edge, horn.edge, horn.δ, δ, Fin.succAbove] at b ⊢
    fin_cases b <;> simp

lemma nerve.arrow_app_congr' {n : ℕ} {i : Fin (n+4)} (σ : Λ[n+3, i] ⟶ nerve C)
  {f₁ f₂ f₃ g₁ g₂ g₃ : Λ[n+3, i] _[1]}
  {h₁ : f₁ = g₁} {h₂ : f₂ = g₂} {h₃ : f₃ = g₃} {hf₁} {hf₂} {hf₃} {hg₁} {hg₂} {hg₃}
  (H : arrow (σ.app (op [1]) f₁) =
    eqToHom hf₁
    ≫ arrow (σ.app (op [1]) f₂)
    ≫ eqToHom hf₂
    ≫ arrow (σ.app (op [1]) f₃)
    ≫ eqToHom hf₃) :
  arrow (σ.app (op [1]) g₁) =
    eqToHom hg₁
    ≫ arrow (σ.app (op [1]) g₂)
    ≫ eqToHom hg₂
    ≫ arrow (σ.app (op [1]) g₃)
    ≫ eqToHom hg₃ := by
  subst h₁ h₂ h₃
  exact H

open SimplexCategory in
lemma filler_spec_succ_aux
  ⦃i : Fin (n + 4)⦄ (σ₀ : horn (n + 3) i ⟶ nerve C) (h₀ : 0 < i)
  (hₙ : i < Fin.last (n + 3)) (j : Fin (n + 4)) (hj : j ≠ i) (k : ℕ) (hk : k < n + 2)
  (hkj : ¬k + 1 < ↑j) (hkj' : k + 1 = ↑j) (h2 : k < n + 2)
  (h3 :
    (σ₀.app (op [1]) (horn.edge' (horn.δ i j hj) k hk)).obj 0 =
      (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ (Fin.castSucc { val := k, isLt := h2 }))).obj 0)
  (h4 : Nat.succ k < Nat.succ (n + 2))
  (h5 :
    (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ (Fin.castSucc { val := k, isLt := h2 }))).obj 1 =
      (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ (Fin.succ { val := k, isLt := h2 }))).obj 0)
  (h6 :
    (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ (Fin.succ { val := k, isLt := h2 }))).obj 1 =
      (σ₀.app (op [1]) (horn.edge' (horn.δ i j hj) k hk)).obj 1) :
  eqToHom h3 ≫
      (nerve.arrow (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ { val := k, isLt := _ })) ≫
          eqToHom h5 ≫ nerve.arrow (σ₀.app (op [1]) (horn.primitiveEdge h₀ hₙ { val := k + 1, isLt := h4 }))) ≫
        eqToHom h6 =
    nerve.arrow (σ₀.app (op [1]) (horn.edge' (horn.δ i j hj) k hk)) := by
  obtain ⟨j, hj'⟩ := j
  dsimp only [Fin.eta] at *
  subst hkj'
  let F := σ₀.app (op [2]) (horn.primitiveTriangle i h₀ hₙ k h2)
  have H := F.map'_comp 0 1 2 (by omega) (by omega) (by dsimp; omega)
  dsimp only at H
  have := nerve.horn_app_map n i σ₀ _ (horn.primitiveTriangle i h₀ hₙ k h2) 0 1 zero_le' one_le_two
  rw [this] at H; clear this
  have := nerve.horn_app_map n i σ₀ _ (horn.primitiveTriangle i h₀ hₙ k h2) 1 2 one_le_two le_rfl
  rw [this] at H; clear this
  have := nerve.horn_app_map n i σ₀ _ (horn.primitiveTriangle i h₀ hₙ k h2) 0 2 zero_le' le_rfl
  rw [this] at H; clear this
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at H
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc] at H
  symm
  simp only [Category.assoc]
  apply nerve.arrow_app_congr' σ₀ H
  · apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveTriangle, standardSimplex.triangle, standardSimplex.edge, horn.δ, horn.edge'', horn.edge', horn.edge₃, horn.edge,
      δ, Fin.succAbove] at b ⊢
    simp only [Matrix.cons_val_succ', Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons,
      lt_add_iff_pos_right, zero_lt_one, ite_true, lt_self_iff_false, ite_false]
  · apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.primitiveTriangle, standardSimplex.triangle, standardSimplex.edge, horn.δ, horn.edge'', horn.edge',
      horn.edge₃, horn.edge, δ, Fin.succAbove] at b ⊢
    -- simp only [Matrix.cons_val_succ', Fin.zero_eta, Matrix.cons_val_zero]
  · apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.primitiveTriangle, standardSimplex.triangle, standardSimplex.edge, horn.δ, horn.edge'', horn.edge',
      horn.edge₃, horn.edge, δ, Fin.succAbove] at b ⊢
    simp only [Matrix.cons_val_succ', Fin.zero_eta, Matrix.cons_val_zero]

open SimplexCategory in
lemma filler_spec_succ ⦃i : Fin (n + 4)⦄
    (σ₀ : Λ[n + 3, i] ⟶ nerve C) (h₀ : 0 < i) (hₙ : i < Fin.last (n + 3))
    (j : Fin (n + 4)) (hj : j ≠ i) :
    (nerve C).δ j (filler σ₀ h₀ hₙ) = σ₀.app (op [n + 2]) (horn.δ i j hj) := by
  rw [filler, nerve.δ_mk]
  refine ComposableArrows.ext ?_ ?_
  · dsimp [nerve.mk]
    intro k
    symm
    apply nerve.horn_app_obj
  intro k hk
  dsimp only [nerve.mk]
  rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k (by omega)]
  dsimp only [nerve.δ_mk_mor]
  split <;> rename_i hkj
  · rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [eq_comm, nerve.horn_app_obj]; rfl
    swap; rw [nerve.horn_app_obj]; rfl
    have := nerve.horn_app_map n i σ₀ _ (horn.δ i j hj) k (k+1) (k.le_add_right 1) hk
    rw [this, ← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [nerve.horn_app_obj, eq_comm, nerve.horn_app_obj]; rfl
    swap; rw [nerve.horn_app_obj, eq_comm, nerve.horn_app_obj]; rfl
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    apply nerve.arrow_app_congr
    apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.primitiveTriangle, horn.δ, horn.edge'', horn.edge',
      horn.edge₃, horn.edge, δ, Fin.succAbove] at b ⊢
    have hkj' : k < j.val := by omega
    simp only [hkj', ite_true, hkj]
  split <;> rename_i hkj'
  · rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [eq_comm, nerve.horn_app_obj]; rfl
    swap; rw [nerve.horn_app_obj]; rfl
    have := nerve.horn_app_map n i σ₀ _ (horn.δ i j hj) k (k+1) (k.le_add_right 1) hk
    rw [this, ← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [nerve.horn_app_obj, eq_comm, nerve.horn_app_obj]; rfl
    swap; rw [nerve.horn_app_obj, eq_comm, nerve.horn_app_obj]; rfl
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    slice_lhs 2 4 => skip
    simp only [unop_op, len_mk, Int.ofNat_eq_coe, Int.Nat.cast_ofNat_Int, id_eq, Fin.castSucc_mk,
      Fin.succ_mk]
    apply filler_spec_succ_aux <;> assumption
  · rw [← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [eq_comm, nerve.horn_app_obj]; rfl
    swap; rw [nerve.horn_app_obj]; rfl
    have := nerve.horn_app_map n i σ₀ _ (horn.δ i j hj) k (k+1) (k.le_add_right 1) hk
    rw [this, ← eqToHom_comp_iff, ← comp_eqToHom_iff]
    swap; rw [nerve.horn_app_obj, eq_comm, nerve.horn_app_obj]; rfl
    swap; rw [nerve.horn_app_obj, eq_comm, nerve.horn_app_obj]; rfl
    dsimp only [filler.mor]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    symm
    apply nerve.arrow_app_congr
    apply Subtype.ext
    apply Hom.ext
    ext b
    dsimp [horn.primitiveEdge, horn.primitiveTriangle, horn.δ, horn.edge'', horn.edge',
      horn.edge₃, horn.edge, δ, Fin.succAbove] at b ⊢
    have hkj'' : ¬ k < j.val := by omega
    simp only [hkj'', ite_false, hkj]

end

/-- The nerve of a category is a quasicategory.

[Kerodon, 0032] -/
instance (C : Type) [Category C] : Quasicategory (nerve C) := by
  apply quasicategory_of_filler
  intro n i σ₀ h₀ hₙ
  use filler σ₀ h₀ hₙ
  intro j hj
  cases n using Nat.casesAuxOn with
  | zero => apply filler_spec_zero _ _ _ _ hj
  | succ n => apply filler_spec_succ _ _ _ _ hj

end SSet
