/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.Order.Fin.InsertNth
public import Mathlib.Order.Fin.Prod

/-!
# Binary product of standard simplices

In this file, we show that `Δ[p] ⊗ Δ[q]` identifies to the nerve of
`ULift (Fin (p + 1) × Fin (q + 1))`. We relate the `n`-simplices
of `Δ[p] ⊗ Δ[q]` to order preserving maps `Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`,
Via this bijection, a simplex in `Δ[p] ⊗ Δ[q]` is nondegenerate iff
the corresponding monotone map `Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`
is injective (or a strict mono).

We also show that the dimension of `Δ[p] ⊗ Δ[q]` is `≤ p + q`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory

namespace SSet

namespace prodStdSimplex

variable {p q : ℕ}

/-- `n`-simplices in `Δ[p] ⊗ Δ[q]` identify to order preserving maps
`Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`. -/
def objEquiv {n : ℕ} :
    (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌ ≃ (Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) where
  toFun := fun ⟨x, y⟩ ↦ OrderHom.prod
      (stdSimplex.objEquiv x).toOrderHom
      (stdSimplex.objEquiv y).toOrderHom
  invFun f :=
    ⟨stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.fst.comp f)),
      stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.snd.comp f))⟩
  left_inv := fun ⟨x, y⟩ ↦ by simp

@[simp]
lemma objEquiv_apply_symm_apply {n : ℕ} (f : (Fin (n + 1) →o Fin (p + 1) × Fin (q + 1))) :
    dsimp% objEquiv (objEquiv.{u}.symm f) = f := rfl

@[simp]
lemma objEquiv_apply_fst {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    dsimp% (objEquiv x i).1 = x.1 i := rfl

@[simp]
lemma objEquiv_apply_snd {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    dsimp% (objEquiv x i).2 = x.2 i := rfl

lemma objEquiv_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) :
    (objEquiv z).comp f.toOrderHom = objEquiv ((Δ[p] ⊗ Δ[q]).map f.op z) :=
  rfl

lemma objEquiv_map_apply {n m : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
      objEquiv ((Δ[p] ⊗ Δ[q]).map f.op x) i = objEquiv x (f.toOrderHom i) :=
  rfl

lemma objEquiv_δ_apply {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n + 1⦌) (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    dsimp% objEquiv ((Δ[p] ⊗ Δ[q]).δ i x) j = objEquiv x (i.succAbove j) := rfl

variable (p q) in
/-- The binary product `Δ[p] ⊗ Δ[q]` identifies to the nerve
of `ULift (Fin (p + 1) × Fin (q + 1))`. -/
def isoNerve : Δ[p] ⊗ Δ[q] ≅ nerve (ULift.{u} (Fin (p + 1) × Fin (q + 1))) :=
  NatIso.ofComponents (fun ⟨⟨d⟩⟩ ↦ Equiv.toIso (objEquiv.trans
      { toFun f := (ULift.orderIso.symm.monotone.comp f.monotone).functor
        invFun s := ULift.orderIso.toOrderEmbedding.toOrderHom.comp ⟨_, s.monotone⟩ }))

lemma nonDegenerate_iff_injective_objEquiv {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) :
    z ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate n ↔ Function.Injective (objEquiv z) := by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom,
    PartialOrder.mem_nerve_nonDegenerate_iff_injective,
    ← Function.Injective.of_comp_iff ULift.down_injective]
  rfl

lemma nonDegenerate_iff_strictMono_objEquiv {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) :
    z ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate n ↔ StrictMono (objEquiv z) := by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom,
    PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

/-- Given a `n`-simplex `x` in `Δ[p] ⊗ Δ[q]`, this is the order preserving
map `Fin (n + 1) →o Fin (m + 1)` (with `p + q = m`) which corresponds to the
sum of the two components of `objEquiv x : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`. -/
@[simps coe]
def orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) {m : ℕ} (hm : p + q = m) :
    Fin (n + 1) →o Fin (m + 1) where
  toFun i := ⟨(x.1 i : ℕ) + x.2 i, by lia⟩
  monotone' i j h := by
    dsimp
    simp only [Fin.mk_le_mk]
    have := (objEquiv x).monotone h
    have h₁ : x.1 i ≤ x.1 j := this.1
    have h₂ : x.2 i ≤ x.2 j := this.2
    lia

lemma strictMono_orderHomOfSimplex_iff {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) {m : ℕ}
    (hm : p + q = m) :
    StrictMono (orderHomOfSimplex x hm) ↔ StrictMono (objEquiv x) := by
  have (a b : Fin (p + 1) × Fin (q + 1)) (hab : a ≤ b) :
      a < b ↔ ((a.1 : ℕ) + a.2 < (b.1 : ℕ) + b.2) := by
    obtain ⟨h₁, h₂⟩ := hab
    rw [Prod.lt_iff]
    lia
  simp only [Fin.strictMono_iff_lt_succ]
  exact forall_congr' (fun i ↦ (this _ _ ((objEquiv x).monotone i.castSucc_le_succ)).symm)

lemma strictMono_orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n) {m : ℕ}
    (hm : p + q = m) :
    StrictMono (orderHomOfSimplex x.1 hm) := by
  simpa only [strictMono_orderHomOfSimplex_iff, ← nonDegenerate_iff_strictMono_objEquiv] using x.2

instance : (Δ[p] ⊗ Δ[q] : SSet.{u}).HasDimensionLE (p + q) where
  degenerate_eq_top n hn := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    by_contra hx
    rw [← mem_nonDegenerate_iff_notMem_degenerate,
      nonDegenerate_iff_strictMono_objEquiv,
      ← strictMono_orderHomOfSimplex_iff _ rfl] at hx
    replace hx := Fintype.card_le_of_injective _ hx.injective
    simp only [Fintype.card_fin, add_le_add_iff_right] at hx
    lia

instance : (Δ[p] ⊗ Δ[q] : SSet.{u}).Finite :=
  finite_of_hasDimensionLT _ (p + q + 1) inferInstance

lemma le_orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n) {m : ℕ}
    (hm : p + q = m) (i : Fin (n + 1)) : i.1 ≤ orderHomOfSimplex x.1 hm i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    simpa using! lt_of_le_of_lt hi (strictMono_orderHomOfSimplex x hm Fin.castSucc_lt_succ)

lemma nonDegenerate_max_dim_iff {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌)
    (hn : p + q = n := by lia) :
    z ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate n ↔ orderHomOfSimplex z hn = .id := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · exact OrderHom.eq_id_of_injective _ (strictMono_orderHomOfSimplex ⟨z, h⟩ hn).injective
  · rw [nonDegenerate_iff_injective_objEquiv]
    intro h a b hab
    simp only [DFunLike.ext_iff, orderHomOfSimplex_coe, OrderHom.id_coe, id_eq] at h
    rw [← h a, ← h b, Fin.ext_iff]
    change ((objEquiv z a).1 : ℕ) + (objEquiv z a).2 = (objEquiv z b).1 + (objEquiv z b).2
    simp only [hab]

lemma nonDegenerate_ext₁ {n : ℕ} {z₁ z₂ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n}
    (h : z₁.1.1 = z₂.1.1) (hn : p + q = n := by lia) :
    z₁ = z₂ := by
  ext
  apply objEquiv.injective
  ext i : 3
  · exact DFunLike.congr_fun h i
  · have h₁ := z₁.2
    have h₂ := z₂.2
    rw [nonDegenerate_max_dim_iff] at h₁ h₂
    simpa only [orderHomOfSimplex_coe, h, Fin.ext_iff, add_right_inj]
      using! DFunLike.congr_fun (h₁.trans h₂.symm) i

lemma nonDegenerate_ext₂ {n : ℕ} {z₁ z₂ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n}
    (h : z₁.1.2 = z₂.1.2) (hn : p + q = n := by lia) :
    z₁ = z₂ :=
  (nonDegenerateEquivOfIso (β_ _ _)).injective (nonDegenerate_ext₁ h)

private lemma exists_nonDegenerate_max_dim_aux {d : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate d) (hd : d < p + q) :
    ∃ (y : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (d + 1)),
      x.1 ∈ (Subcomplex.ofSimplex y.1).obj _ := by
  have hx := (nonDegenerate_iff_strictMono_objEquiv _).1 x.2
  suffices ∃ (i : Fin (d + 2)) (u : Fin (p + 1) × Fin (q + 1)),
      StrictMono (Fin.insertNth (α := fun _ ↦ Fin (p + 1) × Fin (q + 1)) i u
        (objEquiv x.val)) by
    obtain ⟨i, u, hf⟩ := this
    simp only [stdSimplex.mem_ofSimplex_obj_iff]
    refine ⟨⟨objEquiv.symm ⟨_, hf.monotone⟩,
      (nonDegenerate_iff_strictMono_objEquiv _).2 hf⟩,
      stdSimplex.objEquiv.symm (SimplexCategory.δ i),
      objEquiv.injective ?_⟩
    ext k : 2
    rw [yonedaEquiv_symm_app, Equiv.apply_symm_apply, ← SimplicialObject.δ_def]
    simp [objEquiv_δ_apply]
  let S : Finset (Fin (d + 1)) :=
    { i | i.castLE (by lia) < orderHomOfSimplex x.1 rfl i }
  by_cases hS : S.Nonempty
  · generalize hi₀ : S.min' hS = i₀
    obtain rfl | ⟨i₀, rfl⟩ := Fin.eq_zero_or_eq_succ i₀
    · refine ⟨_, _, Fin.strictMono_insertNth_zero hx (0, 0) ?_⟩
      have : 0 ∈ S := by simpa [← hi₀] using S.min'_mem hS
      simpa [-Fin.val_pos_iff, S, Fin.lt_def, Fin.prod_zero_zero_lt_iff] using this
    · obtain ⟨u, hu₁, hu₂⟩ :=
        Fin.prod_exists_lt_lt_of_le_of_le (objEquiv x.val i₀.castSucc)
          (objEquiv x.val i₀.succ) ((objEquiv x.val).monotone i₀.castSucc_le_succ) (by
            have h₀ : i₀.castSucc ∉ S := fun h ↦ by simpa [hi₀] using S.min'_le _ h
            have h₁ : i₀.succ ∈ S := by
              simpa only [hi₀] using S.min'_mem hS
            simp [S, Fin.lt_def] at h₀ h₁ ⊢
            lia)
      exact ⟨_, _, Fin.strictMono_insertNth hx i₀ u hu₁ hu₂⟩
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    refine ⟨_, _, Fin.strictMono_insertNth_last hx (Fin.last _, Fin.last _) ?_⟩
    rw [Fin.prod_lt_last_last_iff]
    refine lt_of_le_of_lt ?_ hd
    simpa [← hS, S, Fin.le_def] using Finset.notMem_empty (Fin.last d)

lemma exists_nonDegenerate_max_dim {d : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate d) {n : ℕ} (hn : p + q = n) :
    ∃ (y : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n),
      x.val ∈ (Subcomplex.ofSimplex y.val).obj _ := by
  subst hn
  obtain ⟨i, hi⟩ := Nat.le.dest (Nat.le_of_lt_succ (dim_lt_of_nonDegenerate _ x (p + q + 1)))
  induction i generalizing d with
  | zero =>
      obtain rfl : d = p + q := by lia
      exact ⟨x, Subcomplex.mem_ofSimplex_obj _⟩
  | succ d' hd' =>
      obtain ⟨y, hy⟩ := exists_nonDegenerate_max_dim_aux x (by lia)
      obtain ⟨z, hz⟩ := hd' y (by lia)
      rw [← Subcomplex.ofSimplex_le_iff] at hz
      exact ⟨z, hz _ hy⟩

end prodStdSimplex

end SSet
