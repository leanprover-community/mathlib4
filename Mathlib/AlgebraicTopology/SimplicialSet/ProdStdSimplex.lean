/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

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
lemma objEquiv_apply_fst {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    (objEquiv x i).1 = x.1 i := rfl

@[simp]
lemma objEquiv_apply_snd {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    (objEquiv x i).2 = x.2 i := rfl

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
    objEquiv ((Δ[p] ⊗ Δ[q]).δ i x) j = objEquiv x (i.succAbove j) := rfl

variable (p q) in
/-- The binary product `Δ[p] ⊗ Δ[q]` identifies to the nerve
of `ULift (Fin (p + 1) × Fin (q + 1))`. -/
def isoNerve : Δ[p] ⊗ Δ[q] ≅ nerve (ULift.{u} (Fin (p + 1) × Fin (q + 1))) :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso (by
    obtain ⟨d⟩ := d
    induction d using SimplexCategory.rec with | _ d
    exact objEquiv.trans
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

end prodStdSimplex

end SSet
