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

lemma Fin.orderHom_ext_of_injective_aux {α : Type*} [PartialOrder α] [DecidableEq α]
    {n : ℕ} {f g : Fin n →o α}
    (hg : Function.Injective g)
    (h : Finset.image f ⊤ = Finset.image g ⊤) (i : Fin n)
    (h' : ∀ (j : Fin n), j < i → f j = g j) :
    f i ≤ g i := by
  have : g i ∈ Finset.image f ⊤ := by rw [h]; simp
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at this
  obtain ⟨j, hj⟩ := this
  rw [← hj]
  apply f.monotone
  by_contra!
  rw [h' j this] at hj
  lia

-- to be moved
lemma Fin.orderHom_ext_of_injective {α : Type*} [PartialOrder α] [DecidableEq α]
    {n : ℕ} {f g : Fin n →o α}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : Finset.image f ⊤ = Finset.image g ⊤) :
    f = g := by
  let P (i : ℕ) := ∀ (j : ℕ) (hij : j < i) (hj : j < n), f ⟨j, by lia⟩ = g ⟨j, by lia⟩
  suffices ∀ i, P i by ext i; exact this (i.1 + 1) i.1 (by lia) (by lia)
  suffices ∀ i, P i → P (i + 1) from fun i ↦ by
    induction i with
    | zero => lia
    | succ i hi => exact fun j hij hj ↦ this _ hi j hij hj
  intro i hi j hij hj
  obtain hij | rfl := (Nat.le_of_lt_succ hij).lt_or_eq
  · exact hi j hij hj
  · apply le_antisymm
    · exact orderHom_ext_of_injective_aux hg h _
        (fun k hk ↦ hi k hk (by lia))
    · exact orderHom_ext_of_injective_aux hf h.symm _
        (fun k hk ↦ (hi k hk (by lia)).symm)

-- to be moved
lemma Fin.eq_id_of_strictMono {n : ℕ} (f : Fin (n + 1) →o Fin (n + 1)) (hf : StrictMono f) :
    f = .id := by
  refine orderHom_ext_of_injective hf.injective (fun _ _ h ↦ h) ?_
  simp only [Finset.top_eq_univ, OrderHom.id_coe, Finset.image_id]
  exact Finset.image_univ_of_surjective (Finite.surjective_of_injective hf.injective)

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
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => simp
  | succ i hi' =>
      have h : (⟨i, by lia⟩ : Fin (n + 1)) < ⟨i + 1, hi⟩ := by simp
      simpa only [Nat.succ_le_iff] using
        lt_of_le_of_lt (hi' (by lia)) (strictMono_orderHomOfSimplex x hm h)

lemma nonDegenerate_max_dim_iff {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _⦋n⦌) (hn : p + q = n) :
    z ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate n ↔ orderHomOfSimplex z hn = .id := by
  constructor
  · intro h
    exact Fin.eq_id_of_strictMono _ (strictMono_orderHomOfSimplex ⟨z, h⟩ hn)
  · rw [nonDegenerate_iff_injective_objEquiv]
    intro h a b hab
    simp only [DFunLike.ext_iff, orderHomOfSimplex_coe, OrderHom.id_coe, id_eq] at h
    rw [← h a, ← h b, Fin.ext_iff]
    change ((objEquiv z a).1 : ℕ) + (objEquiv z a).2 = (objEquiv z b).1 + (objEquiv z b).2
    simp only [hab]

lemma nonDegenerate_ext₁ {n : ℕ} {z₁ z₂ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n}
    (hn : p + q = n) (h : z₁.1.1 = z₂.1.1) :
    z₁ = z₂ := by
  ext
  apply objEquiv.injective
  ext i : 3
  · exact DFunLike.congr_fun h i
  · have h₁ := z₁.2
    have h₂ := z₂.2
    rw [nonDegenerate_max_dim_iff _ hn] at h₁ h₂
    simpa only [orderHomOfSimplex_coe, h, Fin.ext_iff, add_right_inj]
      using DFunLike.congr_fun (h₁.trans h₂.symm) i

lemma nonDegenerate_ext₂ {n : ℕ} {z₁ z₂ : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate n}
    (hn : p + q = n) (h : z₁.1.2 = z₂.1.2) :
    z₁ = z₂ :=
  (nonDegenerateEquivOfIso (β_ _ _)).injective (nonDegenerate_ext₁ (by lia) h)

end prodStdSimplex

end SSet
