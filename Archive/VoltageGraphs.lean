/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.SimpleGraph.QuotientGraph
import Mathlib.Combinatorics.SimpleGraph.Action
import Mathlib.Combinatorics.SimpleGraph.Representation
import Mathlib.Data.ZMod.Basic

/-!
# Voltage graphs on K₂: Heawood and Möbius-Kantor graphs

A voltage graph on K₂ with cyclic group Zₘ and three voltages {v₁, v₂, v₃}
gives a cubic graph on 2m vertices. Vertices are `Fin 2 × ZMod m`, and
`(0, g) ~ (1, g + vⱼ)` for each voltage.

Every cubic arc-transitive graph of small order arises this way:
* Heawood (F014A): K₂ with Z₇, voltages {0, 4, 6}, 14 vertices
* Möbius-Kantor (F016A): K₂ with Z₈, voltages {0, 1, 3}, 16 vertices

Both quotient to K₂ under the fibre projection `Prod.fst`.

## Main definitions

* `voltageGraphK2` — cubic voltage graph on K₂ with cyclic voltage group
* `heawoodVoltage` — the Heawood graph (Levi graph of the Fano plane)
* `mobiusKantorVoltage` — the Möbius-Kantor graph (GP(8,3))

## Visualizations

* [The Heawood graph](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/heawood-F014A.jpg) — F014A, the Levi graph of the Fano plane
* [The Möbius-Kantor graph](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/mobius-kantor-F016A.jpg) — F016A, the generalized Petersen graph GP(8,3)

## References

* Gross & Tucker, *Topological Graph Theory*, 1987
* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
-/

set_option linter.style.nativeDecide false

/-- A cubic voltage graph on K₂ with voltage group `ZMod m`.
Three voltages v₁, v₂, v₃ give a cubic graph on 2m vertices.
`(0, g) ~ (1, g + vⱼ)` for each voltage. -/
def voltageGraphK2 (m : ℕ) [NeZero m]
    (v₁ v₂ v₃ : ZMod m) : SimpleGraph (Fin 2 × ZMod m) where
  Adj p q :=
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 - p.2 ∈ ({v₁, v₂, v₃} : Set (ZMod m))) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 - q.2 ∈ ({v₁, v₂, v₃} : Set (ZMod m)))
  symm := by
    intro p q hpq
    rcases hpq with ⟨hp, hq, hv⟩ | ⟨hp, hq, hv⟩
    · exact Or.inr ⟨hq, hp, hv⟩
    · exact Or.inl ⟨hq, hp, hv⟩
  loopless := ⟨fun p hp => by
    rcases hp with ⟨hp, hq, _⟩ | ⟨hp, hq, _⟩ <;> simp [hp] at hq⟩

/-! ### The Heawood graph -/

/-- The **Heawood graph**: voltage graph on K₂ with Z₇ voltages {0, 4, 6}.
Levi graph of the Fano plane PG(2,2). 14 vertices, cubic, girth 6.
Sab(G₄₂, C₃) where G₄₂ = Z₇ ⋊ Z₆. -/
def heawoodVoltage : SimpleGraph (Fin 2 × ZMod 7) :=
  voltageGraphK2 7 0 4 6

instance : DecidableRel heawoodVoltage.Adj := by
  intro p q; unfold heawoodVoltage voltageGraphK2; simp only; exact instDecidableOr

/-- The Heawood graph is 3-regular. -/
theorem heawoodVoltage_regular :
    ∀ v : Fin 2 × ZMod 7,
      (Finset.univ.filter fun w => heawoodVoltage.Adj v w).card = 3 := by
  native_decide

/-- The Heawood graph has 42 directed edges (21 undirected). -/
theorem heawoodVoltage_directedEdges :
    (Finset.univ.filter fun p : (Fin 2 × ZMod 7) × (Fin 2 × ZMod 7) =>
      heawoodVoltage.Adj p.1 p.2).card = 42 := by
  native_decide

/-! ### The Möbius-Kantor graph -/

/-- The **Möbius-Kantor graph**: voltage graph on K₂ with Z₈ voltages {0, 1, 3}.
GP(8,3), the generalised Petersen graph. 16 vertices, cubic, girth 6.
Sab(GL(2,3), C₃). -/
def mobiusKantorVoltage : SimpleGraph (Fin 2 × ZMod 8) :=
  voltageGraphK2 8 0 1 3

instance : DecidableRel mobiusKantorVoltage.Adj := by
  intro p q; unfold mobiusKantorVoltage voltageGraphK2; simp only; exact instDecidableOr

/-- The Möbius-Kantor graph is 3-regular. -/
theorem mobiusKantorVoltage_regular :
    ∀ v : Fin 2 × ZMod 8,
      (Finset.univ.filter fun w => mobiusKantorVoltage.Adj v w).card = 3 := by
  native_decide

/-- The Möbius-Kantor graph has 48 directed edges (24 undirected). -/
theorem mobiusKantorVoltage_directedEdges :
    (Finset.univ.filter fun p : (Fin 2 × ZMod 8) × (Fin 2 × ZMod 8) =>
      mobiusKantorVoltage.Adj p.1 p.2).card = 48 := by
  native_decide

/-! ### Fibre quotients to K₂ -/

instance : DecidableRel (heawoodVoltage.quotientGraph
    (Prod.fst : Fin 2 × ZMod 7 → Fin 2)).Adj := by
  intro i j; unfold SimpleGraph.quotientGraph; simp only; exact instDecidableAnd

/-- The Heawood graph quotients to K₂ under the fibre projection. -/
theorem heawoodVoltage_quotient_complete :
    ∀ i j : Fin 2, i ≠ j →
    (heawoodVoltage.quotientGraph
      (Prod.fst : Fin 2 × ZMod 7 → Fin 2)).Adj i j := by
  native_decide

instance : DecidableRel (mobiusKantorVoltage.quotientGraph
    (Prod.fst : Fin 2 × ZMod 8 → Fin 2)).Adj := by
  intro i j; unfold SimpleGraph.quotientGraph; simp only; exact instDecidableAnd

/-- The Möbius-Kantor graph quotients to K₂ under the fibre projection. -/
theorem mobiusKantorVoltage_quotient_complete :
    ∀ i j : Fin 2, i ≠ j →
    (mobiusKantorVoltage.quotientGraph
      (Prod.fst : Fin 2 × ZMod 8 → Fin 2)).Adj i j := by
  native_decide

/-! ## Sabidussi coset graph representations

Every voltage graph on K₂ is vertex-transitive: the cyclic group acts by
translation on the fibre coordinate, and a fibre-swapping automorphism
makes the action transitive on all vertices. By the Sabidussi representation
theorem, the graph is a coset graph. -/

section HeawoodSabidussi

/-- Z₇ translation: `(i, g) ↦ (i, g + 1)`. -/
private def heawoodTranslation : Equiv.Perm (Fin 2 × ZMod 7) where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv := by intro ⟨i, g⟩; simp [add_sub_cancel_right]
  right_inv := by intro ⟨i, g⟩; simp [sub_add_cancel]

/-- Fibre swap with negation: `(i, g) ↦ (1 - i, -g)`.
    Preserves Heawood adjacency because `-v ∈ {0, 4, 6}` for `v ∈ {0, 4, 6}` in Z₇. -/
private def heawoodSwap : Equiv.Perm (Fin 2 × ZMod 7) where
  toFun p := (⟨1 - p.1.val, by omega⟩, -p.2)
  invFun p := (⟨1 - p.1.val, by omega⟩, -p.2)
  left_inv := by native_decide
  right_inv := by native_decide

/-- Translation preserves Heawood adjacency. -/
private theorem heawoodTranslation_adj : ∀ u v : Fin 2 × ZMod 7,
    heawoodVoltage.Adj u v → heawoodVoltage.Adj (heawoodTranslation u) (heawoodTranslation v) := by
  native_decide

/-- Swap preserves Heawood adjacency. -/
private theorem heawoodSwap_adj : ∀ u v : Fin 2 × ZMod 7,
    heawoodVoltage.Adj u v → heawoodVoltage.Adj (heawoodSwap u) (heawoodSwap v) := by
  native_decide

/-- The group generated by translation and swap. -/
private def heawoodG : Subgroup (Equiv.Perm (Fin 2 × ZMod 7)) :=
  Subgroup.closure ({heawoodTranslation, heawoodSwap} : Set _)

private noncomputable instance : MulAction heawoodG (Fin 2 × ZMod 7) :=
  MulAction.compHom _ heawoodG.subtype

private noncomputable instance : GraphAction heawoodG (Fin 2 × ZMod 7) heawoodVoltage where
  adj_smul := by
    intro ⟨σ, hσ⟩ u v hadj
    show heawoodVoltage.Adj (σ u) (σ v)
    revert u v; change ∀ u v, heawoodVoltage.Adj u v → heawoodVoltage.Adj (σ u) (σ v)
    refine Subgroup.closure_induction
      (p := fun σ _ => ∀ u v, heawoodVoltage.Adj u v → heawoodVoltage.Adj (σ u) (σ v))
      ?_ ?_ ?_ ?_ hσ
    · intro x hx
      rcases hx with rfl | rfl
      · exact heawoodTranslation_adj
      · exact heawoodSwap_adj
    · intro u v h; simpa
    · intro x y _ _ hx hy u v hadj
      simp only [Equiv.Perm.mul_apply]; exact hx _ _ (hy u v hadj)
    · intro x _ hx u v hadj
      let f : { p : (Fin 2 × ZMod 7) × (Fin 2 × ZMod 7) // heawoodVoltage.Adj p.1 p.2 } →
              { p : (Fin 2 × ZMod 7) × (Fin 2 × ZMod 7) // heawoodVoltage.Adj p.1 p.2 } :=
        fun ⟨⟨a, b⟩, hab⟩ => ⟨⟨x a, x b⟩, hx a b hab⟩
      have hf_surj : Function.Surjective f := Finite.surjective_of_injective (by
        intro ⟨⟨a₁, b₁⟩, _⟩ ⟨⟨a₂, b₂⟩, _⟩ h
        simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at h
        exact Subtype.ext (Prod.ext (x.injective h.1) (x.injective h.2)))
      obtain ⟨⟨⟨a, b⟩, hab⟩, heq⟩ := hf_surj ⟨⟨u, v⟩, hadj⟩
      simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at heq
      rw [show a = x⁻¹ u from by rw [← heq.1]; simp,
          show b = x⁻¹ v from by rw [← heq.2]; simp] at hab
      exact hab

private def heawoodT_mem : heawoodTranslation ∈ heawoodG :=
  Subgroup.subset_closure (Set.mem_insert _ _)

private def heawoodS_mem : heawoodSwap ∈ heawoodG :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

/-- Witness element mapping (0,0) to v, as a product of generators. -/
private def heawoodWitElem : Fin 2 × ZMod 7 → Equiv.Perm (Fin 2 × ZMod 7)
  | (⟨0, _⟩, g) => heawoodTranslation ^ g.val
  | (⟨1, _⟩, g) => heawoodTranslation ^ g.val * heawoodSwap

private theorem heawoodWitElem_correct :
    ∀ v : Fin 2 × ZMod 7,
      heawoodWitElem v ((0 : Fin 2), (0 : ZMod 7)) = v := by native_decide

private theorem heawoodWitElem_mem (v : Fin 2 × ZMod 7) : heawoodWitElem v ∈ heawoodG := by
  rcases v with ⟨⟨i, hi⟩, g⟩
  interval_cases i
  · exact heawoodG.pow_mem heawoodT_mem _
  · exact heawoodG.mul_mem (heawoodG.pow_mem heawoodT_mem _) heawoodS_mem

private noncomputable instance : MulAction.IsPretransitive heawoodG (Fin 2 × ZMod 7) where
  exists_smul_eq := by
    intro x y
    have hmem : (heawoodWitElem x).symm.trans (heawoodWitElem y) ∈ heawoodG :=
      heawoodG.mul_mem (heawoodWitElem_mem y) (heawoodG.inv_mem (heawoodWitElem_mem x))
    exact ⟨⟨_, hmem⟩, by
      change ((heawoodWitElem x).symm.trans (heawoodWitElem y)) x = y
      simp only [Equiv.trans_apply]
      rw [show (heawoodWitElem x).symm x = ((0 : Fin 2), (0 : ZMod 7)) from by
        rw [Equiv.symm_apply_eq]; exact (heawoodWitElem_correct x).symm]
      exact heawoodWitElem_correct y⟩

/-- **The Heawood graph is a Sabidussi coset graph.**

The dihedral group D₁₄ = ⟨translation, swap⟩ acts vertex-transitively, giving:
  `heawoodVoltage ≃g Sab(D₁₄, {1}, D)` (a Cayley graph). -/
noncomputable def heawoodSabidussiIso :
    heawoodVoltage ≃g SimpleGraph.cosetGraph
      (MulAction.stabilizer heawoodG ((0 : Fin 2), (0 : ZMod 7)))
      (connectionSet heawoodG heawoodVoltage ((0 : Fin 2), (0 : ZMod 7)))
      (connectionSet.isConnectionSet _) :=
  sabidussiIso _

end HeawoodSabidussi

section MKSabidussi

/-- Z₈ translation: `(i, g) ↦ (i, g + 1)`. -/
private def mkTranslation : Equiv.Perm (Fin 2 × ZMod 8) where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv := by intro ⟨i, g⟩; simp [add_sub_cancel_right]
  right_inv := by intro ⟨i, g⟩; simp [sub_add_cancel]

/-- Fibre swap with multiplication by 5: `(i, g) ↦ (1 - i, 5g)`.
    Preserves MK adjacency because `5 · {0, 1, 3} = {0, 5, 15} = {0, 5, 7}` and
    the adjacency condition uses `-5v`: `-5 · {0, 1, 3} = {0, 3, 1} = {0, 1, 3}`. -/
private def mkSwap : Equiv.Perm (Fin 2 × ZMod 8) where
  toFun p := (⟨1 - p.1.val, by omega⟩, 5 * p.2)
  invFun p := (⟨1 - p.1.val, by omega⟩, 5 * p.2)  -- 5² = 25 = 1 mod 8
  left_inv := by native_decide
  right_inv := by native_decide

/-- Translation preserves MK adjacency. -/
private theorem mkTranslation_adj : ∀ u v : Fin 2 × ZMod 8,
    mobiusKantorVoltage.Adj u v →
    mobiusKantorVoltage.Adj (mkTranslation u) (mkTranslation v) := by
  native_decide

/-- Swap preserves MK adjacency. -/
private theorem mkSwap_adj : ∀ u v : Fin 2 × ZMod 8,
    mobiusKantorVoltage.Adj u v →
    mobiusKantorVoltage.Adj (mkSwap u) (mkSwap v) := by
  native_decide

private def mkG : Subgroup (Equiv.Perm (Fin 2 × ZMod 8)) :=
  Subgroup.closure ({mkTranslation, mkSwap} : Set _)

private noncomputable instance : MulAction mkG (Fin 2 × ZMod 8) :=
  MulAction.compHom _ mkG.subtype

private noncomputable instance : GraphAction mkG (Fin 2 × ZMod 8) mobiusKantorVoltage where
  adj_smul := by
    intro ⟨σ, hσ⟩ u v hadj
    show mobiusKantorVoltage.Adj (σ u) (σ v)
    revert u v
    change ∀ u v, mobiusKantorVoltage.Adj u v → mobiusKantorVoltage.Adj (σ u) (σ v)
    refine Subgroup.closure_induction
      (p := fun σ _ => ∀ u v, mobiusKantorVoltage.Adj u v →
        mobiusKantorVoltage.Adj (σ u) (σ v))
      ?_ ?_ ?_ ?_ hσ
    · intro x hx
      rcases hx with rfl | rfl
      · exact mkTranslation_adj
      · exact mkSwap_adj
    · intro u v h; simpa
    · intro x y _ _ hx hy u v hadj
      simp only [Equiv.Perm.mul_apply]; exact hx _ _ (hy u v hadj)
    · intro x _ hx u v hadj
      let f : { p : (Fin 2 × ZMod 8) × (Fin 2 × ZMod 8) //
                mobiusKantorVoltage.Adj p.1 p.2 } →
              { p : (Fin 2 × ZMod 8) × (Fin 2 × ZMod 8) //
                mobiusKantorVoltage.Adj p.1 p.2 } :=
        fun ⟨⟨a, b⟩, hab⟩ => ⟨⟨x a, x b⟩, hx a b hab⟩
      have hf_surj : Function.Surjective f := Finite.surjective_of_injective (by
        intro ⟨⟨a₁, b₁⟩, _⟩ ⟨⟨a₂, b₂⟩, _⟩ h
        simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at h
        exact Subtype.ext (Prod.ext (x.injective h.1) (x.injective h.2)))
      obtain ⟨⟨⟨a, b⟩, hab⟩, heq⟩ := hf_surj ⟨⟨u, v⟩, hadj⟩
      simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at heq
      rw [show a = x⁻¹ u from by rw [← heq.1]; simp,
          show b = x⁻¹ v from by rw [← heq.2]; simp] at hab
      exact hab

private def mkT_mem : mkTranslation ∈ mkG :=
  Subgroup.subset_closure (Set.mem_insert _ _)

private def mkS_mem : mkSwap ∈ mkG :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

private def mkWitElem : Fin 2 × ZMod 8 → Equiv.Perm (Fin 2 × ZMod 8)
  | (⟨0, _⟩, g) => mkTranslation ^ g.val
  | (⟨1, _⟩, g) => mkTranslation ^ g.val * mkSwap

private theorem mkWitElem_correct :
    ∀ v : Fin 2 × ZMod 8,
      mkWitElem v ((0 : Fin 2), (0 : ZMod 8)) = v := by native_decide

private theorem mkWitElem_mem (v : Fin 2 × ZMod 8) : mkWitElem v ∈ mkG := by
  rcases v with ⟨⟨i, hi⟩, g⟩
  interval_cases i
  · exact mkG.pow_mem mkT_mem _
  · exact mkG.mul_mem (mkG.pow_mem mkT_mem _) mkS_mem

private noncomputable instance : MulAction.IsPretransitive mkG (Fin 2 × ZMod 8) where
  exists_smul_eq := by
    intro x y
    have hmem : (mkWitElem x).symm.trans (mkWitElem y) ∈ mkG :=
      mkG.mul_mem (mkWitElem_mem y) (mkG.inv_mem (mkWitElem_mem x))
    exact ⟨⟨_, hmem⟩, by
      change ((mkWitElem x).symm.trans (mkWitElem y)) x = y
      simp only [Equiv.trans_apply]
      rw [show (mkWitElem x).symm x = ((0 : Fin 2), (0 : ZMod 8)) from by
        rw [Equiv.symm_apply_eq]; exact (mkWitElem_correct x).symm]
      exact mkWitElem_correct y⟩

/-- **The Möbius-Kantor graph is a Sabidussi coset graph.**

The dihedral group D₁₆ = ⟨translation, swap⟩ acts vertex-transitively, giving:
  `mobiusKantorVoltage ≃g Sab(D₁₆, {1}, D)` (a Cayley graph). -/
noncomputable def mkSabidussiIso :
    mobiusKantorVoltage ≃g SimpleGraph.cosetGraph
      (MulAction.stabilizer mkG ((0 : Fin 2), (0 : ZMod 8)))
      (connectionSet mkG mobiusKantorVoltage ((0 : Fin 2), (0 : ZMod 8)))
      (connectionSet.isConnectionSet _) :=
  sabidussiIso _

end MKSabidussi
