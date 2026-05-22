/-
Copyright (c) 2026 Robin Langer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Langer
-/
import Mathlib.Combinatorics.SimpleGraph.QuotientGraph
import Mathlib.Combinatorics.SimpleGraph.Action
import Mathlib.Combinatorics.SimpleGraph.Representation

/-!
# Named graphs and antipodal quotients

The dodecahedron has an antipodal involution (distance 5) whose quotient is the
Petersen graph. The 3-cube has an antipodal involution (bitwise complement, distance 3)
whose quotient is K₄.

## Main definitions

* `dodecahedronGraph` — the dodecahedron on `Fin 20`, 3-regular, 30 edges
* `petersenGraph` — the Petersen graph on `Fin 10`, as `dodecahedronGraph.quotientGraph`
* `cubeGraph` — the 3-cube Q₃ on `Fin 8`, 3-regular, 12 edges

## Main results

* `dodecahedronGraph_regular` — the dodecahedron is 3-regular
* `petersenGraph_regular` — the Petersen graph is 3-regular
* `cubeQuotient_eq_top` — the antipodal quotient of the cube is K₄

## Visualizations

* [Dodecahedron → Petersen quotient](https://raw.githubusercontent.com/RaggedR/symmetric-graphs/main/lean/named_graphs/dodecahedron-quotient-petersen.jpeg) — the Z₂ antipodal quotient, with fibers color-coded

## References

* Robin Langer, *Symmetric Graphs and their Quotients*, arXiv:1306.4798
-/

set_option linter.style.nativeDecide false

open SimpleGraph

/-! ### The dodecahedron graph -/

private def dodecAdjBool (u v : Fin 20) : Bool :=
  let edges : List (Fin 20 × Fin 20) := [
    (0, 1), (0, 4), (0, 5), (1, 2), (1, 7), (2, 3), (2, 9), (3, 4), (3, 11), (4, 13),
    (5, 6), (5, 14), (6, 7), (6, 15), (7, 8), (8, 9), (8, 16), (9, 10), (10, 11), (10, 17),
    (11, 12), (12, 13), (12, 18), (13, 14), (14, 19), (15, 16), (15, 19), (16, 17), (17, 18),
    (18, 19)]
  edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **dodecahedron graph**, the 1-skeleton of the regular dodecahedron. -/
def dodecahedronGraph : SimpleGraph (Fin 20) where
  Adj u v := dodecAdjBool u v
  symm u v := by simp only [dodecAdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [dodecAdjBool]; revert u; native_decide⟩

instance : DecidableRel dodecahedronGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (dodecAdjBool u v))

/-! ### The antipodal quotient map -/

private def dodecAntipodalData : List (Fin 10) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 6, 7, 8, 9, 3, 4, 0, 1, 2]

private theorem dodecAntipodalData_length : dodecAntipodalData.length = 20 := by native_decide

/-- The antipodal quotient map: `Fin 20 → Fin 10`. -/
def dodecAntipodalMap (v : Fin 20) : Fin 10 :=
  dodecAntipodalData.get (v.cast dodecAntipodalData_length.symm)

/-! ### The Petersen graph -/

/-- The **Petersen graph**, the antipodal quotient of the dodecahedron. -/
def petersenGraph : SimpleGraph (Fin 10) :=
  dodecahedronGraph.quotientGraph dodecAntipodalMap

instance : DecidableRel petersenGraph.Adj := by
  intro i j; unfold petersenGraph quotientGraph; simp only; exact instDecidableAnd

/-- The dodecahedron is 3-regular. -/
theorem dodecahedronGraph_regular :
    ∀ v : Fin 20, (Finset.univ.filter fun w => dodecahedronGraph.Adj v w).card = 3 := by
  native_decide

/-- The dodecahedron has 30 edges. -/
theorem dodecahedronGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 20 × Fin 20 =>
      p.1 < p.2 ∧ dodecahedronGraph.Adj p.1 p.2).card = 30 := by
  native_decide

/-- The Petersen graph is 3-regular. -/
theorem petersenGraph_regular :
    ∀ v : Fin 10, (Finset.univ.filter fun w => petersenGraph.Adj v w).card = 3 := by
  native_decide

/-- The Petersen graph has 15 edges. -/
theorem petersenGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 10 × Fin 10 =>
      p.1 < p.2 ∧ petersenGraph.Adj p.1 p.2).card = 15 := by
  native_decide

/-! ### The 3-cube graph -/

private def cubeAdjBool (u v : Fin 8) : Bool :=
  let edges : List (Fin 8 × Fin 8) := [
    (0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7),
    (4, 5), (4, 6), (5, 7), (6, 7)]
  edges.any fun (a, b) => (u == a && v == b) || (u == b && v == a)

/-- The **3-cube graph** Q₃, the 1-skeleton of the 3-dimensional hypercube. -/
def cubeGraph : SimpleGraph (Fin 8) where
  Adj u v := cubeAdjBool u v
  symm u v := by simp only [cubeAdjBool]; revert u v; native_decide
  loopless := ⟨fun u => by simp only [cubeAdjBool]; revert u; native_decide⟩

instance : DecidableRel cubeGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (cubeAdjBool u v))

/-! ### The cube antipodal quotient -/

private def cubeAntipodalData : List (Fin 4) := [0, 1, 2, 3, 3, 2, 1, 0]

private theorem cubeAntipodalData_length : cubeAntipodalData.length = 8 := by native_decide

/-- The antipodal quotient map on Q₃: `Fin 8 → Fin 4`. -/
def cubeAntipodalMap (v : Fin 8) : Fin 4 :=
  cubeAntipodalData.get (v.cast cubeAntipodalData_length.symm)

/-- The antipodal quotient of the 3-cube. -/
def cubeQuotientGraph : SimpleGraph (Fin 4) :=
  cubeGraph.quotientGraph cubeAntipodalMap

instance : DecidableRel cubeQuotientGraph.Adj := by
  intro i j; unfold cubeQuotientGraph quotientGraph; simp only; exact instDecidableAnd

/-- The 3-cube is 3-regular. -/
theorem cubeGraph_regular :
    ∀ v : Fin 8, (Finset.univ.filter fun w => cubeGraph.Adj v w).card = 3 := by
  native_decide

/-- The 3-cube has 12 edges. -/
theorem cubeGraph_edgeCount :
    (Finset.univ.filter fun p : Fin 8 × Fin 8 =>
      p.1 < p.2 ∧ cubeGraph.Adj p.1 p.2).card = 12 := by
  native_decide

/-- The antipodal quotient of the 3-cube is 3-regular. -/
theorem cubeQuotientGraph_regular :
    ∀ v : Fin 4, (Finset.univ.filter fun w => cubeQuotientGraph.Adj v w).card = 3 := by
  native_decide

/-- The antipodal quotient of the 3-cube is the complete graph K₄. -/
theorem cubeQuotient_eq_top : cubeQuotientGraph = ⊤ := by
  ext u v; revert u v; native_decide

/-! ## Sabidussi coset graph representations -/

section WordMachinery
variable {n k : ℕ}
private def genOrInv' (gens : Fin k → Equiv.Perm (Fin n)) (i : Fin (2 * k)) :
    Equiv.Perm (Fin n) :=
  if h : i.val < k then gens ⟨i.val, h⟩ else (gens ⟨i.val - k, by omega⟩).symm
private def applyWord' (gens : Fin k → Equiv.Perm (Fin n)) :
    List (Fin (2 * k)) → Equiv.Perm (Fin n)
  | [] => Equiv.refl _
  | i :: rest => (genOrInv' gens i).trans (applyWord' gens rest)
private theorem genOrInv'_mem (gens : Fin k → Equiv.Perm (Fin n)) (i : Fin (2 * k)) :
    genOrInv' gens i ∈ Subgroup.closure (Set.range gens) := by
  unfold genOrInv'; split
  · exact Subgroup.subset_closure ⟨_, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, rfl⟩)
private theorem applyWord'_mem (gens : Fin k → Equiv.Perm (Fin n))
    (w : List (Fin (2 * k))) : applyWord' gens w ∈ Subgroup.closure (Set.range gens) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i rest ih => exact Subgroup.mul_mem _ ih (genOrInv'_mem gens i)
private theorem closureGraphAction {Γ : SimpleGraph (Fin n)}
    (gens : Fin k → Equiv.Perm (Fin n))
    (hadj : ∀ i u v, Γ.Adj u v → Γ.Adj (gens i u) (gens i v))
    (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ Subgroup.closure (Set.range gens))
    (u v : Fin n) (h : Γ.Adj u v) : Γ.Adj (σ u) (σ v) := by
  refine Subgroup.closure_induction
    (p := fun σ _ => ∀ u v, Γ.Adj u v → Γ.Adj (σ u) (σ v)) ?_ ?_ ?_ ?_ hσ u v h
  · intro x ⟨i, hi⟩; subst hi; exact hadj i
  · intro u v h; simpa
  · intro x y _ _ hx hy u v h; simp only [Equiv.Perm.mul_apply]; exact hx _ _ (hy u v h)
  · intro x _ hx u v h
    let f : { p : Fin n × Fin n // Γ.Adj p.1 p.2 } →
            { p : Fin n × Fin n // Γ.Adj p.1 p.2 } :=
      fun ⟨⟨a, b⟩, hab⟩ => ⟨⟨x a, x b⟩, hx a b hab⟩
    have := (Finite.surjective_of_injective (fun ⟨⟨a₁,b₁⟩,_⟩ ⟨⟨a₂,b₂⟩,_⟩ h => by
      simp only [f,Subtype.mk.injEq,Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext (x.injective h.1) (x.injective h.2)))
      : Function.Surjective f) ⟨⟨u,v⟩,h⟩
    obtain ⟨⟨⟨a,b⟩,hab⟩,heq⟩ := this
    simp only [f,Subtype.mk.injEq,Prod.mk.injEq] at heq
    rw [show a = x⁻¹ u from by rw [← heq.1]; simp,
        show b = x⁻¹ v from by rw [← heq.2]; simp] at hab; exact hab
end WordMachinery

section DodecahedronSabidussi
private def dGen1Fwd : Array (Fin 20) := #[1,2,3,4,0,7,8,9,10,11,12,13,14,5,6,16,17,18,19,15]
private def dGen1Inv : Array (Fin 20) := #[4,0,1,2,3,13,14,5,6,7,8,9,10,11,12,19,15,16,17,18]
private def dGen2Fwd : Array (Fin 20) := #[0,4,13,14,5,1,2,3,11,12,18,19,15,6,7,9,10,17,16,8]
private def dGen2Inv : Array (Fin 20) := #[0,5,6,7,1,4,13,14,19,15,16,8,9,2,3,12,18,17,10,11]
private theorem dG1F_s : dGen1Fwd.size = 20 := by native_decide
private theorem dG1I_s : dGen1Inv.size = 20 := by native_decide
private theorem dG2F_s : dGen2Fwd.size = 20 := by native_decide
private theorem dG2I_s : dGen2Inv.size = 20 := by native_decide
private def dG1 : Equiv.Perm (Fin 20) where
  toFun i := dGen1Fwd[i.val]'(by have := dG1F_s; omega)
  invFun i := dGen1Inv[i.val]'(by have := dG1I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def dG2 : Equiv.Perm (Fin 20) where
  toFun i := dGen2Fwd[i.val]'(by have := dG2F_s; omega)
  invFun i := dGen2Inv[i.val]'(by have := dG2I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def dGens : Fin 2 → Equiv.Perm (Fin 20) | 0 => dG1 | 1 => dG2
private def dGroup : Subgroup (Equiv.Perm (Fin 20)) := Subgroup.closure (Set.range dGens)
private def dWitData : Array (List (Fin 4)) := #[
  [],[0],[0,0],[2,2],[2],[0,3],[0,0,3],[0,3,0],[0,0,3,0],[0,3,0,0],
  [0,0,3,0,0],[0,0,1,2],[2,2,1,2],[0,0,1],[2,2,1],
  [0,3,0,0,3],[0,0,3,0,0,3],[0,0,1,2,1,2,2],[0,0,1,2,1,2],[0,0,1,2,1]]
private theorem dWitData_s : dWitData.size = 20 := by native_decide
private def dWit (v : Fin 20) : List (Fin 4) := dWitData[v.val]'(by have := dWitData_s; omega)
private theorem dWit_ok : ∀ v : Fin 20, applyWord' dGens (dWit v) 0 = v := by native_decide
private noncomputable instance : MulAction dGroup (Fin 20) := MulAction.compHom _ dGroup.subtype
private noncomputable instance : GraphAction dGroup (Fin 20) dodecahedronGraph where
  adj_smul g u v h := closureGraphAction dGens
    (fun i => by match i with | 0 => exact (by native_decide) | 1 => exact (by native_decide))
    g.1 g.2 u v h
private noncomputable instance : MulAction.IsPretransitive dGroup (Fin 20) where
  exists_smul_eq x y := ⟨⟨_, dGroup.mul_mem (applyWord'_mem dGens _)
    (dGroup.inv_mem (applyWord'_mem dGens _))⟩, by
    change ((applyWord' dGens (dWit x)).symm.trans (applyWord' dGens (dWit y))) x = y
    simp only [Equiv.trans_apply]
    rw [show (applyWord' dGens (dWit x)).symm x = 0 from by
      rw [Equiv.symm_apply_eq]; exact (dWit_ok x).symm]; exact dWit_ok y⟩

/-- **The dodecahedron is a Sabidussi coset graph**: `Sab(A₅, C₃, D)`. -/
noncomputable def dodecahedronSabidussiIso :
    dodecahedronGraph ≃g SimpleGraph.cosetGraph (MulAction.stabilizer dGroup (0 : Fin 20))
      (connectionSet dGroup dodecahedronGraph 0) (connectionSet.isConnectionSet 0) :=
  sabidussiIso 0
end DodecahedronSabidussi

section CubeSabidussi
private def cG1F : Array (Fin 8) := #[2,3,6,7,0,1,4,5]
private def cG1I : Array (Fin 8) := #[4,5,0,1,6,7,2,3]
private def cG2F : Array (Fin 8) := #[0,2,4,6,1,3,5,7]
private def cG2I : Array (Fin 8) := #[0,4,1,5,2,6,3,7]
private theorem cG1F_s : cG1F.size = 8 := by native_decide
private theorem cG1I_s : cG1I.size = 8 := by native_decide
private theorem cG2F_s : cG2F.size = 8 := by native_decide
private theorem cG2I_s : cG2I.size = 8 := by native_decide
private def cG1 : Equiv.Perm (Fin 8) where
  toFun i := cG1F[i.val]'(by have := cG1F_s; omega)
  invFun i := cG1I[i.val]'(by have := cG1I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def cG2 : Equiv.Perm (Fin 8) where
  toFun i := cG2F[i.val]'(by have := cG2F_s; omega)
  invFun i := cG2I[i.val]'(by have := cG2I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def cGens : Fin 2 → Equiv.Perm (Fin 8) | 0 => cG1 | 1 => cG2
private def cGroup : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.closure (Set.range cGens)
private def cWitData : Array (List (Fin 4)) := #[[],[0,3],[0],[0,0,3],[2],[0,0,1],[0,0],[0,0,1,2]]
private theorem cWitData_s : cWitData.size = 8 := by native_decide
private def cWit (v : Fin 8) : List (Fin 4) := cWitData[v.val]'(by have := cWitData_s; omega)
private theorem cWit_ok : ∀ v : Fin 8, applyWord' cGens (cWit v) 0 = v := by native_decide
private noncomputable instance : MulAction cGroup (Fin 8) := MulAction.compHom _ cGroup.subtype
private noncomputable instance : GraphAction cGroup (Fin 8) cubeGraph where
  adj_smul g u v h := closureGraphAction cGens
    (fun i => by match i with | 0 => exact (by native_decide) | 1 => exact (by native_decide))
    g.1 g.2 u v h
private noncomputable instance : MulAction.IsPretransitive cGroup (Fin 8) where
  exists_smul_eq x y := ⟨⟨_, cGroup.mul_mem (applyWord'_mem cGens _)
    (cGroup.inv_mem (applyWord'_mem cGens _))⟩, by
    change ((applyWord' cGens (cWit x)).symm.trans (applyWord' cGens (cWit y))) x = y
    simp only [Equiv.trans_apply]
    rw [show (applyWord' cGens (cWit x)).symm x = 0 from by
      rw [Equiv.symm_apply_eq]; exact (cWit_ok x).symm]; exact cWit_ok y⟩

/-- **The 3-cube is a Sabidussi coset graph**: `Sab(S₄, C₃, D)`. -/
noncomputable def cubeSabidussiIso :
    cubeGraph ≃g SimpleGraph.cosetGraph (MulAction.stabilizer cGroup (0 : Fin 8))
      (connectionSet cGroup cubeGraph 0) (connectionSet.isConnectionSet 0) :=
  sabidussiIso 0
end CubeSabidussi

section PetersenSabidussi
private def pG1F : Array (Fin 10) := #[2,1,7,6,3,9,5,0,4,8]
private def pG1I : Array (Fin 10) := #[7,1,0,4,8,6,3,2,9,5]
private def pG2F : Array (Fin 10) := #[3,4,0,5,6,2,9,8,7,1]
private def pG2I : Array (Fin 10) := #[2,9,5,0,1,3,4,8,7,6]
private theorem pG1F_s : pG1F.size = 10 := by native_decide
private theorem pG1I_s : pG1I.size = 10 := by native_decide
private theorem pG2F_s : pG2F.size = 10 := by native_decide
private theorem pG2I_s : pG2I.size = 10 := by native_decide
private def pG1 : Equiv.Perm (Fin 10) where
  toFun i := pG1F[i.val]'(by have := pG1F_s; omega)
  invFun i := pG1I[i.val]'(by have := pG1I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def pG2 : Equiv.Perm (Fin 10) where
  toFun i := pG2F[i.val]'(by have := pG2F_s; omega)
  invFun i := pG2I[i.val]'(by have := pG2I_s; omega)
  left_inv := by native_decide
  right_inv := by native_decide
private def pGens : Fin 2 → Equiv.Perm (Fin 10) | 0 => pG1 | 1 => pG2
private def pGroup : Subgroup (Equiv.Perm (Fin 10)) := Subgroup.closure (Set.range pGens)
private def pWD : Array (List (Fin 4)) :=
  #[[], [1,2,3], [0], [1], [1,2], [0,3], [1,0], [2], [2,1], [0,3,0]]
private theorem pWD_s : pWD.size = 10 := by native_decide
private def pWit (v : Fin 10) : List (Fin 4) := pWD[v.val]'(by have := pWD_s; omega)
private theorem pWit_ok :
    ∀ v : Fin 10, applyWord' pGens (pWit v) 0 = v := by native_decide
private noncomputable instance : MulAction pGroup (Fin 10) := MulAction.compHom _ pGroup.subtype
private noncomputable instance : GraphAction pGroup (Fin 10) petersenGraph where
  adj_smul g u v h := closureGraphAction pGens
    (fun i => by match i with | 0 => exact (by native_decide) | 1 => exact (by native_decide))
    g.1 g.2 u v h
private noncomputable instance : MulAction.IsPretransitive pGroup (Fin 10) where
  exists_smul_eq x y :=
    ⟨⟨_, pGroup.mul_mem (applyWord'_mem pGens _) (pGroup.inv_mem (applyWord'_mem pGens _))⟩, by
      change ((applyWord' pGens (pWit x)).symm.trans (applyWord' pGens (pWit y))) x = y
      simp only [Equiv.trans_apply]
      rw [show (applyWord' pGens (pWit x)).symm x = 0 from by
        rw [Equiv.symm_apply_eq]; exact (pWit_ok x).symm]; exact pWit_ok y⟩

/-- **The Petersen graph is a Sabidussi coset graph**: `Sab(S₅, S₂×S₃, D)`. -/
noncomputable def petersenSabidussiIso :
    petersenGraph ≃g SimpleGraph.cosetGraph (MulAction.stabilizer pGroup (0 : Fin 10))
      (connectionSet pGroup petersenGraph 0) (connectionSet.isConnectionSet 0) :=
  sabidussiIso 0
end PetersenSabidussi
