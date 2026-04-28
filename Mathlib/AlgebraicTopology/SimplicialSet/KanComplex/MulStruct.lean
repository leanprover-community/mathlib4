/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism

/-!
# Pointed simplices

Given a simplicial set `X`, `n : ℕ` and `x : X _⦋0⦌`, we introduce the
type `X.PtSimplex n x` of morphisms `Δ[n] ⟶ X` which send `∂Δ[n]` to `x`.
We introduce structures `PtSimplex.RelStruct` and `PtSimplex.MulStruct`
which will be used in the definition of homotopy groups of Kan complexes.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial
namespace SSet

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

/-- The bijection between `n`-simplices of `X.op` and of `X`
that are constant on the boundary. -/
@[simps]
def opEquiv : X.op.PtSimplex n (opObjEquiv.symm x) ≃ X.PtSimplex n x where
  toFun f :=
    { map := yonedaEquiv.symm (opObjEquiv (yonedaEquiv f.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i ↦ ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm,
            δ_opObjEquiv, ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_yonedaEquiv_const]}
  invFun g :=
    { map := yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv g.map))
      comm := by
        obtain _ | n := n
        · ext
        · refine boundary.hom_ext (fun i ↦ ?_)
          simp [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ,
            ← stdSimplex.yonedaEquiv_δ_comp,
            opObjEquiv_symm_yonedaEquiv_const] }
  left_inv _ := by simp
  right_inv _ := by simp

/-- Given a `n`-simplex of `X` that is constant on the boundary, this
is the corresponding `n`-simplex of `X.op`. -/
abbrev op (f : X.PtSimplex n x) : X.op.PtSimplex n (opObjEquiv.symm x) :=
  opEquiv.symm f

/-- Given a `n`-simplex of `X.op` that is constant on the boundary, this
is the corresponding `n`-simplex of `X`. -/
abbrev unop (f : X.op.PtSimplex n (opObjEquiv.symm x)) : X.PtSimplex n x :=
  opEquiv f

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

/-- The `Mulstruct` for `X.op` that is deduced from a `Mulstruct` for the simplicial
set `X`. -/
def op {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct f g fg i) {j : Fin n}
    (hij : i.rev = j := by grind) :
    MulStruct g.op f.op fg.op j where
  map := yonedaEquiv.symm (opObjEquiv.symm (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ, Equiv.apply_symm_apply,
      ← stdSimplex.yonedaEquiv_δ_comp, opEquiv_symm_apply_map, ← h.δ_succ_succ_map,
      Fin.rev_castSucc, Fin.rev_castSucc, ← hij, Fin.rev_rev]
  δ_succ_castSucc_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ, Equiv.apply_symm_apply,
      ← stdSimplex.yonedaEquiv_δ_comp, opEquiv_symm_apply_map, ← h.δ_succ_castSucc_map,
      Fin.rev_succ, Fin.rev_castSucc, Fin.castSucc_succ, ← hij, Fin.rev_rev]
  δ_succ_succ_map := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, op_δ, Equiv.apply_symm_apply,
      ← stdSimplex.yonedaEquiv_δ_comp, opEquiv_symm_apply_map, ← h.δ_castSucc_castSucc_map,
      Fin.rev_succ, Fin.rev_succ, ← hij, Fin.rev_rev]
  δ_map_of_lt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_gt k.rev (by grind)]
  δ_map_of_gt k hk := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, ← stdSimplex.yonedaEquiv_δ_comp,
      opObjEquiv_symm_yonedaEquiv_const, h.δ_map_of_lt k.rev (by grind)]

/-- The `Mulstruct` for a simplicial set `X` that is deduced from a `Mulstruct` for `X.op`. -/
def unop {f g fg : X.PtSimplex n x} {i : Fin n} (h : MulStruct g.op f.op fg.op i) {j : Fin n}
    (hij : i.rev = j := by grind) :
    MulStruct f g fg j where
  map := yonedaEquiv.symm (opObjEquiv (yonedaEquiv h.map))
  δ_castSucc_castSucc_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_castSucc]
  δ_succ_castSucc_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_castSucc, Fin.rev_succ]
  δ_succ_succ_map := by
    simp [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, ← hij, Fin.rev_succ]
  δ_map_of_lt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, h.δ_map_of_gt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]
  δ_map_of_gt k hk := by
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, δ_opObjEquiv,
      ← stdSimplex.yonedaEquiv_δ_comp, h.δ_map_of_lt _ (by grind)]
    simp [opObjEquiv_yonedaEquiv_const]

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
        exacts [h.δ_succ_succ_map, h.δ_map_of_gt j hj] }

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
        obtain rfl | hj := (Fin.le_castSucc_iff.mpr hj).eq_or_lt
        exacts [h.δ_castSucc_castSucc_map, h.δ_map_of_lt j hj] }

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

end MulStruct

end PtSimplex

end SSet
