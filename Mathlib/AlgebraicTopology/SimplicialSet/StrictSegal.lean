/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Path
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Strict Segal simplicial sets

A simplicial set `X` satisfies the `StrictSegal` condition if for all `n`, the map
`X.spine n : X _[n] → X.Path n` is a bijection.

Examples of `StrictSegal` simplicial sets are given by nerves of categories.

TODO: Show that these are the only examples: that a `StrictSegal` simplicial set is isomorphic to
the nerve of its homotopy category.

`StrictSegal` simplicial sets have an important property of being 2-coskeletal.

-/

universe v u

open CategoryTheory

open Simplicial SimplexCategory

namespace SSet

variable (X : SSet.{u})

/-- A simplicial set `X` satisfies the strict Segal condition if its simplices are uniquely
determined by their spine. -/
class StrictSegal : Prop where
  segal : ∀ (n : ℕ), Function.Bijective (X.spine n)

variable {X} in
/-- The diagonal of a simplex is the long edge of the simplex.-/
def diagonal {n : ℕ} (Δ : X _[n]) : X _[1] := X.map ((mkOfDiag n).op) Δ

namespace StrictSegal
variable {X : SSet.{u}} [StrictSegal X] {n : ℕ}

/-- In the presence of the strict Segal condition, a path of length `n` extends to an `n`-simplex
whose spine is that path. -/
noncomputable def spineToSimplex : Path X n → X _[n] :=
  (Equiv.ofBijective _ (segal n)).invFun

@[simp]
theorem spineToSimplex_spine (f : Path X n) :
    X.spine n (StrictSegal.spineToSimplex f) = f :=
  (Equiv.ofBijective _ (segal n)).right_inv f

@[simp]
theorem spineToSimplex_vertex (i : Fin (n + 1)) (f : Path X n) :
    X.map (const [0] [n] i).op (spineToSimplex f) = f.vertex i := by
  rw [← spine_vertex, spineToSimplex_spine]

@[simp]
theorem spineToSimplex_spine_edge (i : Fin n) (f : Path X n) :
    X.map (mkOfSucc i).op (spineToSimplex f) = f.arrow i := by
  rw [← spine_arrow, spineToSimplex_spine]


/-- In the presence of the strict Segal condition, a path of length `n` can be "composed" by taking
the diagonal edge of the resulting `n`-simplex. -/
noncomputable def spineToDiagonal (f : Path X n) : X _[1] := diagonal (spineToSimplex f)

@[simp]
theorem spineToSimplex_interval (f : Path X n) (j l : ℕ) (hjl : j + l < n + 1)  :
    X.map (subinterval j l hjl).op (spineToSimplex f) =
      spineToSimplex (Path.interval f j l hjl) := by
  apply (segal _).injective
  rw [StrictSegal.spineToSimplex_spine]
  ext i
  · unfold Path.interval
    simp only [mkHom, Equiv.invFun_as_coe, spine_vertex, Fin.coe_addNat]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    simp only [const_comp, len_mk]
    unfold subinterval
    simp only [spineToSimplex_vertex]
    congr 1
    apply Fin.eq_of_val_eq
    simp only [mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk, Fin.val_natCast]
    have : (i.1 + j) % (n + 1) = i.1 + j := by exact Nat.mod_eq_of_lt (by omega)
    rw [this]
  · unfold Path.interval
    simp only [Equiv.invFun_as_coe, spine_arrow, Fin.coe_addNat]
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    have ceq : mkOfSucc i ≫ subinterval j l hjl = mkOfSucc ⟨i + j, (by omega)⟩ := by
      ext ⟨e, he⟩ : 3
      unfold subinterval
      match e with
      | 0 => rfl
      | 1 => ?_
      conv_rhs =>
        apply mkOfSucc_homToOrderHom_one
      simp only [len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, Fin.mk_one,
        Fin.isValue, OrderHom.comp_coe, OrderHom.coe_mk, Function.comp_apply, Fin.succ_mk,
        Fin.mk.injEq]
      exact Nat.succ_add_eq_add_succ ↑i ↑j
    rw [ceq]
    simp only [spineToSimplex_spine_edge]

@[simp]
theorem spineToSimplex_edge (f : Path X n) (j l : ℕ) (hn : j + l < n + 1) :
    X.map (mkOfLe ⟨j, (by omega)⟩ ⟨j + l, hn⟩ (Nat.le_add_right j l)).op (spineToSimplex f) =
      spineToDiagonal (Path.interval f j l hn) := by
  unfold spineToDiagonal
  rw [← congrArg diagonal (spineToSimplex_interval f j l hn)]
  unfold diagonal
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  have : mkOfLe ⟨j, (by omega)⟩ ⟨j + l, hn⟩ (Nat.le_add_right j l) =
      mkOfDiag l ≫ subinterval j l hn := by
    ext e : 3
    unfold subinterval mkOfDiag mkOfLe
    simp only [len_mk, Nat.reduceAdd, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk,
      Fin.natCast_eq_last, comp_toOrderHom, OrderHom.mk_comp_mk, Function.comp_apply]
    match e with
    | 0 => simp
    | 1 =>
    apply Fin.eq_of_val_eq
    simp only [Fin.isValue, Fin.val_last]
    exact Nat.add_comm j l
  rw [this]

end StrictSegal

end SSet

namespace Nerve

open SSet

variable {C : Type*} [Category C] {n : ℕ}

/-- Simplices in the nerve of categories are uniquely determined by their spine. Indeed, this
property describes the essential image of the nerve functor.-/
instance strictSegal (C : Type u) [Category.{v} C] : StrictSegal (nerve C) where
  segal n := by
    constructor
    · intro Δ Δ' h
      exact ComposableArrows.ext
        (fun i ↦ Functor.congr_obj (congr_fun (congr_arg Path.vertex h) i) 0)
        (fun i hi ↦
          Functor.congr_hom (congr_fun (congr_arg Path.arrow h) ⟨i, hi⟩) (show 0 ⟶ 1 by tauto))
    · intro F
      refine ⟨ComposableArrows.mkOfObjOfMapSucc (fun i ↦ (F.vertex i).obj 0)
        (fun i ↦ eqToHom (Functor.congr_obj (F.arrow_src i).symm 0) ≫
          (F.arrow i).map' 0 1 ≫ eqToHom (Functor.congr_obj (F.arrow_tgt i) 0)), ?_⟩
      ext i
      · exact ComposableArrows.ext₀ rfl
      · refine ComposableArrows.ext₁ ?_ ?_ ?_
        · exact Functor.congr_obj (F.arrow_src i).symm 0
        · exact Functor.congr_obj (F.arrow_tgt i).symm 0
        · dsimp
          apply ComposableArrows.mkOfObjOfMapSucc_map_succ

end Nerve

namespace SSet

open Opposite CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion (n := 2)).op`.-/
@[simps!]
def rightExtensionInclusion (X : SSet.{u}) (n : ℕ) :
    RightExtension (Truncated.inclusion (n := n)).op
      (Functor.op Truncated.inclusion ⋙ X) := RightExtension.mk _ (𝟙 _)

section

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))

/-- The object of `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` corresponding to the
map [0] ⟶ [n] with image `i`. -/
private
def pt {n} (i : Fin (n + 1)) : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
  .mk (Y := op [0]₂) (.op (SimplexCategory.const _ _ i))

/-- The object of `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` corresponding to
the map `[1] ⟶ [n]` with image `i ⟶ i+1`. -/
private
def ar {n} (i : Fin n) : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
  .mk (Y := op [1]₂) (.op (mkOfLe _ _ (Fin.castSucc_le_succ i)))

/-- The object of StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op corresponding to
`ar k`. -/
private
def ar' {n} {i j : Fin (n+1)} (k : i ⟶ j) :
    StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
  .mk (Y := op [1]₂) (mkOfLe _ _ k.le).op

/-- An arrow in `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` arising from
`const 0 : [0] ⟶ [1]`. -/
private
def ar.src {n} (i : Fin n) : (ar i) ⟶ (pt i.castSucc) := by
  refine StructuredArrow.homMk (.op (SimplexCategory.const _ _ 0)) ?_
  apply Quiver.Hom.unop_inj
  ext z; revert z
  intro (0 : Fin 1)
  unfold ar pt
  simp only [StructuredArrow.mk_left, const_obj_obj, len_mk, StructuredArrow.mk_right, op_obj,
    StructuredArrow.mk_hom_eq_self, Fin.isValue, op_map, Quiver.Hom.unop_op, unop_comp,
    comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  rfl

/-- An arrow in `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` arising from
`const 1 : [0] ⟶ [1]`. -/
private
def ar.tgt {n} (i : Fin n) : (ar i) ⟶ (pt i.succ) := by
  refine StructuredArrow.homMk (.op (SimplexCategory.const _ _ 1)) ?_
  apply Quiver.Hom.unop_inj
  ext z; revert z
  intro (0 : Fin 1)
  unfold ar pt
  simp only [StructuredArrow.mk_left, const_obj_obj, len_mk, StructuredArrow.mk_right, op_obj,
    StructuredArrow.mk_hom_eq_self, Fin.isValue, op_map, Quiver.Hom.unop_op, unop_comp,
    comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  rfl

theorem ran.lift.arrow_src {X : SSet.{u}} {n} {i : Fin n}
    (s : Cone (StructuredArrow.proj (op [n]) (Truncated.inclusion (n := 2)).op ⋙
      (Truncated.inclusion (n := 2)).op ⋙ X)) (x : s.pt) :
    X.δ 1 (s.π.app (ar i) x) = s.π.app (pt i.castSucc) x := by
  have hi := congr_fun (s.π.naturality (ar.src i)) x
  unfold hom at hi
  simp at hi
  rw [hi]
  simp [ar.src, Truncated.inclusion]
  have : δ 1 = [0].const [1] 0 := SimplexCategory.eq_const_of_zero _
  rw [← this]
  rfl

theorem ran.lift.arrow_tgt {X : SSet.{u}} {n} {i : Fin n}
    (s : Cone (StructuredArrow.proj (op [n]) (Truncated.inclusion (n := 2)).op ⋙
      (Truncated.inclusion (n := 2)).op ⋙ X)) (x : s.pt) :
    X.δ 0 (s.π.app (ar i) x) = s.π.app (pt i.succ) x := by
  have hi := congr_fun (s.π.naturality (ar.tgt i)) x
  simp at hi
  rw [hi]
  simp [ar.tgt, Truncated.inclusion]
  have : δ 0 = [0].const [1] 1 := SimplexCategory.eq_const_of_zero _
  rw [← this]
  rfl

/-- An object `j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op`, corresponding to a
map `j.right.unop.obj ⟶ [n]` in the simplex category, defines a morphism
`Fin (jlen+1) -> Fin(n+1)`. This calculates the image of `i : Fin(jlen+1)`, which we might think of
as j(i).-/
private
def strArr.homEv {n} (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin (j.right.unop.obj.len + 1)) :
    Fin (n + 1) := (SimplexCategory.Hom.toOrderHom j.hom.unop) i

/-- This is the unique arrow in `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` from
`j` to `j ⟶ (pt (strArr.homEv j i))`. This is used to prove that ran.lift defines a factorization
on objects.-/
private
def fact.obj.arr {n}
    (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin (j.right.unop.obj.len + 1)) : j ⟶ (pt (strArr.homEv j i)) :=
  StructuredArrow.homMk (.op (SimplexCategory.const _ _ i)) <| by
    apply Quiver.Hom.unop_inj
    ext z; revert z; intro | 0 => rfl

/-- An object `j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op`, corresponding to a
map `j.right.unop.obj ⟶ [n]` in the simplex category, defines a morphism
`Fin (jlen+1) -> Fin(n+1)`. This calculates the image of `i.succ : Fin(jlen+1)`, which we might
think of as j(i.succ). -/
private
def strArr.homEvSucc {n} (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin j.right.unop.obj.len) :
    Fin (n + 1) := (SimplexCategory.Hom.toOrderHom j.hom.unop) i.succ

/-- The unique arrow `(strArr.homEv j i.castSucc) ⟶ (strArr.homEvSucc j i)` in `Fin(n+1)`. -/
private
def strArr.homEv.map {n} (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin j.right.unop.obj.len) :
    strArr.homEv j i.castSucc ⟶ strArr.homEvSucc j i :=
  (Monotone.functor (j.hom.unop.toOrderHom).monotone).map (Fin.hom_succ i)

/-- This is the unique arrow in `StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op` from
`j` to `ar' (strArr.homEv.map j i)`. This is used to prove that ran.lift defines a
factorization on maps.-/
private
def fact.map.arr {n}
    (j : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op)
    (i : Fin (unop j.right).1.len) : j ⟶ ar' (strArr.homEv.map j i) := by
  fapply StructuredArrow.homMk
  · exact .op (mkOfSucc i : [1] ⟶ [(unop j.right).1.len])
  · apply Quiver.Hom.unop_inj
    ext z; revert z
    intro |0 | 1 => rfl

/-- Given a term in the cone over the diagram `(StructuredArrow.proj (op [n])`
`(Truncated.inclusion (n := 2)).op ⋙ (Truncated.inclusion (n := 2)).op ⋙ X)` where `X` is
Strict Segal, one can produce an `n`-simplex in `X`.-/
@[simp]
private
noncomputable def ran.lift {X : SSet.{u}} [StrictSegal X] {n}
    (s : Cone (StructuredArrow.proj (op [n]) (Truncated.inclusion (n := 2)).op ⋙
      (Truncated.inclusion (n := 2)).op ⋙ X)) (x : s.pt) : X _[n] :=
  StrictSegal.spineToSimplex {
    vertex := fun i ↦ s.π.app (pt i) x
    arrow := fun i ↦ s.π.app (ar i) x
    arrow_src := fun _ ↦ ran.lift.arrow_src s x
    arrow_tgt := fun _ ↦ ran.lift.arrow_tgt s x
  }

/-- This theorem is used to prove the factorization property of `ran.lift`.-/
theorem ran.lift.map {X : SSet.{u}} [StrictSegal X] {n}
    (s : Cone (StructuredArrow.proj (op [n])
    (Truncated.inclusion (n := 2)).op ⋙ (Truncated.inclusion (n := 2)).op ⋙ X)) (x : s.pt)
    (j k : Fin (n + 1)) (hjk : j ⟶ k) :
      X.map (mkOfLe j k hjk.le).op (ran.lift s x) = s.π.app (ar' hjk) x := by
  have ⟨i, hi⟩ : ∃ (i : ℕ), k.1 = j.1 + i := by
    use k.1 - j.1
    simp [Nat.add_sub_cancel' hjk.le, hjk.le]
  induction i generalizing k with
  | zero =>
    simp [Fin.val_inj] at hi; cases hi
    have ceq : mkOfLe j j (by omega) = [1].const [0] 0 ≫ [0].const [n] j := Hom.ext_one_left ..
    rw [ceq]
    let map : pt j ⟶ ar' hjk := by
      refine StructuredArrow.homMk ([1].const [0] 0).op ?_
      unfold pt ar'
      dsimp only [StructuredArrow.mk_left, const_obj_obj, Fin.val_zero, Nat.add_zero, id_eq,
        Int.reduceNeg, Int.Nat.cast_ofNat_Int, Int.reduceAdd, Fin.eta, homOfLE_refl,
        StructuredArrow.mk_right, op_obj, StructuredArrow.mk_hom_eq_self, Fin.isValue, op_map]
      rw [ceq]
      rfl
    have nat := congr_fun (s.π.naturality map) x
    dsimp only [Fin.val_zero, Nat.add_zero, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int,
      Int.reduceAdd, Fin.eta, comp_obj, StructuredArrow.proj_obj, op_obj, const_obj_obj,
      const_obj_map, types_comp_apply, types_id_apply, Functor.comp_map, StructuredArrow.proj_map,
      op_map] at nat
    rw [nat]
    simp only [map, StructuredArrow.homMk_right]
    rw [op_comp, Functor.map_comp]
    simp only [types_comp_apply]
    refine congrArg (X.map ([1].const [0] 0).op) ?_
    rw [ran.lift, StrictSegal.spineToSimplex_vertex]
  | succ i ih =>
    obtain ⟨k₀, rfl⟩ : ∃ k₀ : Fin n, k = Fin.succ k₀ := by
      let ⟨k+1, hk⟩ := k
      exact ⟨⟨k, Nat.lt_of_succ_lt_succ hk⟩, rfl⟩
    have hjk₀ : j.1 ≤ k₀.1 := by
      rw [Nat.succ_inj.1 hi]
      exact Nat.le_add_right ..
    let tri : ([2] : SimplexCategory) ⟶ [n] :=
      mkOfLeComp j k₀.castSucc k₀.succ hjk₀ (Nat.le_succ _)
    let tri' : StructuredArrow (op [n]) (Truncated.inclusion (n := 2)).op :=
      .mk (Y := op [2]₂) tri.op
    let facemap₂ : tri' ⟶ ar' (hjk₀.hom (y := k₀.castSucc)) := by
      refine StructuredArrow.homMk (.op (δ 2)) ?_
      dsimp [tri', tri, ar']
      rw [← op_comp]
      apply Quiver.Hom.unop_inj
      exact Hom.ext_one_left ..
    let facemap₀ : tri' ⟶ ar k₀ :=
      StructuredArrow.homMk (.op (δ 0)) (Quiver.Hom.unop_inj (Hom.ext_one_left ..))
    let facemap₁ : tri' ⟶ ar' hjk :=
      StructuredArrow.homMk (.op (δ 1)) (Quiver.Hom.unop_inj (Hom.ext_one_left ..))
    let tri₀ : tri' ⟶ pt j :=
      StructuredArrow.homMk (.op (const [0] _ 0)) (Quiver.Hom.unop_inj (Hom.ext_zero_left ..))
    let tri₁ : tri' ⟶ pt k₀.castSucc :=
      StructuredArrow.homMk (.op (const [0] _ 1)) (Quiver.Hom.unop_inj (Hom.ext_zero_left ..))
    let tri₂ : tri' ⟶ pt k₀.succ :=
      StructuredArrow.homMk (.op (const [0] _ 2)) (Quiver.Hom.unop_inj (Hom.ext_zero_left ..))
    have nat := congr_fun (s.π.naturality facemap₁) x
    simp only [Int.reduceNeg, id_eq, Int.Nat.cast_ofNat_Int, homOfLE_leOfHom,
      comp_obj, StructuredArrow.proj_obj, op_obj, const_obj_obj, const_obj_map, types_comp_apply,
      types_id_apply, Functor.comp_map, StructuredArrow.proj_map, op_map] at nat
    rw [nat]
    unfold facemap₁
    simp only [StructuredArrow.homMk_right, Quiver.Hom.unop_op]
    rw [show mkOfLe _ _ hjk.le = (δ 1) ≫ tri from Hom.ext_one_left .., op_comp, Functor.map_comp]
    refine congrArg (X.map (δ 1).op) ?_
    apply (StrictSegal.segal 2).injective
    ext i'
    · simp only [spine_vertex, ← FunctorToTypes.map_comp_apply, ← op_comp]
      rw [show [0].const [2] i' ≫ tri = [0].const [n] (([0].const [2] i' ≫ tri).toOrderHom 0) from
        eq_const_of_zero _]
      simp only [ran.lift, StrictSegal.spineToSimplex_vertex]
      match i' with
      | 0 => exact congr_fun (s.π.naturality tri₀) x
      | 1 => exact congr_fun (s.π.naturality tri₁) x
      | 2 => exact congr_fun (s.π.naturality tri₂) x
    · simp only [spine_arrow, ← FunctorToTypes.map_comp_apply, ← op_comp]
      unfold ran.lift
      match i' with
      | 0 =>
        rw [show mkOfSucc 0 ≫ tri = mkOfLe j k₀.castSucc hjk₀ from Hom.ext_one_left ..]
        have eq' := congr_fun (s.π.naturality facemap₂) x
        unfold facemap₂ at eq'
        simp only [Int.reduceNeg, homOfLE_leOfHom, comp_obj, StructuredArrow.proj_obj, op_obj,
          const_obj_obj, len_mk, Fin.isValue, const_obj_map, types_comp_apply, types_id_apply,
          Functor.comp_map, StructuredArrow.proj_map, StructuredArrow.homMk_right, op_map,
          Quiver.Hom.unop_op] at eq'
        rw [show (δ 2 : [1] ⟶ [2]) = mkOfSucc 0 from Hom.ext_one_left ..] at eq'
        simp [Truncated.inclusion] at eq'
        rw [← eq']
        exact ih k₀.castSucc hjk₀.hom (Nat.succ_inj.1 hi)
      | 1 =>
        rw [show mkOfSucc 1 ≫ tri = mkOfSucc k₀ from Hom.ext_one_left ..]
        simp only [StrictSegal.spineToSimplex_spine_edge]
        have := congr_fun (s.π.naturality facemap₀) x
        dsimp [facemap₀] at this
        rw [this, show (δ 0 : [1] ⟶ [2]) = mkOfSucc 1 from Hom.ext_one_left ..]
        rfl

/-- A strict Segal simplicial set is 2-coskeletal. -/
noncomputable def rightExtensionInclusion₂IsPointwiseRightKanExtensionAt
    (X : SSet.{u}) [StrictSegal X] (n : ℕ) :
    (rightExtensionInclusion X 2).IsPointwiseRightKanExtensionAt ⟨[n]⟩ := by
  show IsLimit _
  unfold rightExtensionInclusion
  simp only [RightExtension.mk, RightExtension.coneAt, Truncated.inclusion,
    CostructuredArrow.mk_left, const_obj_obj, op_obj, fullSubcategoryInclusion.obj,
    comp_obj, StructuredArrow.proj_obj, whiskeringLeft_obj_obj, CostructuredArrow.mk_right,
    CostructuredArrow.mk_hom_eq_self, NatTrans.id_app, comp_id]
  exact {
    lift := fun s x => ran.lift s x
    fac := by
      intro s j
      ext x
      apply (StrictSegal.segal (unop j.right).1.len).injective
      ext i
      · simp only [spine_vertex, id_eq, types_comp_apply, ran.lift]
        simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
        have ceq : (j.hom ≫ ([0].const [(unop j.right).obj.len] i).op) =
          (const [0] [n] (strArr.homEv j i)).op := rfl
        rw [ceq, StrictSegal.spineToSimplex_vertex]
        have eq := congr_fun (s.π.naturality (fact.obj.arr j i)) x
        unfold pt fact.obj.arr strArr.homEv at eq
        dsimp at eq
        simp only [len_mk, mk_len]
        rw [← eq]
        rfl
      · simp only [spine_arrow, id_eq, types_comp_apply]
        have nat := congr_fun (s.π.naturality (fact.map.arr j i)) x
        dsimp [fact.map.arr] at nat
        rw [← nat]
        simp only [← FunctorToTypes.map_comp_apply]
        rw [← Quiver.Hom.op_unop j.hom]
        simp only [← op_comp]
        rw [show mkOfSucc i ≫ j.hom.unop = mkOfLe _ _ (strArr.homEv.map j i).le by
          simp [strArr.homEv, strArr.homEvSucc, mkOfSucc, mkOfLe]
          exact Hom.ext_one_left ..]
        exact ran.lift.map s x (strArr.homEv j i.castSucc) (strArr.homEvSucc j i)
          (strArr.homEv.map j i)
    uniq := by
      intro s lift' fact'
      ext x
      apply (StrictSegal.segal n).injective
      simp only [ran.lift, const_obj_obj, comp_obj, StructuredArrow.proj_obj, op_obj,
        fullSubcategoryInclusion.obj, RightExtension.mk_left, whiskeringLeft_obj_obj,
        RightExtension.mk_hom, NatTrans.id_app, const_obj_map, Functor.comp_map,
        StructuredArrow.proj_map, op_map, fullSubcategoryInclusion.map,
        Equiv.invFun_as_coe, id_eq]
      rw [StrictSegal.spineToSimplex_spine]
      ext i
      · exact congr_fun (fact' (StructuredArrow.mk (Y := op [0]₂) ([0].const [n] i).op)) x
      · exact congr_fun (fact' (ar i)) x
  }

end

end SSet
