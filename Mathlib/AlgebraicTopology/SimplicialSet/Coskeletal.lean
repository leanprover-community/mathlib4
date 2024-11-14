/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Coskeletal simplicial sets

The identity natural transformation exhibits a simplicial set `X` as a right extension of its
restriction along `(Truncated.inclusion (n := n)).op` recorded by `rightExtensionInclusion X n`.

The simplicial set `X` is *n-coskeletal* if
`(rightExtensionInclusion X n).IsPointwiseRightKanExtension` holds.

In this file, we prove that if `X` is `StrictSegal` then `X` is 2-coskeletal defining

`StrictSegal.cosk2Iso : X ≅ (Truncated.cosk 2).obj ((truncation 2).obj X)`

In particular, nerves of categories are 2-coskeletal.
-/

universe v u

open CategoryTheory Simplicial SimplexCategory Opposite Category Functor Limits

namespace SSet

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion (n := n)).op`.-/
@[simps!]
def rightExtensionInclusion (X : SSet.{u}) (n : ℕ) :
    RightExtension (Truncated.inclusion (n := n)).op
      (Functor.op Truncated.inclusion ⋙ X) := RightExtension.mk _ (𝟙 _)

section

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

set_option quotPrecheck false
local macro:max (priority := high) "[" n:term "]₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))


namespace StructuredArrow

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

/-- For any cone over the diagram
  `(StructuredArrow.proj (op [n])
  (Truncated.inclusion (n := 2)).op ⋙ (Truncated.inclusion (n := 2)).op ⋙ X)`,
the map `ar.src` induces a commutative triangle.-/
private
theorem ranCone_ar_src {X : SSet.{u}} {n} {i : Fin n}
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

/-- For any cone over the diagram `(StructuredArrow.proj (op [n])`
`(Truncated.inclusion (n := 2)).op ⋙ (Truncated.inclusion (n := 2)).op ⋙ X)`,
the map `ar.tgt` induces a commutative triangle.-/
private
theorem ranCone_ar_tgt {X : SSet.{u}} {n} {i : Fin n}
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
as "j(i)"".-/
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

end StructuredArrow

open StructuredArrow

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
    arrow_src := fun _ ↦ ranCone_ar_src s x
    arrow_tgt := fun _ ↦ ranCone_ar_tgt s x
  }

/-- This theorem is used to prove the factorization property of `ran.lift`.-/
private
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
    apply StrictSegal.spineInjective
    unfold StrictSegal.spineEquiv
    dsimp
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
        simp only [StrictSegal.spineToSimplex_arrow]
        have := congr_fun (s.π.naturality facemap₀) x
        dsimp [facemap₀] at this
        rw [this, show (δ 0 : [1] ⟶ [2]) = mkOfSucc 1 from Hom.ext_one_left ..]
        rfl

namespace StrictSegal
variable (X : SSet.{u}) [StrictSegal X]

/-- A strict Segal simplicial set is 2-coskeletal. -/
noncomputable def IsPointwiseRightKanExtensionAt (n : ℕ) :
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
      apply StrictSegal.spineInjective (X := X) (n := (unop j.right).1.len)
      unfold spineEquiv
      dsimp
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
      apply StrictSegal.spineInjective
      unfold spineEquiv
      dsimp
      rw [StrictSegal.spine_spineToSimplex]
      ext i
      · exact congr_fun (fact' (StructuredArrow.mk (Y := op [0]₂) ([0].const [n] i).op)) x
      · exact congr_fun (fact' (ar i)) x
  }



/-- Since `rightExtensionInclusion₂IsPointwiseRightKanExtensionAt X n` proves that the appropriate
cones are limit cones, `rightExtensionInclusion X 2` is a pointwise right Kan extension.-/
noncomputable def isPointwiseRightKanExtension :
    RightExtension.IsPointwiseRightKanExtension (rightExtensionInclusion X 2) :=
  fun Δ => IsPointwiseRightKanExtensionAt X Δ.unop.len

/-- Since `rightExtensionInclusion X 2` is a pointwise right Kan extension,
`rightExtensionInclusion X 2` is universal as a costructured arrow.-/
noncomputable def isPointwiseRightKanExtension.isUniversal :
    CostructuredArrow.IsUniversal (rightExtensionInclusion X 2) :=
  RightExtension.IsPointwiseRightKanExtension.isUniversal (isPointwiseRightKanExtension X)

theorem isRightKanExtension :
    (rightExtensionInclusion X 2).left.IsRightKanExtension (rightExtensionInclusion X 2).hom :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (isPointwiseRightKanExtension X)

/-- There is a map of costructured arrows from `rightExtensionInclusion X 2` to the right extension
of the 2-truncation of `X` defined by the counit of `coskAdj 2`.-/
noncomputable def cosk2RightExtension.hom : rightExtensionInclusion X 2 ⟶
    RightExtension.mk _
      ((Truncated.inclusion (n := 2)).op.ranCounit.app ((Truncated.inclusion (n := 2)).op ⋙ X)) :=
  CostructuredArrow.homMk ((coskAdj 2).unit.app X) ((coskAdj 2).left_triangle_components X)

/-- The map `cosk2RightExtension.hom X` is a natural transformation between two right Kan extensions
of the diagram `((Truncated.inclusion (n := 2)).op ⋙ X)` and thus is an isomorphism. -/
instance cosk2RightExtension.hom_isIso : IsIso (cosk2RightExtension.hom X) :=
  isIso_of_isTerminal (isPointwiseRightKanExtension.isUniversal X)
    (((Truncated.cosk 2).obj
      ((Truncated.inclusion (n := 2)).op ⋙ X)).isUniversalOfIsRightKanExtension
        ((Truncated.inclusion (n := 2)).op.ranCounit.app ((Truncated.inclusion (n := 2)).op ⋙ X)))
      (cosk2RightExtension.hom X)

/-- The map `cosk2RightExtension.hom X` is a natural transformation between two right Kan extensions
of the diagram `((Truncated.inclusion (n := 2)).op ⋙ X)` and thus is an isomorphism. -/
noncomputable def cosk2RightExtension.homIso : rightExtensionInclusion X 2 ≅
   RightExtension.mk _
      ((Truncated.inclusion (n := 2)).op.ranCounit.app ((Truncated.inclusion (n := 2)).op ⋙ X)) :=
  asIso (cosk2RightExtension.hom X)

/-- The isomorphism `X ≅ (Truncated.cosk 2).obj X\` which shows that the nerve is
2-coskeletal.-/
noncomputable def cosk2Iso : X ≅ (Truncated.cosk 2).obj ((truncation 2).obj X) :=
  (CostructuredArrow.proj ((whiskeringLeft _ _ _).obj (Truncated.inclusion (n := 2)).op)
    ((Truncated.inclusion (n := 2)).op ⋙ X)).mapIso (cosk2RightExtension.homIso X)

end StrictSegal

end

end SSet

namespace CategoryTheory

namespace Nerve

open SSet

/-- The essential data of the nerve functor is contained in the 2-truncation, which is
recorded by the composite functor `nerveFunctor₂`.-/
def nerveFunctor₂ : Cat.{v, u} ⥤ SSet.Truncated 2 := nerveFunctor ⋙ truncation 2

/-- The counit of `coskAdj 2` defines a natural transformation from the nerve to the right
Kan extension of the 2-truncated nerve.-/
noncomputable def cosk2NatTrans : nerveFunctor.{u, v} ⟶ nerveFunctor₂ ⋙ Truncated.cosk 2 :=
  whiskerLeft nerveFunctor (coskAdj 2).unit

/-- The natural isomorphism between `nerveFunctor` and `nerveFunctor ⋙ Truncated.cosk 2` whose
components `nerve C ≅  (Truncated.cosk 2).obj (nerve₂ C)` shows that nerves of categories are
2-coskeletal.-/
noncomputable def cosk2Iso : nerveFunctor.{u, u} ≅ nerveFunctor₂.{u, u} ⋙ Truncated.cosk 2 := by
  refine NatIso.ofComponents ?_ ?_
  · intro C
    dsimp [nerveFunctor, nerveFunctor₂]
    exact (StrictSegal.cosk2Iso (nerve C))
  · simp only [nerveFunctor_obj, comp_obj, id_eq, Functor.comp_map]
    convert cosk2NatTrans.naturality

end Nerve

end CategoryTheory
