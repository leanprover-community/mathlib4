/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Op
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Finset
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# The standard simplex

We define the standard simplices `Δ[n]` as simplicial sets.
See files `SimplicialSet.Boundary` and `SimplicialSet.Horn`
for their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open Simplicial`.)

-/

@[expose] public section

universe u

open CategoryTheory Limits Simplicial Opposite

namespace SSet

/-- The functor `SimplexCategory ⥤ SSet` which sends `⦋n⦌` to the standard simplex `Δ[n]` is a
cosimplicial object in the category of simplicial sets. (This functor is essentially given by the
Yoneda embedding). -/
def stdSimplex : CosimplicialObject SSet.{u} := uliftYoneda

@[inherit_doc SSet.stdSimplex]
scoped[Simplicial] notation3 "Δ[" n "]" => SSet.stdSimplex.obj (SimplexCategory.mk n)

instance : Inhabited SSet :=
  ⟨Δ[0]⟩

instance {n} : Inhabited (SSet.Truncated n) :=
  ⟨(truncation n).obj <| Δ[0]⟩

namespace stdSimplex

open Finset Opposite SimplexCategory

@[simp]
lemma map_id (n : SimplexCategory) :
    (SSet.stdSimplex.map (SimplexCategory.Hom.mk OrderHom.id : n ⟶ n)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

/-- Simplices of the standard simplex identify to morphisms in `SimplexCategory`. -/
def objEquiv {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} :
    (stdSimplex.{u}.obj n).obj m ≃ (m.unop ⟶ n) :=
  Equiv.ulift.{u, 0}

instance (n : SimplexCategory) (m : SimplexCategoryᵒᵖ) :
    DecidableEq ((stdSimplex.{u}.obj n).obj m) :=
  fun a b ↦ decidable_of_iff (stdSimplex.objEquiv a = stdSimplex.objEquiv b) (by simp)

/-- If `x : Δ[n] _⦋d⦌` and `i : Fin (d + 1)`, we may evaluate `x i : Fin (n + 1)`. -/
instance (n i : ℕ) : FunLike (Δ[n] _⦋i⦌) (Fin (i + 1)) (Fin (n + 1)) where
  coe x j := (objEquiv x).toOrderHom j
  coe_injective' _ _ h := objEquiv.injective (by ext : 3; apply congr_fun h)

lemma monotone_apply {n i : ℕ} (x : Δ[n] _⦋i⦌) :
    Monotone (fun (j : Fin (i + 1)) ↦ x j) :=
  (objEquiv x).toOrderHom.monotone

@[ext]
lemma ext {n d : ℕ} (x y : Δ[n] _⦋d⦌) (h : ∀ (i : Fin (d + 1)), x i = y i) : x = y :=
  DFunLike.ext _ _ h

@[simp]
lemma objEquiv_toOrderHom_apply {n i : ℕ}
    (x : (stdSimplex.{u} ^⦋n⦌).obj (op ⦋i⦌)) (j : Fin (i + 1)) :
    DFunLike.coe (F := Fin (i + 1) →o Fin (n + 1))
      ((DFunLike.coe (F := Δ[n].obj (op ⦋i⦌) ≃ (⦋i⦌ ⟶ ⦋n⦌))
        objEquiv x)).toOrderHom j = x j :=
  rfl

lemma objEquiv_symm_comp {n n' : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) (g : n ⟶ n') :
    objEquiv.{u}.symm (f ≫ g) =
      (stdSimplex.map g).app _ (objEquiv.{u}.symm f) := rfl

lemma map_objEquiv_symm {n : SimplexCategory} {m m' : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) (g : m ⟶ m') :
    (stdSimplex.{u}.obj n).map g (objEquiv.symm f) =
      objEquiv.symm (g.unop ≫ f) :=
  rfl

@[simp]
lemma objEquiv_symm_apply {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (objEquiv.{u}.symm f : Δ[n] _⦋m⦌) i = f.toOrderHom i := rfl

@[simp]
lemma δ_objEquiv_symm_apply
    {n : ℕ} {m : SimplexCategory} (f : .mk (n + 1) ⟶ m) (i : Fin (n + 2)) :
    dsimp% (stdSimplex.obj _).δ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := op ⦋n⦌)).symm (SimplexCategory.δ i ≫ f) := by
  rfl

@[simp]
lemma σ_objEquiv_symm_apply
    {n : ℕ} {m : SimplexCategory} (f : .mk n ⟶ m) (i : Fin (n + 1)) :
    dsimp% (stdSimplex.obj _).σ i (objEquiv.symm f) =
      (objEquiv (n := m) (m := op ⦋n + 1⦌)).symm (SimplexCategory.σ i ≫ f) := by
  rfl

/-- Constructor for simplices of the standard simplex which takes a `OrderHom` as an input. -/
abbrev objMk {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : Fin (len m.unop + 1) →o Fin (n.len + 1)) :
    (stdSimplex.{u}.obj n).obj m :=
  objEquiv.symm (Hom.mk f)

@[simp]
lemma objMk_apply {n m : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    objMk.{u} (n := ⦋n⦌) (m := op ⦋m⦌) f i = f i :=
  rfl

lemma objMk_bijective {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} :
    Function.Bijective (objMk (n := n) (m := m)) :=
  (objEquiv.trans homEquivOrderHom).symm.bijective

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `Fin (m+1)` to `Fin (n+1)`. -/
def asOrderHom {n} {m} (α : Δ[n].obj m) : OrderHom (Fin (m.unop.len + 1)) (Fin (n + 1)) :=
  α.down.toOrderHom

lemma map_apply {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : SimplexCategory}
    (x : (stdSimplex.{u}.obj n).obj m₁) :
    (stdSimplex.{u}.obj n).map f x = objEquiv.symm (f.unop ≫ objEquiv x) := by
  rfl

@[simp]
lemma coe_asOrderHom_objEquiv_symm {n m : ℕ} (α : ⦋n⦌ ⟶ ⦋m⦌) :
    ⇑(asOrderHom (objEquiv.{u}.symm α)) = α := rfl

end stdSimplex

/-- The canonical bijection `(stdSimplex.obj n ⟶ X) ≃ X.obj (op n)`. -/
def yonedaEquiv {X : SSet.{u}} {n : SimplexCategory} :
    (stdSimplex.obj n ⟶ X) ≃ X.obj (op n) :=
  uliftYonedaEquiv

instance (X : SSet.{u}) (n : SimplexCategory) [DecidableEq (X.obj (op n))] :
    DecidableEq (stdSimplex.obj n ⟶ X) :=
  fun a b ↦ decidable_of_iff (yonedaEquiv a = yonedaEquiv b) (by simp)

@[simp]
lemma _root_.SSet.yonedaEquiv_symm_comp {X Y : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
    (f : X ⟶ Y) :
    yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app _ x) :=
  uliftYonedaEquiv_symm_comp ..

set_option backward.isDefEq.respectTransparency false in
lemma _root_.SSet.yonedaEquiv_const {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv (const x : Δ[0] ⟶ X) = x := by
  simp [yonedaEquiv, uliftYonedaEquiv]

@[simp]
lemma _root_.SSet.yonedaEquiv_symm_zero {X : SSet.{u}} (x : X _⦋0⦌) :
    yonedaEquiv.symm x = const x := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_const]

lemma yonedaEquiv_map {n m : SimplexCategory} (f : n ⟶ m) :
    yonedaEquiv.{u} (stdSimplex.map f) = stdSimplex.objEquiv.symm f :=
  yonedaEquiv.symm.injective rfl

@[deprecated (since := "2026-03-21")] alias stdSimplex.yonedaEquiv_map := yonedaEquiv_map

@[simp]
lemma yonedaEquiv_symm_app {S : SSet} (n : SimplexCategory) (x : S.obj (op n))
    (α : (stdSimplex.obj n).obj (op n)) :
    (yonedaEquiv.symm x).app (op n) α = S.map (SSet.stdSimplex.objEquiv α).op x := rfl

@[simp]
lemma yonedaEquiv_symm_stdSimplex_id (n : SimplexCategory) :
    yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm (β := n ⟶ _) (𝟙 n)) = 𝟙 (stdSimplex.obj n) :=
  yonedaEquiv.symm_apply_eq.mpr rfl

open Finset Opposite SimplexCategory

lemma yonedaEquiv_symm_app_objEquiv_symm {X : SSet.{u}} {n : SimplexCategory}
    (x : X.obj (op n)) {m : SimplexCategoryᵒᵖ} (f : unop m ⟶ n) :
    dsimp% (yonedaEquiv.symm x).app _ (stdSimplex.objEquiv.symm f) =
      X.map f.op x :=
  rfl

lemma opObjEquiv_yonedaEquiv_const {X : SSet.{u}} {n : SimplexCategory} (x : X.op _⦋0⦌) :
    opObjEquiv (n := op n) (yonedaEquiv (const x)) =
      yonedaEquiv (const (opObjEquiv x)) := rfl

lemma opObjEquiv_symm_yonedaEquiv_const {X : SSet.{u}} {n : SimplexCategory} (x : X _⦋0⦌) :
    (opObjEquiv (n := op n)).symm (yonedaEquiv (const x)) =
      yonedaEquiv (const (opObjEquiv.symm x)) := rfl

namespace stdSimplex

set_option backward.isDefEq.respectTransparency false in
lemma map_comp_yonedaEquiv_symm {X : SSet.{u}} {n m : SimplexCategory} (f : n ⟶ m)
    (x : X.obj (op m)) :
    stdSimplex.map f ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.map f.op x) := by
  simp [yonedaEquiv, stdSimplex, ← dsimp% uliftYonedaEquiv_symm_map f.op]

lemma δ_comp_yonedaEquiv_symm
    {X : SSet.{u}} {n : ℕ} (x : X _⦋n + 1⦌) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ yonedaEquiv.symm x = yonedaEquiv.symm (X.δ i x) :=
  map_comp_yonedaEquiv_symm ..

lemma yonedaEquiv_map_comp
    {X : SSet.{u}} {n m : SimplexCategory} (f : n ⟶ m) (g : stdSimplex.obj m ⟶ X) :
    yonedaEquiv (stdSimplex.map f ≫ g) = X.map f.op (yonedaEquiv g) :=
  yonedaEquiv.symm.injective (by simp [← map_comp_yonedaEquiv_symm])

lemma yonedaEquiv_δ_comp
    {X : SSet.{u}} {n : ℕ} (g : Δ[n + 1] ⟶ X) (i : Fin (n + 2)) :
    yonedaEquiv (stdSimplex.δ i ≫ g) = X.δ i (yonedaEquiv g) :=
  yonedaEquiv_map_comp ..

@[simp]
lemma objEquiv_yonedaEquiv_id (n : ℕ) :
    dsimp% objEquiv (yonedaEquiv.{u} (𝟙 Δ[n])) = 𝟙 _ := rfl

lemma map_objEquiv_op_apply
    {X : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n))
    {m : SimplexCategoryᵒᵖ} (y : (stdSimplex.obj n).obj m) :
    dsimp% X.map (stdSimplex.objEquiv y).op x = (yonedaEquiv.symm x).app m y := by
  rfl

/-- The (degenerate) `m`-simplex in the standard simplex concentrated in vertex `k`. -/
def const (n : ℕ) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) : Δ[n].obj m :=
  objMk (OrderHom.const _ k)

@[simp]
lemma const_down_toOrderHom (n : ℕ) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) :
    (const n k m).down.toOrderHom = OrderHom.const _ k :=
  rfl

/-- The `0`-simplices of `Δ[n]` identify to the elements in `Fin (n + 1)`. -/
@[simps]
def obj₀Equiv {n : ℕ} : Δ[n] _⦋0⦌ ≃ Fin (n + 1) where
  toFun x := x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl

lemma δ_one_eq_const : stdSimplex.{u}.δ (1 : Fin 2) = SSet.const (obj₀Equiv.symm 0) := by
  decide

lemma δ_zero_eq_const : stdSimplex.{u}.δ (0 : Fin 2) = SSet.const (obj₀Equiv.symm 1) := by
  decide

/-- The edge of the standard simplex with endpoints `a` and `b`. -/
def edge (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n] _⦋1⦌ := by
  refine objMk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab

lemma coe_edge_down_toOrderHom (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) :
    ↑(edge n a b hab).down.toOrderHom = ![a, b] :=
  rfl

/-- The triangle in the standard simplex with vertices `a`, `b`, and `c`. -/
def triangle {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c) : Δ[n] _⦋2⦌ := by
  refine objMk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, true_and]

lemma coe_triangle_down_toOrderHom {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c) :
    ↑(triangle a b c hab hbc).down.toOrderHom = ![a, b, c] :=
  rfl

attribute [local simp] image_subset_iff

/-- Given `S : Finset (Fin (n + 1))`, this is the corresponding face of `Δ[n]`,
as a subcomplex. -/
@[simps -isSimp obj]
def face {n : ℕ} (S : Finset (Fin (n + 1))) : (Δ[n] : SSet.{u}).Subcomplex where
  obj U := setOf (fun f ↦ Finset.image (objEquiv f).toOrderHom ⊤ ≤ S)
  map {U V} i := by aesop

attribute [local simp] face_obj

@[simp]
lemma mem_face_iff {n : ℕ} (S : Finset (Fin (n + 1))) {d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    x ∈ (face S).obj _ ↔ ∀ (i : Fin (d + 1)), x i ∈ S := by
  simp

lemma face_inter_face {n : ℕ} (S₁ S₂ : Finset (Fin (n + 1))) :
    face S₁ ⊓ face S₂ = face (S₁ ⊓ S₂) := by
  aesop

@[simp]
lemma face_empty (n : ℕ) :
    face.{u} (∅ : Finset (Fin (n + 1))) = ⊥ := by
  ext
  simpa using Finset.univ_neq_empty _

@[simp]
lemma face_univ (n : ℕ) :
    face.{u} (.univ : Finset (Fin (n + 1))) = ⊤ := by
  ext
  simp only [Subfunctor.top_obj, Set.top_eq_univ, Set.mem_univ, iff_true]
  apply Finset.subset_univ

end stdSimplex

lemma yonedaEquiv_comp {X Y : SSet.{u}} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ X) (g : X ⟶ Y) :
    yonedaEquiv (f ≫ g) = g.app _ (yonedaEquiv f) := rfl

@[simp high]
lemma yonedaEquiv_symm_app_id {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    (yonedaEquiv.symm x).app _ (yonedaEquiv (𝟙 _)) = x := by
  simp


namespace Subcomplex

variable {X : SSet.{u}}

lemma range_eq_ofSimplex {n : ℕ} (f : Δ[n] ⟶ X) :
    range f = ofSimplex (yonedaEquiv f) :=
  Subfunctor.range_eq_ofSection' _

lemma yonedaEquiv_coe {A : X.Subcomplex} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ A) :
    (yonedaEquiv f).val = yonedaEquiv (f ≫ A.ι) := by
  rfl

end Subcomplex

namespace stdSimplex

lemma obj₀Equiv_symm_mem_face_iff
    {n : ℕ} (S : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    (obj₀Equiv.symm i) ∈ (face.{u} S).obj (op (.mk 0)) ↔ i ∈ S :=
  ⟨fun h ↦ by simpa using h, by aesop⟩

lemma face_le_face_iff {n : ℕ} (S₁ S₂ : Finset (Fin (n + 1))) :
    face.{u} S₁ ≤ face S₂ ↔ S₁ ≤ S₂ := by
  refine ⟨fun h i hi ↦ ?_, fun h d a ha ↦ ha.trans h⟩
  simp only [← obj₀Equiv_symm_mem_face_iff.{u}] at hi ⊢
  exact h _ hi

lemma face_eq_ofSimplex {n : ℕ} (S : Finset (Fin (n + 1))) (m : ℕ) (e : Fin (m + 1) ≃o S) :
    face.{u} S =
      Subcomplex.ofSimplex (X := Δ[n])
        (objMk ((OrderHom.Subtype.val _).comp
          e.toOrderEmbedding.toOrderHom)) := by
  apply le_antisymm
  · rintro ⟨k⟩ x hx
    induction k using SimplexCategory.rec with | _ k
    rw [mem_face_iff] at hx
    let φ : Fin (k + 1) →o S :=
      { toFun i := ⟨x i, hx i⟩
        monotone' := (objEquiv x).toOrderHom.monotone }
    refine ⟨Quiver.Hom.op
      (SimplexCategory.Hom.mk ((e.symm.toOrderEmbedding.toOrderHom.comp φ))), ?_⟩
    ext j : 1
    simpa only [Subtype.ext_iff] using e.apply_symm_apply ⟨_, hx j⟩
  · simp

/-- If `S : Finset (Fin (n + 1))` is order isomorphic to `Fin (m + 1)`,
then the face `face S` of `Δ[n]` is representable by `m`,
i.e. `face S` is isomorphic to `Δ[m]`, see `stdSimplex.isoOfRepresentableBy`. -/
def faceRepresentableBy {n : ℕ} (S : Finset (Fin (n + 1)))
    (m : ℕ) (e : Fin (m + 1) ≃o S) :
    (face S : SSet.{u}).RepresentableBy ⦋m⦌ where
  homEquiv {j} :=
    { toFun f := ⟨objMk ((OrderHom.Subtype.val (· ∈ S)).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ ↦ by aesop⟩
      invFun := fun ⟨x, hx⟩ ↦ SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv x).toOrderHom i, hx (by simp)⟩
          monotone' i₁ i₂ h := e.symm.monotone (by
            simp only [Subtype.mk_le_mk]
            exact OrderHom.monotone _ h) }
      left_inv f := by
        ext i : 3
        apply e.symm_apply_apply
      right_inv := fun ⟨x, hx⟩ ↦ by
        induction j using SimplexCategory.rec with | _ j
        dsimp
        ext i : 2
        exact congr_arg Subtype.val
          (e.apply_symm_apply ⟨(objEquiv x).toOrderHom i, _⟩) }
  homEquiv_comp f g := by aesop

/-- If a simplicial set `X` is representable by `⦋m⦌` for some `m : ℕ`, then this is the
corresponding isomorphism `Δ[m] ≅ X`. -/
def isoOfRepresentableBy {X : SSet.{u}} {m : ℕ} (h : X.RepresentableBy ⦋m⦌) :
    Δ[m] ≅ X :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso (objEquiv.trans h.homEquiv))
    (fun _ ↦ by ext; apply h.homEquiv_comp)

lemma ofSimplex_yonedaEquiv_δ {n : ℕ} (i : Fin (n + 2)) :
    Subcomplex.ofSimplex (yonedaEquiv (stdSimplex.δ i)) = face.{u} {i}ᶜ :=
  (face_eq_ofSimplex _ _ (Fin.succAboveOrderIso i)).symm

@[simp]
lemma range_δ {n : ℕ} (i : Fin (n + 2)) :
    Subcomplex.range (stdSimplex.δ i) = face.{u} {i}ᶜ := by
  rw [Subcomplex.range_eq_ofSimplex]
  exact ofSimplex_yonedaEquiv_δ i

/-- The standard simplex identifies to the nerve to the preordered type
`ULift (Fin (n + 1))`. -/
@[pp_with_univ]
def isoNerve (n : ℕ) :
    (Δ[n] : SSet.{u}) ≅ nerve (ULift.{u} (Fin (n + 1))) :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso (objEquiv.trans
    { toFun f := (ULift.orderIso.symm.monotone.comp f.toOrderHom.monotone).functor
      invFun f :=
        SimplexCategory.Hom.mk
          (ULift.orderIso.toOrderEmbedding.toOrderHom.comp f.toOrderHom)
      left_inv _ := by aesop }))

@[simp]
lemma isoNerve_hom_app_apply {n d : ℕ}
    (s : (Δ[n] _⦋d⦌)) (i : Fin (d + 1)) :
    dsimp% ((isoNerve.{u} n).hom.app _ s).obj i = ULift.up (s i) := rfl

@[simp]
lemma isoNerve_inv_app_apply {n d : ℕ}
    (F : (nerve (ULift.{u} (Fin (n + 1)))) _⦋d⦌) (i : Fin (d + 1)) :
    dsimp% (isoNerve.{u} n).inv.app _ F i = (F.obj i).down := rfl

lemma mem_nonDegenerate_iff_strictMono {n d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    s ∈ Δ[n].nonDegenerate d ↔ StrictMono s := by
  rw [← nonDegenerate_iff_of_mono (isoNerve n).hom,
    PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

lemma mem_nonDegenerate_iff_mono {n d : ℕ} (s : (Δ[n] : SSet.{u}) _⦋d⦌) :
    s ∈ Δ[n].nonDegenerate d ↔ Mono (objEquiv s) := by
  rw [mem_nonDegenerate_iff_strictMono,
    SimplexCategory.mono_iff_injective]
  refine ⟨fun h ↦ h.injective, fun h ↦ ?_⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain h' | h' := (stdSimplex.monotone_apply s i.castSucc_le_succ).lt_or_eq
  · exact h'
  · simpa [Fin.ext_iff] using h h'

lemma objEquiv_symm_mem_nonDegenerate_iff_mono {n d : ℕ} (f : ⦋d⦌ ⟶ ⦋n⦌) :
    (objEquiv.{u} (m := (op ⦋d⦌))).symm f ∈ Δ[n].nonDegenerate d ↔ Mono f := by
  simp [mem_nonDegenerate_iff_mono]

/-- Nondegenerate `d`-dimensional simplices of the standard simplex `Δ[n]`
identify to order embeddings `Fin (d + 1) ↪o Fin (n + 1)`. -/
@[simps! apply_apply symm_apply_coe]
def nonDegenerateEquiv {n d : ℕ} :
    (Δ[n] : SSet.{u}).nonDegenerate d ≃ (Fin (d + 1) ↪o Fin (n + 1)) where
  toFun s := OrderEmbedding.ofStrictMono _ ((mem_nonDegenerate_iff_strictMono _).1 s.2)
  invFun s := ⟨objEquiv.symm (.mk s.toOrderHom), by
    simpa [mem_nonDegenerate_iff_strictMono] using s.strictMono⟩
  left_inv _ := by aesop

instance (n : ℕ) : (Δ[n] : SSet.{u}).HasDimensionLE n where
  degenerate_eq_top i hi := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    by_contra hx
    have : Mono (objEquiv x) := by rwa [← mem_nonDegenerate_iff_mono]
    have := SimplexCategory.len_le_of_mono (objEquiv x)
    dsimp at this
    lia

/-- If `i : Fin (n + 2)`, this is the order isomorphism between `Fin (n +1)`
and the complement of `{i}` as a finset. -/
def finSuccAboveOrderIsoFinset {n : ℕ} (i : Fin (n + 2)) :
    Fin (n + 1) ≃o ({i}ᶜ : Finset _) where
  toEquiv := (finSuccAboveEquiv (p := i)).trans
    { toFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩
      invFun := fun ⟨x, hx⟩ ↦ ⟨x, by simpa using hx⟩ }
  map_rel_iff' := (Fin.succAboveOrderEmb i).map_rel_iff

lemma face_singleton_compl {n : ℕ} (i : Fin (n + 2)) :
    face.{u} {i}ᶜ =
      Subcomplex.ofSimplex (objEquiv.symm (SimplexCategory.δ i)) :=
  face_eq_ofSimplex _ _ (finSuccAboveOrderIsoFinset i)

/-- In `Δ[n + 1]`, the face corresponding to the complement of `{i}`
for `i : Fin (n + 2)` is isomorphic to `Δ[n]`. -/
def faceSingletonComplIso {n : ℕ} (i : Fin (n + 2)) :
    Δ[n] ≅ (face {i}ᶜ : SSet.{u}) :=
  isoOfRepresentableBy (faceRepresentableBy _ _ (finSuccAboveOrderIsoFinset i))

@[reassoc (attr := simp)]
lemma faceSingletonComplIso_hom_ι {n : ℕ} (i : Fin (n + 2)) :
    (faceSingletonComplIso.{u} i).hom ≫ (face {i}ᶜ).ι =
      stdSimplex.δ i := rfl

/-- Given `i : Fin (n + 1)`, this is the isomorphism from `Δ[0]` to the face
of `Δ[n]` corresponding to `{i}`. -/
noncomputable def faceSingletonIso {n : ℕ} (i : Fin (n + 1)) :
    Δ[0] ≅ (face {i} : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoSingleton i))

@[reassoc]
lemma faceSingletonIso_zero_hom_comp_ι_eq_δ :
    (faceSingletonIso.{u} (0 : Fin 2)).hom ≫ (face {0}).ι = stdSimplex.δ 1 := by
  decide

@[reassoc]
lemma faceSingletonIso_one_hom_comp_ι_eq_δ :
    (faceSingletonIso.{u} (1 : Fin 2)).hom ≫ (face {1}).ι = stdSimplex.δ 0 := by
  decide

/-- Given `i` and `j` in `Fin (n + 1)` such that `i < j`,
this is the isomorphism from `Δ[1]` to the face
of `Δ[n]` corresponding to `{i, j}`. -/
noncomputable def facePairIso {n : ℕ} (i j : Fin (n + 1)) (hij : i < j) :
    Δ[1] ≅ (face {i, j} : SSet.{u}) :=
  stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} _ _ (Fin.orderIsoPair i j hij))

variable (n) in
private lemma bijective_image_objEquiv_toOrderHom_univ (m : ℕ) :
    Function.Bijective (fun (⟨x, hx⟩ : (Δ[n] : SSet.{u}).nonDegenerate m) ↦
      (⟨Finset.image (objEquiv x).toOrderHom .univ, by
        dsimp
        rw [mem_nonDegenerate_iff_mono, SimplexCategory.mono_iff_injective] at hx
        rw [Finset.card_image_of_injective _ (by exact hx), Finset.card_univ,
          Fintype.card_fin]⟩ : { S : Finset (Fin (n + 1)) | S.card = m + 1 })) := by
  constructor
  · rintro ⟨x₁, h₁⟩ ⟨x₂, h₂⟩ h₃
    obtain ⟨f₁, rfl⟩ := objEquiv.symm.surjective x₁
    obtain ⟨f₂, rfl⟩ := objEquiv.symm.surjective x₂
    simp only [mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply,
      SimplexCategory.mono_iff_injective, SimplexCategory.len_mk] at h₁ h₂
    simp only [Set.mem_setOf_eq, SimplexCategory.len_mk, Equiv.apply_symm_apply,
      Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h₃ ⊢
    apply SimplexCategory.Hom.ext
    rw [← OrderHom.range_eq_iff h₁ h₂]
    ext x
    simpa using congr_fun (congrArg Membership.mem h₃) x
  · intro ⟨S, hS⟩
    dsimp at hS
    let e := monoEquivOfFin S (k := m + 1) (by simpa using hS)
    refine ⟨⟨objMk ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom), ?_⟩, ?_⟩
    · rw [mem_nonDegenerate_iff_mono, SimplexCategory.mono_iff_injective]
      intro a b h
      grind [e.injective, dsimp% h]
    · simp [e, ← Finset.image_image, Finset.image_univ_of_surjective e.surjective]

/-- Nondegenerate `d`-dimensional simplices of the standard simplex `Δ[n]`
identify to subsets of `Fin (n + 1)` of cardinality `d + 1`. -/
@[no_expose] noncomputable def nonDegenerateEquiv' {n d : ℕ} :
    (Δ[n] : SSet.{u}).nonDegenerate d ≃ { S : Finset (Fin (n + 1)) | S.card = d + 1 } :=
  Equiv.ofBijective _ (bijective_image_objEquiv_toOrderHom_univ n d)

set_option backward.isDefEq.respectTransparency false in
lemma nonDegenerateEquiv'_iff {n d : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate d) (j : Fin (n + 1)) :
    j ∈ (nonDegenerateEquiv' x).val ↔ ∃ (i : Fin (d + 1)), x.val i = j := by
  simp only [Set.mem_setOf_eq, Set.coe_setOf]
  dsimp [nonDegenerateEquiv']
  aesop

/-- If `x` is a nondegenerate `d`-simplex of `Δ[n]`, this is the order isomorphism
between `Fin (d + 1)` and the corresponding subset of `Fin (n + 1)` of cardinality `d + 1`. -/
@[no_expose] noncomputable def orderIsoOfNonDegenerate
    {n d : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate d) :
    Fin (d + 1) ≃o nonDegenerateEquiv' x where
  toEquiv := Equiv.ofBijective (fun i ↦ ⟨x.val i, Finset.mem_image_of_mem _ (by simp)⟩) (by
    constructor
    · have := (mem_nonDegenerate_iff_mono x.val).1 x.property
      rw [SimplexCategory.mono_iff_injective] at this
      exact fun _ _ h ↦ this (by simpa using h)
    · rintro ⟨j, hj⟩
      rw [nonDegenerateEquiv'_iff] at hj
      aesop)
  map_rel_iff' := by
    have := (mem_nonDegenerate_iff_mono x.val).1 x.property
    rw [SimplexCategory.mono_iff_injective] at this
    intro a b
    dsimp
    simp only [Subtype.mk_le_mk]
    constructor
    · rw [← not_lt, ← not_lt]
      intro h h'
      apply h
      obtain h'' | h'' := (monotone_apply x.val h'.le).lt_or_eq
      · assumption
      · simp only [this h'', lt_self_iff_false] at h'
    · intro h
      exact monotone_apply _ h

lemma face_nonDegenerateEquiv' {n d : ℕ} (x : (Δ[n] : SSet.{u}).nonDegenerate d) :
    face (nonDegenerateEquiv' x) = Subcomplex.ofSimplex x.val :=
  face_eq_ofSimplex.{u} _ _ (orderIsoOfNonDegenerate x)

set_option backward.isDefEq.respectTransparency false in
lemma nonDegenerateEquiv'_symm_apply_mem {n d : ℕ}
    (S : { S : Finset (Fin (n + 1)) | S.card = d + 1 }) (i : Fin (d + 1)) :
      (nonDegenerateEquiv'.{u}.symm S).val i ∈ S.val := by
  obtain ⟨f, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  dsimp [nonDegenerateEquiv']
  simp only [Equiv.ofBijective_symm_apply_apply, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, rfl⟩

lemma nonDegenerateEquiv'_symm_mem_iff_face_le {n d : ℕ}
    (S : { S : Finset (Fin (n + 1)) | S.card = d + 1 })
    (A : (Δ[n] : SSet.{u}).Subcomplex) :
    (nonDegenerateEquiv'.symm S).val ∈ A.obj _ ↔ face S ≤ A := by
  obtain ⟨x, rfl⟩ := nonDegenerateEquiv'.{u}.surjective S
  rw [face_nonDegenerateEquiv' x, Equiv.symm_apply_apply, Subcomplex.ofSimplex_le_iff]

instance (n : SimplexCategory) (d : SimplexCategoryᵒᵖ) :
    Finite ((stdSimplex.{u}.obj n).obj d) := by
  rw [objEquiv.finite_iff]
  infer_instance

instance (n : SimplexCategory) : (stdSimplex.{u}.obj n).Finite := by
  induction n using SimplexCategory.rec with | _ n
  exact finite_of_hasDimensionLT _ (n + 1) inferInstance

instance {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    SSet.Finite (Subcomplex.ofSimplex x) := by
  obtain ⟨f, rfl⟩ := yonedaEquiv.surjective x
  rw [← Subcomplex.range_eq_ofSimplex]
  infer_instance

lemma hasDimensionLT_face {n : ℕ} (S : Finset (Fin (n + 1)))
    (d : ℕ) (hd : S.card ≤ d) :
    HasDimensionLT (face.{u} S) d := by
  generalize hm : S.card = m
  obtain _ | m := m
  · obtain rfl : S = ∅ := by rwa [← Finset.card_eq_zero]
    rw [face_empty]
    infer_instance
  · rw [← hasDimensionLT_iff_of_iso
      (isoOfRepresentableBy (faceRepresentableBy S m (monoEquivOfFin S (by simpa))))]
    exact hasDimensionLT_of_le _ (m + 1) _

lemma ofSimplex_objEquiv_symm_id (n : ℕ) :
    Subcomplex.ofSimplex (objEquiv.{u}.symm (𝟙 ⦋n⦌)) = ⊤ :=
  le_antisymm (by simp) (fun _ x _ ↦ by
    obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    simp only [Subcomplex.mem_ofSimplex_obj_iff, op_unop]
    exact ⟨f, by simp [map_objEquiv_symm.{u}]⟩)

lemma objEquiv_symm_id_mem_nonDegenerate (n : ℕ) :
    (objEquiv (m := (op ⦋n⦌))).symm (𝟙 _) ∈ (Δ[n] : SSet.{u}).nonDegenerate n := by
  rw [mem_nonDegenerate_iff_strictMono]
  exact fun _ _ h ↦ h

lemma nonDegenerate_top_dim (n : ℕ) :
    (Δ[n] : SSet.{u}).nonDegenerate n = {(objEquiv (m := (op ⦋n⦌))).symm (𝟙 _)} := by
  ext x
  simp only [Set.mem_singleton_iff]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    have : Mono f := by simpa using (mem_nonDegenerate_iff_mono _).mp h
    simpa only [EmbeddingLike.apply_eq_iff_eq] using SimplexCategory.eq_id_of_mono f
  · rintro rfl
    apply objEquiv_symm_id_mem_nonDegenerate

lemma not_hasDimensionLT (n : ℕ) (_ : HasDimensionLT.{u} Δ[n] n := by infer_instance) :
    False :=
  (lt_self_iff_false n).1 (Δ[n].dim_lt_of_nonDegenerate
    (nonDegenerateEquiv.2 (.refl _)) n)

/-- The bijection `(stdSimplex.obj n).op.obj d ≃ (stdSimplex.obj n).obj d` for any
`n : ℕ` and `d : ℕ`. See also `stdSimplex.opIso`. -/
protected def opObjEquiv {n : SimplexCategory} {d : SimplexCategoryᵒᵖ} :
    (stdSimplex.{u}.obj n).op.obj d ≃ (stdSimplex.obj n).obj d :=
  SSet.opObjEquiv.trans (objEquiv.trans
    (SimplexCategory.revEquivalence.fullyFaithfulFunctor.homEquiv.trans objEquiv.symm))

protected lemma opObjEquiv_apply {d n : ℕ} (f : Δ[n].op _⦋d⦌) (i : Fin (d + 1)) :
    stdSimplex.opObjEquiv.{u} f i = (opObjEquiv f i.rev).rev := rfl

lemma opObjEquiv_opObjEquiv_symm_apply {d n : ℕ} (f : (Δ[n] _⦋d⦌)) (i : Fin (d + 1)) :
    SSet.opObjEquiv (stdSimplex.opObjEquiv.{u}.symm f) i = (f i.rev).rev :=
  rfl

lemma map_rev_map_op_apply {n d d' : ℕ} (f : ⦋d⦌ ⟶ ⦋d'⦌) (g : Δ[n] _⦋d'⦌) (i : Fin (d + 1)) :
    dsimp% (show Δ[n] _⦋d⦌ from (Δ[n] : SSet.{u}).map (rev.map f).op g : Δ[n] _⦋d⦌) i =
      g (f i.rev).rev := rfl

/-- The opposite of `Δ[n]` is isomorphic to `Δ[n]`. -/
@[simps! hom_app_hom_apply inv_app_hom_apply]
def opIso (n : SimplexCategory) :
    (stdSimplex.{u}.obj n).op ≅ stdSimplex.obj n :=
  NatIso.ofComponents (fun d ↦ stdSimplex.opObjEquiv.toIso) (fun {d d'} f ↦ by
    ext g
    refine stdSimplex.ext _ _ (fun i ↦ ?_)
    dsimp
    rw [stdSimplex.opObjEquiv_apply, op_map]
    erw [Equiv.apply_symm_apply]
    dsimp
    rw [map_rev_map_op_apply]
    aesop)

end stdSimplex

section Examples

open Simplicial

/-- The simplicial circle. -/
noncomputable def S1 : SSet :=
  Limits.colimit <|
    Limits.parallelPair (stdSimplex.δ 0 : Δ[0] ⟶ Δ[1]) (stdSimplex.δ 1)

end Examples

namespace Augmented

/-- The functor which sends `⦋n⦌` to the simplicial set `Δ[n]` equipped by
the obvious augmentation towards the terminal object of the category of sets. -/
@[simps]
noncomputable def stdSimplex : SimplexCategory ⥤ SSet.Augmented.{u} where
  obj Δ :=
    { left := SSet.stdSimplex.obj Δ
      right := terminal _
      hom := { app := fun _ => terminal.from _ } }
  map θ :=
    { left := SSet.stdSimplex.map θ
      right := terminal.from _ }

end Augmented

end SSet
