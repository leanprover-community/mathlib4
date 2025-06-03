/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.CategoryTheory.Subpresheaf.OfSection
import Mathlib.CategoryTheory.Limits.Types.Shapes
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.SuccAboveOrderIso

/-!
# The standard simplex

We define the standard simplices `Δ[n]` as simplicial sets.
See files `SimplicialSet.Boundary` and `SimplicialSet.Horn`
for their boundaries`∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open Simplicial`.)

-/

universe u

open CategoryTheory Limits Simplicial Opposite

namespace SSet

/-- The functor `SimplexCategory ⥤ SSet` which sends `SimplexCategory.mk n` to
the standard simplex `Δ[n]` is a cosimplicial object in the category of simplicial sets.
(This functor is essentially given by the Yoneda embedding). -/
def stdSimplex : CosimplicialObject SSet.{u} :=
  yoneda ⋙ uliftFunctor

@[deprecated (since := "2025-01-23")] alias standardSimplex := stdSimplex

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

/-- If `x : Δ[n] _⦋d⦌` and `i : Fin (d + 1)`, we may evaluate `x i : Fin (n + 1)`. -/
instance (n i : ℕ) : DFunLike (Δ[n] _⦋i⦌) (Fin (i + 1)) (fun _ ↦ Fin (n + 1)) where
  coe x j := (objEquiv x).toOrderHom j
  coe_injective' _ _ h := objEquiv.injective (by ext : 3; apply congr_fun h)

@[ext]
lemma ext {n d : ℕ} (x y : Δ[n] _⦋d⦌) (h : ∀ (i : Fin (d + 1)), x i = y i) : x = y :=
  DFunLike.ext _ _ h

@[simp]
lemma objEquiv_toOrderHom_apply {n i : ℕ}
    (x : (stdSimplex.{u} ^⦋n⦌).obj (op (.mk i))) (j : Fin (i + 1)) :
    DFunLike.coe (F := Fin (i + 1) →o Fin (n + 1))
      ((DFunLike.coe (F := Δ[n].obj (op ⦋i⦌) ≃ (⦋i⦌ ⟶ ⦋n⦌))
        objEquiv x)).toOrderHom j = x j :=
  rfl

lemma objEquiv_symm_comp {n n' : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : m.unop ⟶ n) (g : n ⟶ n') :
    objEquiv.{u}.symm (f ≫ g) =
      (stdSimplex.map g).app _ (objEquiv.{u}.symm f) := rfl

@[simp]
lemma objEquiv_symm_apply {n m : ℕ}
    (f : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (i : Fin (m + 1)) :
    (objEquiv.{u}.symm f : Δ[n] _⦋m⦌) i = f.toOrderHom i := rfl

/-- Constructor for simplices of the standard simplex which takes a `OrderHom` as an input. -/
abbrev objMk {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : Fin (len m.unop + 1) →o Fin (n.len + 1)) :
    (stdSimplex.{u}.obj n).obj m :=
  objEquiv.symm (Hom.mk f)

@[simp]
lemma objMk_apply {n m : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    objMk.{u} (n := .mk n) (m := op (.mk m)) f i = f i :=
  rfl

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `Fin (m+1)` to `Fin (n+1)`. -/
def asOrderHom {n} {m} (α : Δ[n].obj m) : OrderHom (Fin (m.unop.len + 1)) (Fin (n + 1)) :=
  α.down.toOrderHom

lemma map_apply {m₁ m₂ : SimplexCategoryᵒᵖ} (f : m₁ ⟶ m₂) {n : SimplexCategory}
    (x : (stdSimplex.{u}.obj n).obj m₁) :
    (stdSimplex.{u}.obj n).map f x = objEquiv.symm (f.unop ≫ objEquiv x) := by
  rfl

/-- The canonical bijection `(stdSimplex.obj n ⟶ X) ≃ X.obj (op n)`. -/
def _root_.SSet.yonedaEquiv {X : SSet.{u}} {n : SimplexCategory} :
    (stdSimplex.obj n ⟶ X) ≃ X.obj (op n) :=
  yonedaCompUliftFunctorEquiv X n

lemma yonedaEquiv_map {n m : SimplexCategory} (f : n ⟶ m) :
    yonedaEquiv.{u} (stdSimplex.map f) = objEquiv.symm f :=
  yonedaEquiv.symm.injective rfl

/-- The (degenerate) `m`-simplex in the standard simplex concentrated in vertex `k`. -/
def const (n : ℕ) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) : Δ[n].obj m :=
  objMk (OrderHom.const _ k )

@[simp]
lemma const_down_toOrderHom (n : ℕ) (k : Fin (n+1)) (m : SimplexCategoryᵒᵖ) :
    (const n k m).down.toOrderHom = OrderHom.const _ k :=
  rfl

/-- The `0`-simplices of `Δ[n]` identify to the elements in `Fin (n + 1)`. -/
@[simps]
def obj₀Equiv {n : ℕ} : Δ[n] _⦋0⦌ ≃ Fin (n + 1) where
  toFun x := x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl

/-- The edge of the standard simplex with endpoints `a` and `b`. -/
def edge (n : ℕ) (a b : Fin (n + 1)) (hab : a ≤ b) : Δ[n] _⦋1⦌ := by
  refine objMk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab

lemma coe_edge_down_toOrderHom (n : ℕ) (a b : Fin (n+1)) (hab : a ≤ b) :
    ↑(edge n a b hab).down.toOrderHom = ![a, b] :=
  rfl

/-- The triangle in the standard simplex with vertices `a`, `b`, and `c`. -/
def triangle {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c) : Δ[n] _⦋2⦌ := by
  refine objMk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, Matrix.tail_cons, Matrix.head_cons, true_and]

lemma coe_triangle_down_toOrderHom {n : ℕ} (a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b ≤ c) :
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

end stdSimplex

lemma yonedaEquiv_comp {X Y : SSet.{u}} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ X) (g : X ⟶ Y) :
    yonedaEquiv (f ≫ g) = g.app _ (yonedaEquiv f) := rfl

namespace Subcomplex

variable {X : SSet.{u}}

/-- The subcomplex of a simplicial set that is generated by a simplex. -/
abbrev ofSimplex {n : ℕ} (x : X _⦋n⦌) : X.Subcomplex := Subpresheaf.ofSection x

lemma range_eq_ofSimplex {n : ℕ} (f : Δ[n] ⟶ X) :
    Subpresheaf.range f = ofSimplex (yonedaEquiv f) :=
  Subpresheaf.range_eq_ofSection' _

lemma mem_ofSimplex_obj {n : ℕ} (x : X _⦋n⦌) :
    x ∈ (ofSimplex x).obj _ :=
  Subpresheaf.mem_ofSection_obj x

lemma ofSimplex_le_iff {n : ℕ} (x : X _⦋n⦌) (A : X.Subcomplex) :
     ofSimplex x ≤ A ↔ x ∈ A.obj _ :=
  Subpresheaf.ofSection_le_iff _ _

lemma yonedaEquiv_coe {A : X.Subcomplex} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ A) :
    (DFunLike.coe (F := ((stdSimplex.obj n ⟶ Subpresheaf.toPresheaf A) ≃ A.obj (op n)))
      yonedaEquiv f).val = yonedaEquiv (f ≫ A.ι) := by
  rfl

end Subcomplex

namespace stdSimplex

lemma face_eq_ofSimplex {n : ℕ} (S : Finset (Fin (n + 1))) (m : ℕ) (e : Fin (m + 1) ≃o S) :
    face.{u} S =
      Subcomplex.ofSimplex (X := Δ[n])
        (objMk ((OrderHom.Subtype.val _).comp
          e.toOrderEmbedding.toOrderHom)) := by
  apply le_antisymm
  · rintro ⟨k⟩ x hx
    induction' k using SimplexCategory.rec with k
    rw [mem_face_iff] at hx
    let φ : Fin (k + 1) →o S :=
      { toFun i := ⟨x i, hx i⟩
        monotone' := (objEquiv x).toOrderHom.monotone }
    refine ⟨Quiver.Hom.op
      (SimplexCategory.Hom.mk ((e.symm.toOrderEmbedding.toOrderHom.comp φ))), ?_⟩
    obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
    ext j : 1
    simpa only [Subtype.ext_iff] using e.apply_symm_apply ⟨_, hx j⟩
  · simp [Subcomplex.ofSimplex_le_iff]

/-- If `S : Finset (Fin (n + 1))` is order isomorphic to `Fin (m + 1)`,
then the face `face S` of `Δ[n]` is representable by `m`,
i.e. `face S` is isomorphic to `Δ[m]`, see `stdSimplex.isoOfRepresentableBy`. -/
def faceRepresentableBy {n : ℕ} (S : Finset (Fin (n + 1)))
    (m : ℕ) (e : Fin (m + 1) ≃o S) :
    (face S : SSet.{u}).RepresentableBy (.mk m) where
  homEquiv {j} :=
    { toFun f := ⟨objMk ((OrderHom.Subtype.val S.toSet).comp
          (e.toOrderEmbedding.toOrderHom.comp f.toOrderHom)), fun _ ↦ by aesop⟩
      invFun := fun ⟨x, hx⟩ ↦ SimplexCategory.Hom.mk
        { toFun i := e.symm ⟨(objEquiv x).toOrderHom i, hx (by aesop)⟩
          monotone' i₁ i₂ h := e.symm.monotone (by
            simp only [Subtype.mk_le_mk]
            exact OrderHom.monotone _ h) }
      left_inv f := by
        ext i : 3
        apply e.symm_apply_apply
      right_inv := fun ⟨x, hx⟩ ↦ by
        induction' j using SimplexCategory.rec with j
        dsimp
        ext i : 2
        exact congr_arg Subtype.val
          (e.apply_symm_apply ⟨(objEquiv x).toOrderHom i, _⟩) }
  homEquiv_comp f g := by aesop

/-- If a simplicial set `X` is representable by `SimplexCategory.mk m` for some `m : ℕ`,
then this is the corresponding isomorphism `Δ[m] ≅ X`. -/
def isoOfRepresentableBy {X : SSet.{u}} {m : ℕ} (h : X.RepresentableBy (.mk m)) :
    Δ[m] ≅ X :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso (objEquiv.trans h.homEquiv)) (by
    intros
    ext
    apply h.homEquiv_comp)

lemma ofSimplex_yonedaEquiv_δ {n : ℕ} (i : Fin (n + 2)) :
    Subcomplex.ofSimplex (yonedaEquiv (stdSimplex.δ i)) = face.{u} {i}ᶜ :=
  (face_eq_ofSimplex _ _ (Fin.succAboveOrderIso i)).symm

@[simp]
lemma range_δ {n : ℕ} (i : Fin (n + 2)) :
    Subpresheaf.range (stdSimplex.δ i) = face.{u} {i}ᶜ := by
  rw [Subcomplex.range_eq_ofSimplex]
  exact ofSimplex_yonedaEquiv_δ i

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

@[deprecated (since := "2025-01-26")] alias asOrderHom := stdSimplex.asOrderHom

end SSet
