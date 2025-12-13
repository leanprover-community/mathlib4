/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Finset
public import Mathlib.Order.Fin.SuccAboveOrderIso

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

@[simp]
lemma objEquiv_symm_apply {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (objEquiv.{u}.symm f : Δ[n] _⦋m⦌) i = f.toOrderHom i := rfl

/-- Constructor for simplices of the standard simplex which takes a `OrderHom` as an input. -/
abbrev objMk {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : Fin (len m.unop + 1) →o Fin (n.len + 1)) :
    (stdSimplex.{u}.obj n).obj m :=
  objEquiv.symm (Hom.mk f)

@[simp]
lemma objMk_apply {n m : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (i : Fin (m + 1)) :
    objMk.{u} (n := ⦋n⦌) (m := op ⦋m⦌) f i = f i :=
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
  uliftYonedaEquiv

instance (X : SSet.{u}) (n : SimplexCategory) [DecidableEq (X.obj (op n))] :
    DecidableEq (stdSimplex.obj n ⟶ X) :=
  fun a b ↦ decidable_of_iff (yonedaEquiv a = yonedaEquiv b) (by simp)

lemma yonedaEquiv_map {n m : SimplexCategory} (f : n ⟶ m) :
    yonedaEquiv.{u} (stdSimplex.map f) = objEquiv.symm f :=
  yonedaEquiv.symm.injective rfl

/-- The (degenerate) `m`-simplex in the standard simplex concentrated in vertex `k`. -/
def const (n : ℕ) (k : Fin (n + 1)) (m : SimplexCategoryᵒᵖ) : Δ[n].obj m :=
  objMk (OrderHom.const _ k )

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

end stdSimplex

lemma yonedaEquiv_comp {X Y : SSet.{u}} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ X) (g : X ⟶ Y) :
    yonedaEquiv (f ≫ g) = g.app _ (yonedaEquiv f) := rfl

namespace Subcomplex

variable {X : SSet.{u}}

lemma range_eq_ofSimplex {n : ℕ} (f : Δ[n] ⟶ X) :
    Subfunctor.range f = ofSimplex (yonedaEquiv f) :=
  Subfunctor.range_eq_ofSection' _

lemma yonedaEquiv_coe {A : X.Subcomplex} {n : SimplexCategory}
    (f : stdSimplex.obj n ⟶ A) :
    (DFunLike.coe (F := ((stdSimplex.obj n ⟶ Subfunctor.toFunctor A) ≃ A.obj (op n)))
      yonedaEquiv f).val = yonedaEquiv (f ≫ A.ι) := by
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
    obtain ⟨f, rfl⟩ := objEquiv.symm.surjective x
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
    { toFun f := ⟨objMk ((OrderHom.Subtype.val (SetLike.coe S)).comp
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
    Subfunctor.range (stdSimplex.δ i) = face.{u} {i}ᶜ := by
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
    ((isoNerve.{u} n).hom.app _ s).obj i = ULift.up (s i) := rfl

@[simp]
lemma isoNerve_inv_app_apply {n d : ℕ}
    (F : (nerve (ULift.{u} (Fin (n + 1)))) _⦋d⦌) (i : Fin (d + 1)) :
    (isoNerve.{u} n).inv.app _ F i = (F.obj i).down := rfl

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
