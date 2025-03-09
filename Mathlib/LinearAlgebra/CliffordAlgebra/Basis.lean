/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Sign
import Mathlib.Tactic.SlimCheck

/-!
# A basis for the Clifford algebra

This file constructs `CliffordAlgebra.Model ι B`, which is a model for
`CliffordAlgebra (_ : ι →₀ R)` that also works as a basis.
-/

namespace List

variable {α : Type*} {r : α → α → Prop} [DecidableRel r]

theorem orderedInsert_eq_cons_of_forall_rel {l : List α} {x : α}
    (h : ∀ y ∈ l, r x y) :
    l.orderedInsert r x = x :: l :=
  match l with
  | [] => rfl
  | _ :: _ => if_pos <| h _ <| mem_cons_self _ _

theorem Sublist.orderedInsert_of_sorted [IsTrans α r]
    {l₁ l₂ : List α} (hl : l₁ <+ l₂) (h₁ : Sorted r l₁) (h₂ : Sorted r l₂) (x : α) :
    l₁.orderedInsert r x <+ l₂.orderedInsert r x :=
  match l₁, l₂ with
  | [], [] => .refl _
  | [], _ :: l₂ => by
    simp_rw [orderedInsert]
    split_ifs
    · exact .cons₂ _ (nil_sublist _)
    · exact .cons _ (by simp)
  | x₁ :: l₁, x₂ :: l₂ => by
    simp_rw [orderedInsert]
    cases hl with
    | cons₂ a ha =>
      split_ifs
      · exact (ha.cons₂ _).cons₂ _
      · rw [sorted_cons] at h₁ h₂
        exact (ha.orderedInsert_of_sorted h₁.2 h₂.2 _).cons₂ _
    | cons a ha =>
      rw [sorted_cons] at h₂
      have hx₂x₁:= h₂.1 _ <| ha.subset (mem_cons_self _ _)
      have haih := ha.orderedInsert_of_sorted h₁ h₂.2 x
      rw [orderedInsert] at haih
      split_ifs at * with hxx₁ hxx₂ hxx₂
      · exact (ha.cons _).cons₂ _
      · exact haih.cons _
      · exfalso
        exact (hxx₁ <| _root_.trans hxx₂ hx₂x₁).elim
      · exact haih.cons _

theorem orderedInsert_sublist_orderedInsert_iff_of_sorted [IsTrans α r] [IsRefl α r]
    {l₁ l₂ : List α} (h₁ : Sorted r l₁) (h₂ : Sorted r l₂) (x : α) :
    l₁.orderedInsert r x <+ l₂.orderedInsert r x ↔ l₁ <+ l₂ :=
  ⟨fun h => by classical simpa [erase_orderedInsert] using h.erase x,
    fun h => h.orderedInsert_of_sorted h₁ h₂ _⟩

theorem orderedInsert_sublist_orderedInsert_iff_of_sorted_of_not_mem [IsTrans α r] [IsAntisymm α r]
    {l₁ l₂ : List α} (h₁ : Sorted r l₁) (h₂ : Sorted r l₂) {x : α} (hx₁ : x ∉ l₁) (hx₂ : x ∉ l₂) :
    l₁.orderedInsert r x <+ l₂.orderedInsert r x ↔ l₁ <+ l₂ := by
  refine ⟨fun h => ?_, fun h => h.orderedInsert_of_sorted h₁ h₂ _⟩
  classical
  have := h.erase x
  rwa [erase_orderedInsert_of_not_mem hx₁, erase_orderedInsert_of_not_mem hx₂] at this

theorem erase_sublist_iff_sublist_orderedInsert_of_sorted_of_not_mem
    [DecidableEq α] [IsTrans α r] [IsAntisymm α r]
    (l₁ l₂ : List α) (h₁ : Sorted r l₁) (h₂ : Sorted r l₂) (x : α) (hx₂ : x ∉ l₂) :
    l₁.erase x <+ l₂ ↔ l₁ <+ l₂.orderedInsert r x := by
  by_cases hx₁ : x ∈ l₁; swap
  · rw [List.erase_of_not_mem hx₁]
    constructor
    · intro h
      exact h.trans <| sublist_orderedInsert x l₂
    · intro h
      have := h.erase x
      rwa [List.erase_of_not_mem hx₁, erase_orderedInsert_of_not_mem hx₂] at this
  constructor
  · intro h
    have := h.orderedInsert_of_sorted ?ot h₂ x
    rwa [orderedInsert_erase _ _ hx₁ h₁] at this
    exact h₁.sublist (erase_sublist x l₁)
  · intro h
    have := h.erase x
    rwa [erase_orderedInsert_of_not_mem hx₂] at this

-- -- theorem Pairwise

-- theorem pairwise_concat (R) (l : List α) (x) (h : List.pairwise)

end List

noncomputable section
namespace CliffordAlgebra

variable (ι : Type*) [LinearOrder ι]

/-- A sorted list of indices.

This is chosen instead of `Finset ι` as it makes computing signs more efficient. -/
abbrev Model.Index : Type _ := {l : List ι // l.Sorted (· < ·) }


variable {R : Type*} [CommRing R]

set_option linter.unusedVariables false in
/-- A model of the clifford algebra.

For a basis `b : Basis ι R M`, we have `B i i = Q (b i)` and `B i j = Q.polar (b i) (b j)`.
Note that in some sense this means the diagonal is halved.
-/
@[nolint unusedArguments]
def Model (B : ι → ι → R) : Type _ := Model.Index ι →₀ R

variable (B :  ι → ι → R)
instance : AddCommGroup (Model ι B) := inferInstanceAs <| AddCommGroup (Model.Index ι →₀ R)
instance : Module R (Model ι B) := inferInstanceAs <| Module R (Model.Index ι →₀ R)

namespace Model

variable {B ι} in
/-- Casting function to interpret the model as a finitely-supported function. -/
def ofFinsupp : (Model.Index ι →₀ R) ≃ₗ[R] Model ι B :=
  LinearEquiv.refl _ _

variable {ι}

/-- The index corresponding to a single basis vector `i`. -/
@[match_pattern]
abbrev Index.nil : Model.Index ι := ⟨[], by simp⟩

/-- The index corresponding to a single basis vector `i`. -/
@[simps]
def Index.single (i : ι) : Model.Index ι := ⟨[i], by simp⟩

/-- The element corresponding to a single basis element `is`. -/
def single (is : Model.Index ι) (r : R) : Model ι B :=
  Model.ofFinsupp <| Finsupp.single is r
/-- `Model.single` as a linear map. -/
def lsingle (is : Model.Index ι) : R →ₗ[R] Model ι B :=
  Model.ofFinsupp (B := B) ∘ₗ Finsupp.lsingle is

@[simp]
theorem lsingle_apply (is : Model.Index ι) (r : R) :
    Model.lsingle B is r = Model.single B is r := rfl

@[ext]
theorem lhom_ext {N : Type*} [AddCommMonoid N] [Module R N] ⦃f g : Model ι B →ₗ[R] N⦄
    (h : ∀ is, f ∘ₗ Model.lsingle B is = g ∘ₗ Model.lsingle B is) : f = g :=
  Finsupp.lhom_ext' h

@[simp]
lemma ofFinsupp_single (is : Model.Index ι) (r : R):
    Model.ofFinsupp (Finsupp.single is r) = Model.single B is r := rfl

@[simp]
lemma ofFinsupp_symm_single (is : Model.Index ι) (r : R) :
    Model.ofFinsupp.symm (Model.single B is r) = Finsupp.single is r := rfl

instance : One (Model ι B) where
  one := Model.single B .nil 1

lemma one_def : 1 = Model.single B .nil 1 := rfl

@[simp]
lemma ofFinsupp_symm_one :
    Model.ofFinsupp.symm (1 : Model ι B) = Finsupp.single .nil 1 := by
  rfl

lemma single_nil_eq_smul_one (r : R) : Model.single B .nil r = r • 1 :=
  (Model.ofFinsupp (B := B)).symm.injective <| by simp

open List in
example {ι} [LinearOrder ι] (i j : ι) (xs ys zs : List ι)
    (he1 : ys.erase j <+ zs)  -- zs may have `j` inserted in a sorted way
    (ae2: zs.erase i <+ xs)
    (hgt: j < i)
    (hjx : Sorted (· < ·) (j :: xs))
    (hy : Sorted (· < ·) ys)
    (hz : Sorted (· < ·) zs) :
    ys.erase i <+ j :: xs := by
sorry

/-- Prepend to an index. -/
@[simps]
def Index.cons (i : ι) (l : Model.Index ι) (h : ∀ j ∈ l.1, i < j) : Model.Index ι :=
  ⟨i :: l, l.2.cons h⟩

theorem Index.single_eq_cons (i : ι) : Index.single i = .cons i nil (by simp) := rfl

/-- Append to an index. -/
@[simps]
def Index.concat (l : Model.Index ι) (i : ι) (h : ∀ j ∈ l.1, j < i) : Model.Index ι :=
  ⟨l.val ++ [i], List.pairwise_reverse.mp <| by
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    exact .cons (by simpa only [List.mem_reverse] using h) (List.pairwise_reverse.mpr l.prop)⟩

theorem Index.single_eq_concat (i : ι) : Index.single i = .concat nil i (by simp) := rfl

@[elab_as_elim]
def Index.recOn {motive : Model.Index ι → Sort*}
    (nil : motive .nil) (cons : ∀ i l h, motive l → motive (.cons i l h))
    (l : Model.Index ι) : motive l :=
  match l with
  | .nil => nil
  | ⟨j :: xs, h⟩ =>
    letI xsi : Model.Index ι := ⟨xs, .of_cons h⟩
    cons j xsi (List.rel_of_sorted_cons h) (Index.recOn nil cons xsi)

@[simp]
theorem Index.recOn_nil {motive : Model.Index ι → Sort*}
    (nil : motive .nil) (cons : ∀ i l h, motive l → motive (.cons i l h)) :
    Index.recOn nil cons .nil = nil := rfl

@[simp]
theorem Index.recOn_cons {motive : Model.Index ι → Sort*}
    (nil : motive .nil) (cons : ∀ i l h, motive l → motive (.cons i l h))
    (i : ι) (l : Model.Index ι) (h) :
    Index.recOn nil cons (.cons i l h) = (cons i l h <| Index.recOn nil cons l) := by
  simp [Index.recOn, Index.cons]

@[elab_as_elim]
def Index.reverseRecOn {motive : Model.Index ι → Sort*}
    (nil : motive .nil) (concat : ∀ l i h, motive l → motive (.concat l i h))
    (l : Model.Index ι) : motive l := by
  let ⟨l, hl⟩ := l
  induction l using List.reverseRecOn with
  | nil => exact nil
  | append_singleton xs a ih =>
    letI xsi : Model.Index ι := ⟨xs, (List.pairwise_append.mp hl).1⟩
    refine concat xsi a ?_ (ih xsi.prop)
    simpa using (List.pairwise_append.mp hl).2.2

@[simp]
theorem Index.reverseRecOn_nil {motive : Model.Index ι → Sort*}
    (nil : motive .nil) (concat : ∀ l i h, motive l → motive (.concat l i h)) :
    Index.reverseRecOn nil concat .nil = nil := rfl

@[simp]
theorem Index.reverseRecOn_concat {motive : Model.Index ι → Sort*}
    (nil : motive .nil) (concat : ∀ l i h, motive l → motive (.concat l i h))
    (i : ι) (l : Model.Index ι) (h) :
    Index.reverseRecOn nil concat (.concat l i h) = (concat l i h <| Index.reverseRecOn nil concat l) := by
  simp [Index.reverseRecOn, Index.concat]

open List in
def Index.mulOfLt (i : ι) (l : Model.Index ι) (h : ∀ j ∈ l.1, i < j) :
      (Finsupp.supported _ R {i' | i'.1.erase i <+ l}).comap
        (Model.ofFinsupp (ι := ι) (B := B)).symm :=
    ⟨.single B (.cons i l h) 1,
      Finsupp.single_mem_supported R _ <| show _ <+ _ by simp [Index.cons]⟩

open List in
theorem singleMul_aux₁ {xs ys : List ι} {i j : ι}
    (hji : j < i)
    (h : ∀ k ∈ ↑xs, j < k)
    (hxys : List.erase ys i <+ ↑xs) :
    ∀ k ∈ ys, j < k := by
  intro k hk
  obtain rfl | hij' := eq_or_ne i k
  · exact hji
  · exact h _ <|
      hxys.subset <| (List.mem_erase_of_ne hij'.symm).2 hk

theorem singleMul_aux₂ {xs : List ι} {i j : ι}
    (hij : i < j)
    (h : ∀ k ∈ xs, j < k) :
    ∀ k ∈ j :: xs, i < k :=
  List.forall_mem_cons.mpr ⟨hij, fun _ hx => hij.trans <| h _ hx⟩

open List in
/-- Multiply a single vector `i` by a basis element `l`.

The support of the result is `l` with `i` inserted at the appropriate point. -/
def Index.singleMul (i : ι) (l : Model.Index ι) :
    (Finsupp.supported _ R {i' | i'.1.erase i <+ l}).comap
      (Model.ofFinsupp (ι := ι) (B := B)).symm :=
  l.recOn
    (nil := ⟨.single B (.single i) 1, Finsupp.single_mem_supported _ _ <| show _ <+ _ by simp⟩)
    (cons := fun j xs h ih =>
    ltByCases i j
      (fun hlt : i < j =>
        mulOfLt B i (cons j xs h) <| singleMul_aux₂ hlt h)
      (fun heq : i = j =>
        ⟨.single B xs (B i j),
          Finsupp.single_mem_supported _ _  <| (erase_sublist _ _).trans (sublist_cons _ _)⟩)
      (fun hgt : j < i =>
        -- vᵢ vⱼ ⋯ = (polar vᵢ vⱼ - vⱼ vᵢ) ⋯
        ⟨Model.single B xs (B i j),
          Finsupp.single_mem_supported _ _ <| (erase_sublist _ _).trans (sublist_cons _ _)⟩ -
          (let rest := Model.ofFinsupp.symm ih.1
          rest.support.attach.sum fun ⟨js, hjs⟩ =>
            haveI aux : _ <+ xs.val := ih.2 hjs
            ⟨.single B (.cons j js <| singleMul_aux₁ hgt h aux) (rest js),
            fun i' hi' => show _ <+ _ by
              replace hi' := Finsupp.support_single_subset hi'
              rw [Finset.mem_singleton] at hi'
              rw [hi', Index.cons, erase_cons_tail _ (not_beq_of_ne hgt.ne)]
              exact aux.cons₂ _⟩)))

-- The four lemmas defined by the recursion

@[simp]
lemma Index.singleMul_nil (i : ι) :
    Model.Index.singleMul B i (.nil) = Model.single B (.single i) 1 := rfl

@[simp]
lemma Index.singleMul_cons_same (i : ι) (is) (h) :
    Model.Index.singleMul B i (.cons i is h) = Model.single B is (B i i) := by
  erw [Model.Index.singleMul, Index.recOn]
  rw [ltByCases]
  simp only [single_coe, Submodule.comap_coe, lt_self_iff_false, ↓reduceDite, ofFinsupp_single,
    Model.single_nil_eq_smul_one]

@[simp]
lemma Index.singleMul_cons_of_lt (i j : ι) (hij : i < j) (l : Model.Index ι) (h) :
    Model.Index.singleMul B i (.cons j l h) =
      Model.single B (.cons i (.cons j l h) <| singleMul_aux₂ hij h) 1 := by
  erw [Model.Index.singleMul, Index.recOn]
  rw [ltByCases, dif_pos hij]
  dsimp [mulOfLt]

open scoped BigOperators
@[simp]
lemma Index.singleMul_cons_of_gt (i j : ι) (hij : i > j) (l : Model.Index ι) (h) :
    Model.Index.singleMul B i (.cons j l h) =
      Model.single B l (B i j) -
        ( letI rest' := Index.singleMul B i l
          let rest := ofFinsupp.symm ↑(rest' : Model ι B)
          ∑ js in rest.support.attach,
            Model.single B (.cons j js <| singleMul_aux₁ hij h <| rest'.prop js.prop) (rest js)) := by
  erw [Model.Index.singleMul, Index.recOn]
  rw [ltByCases, dif_pos hij, dif_neg hij.not_lt]
  dsimp
  rw [←Model.Index.singleMul]
  simp

-- some trivial consequences
section

lemma Index.singleMul_single_same (i : ι) :
    Model.Index.singleMul B i (.single i) = B i i • (1 : Model ι B) := by
  rw [single_eq_cons, singleMul_cons_same, single_nil_eq_smul_one]

@[simp]
lemma Index.singleMul_of_forall_le (i : ι) (l : Model.Index ι) (h) :
    Model.Index.singleMul B i l = Model.single B (.cons i l h) 1 := by
  induction l using Model.Index.recOn with
  | nil => simp only [Submodule.comap_coe, singleMul_nil, single_eq_cons]
  | cons j l h' _ih =>
    obtain ⟨hij, _⟩ := List.forall_mem_cons.1 h
    rw [singleMul_cons_of_lt _ _ _ hij]

end

/-- Multiply two basis elements together to get an element of the model. -/
def Index.mul (l₁ l₂ : Model.Index ι) : Model ι B :=
  l₁.recOn
    (.single B l₂ 1)
    (fun i _ _ x => (Model.ofFinsupp.symm x).sum fun ind val => val • ind.singleMul B i)

@[simp]
lemma Index.nil_mul (is : Model.Index ι) :
    Model.Index.mul B (.nil) is = .single B is 1 := by
  rw [Model.Index.mul, Index.recOn_nil]


/-- (xX)Y = x(XY)-/
lemma Index.cons_mul (l₁ l₂ : Model.Index ι) (a : ι) (h) :
  (l₁.cons a h).mul B l₂ =
    (Model.ofFinsupp.symm (Index.mul B l₁ l₂ : Model ι B)).sum fun ind val => val • ind.singleMul B a := by
  rw [mul, recOn_cons]
  rfl

@[simp]
lemma Index.mul_nil (is : Model.Index ι) :
    Model.Index.mul B is (.nil) = .single B is 1 := by
  induction is using Index.recOn with
  | nil => simp
  | cons is i h ih =>
    rw [Index.cons_mul]
    simp
    simp only [Submodule.comap_coe, ih, ofFinsupp_symm_single, zero_smul, Finsupp.sum_single_index,
      one_smul]
    rw [Index.singleMul_of_forall_le]

/-- (Xx)Y = X(xY)-/
lemma Index.concat_mul (l₁ l₂ : Model.Index ι) (a : ι) (h) :
  (l₁.concat a h).mul B l₂ =
    (Model.ofFinsupp.symm (Index.singleMul B a l₂ : Model ι B)).sum fun ind val => val • l₁.mul B ind := by
  rw [mul]
  simp
  sorry

@[simp]
lemma Index.single_mul_single_same (i : ι) :
    Model.Index.mul B (.single i) (.single i) = B i i • (1 : Model ι B) := by
  rw [Model.Index.mul, single_eq_cons, recOn_cons, recOn_nil, ofFinsupp_symm_single,
    Finsupp.sum_single_index, one_smul, ←single_eq_cons, singleMul_single_same]
  rw [zero_smul]

open scoped BigOperators

protected def mul : Model ι B →ₗ[R] Model ι B →ₗ[R] Model ι B :=
  (Finsupp.lsum R fun i => LinearMap.flip <|
    Finsupp.lsum R fun j => LinearMap.flip <|
      (LinearMap.mul R R).compr₂ (LinearMap.toSpanSingleton _ _ (i.mul B j))).compl₁₂
        (ofFinsupp (B := B)).symm.toLinearMap
        (ofFinsupp (B := B)).symm.toLinearMap

instance : Mul (Model ι B) where
  mul v w := Model.mul B v w

lemma mul_def (v w : Model ι B) : v * w = Model.mul B v w := rfl

@[simp]
lemma single_mul_single (i j : Model.Index ι) (r s : R):
    Model.single B i r * Model.single B j s = (r * s) • i.mul B j := by
  change Model.mul _ _ _ = _
  simp [Model.mul]


  -- induction j using Model.Index.recOn with
  -- | nil => simp
  -- | cons j js h ih =>
  --   simp
  --   sorry


/-! ### Algebraic structure instances -/

instance : NonUnitalNonAssocRing (Model ι B) where
  left_distrib _ _ _ := map_add _ _ _
  right_distrib _ _ _ := LinearMap.map_add₂ _ _ _ _
  mul_zero _ := map_zero _
  zero_mul _ := LinearMap.map_zero₂ _ _

instance : SMulCommClass R (Model ι B) (Model ι B) where
  smul_comm r x y := (LinearMap.map_smul (Model.mul B x) r y).symm

instance : IsScalarTower R (Model ι B) (Model ι B) where
  smul_assoc r x y := LinearMap.map_smul₂ (Model.mul B) r x y

instance : NonAssocRing (Model ι B) where
  one_mul x := by
    suffices Model.mul B 1 = .id from DFunLike.congr_fun this x
    ext xi
    simp [one_def, ← mul_def]
  mul_one x := by
    suffices (Model.mul B).flip 1 = .id from DFunLike.congr_fun this x
    ext xi
    simp [one_def, ← mul_def]


-- Associativity
lemma single_mul_indexMul (i j k : Model.Index ι) (r : R) :
    single B i r * j.mul B k = i.mul B j * single B k r := by
  induction i using Model.Index.recOn with
  | nil =>
    simp
    rw [single_nil_eq_smul_one, smul_one_mul]
  | cons i is h ih =>
    rw [Index.cons_mul]
    sorry

instance : Ring (Model ι B) where
  __ := inferInstanceAs (NonAssocRing (Model ι B))
  mul_assoc x y z := by
    -- restate as an equality of morphisms so that we can use `ext`
    suffices LinearMap.llcomp R _ _ _ (Model.mul B) ∘ₗ (Model.mul B) =
        (LinearMap.llcomp R _ _ _ LinearMap.lflip <|
          LinearMap.llcomp R _ _ _ (Model.mul B).flip ∘ₗ (Model.mul B)).flip from
      DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this x) y) z
    ext xi yi zi
    dsimp [← mul_def]
    simp [single_mul_indexMul]

instance : Algebra R (Model ι B) where
  toFun r := .single B .nil r
  map_one' := rfl
  map_mul' r s := by
    rw [single_mul_single]
    simp only [Model.single_nil_eq_smul_one]
    rfl
  map_zero' := Finsupp.single_zero _
  map_add' x y := Finsupp.single_add _ _ _
  commutes' r x := by
    dsimp
    rw [Model.single_nil_eq_smul_one, smul_one_mul, mul_smul_one]
  smul_def' r x := by
    dsimp
    rw [Model.single_nil_eq_smul_one, smul_one_mul]

@[simp]
lemma Model.ofFinsupp_symm_algebra_map (r : R) :
    Model.ofFinsupp.symm (algebraMap R (Model ι B) r) = Finsupp.single ⟨[], by simp⟩ r := by
  rfl

/-!
Un-adapted from below

-/

noncomputable def ofFreeVS : (ι →₀ R) →ₗ[R] Model ι B :=
  Model.ofFinsupp.toLinearMap ∘ₗ Finsupp.lmapDomain R R Model.Index.single

@[simp]
lemma ofFreeVS_single (i : ι) (r : R) :
    ofFreeVS B (Finsupp.single i r) = Model.single B (.single i) r := by
  unfold ofFreeVS
  simp

variable {A : Type} [Ring A] [Algebra R A]
variable {M : Type} [AddCommGroup M] [Module R M]

def liftToFun (f : (ι →₀ R) →ₗ[R] A)
    (hf : ∀ i, f (.single i 1) * f (.single i 1) = algebraMap _ _ (B i i)) :
    Model ι B →ₐ[R] A :=
  letI aux : Model ι B →ₗ[R] A :=
      (Finsupp.lsum (R := R) R fun i =>
        LinearMap.toSpanSingleton _ _ (i.val.map fun x => f (Finsupp.single x 1)).prod)
      ∘ₗ (Model.ofFinsupp (B := B)).symm.toLinearMap
  .ofLinearMap aux
    (by simp [aux])
    (by
      rw [LinearMap.map_mul_iff]
      ext xi yi
      dsimp [LinearMap.toSpanSingleton]
      simp [aux]
      sorry)

@[simps! symm_apply]
def lift :
    { f : (ι →₀ R) →ₗ[R] A // ∀ i, f (.single i 1) * f (.single i 1) = algebraMap _ _ (B i i)} ≃
      (Model ι B →ₐ[R] A) where
  toFun f := liftToFun B f.val f.property
  invFun F := ⟨F ∘ₗ ofFreeVS B, by
    intro m
    simp
    rw [← F.map_mul, single_mul_single, one_mul, one_smul]
    simp [Algebra.algebraMap_eq_smul_one]⟩
  left_inv f := by
    ext
    simp [liftToFun]
  right_inv F := by
    ext
    dsimp [liftToFun]
    sorry

@[simp]
lemma liftToFun_composed_single (i : ι) (r : R) (f : (ι →₀ R) →ₗ[R] A) (hf) :
    liftToFun B f hf (Model.single B (.single i) r) = f (Finsupp.single i r) := by
  simp [liftToFun, ← map_smul f r]

@[ext high]
theorem hom_ext {f g : Model ι B →ₐ[R] A}
    (h : f.toLinearMap.comp (ofFreeVS B) = g.toLinearMap.comp (ofFreeVS B)) :
    f = g := by
  apply (lift B).symm.injective
  rw [lift_symm_apply, lift_symm_apply]
  ext
  exact DFunLike.congr_fun h _

end Model

end CliffordAlgebra
