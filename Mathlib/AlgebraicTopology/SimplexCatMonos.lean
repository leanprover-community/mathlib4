import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.CommSq
import Mathlib.Data.Set.Image
import Mathlib.Order.SuccPred.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Intervals
open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

theorem mono_comp' {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Mono f) (hg : Mono g) :
    Mono (f ≫ g) := by
  letI := hf
  letI := hg
  apply mono_comp

lemma δ_congr {n : ℕ} {i j : Fin (n + 2)}
    (H : SimplexCategory.δ i = SimplexCategory.δ j) : i = j := by
  apply_fun SimplexCategory.Hom.toOrderHom at H
  rw [DFunLike.ext_iff] at H
  exact Fin.succAbove_left_injective <| funext H

lemma Arrow.ext (f g : Arrow C) (hl : f.left = g.left) (hr : f.right = g.right)
    (heq : f.hom ≫ eqToHom hr = eqToHom hl ≫ g.hom) :
    f = g := by
  cases f; cases g; cases hl; cases hr
  simp_all

lemma Arrow.left_eq (f g : Arrow C) (h : f = g) : f.left = g.left := by
  cases f; cases g; cases h
  simp_all

lemma Arrow.right_eq (f g : Arrow C) (h : f = g) : f.right = g.right := by
  cases f; cases g; cases h
  simp_all

lemma Arrow.hom_eq (f g : Arrow C) (h : f = g) :
    eqToHom (f.left_eq g h).symm ≫ f.hom ≫ eqToHom (f.right_eq g h) = g.hom := by
  cases f; cases g; cases h
  simp_all

lemma Arrow.hom_eq' (f g : Arrow C) (h : f = g) :
    HEq f.hom g.hom := by
  cases h
  rfl

lemma Arrow.ugh_left {X Y Z : C} (hX : X = Y) (f : Y ⟶ Z) :
    Arrow.mk (eqToHom hX ≫ f) = Arrow.mk f := by
  apply Arrow.ext
  · simp_all
  · simp_all
  · simp_all

lemma Arrow.ugh_right {X Y Z : C} (hZ : Y = Z) (f : X ⟶ Y) :
    Arrow.mk (f ≫ eqToHom hZ) = Arrow.mk f := by
  apply Arrow.ext
  · simp_all
  · simp_all
  · simp_all

lemma Arrow.ugh {X Y Z W : C} (hX : X = Y) (hZ : Z = W) (f : Y ⟶ Z) :
    Arrow.mk (eqToHom hX ≫ f ≫ eqToHom hZ) = Arrow.mk f := by
  apply Arrow.ext
  · simp_all
  · simp_all
  · simp_all

lemma δ_congr' {m n : ℕ} {i : Fin (m + 2)} {j : Fin (n + 2)}
    (H : Arrow.mk (SimplexCategory.δ i) = Arrow.mk (SimplexCategory.δ j)) : i.val = j.val := by
  have := Arrow.left_eq _ _ H
  have h' := Arrow.hom_eq _ _ H
  simp only [Arrow.mk_left] at this
  unfold SimplexCategory.mk at this
  unfold SimplexCategory at this
  cases this
  simp only [Arrow.mk_left, Arrow.mk_right, eqToHom_refl, Functor.id_obj, Arrow.mk_hom,
    Category.comp_id, Category.id_comp] at h'
  congr
  exact δ_congr h'

end CategoryTheory
namespace List

@[simp]
def simplexMonoInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else b :: simplexMonoInsert (a + 1) l

/-- `simplexMonoSort l` returns `l` sorted using the insertion sort algorithm. -/
@[simp]
def simplexMonoSort : List ℕ → List ℕ
  | [] => []
  | b :: l => simplexMonoInsert b (simplexMonoSort l)

@[simp]
theorem simplexMonoInsert_nil (a : ℕ) : [].simplexMonoInsert a = [a] :=
  rfl

theorem simplexMonoInsert_length : ∀ (L : List ℕ) (a : ℕ), (L.simplexMonoInsert a).length = L.length + 1
  | [], a => rfl
  | hd :: tl, a => by
    dsimp [simplexMonoInsert]
    split_ifs <;> simp [simplexMonoInsert_length tl]

theorem simplexMonoSort_length : ∀ (L : List ℕ), (L.simplexMonoSort).length = L.length
  | [] => rfl
  | hd :: tl => by
    dsimp [simplexMonoSort]
    rw [simplexMonoInsert_length, simplexMonoSort_length tl]

end List

namespace monos

def fml : ∀ (_ : ℕ), List ℕ → Bool
| _, [] => True
| m, a :: l => a < m ∧ fml (m + 1) l

theorem strictMono_of_mono {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    StrictMono (Fin.val ∘ f.toOrderHom) := by
  sorry

instance : DecidableEq SimplexCategory := by
  unfold SimplexCategory
  infer_instance

variable (m n : SimplexCategory)
instance (m n : SimplexCategory) : Repr (m ⟶ n) where
  reprPrec f _ := repr f.toOrderHom.1
instance : Repr SimplexCategory where
  reprPrec m _ := repr m.len
instance {C : Type*} [Category C] [∀ X Y : C, Repr (X ⟶ Y)] : Repr (Arrow C) where
  reprPrec m _ := repr m.hom

open SimplexCategory

structure thingy where
  (C : Type u)
  [instCat : Category.{v} C]
  [instDec : DecidableEq C]
  (obj : ℕ → C)
  (map : ∀ {n : ℕ} (_ : Fin (n + 2)), obj n ⟶ obj (n + 1))
  (cond : ∀ {n : ℕ} (i j : Fin (n + 2)) (_ : i ≤ j),
    map i ≫ map j.succ = map j ≫ map i.castSucc)

attribute [instance] thingy.instCat thingy.instDec

theorem thingy.cond' {M : thingy} {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.castSucc < j) :
    M.map i ≫ M.map j = M.map (j.pred sorry) ≫ M.map i.castSucc := by
  rw [← M.cond]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_iff_val_lt_val] using H

theorem thingy.cond'' {M : thingy} {n : ℕ} {i : Fin (n + 3)}
    {j : Fin (n + 2)} (H : i ≤ j.castSucc) :
    M.map (i.castLT sorry) ≫ M.map j.succ = M.map j ≫ M.map i := by
  rw [M.cond]
  · rfl
  · exact H

def simplexThingy : thingy where
  C := SimplexCategory
  obj := mk
  map := δ
  cond _ _ := δ_comp_δ

variable (a n : ℕ) (l : Arrow SimplexCategory)

def toArrowAux (M : thingy) : ∀ (_ : List ℕ), ℕ → Option (Arrow M.C)
| [], n => some ⟨M.obj n, M.obj n, 𝟙 _⟩
| a :: l, n => Option.recOn (toArrowAux M l (n + 1)) none fun l =>
  if ha : a < n + 2 ∧ M.obj (n + 1) = l.1 then
  some ⟨M.obj n, l.2, M.map ⟨a, ha.1⟩ ≫ eqToHom ha.2 ≫ l.hom⟩ else none

variable {M : thingy}

theorem toArrowAux_none_cons (l : List ℕ) (a n : ℕ) (hl : toArrowAux M l (n + 1) = none) :
    toArrowAux M (a :: l) n = none := by
  rw [toArrowAux]
  simp_all only [Functor.id_obj]

theorem toArrowAux_some_cons (l : List ℕ) (a n : ℕ) (hl : (toArrowAux M (a :: l) n).isSome) :
    (toArrowAux M l (n + 1)).isSome := by
  contrapose! hl
  simp_all only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none,
    toArrowAux_none_cons, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]

def toArrow (l : List ℕ) (n : ℕ) (H : (toArrowAux M l n).isSome) :
  Arrow M.C := Option.get _ H

def toArrowTail {l : List ℕ} {a n : ℕ} (H : (toArrowAux M (a :: l) n).isSome) :
    Arrow M.C := toArrow _ _ (toArrowAux_some_cons _ _ _ H)

theorem toArrowAux_none_cond {l : List ℕ} {a n : ℕ}
    {f : Arrow M.C}
    (hl : (toArrowAux M l (n + 1)) = some f)
    (hcond : ¬(a < n + 2 ∧ M.obj (n + 1) = f.left)) :
    toArrowAux M (a :: l) n = none := by
  rw [toArrowAux]
  simp_all only [not_and, Functor.id_obj, dite_eq_right_iff, imp_false, not_false_eq_true,
    implies_true]

theorem toArrowAux_some_cond {l : List ℕ} {a n : ℕ} {f : Arrow M.C}
    (hl : (toArrowAux M l (n + 1)) = some f)
    (hal : (toArrowAux M (a :: l) n).isSome) :
    a < n + 2 ∧ M.obj (n + 1) = f.left := by
  contrapose hal
  simp_all only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  exact toArrowAux_none_cond hl hal

theorem toArrowAux_some_cond' {l : List ℕ} {a n : ℕ}
    (hal : (toArrowAux M (a :: l) n).isSome) :
    a < n + 2 ∧ M.obj (n + 1) = (toArrowTail hal).left := by
  apply toArrowAux_some_cond (l := l)
  rw [toArrowTail, toArrow]
  simp only [Option.some_get]
  exact hal

theorem toArrow_cons {l : List ℕ} {a n : ℕ} {f : Arrow M.C}
    (hl : (toArrowAux M l (n + 1)) = some f)
    (hal : (toArrowAux M (a :: l) n).isSome) :
    toArrow (a :: l) n hal = ⟨M.obj n, f.2,
      M.map ⟨a, (toArrowAux_some_cond hl hal).1⟩ ≫ eqToHom (toArrowAux_some_cond hl hal).2
      ≫ f.hom⟩ := by
  simp_all only [toArrow, toArrowAux, Functor.id_obj]
  simp_rw [dif_pos (toArrowAux_some_cond hl hal)]
  simp only [Option.get_some]

theorem toArrowTail_eq {l : List ℕ} {a n : ℕ}
    (hal : (toArrowAux M (a :: l) n).isSome) :
    toArrowAux M l (n + 1) = some (toArrowTail hal) := by
  simp_all only [toArrowTail, toArrow, Option.some_get]

theorem toArrow_cons' {l : List ℕ} {a n : ℕ} (hal : (toArrowAux M (a :: l) n).isSome) :
    toArrow (a :: l) n hal = ⟨M.obj n, (toArrowTail hal).2,
      M.map ⟨a, (toArrowAux_some_cond (toArrowTail_eq hal) hal).1⟩
      ≫ eqToHom (toArrowAux_some_cond (toArrowTail_eq hal) hal).2
      ≫ (toArrowTail hal).hom⟩ :=
  toArrow_cons (toArrowTail_eq hal) _

theorem toArrow_left {l : List ℕ} {n : ℕ}
    (hl : (toArrowAux M l n).isSome) :
    (toArrow l n hl).left = M.obj n := by
  induction' l with a l _
  · simp_all only [toArrow, toArrowAux, Functor.id_obj]
    rfl
  · rw [toArrow_cons']

theorem toArrowAux_some_cons' {l : List ℕ} {a n : ℕ} (h : a < n + 2)
    (hl : (toArrowAux M l (n + 1)).isSome) : (toArrowAux M (a :: l) n).isSome := by
  rw [toArrowAux, ← Option.some_get hl]
  simp only [Functor.id_obj]
  rw [dif_pos]
  simp only [Option.isSome_some]
  constructor
  · assumption
  · erw [toArrow_left]

theorem castLE_le_strictMono {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : StrictMono f) (x : Fin (m + 1)) :
    Fin.castLE sorry x ≤ f x := by
  induction' x using Fin.inductionOn with x hx
  · simp only [Fin.castLE_zero, Fin.zero_le]
  · have := Fin.strictMono_iff_lt_succ.1 hf x
    simp_all only [Fin.castLE_castSucc, Fin.castLE_succ, ge_iff_le]
    rw [← Fin.castSucc_lt_iff_succ_le]
    exact lt_of_le_of_lt hx this

theorem eq_castLE {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : StrictMono f)
    (x : Fin (m + 1)) (hx : ∀ y, y ≤ x → Fin.castLE sorry y ∈ Set.range f) (z : Fin (m + 1))
    (hz : z ≤ x) :
    f z = Fin.castLE sorry z := by
  induction' z using Fin.inductionOn with z ih
  · rcases hx 0 (Fin.zero_le _) with ⟨w, hw⟩
    simp_all only [Set.mem_range, Fin.zero_le, Fin.castLE_zero]
    rw [← Fin.le_zero_iff, ← hw, hf.le_iff_le]
    exact Fin.zero_le _
  · specialize ih (le_trans (le_of_lt <| Fin.castSucc_lt_succ _) hz)
    contrapose! hx
    use z.succ, hz
    rintro ⟨w, hw⟩
    rcases lt_trichotomy w z.succ with (hzw | hzw | hzw)
    · rw [← Fin.le_castSucc_iff] at hzw
      apply_fun f at hzw
      · rw [hw, ih] at hzw
        simp_all only [Fin.castLE_castSucc, Fin.castLE_succ, ne_eq]
        rw [← not_lt] at hzw
        apply hzw
        exact Fin.lt_succ
      · exact StrictMono.monotone hf
    · apply_fun f at hzw
      rw [hw] at hzw
      exact hx hzw.symm
    · apply_fun f at hzw
      rw [hw] at hzw
      rw [← not_le] at hzw
      exact hzw (castLE_le_strictMono f hf _)
      exact hf

theorem eqOn_castLE {m : ℕ} {n : SimplexCategory} (f : mk (m + 1) ⟶ n)
    (a : Fin (m + 2)) (hf : Mono f)
    (H : ∀ x, x ≤ a → Fin.castLE sorry x ∈ Set.range f.toOrderHom) :
    Set.EqOn f.toOrderHom (Fin.castLE sorry) ({i | i ≤ a}) :=
  eq_castLE f.toOrderHom (strictMono_of_mono f hf) _ H

abbrev rangeCompl {m n : SimplexCategory} (f : m ⟶ n) :=
  Finset.image Fin.val (Finset.image f.toOrderHom Finset.univ)ᶜ

theorem compl_image_eq_insert_compl {m : ℕ} {n : SimplexCategory} (f : mk (m + 1) ⟶ n) (a : Fin (m + 2)) (hf : Mono f)
    (H : ∀ x, x ≤ a → Fin.castLE sorry x ∈ Set.range f.toOrderHom) :
    (Finset.image (δ a ≫ f).toOrderHom Finset.univ)ᶜ
      = insert ⟨a, sorry⟩ (Finset.image f.toOrderHom Finset.univ)ᶜ := by
  ext x
  constructor
  · contrapose!
    simp only [len_mk, Finset.mem_insert, Finset.mem_compl, Finset.mem_image, Finset.mem_univ,
      true_and, not_exists, not_or, not_forall, Decidable.not_not, comp_toOrderHom,
      OrderHom.comp_coe, Function.comp_apply, and_imp, forall_exists_index]
    intro hx y hy
    by_cases hya : y < a
    · use Fin.castPred y sorry
      simp only [δ, mkHom, Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
        Fin.succAboveOrderEmb_apply]
      rw [Fin.succAbove_castPred_of_lt]
      assumption
      assumption
    · use y.pred sorry
      simp only [δ, mkHom, Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
        Fin.succAboveOrderEmb_apply]
      rw [Fin.succAbove_pred_of_lt]
      assumption
      · rw [lt_iff_le_and_ne]
        refine ⟨not_lt.1 hya, ?_⟩
        intro hnot
        apply_fun f.toOrderHom at hnot
        apply hx
        erw [← hy, ← hnot]
        rw [eqOn_castLE f a hf H (le_refl a)]
        rfl
  · simp only [len_mk, Finset.mem_insert, Finset.mem_compl, Finset.mem_image, Finset.mem_univ,
    true_and, not_exists, comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    rintro (rfl | hright)
    · intro x hx
      by_cases hxa : x.castSucc < a
      · simp_all only [len_mk, Set.mem_range, δ, mkHom, Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply]
        rw [Fin.succAbove_of_castSucc_lt] at hx
        erw [eqOn_castLE f a hf H <| le_of_lt hxa] at hx
        apply ne_of_lt hxa
        ext
        rw [Fin.ext_iff] at hx
        simp only [len_mk, Fin.castLE_castSucc, Fin.coe_castLE] at hx
        exact hx
        exact hxa
      · simp_all only [len_mk, Set.mem_range, δ, mkHom, Hom.toOrderHom_mk,
        OrderEmbedding.toOrderHom_coe, Fin.succAboveOrderEmb_apply, not_lt]
        rw [Fin.succAbove_of_le_castSucc] at hx
        rw [Fin.le_castSucc_iff] at hxa
        apply_fun ⇑f.toOrderHom at hxa
        rw [eqOn_castLE f a hf H (le_refl a)] at hxa
        apply ne_of_lt hxa
        erw [hx]
        rfl
        exact strictMono_of_mono f hf
        assumption
    · intro y hy
      exact hright ((δ a).toOrderHom y) hy

theorem eqToHom_eq_cast {m n : SimplexCategory} (h : m = n) :
    ⇑(eqToHom h).toOrderHom = Fin.cast (h ▸ rfl) := by
  cases h
  rfl

theorem Fin.cast_bijective {m n : ℕ} (h : m = n) : Function.Bijective (Fin.cast h) :=
  (Fin.castOrderIso h).toEquiv.bijective

theorem toArrow_mono (n : ℕ) (l : List ℕ) (hl : l.Pairwise (· < ·))
    (H : (toArrowAux M l n).isSome)
    (hmono : ∀ {n : ℕ} (i : Fin (n + 2)), Mono (M.map i)) :
    Mono (toArrow _ _ H).hom := by
  revert n
  induction' l with a l ih
  · simp_all only [List.Pairwise.nil, toArrow, toArrowAux, Functor.id_obj, Option.get_some]
    infer_instance
  · intro n h
    simp_all only [List.pairwise_cons, true_implies, toArrowAux_some_cons]
    specialize ih (n + 1) (toArrowAux_some_cons _ _ _ h)
    rw [toArrow_cons' h]
    simp only [Functor.id_obj]
    letI : Mono (toArrowTail h).hom := ih
    rw [← Category.assoc]
    convert mono_comp _ _
    · exact mono_comp _ _
    · infer_instance

instance simplexThingy_mono {n : ℕ} (i : Fin (n + 2)) : Mono (simplexThingy.map i) := by
  simp only [simplexThingy]
  infer_instance

theorem rangeCompl_toArrow (n : ℕ) (l : List ℕ) (hl : l.Pairwise (· < ·))
    (H : (toArrowAux simplexThingy l n).isSome) :
    rangeCompl (toArrow l n H).hom = l.toFinset := by
  revert n
  induction' l with a l ih
  · intro n H
    simp_all only [List.Pairwise.nil, simplexThingy, Functor.id_obj, List.toFinset_nil,
      Finset.image_eq_empty, Finset.compl_eq_empty_iff]
    simp_all only [List.Pairwise.nil, rangeCompl, toArrow, toArrowAux, Functor.id_obj,
      Option.get_some, len_mk, id_toOrderHom, OrderHom.id_coe, Finset.image_id, Finset.compl_univ,
      Finset.image_empty, List.toFinset_nil]
  · intro n H
    simp only [List.pairwise_cons, Functor.id_obj, List.toFinset_cons, Finset.coe_insert] at hl ⊢
    specialize ih hl.2 (n + 1) (toArrowAux_some_cons _ _ _ H)
    rw [toArrow_cons']
    --split_ifs with ha
   -- · rw [dif_pos ha]
    dsimp only
    rw [rangeCompl] at *
    erw [compl_image_eq_insert_compl (eqToHom (toArrowAux_some_cond' H).2 ≫ (toArrowTail H).hom)
      ⟨a, (toArrowAux_some_cond' H).1⟩]
    simp only [Functor.id_obj, len_mk, comp_toOrderHom, OrderHom.comp_coe, List.coe_toFinset]
    --rw [Set.range_comp]
    rw [← Finset.image_image]
    erw [eqToHom_eq_cast (toArrowAux_some_cond' H).2]
    rw [Finset.image_univ_of_surjective]
    rw [Finset.image_insert]
    erw [ih]
    exact (Fin.cast_bijective _).2
    letI : Mono (toArrowTail H).hom := toArrow_mono (n + 1) l hl.2
      (toArrowAux_some_cons _ _ _ H) (simplexThingy_mono)
    exact mono_comp _ _
    intro x hx
    by_contra hnot
    rw [← not_lt] at hx
    apply hx
    rw [Fin.lt_iff_val_lt_val]
    apply hl.1
    rw [← List.mem_toFinset]
    show (x : ℕ) ∈ (l.toFinset : Set ℕ)
    rw [← ih]
    rw [Finset.mem_coe, Finset.mem_image]
    use (Fin.castLE sorry x)
    constructor
    · apply Finset.mem_compl.2
      intro hnot'
      apply hnot
      rw [Finset.mem_image] at hnot'
      rcases hnot' with ⟨w, _, hw⟩
      rw [← hw]
      use (eqToHom (toArrowAux_some_cond' H).2.symm).toOrderHom w
      simp only [Functor.id_obj, len_mk, comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
      erw [eqToHom_eq_cast, eqToHom_eq_cast]
      congr
    · rfl

abbrev sorted (l : List ℕ) : Prop := l.simplexMonoSort = l

def order2 {m n : SimplexCategory} (f : m ⟶ n) : List ℕ :=
    Finset.sort (· ≤ ·) (rangeCompl f)

theorem List.sort_toFinset (l : List ℕ) (hl : l.Sorted (· < ·)) :
    Finset.sort (· ≤ ·) l.toFinset = l := by
  have : l.Nodup := hl.nodup
  unfold Finset.sort Multiset.sort List.toFinset Multiset.toFinset
  simp only [Multiset.coe_dedup, Multiset.lift_coe]
  rw [List.dedup_eq_self.2 this]
  rw [List.mergeSort_eq_insertionSort]
  rw [(List.Sorted.le_of_lt hl).insertionSort_eq]

theorem mem_or_le_of_mem_simplexMonoInsert (a : ℕ) (l : List ℕ) (x : ℕ) (hx : x ∈ l.simplexMonoInsert a) :
    x ∈ l ∨ a ≤ x := by
  revert a
  induction' l with b l ih
  · intro a ha
    simp_all only [List.simplexMonoInsert, List.mem_singleton, List.not_mem_nil, le_refl, or_true]
  · intro a ha
    by_cases hab : a < b
    · simp_all only [List.simplexMonoInsert, ite_true, List.mem_cons]
      rcases ha with (rfl | rfl | hl)
      · right; rfl
      · left; left; rfl
      · left; right; assumption
    · simp_all only [List.simplexMonoInsert, ite_false, List.mem_cons, not_lt]
      rcases ha with (rfl | hl)
      · left; left; rfl
      · rcases ih (a + 1) hl with (hl | ha)
        · left; right; assumption
        · right; linarith

theorem idfk (a : ℕ) (l : List ℕ) (hl : l.Pairwise (· < ·)) :
    (l.simplexMonoInsert a).Pairwise (· < ·) := by
  revert a
  induction' l with b l ih
  · simp_all only [List.Pairwise.nil, List.simplexMonoInsert, List.pairwise_cons, List.not_mem_nil,
    false_implies, implies_true, and_self]
  · intro a
    simp_all only [List.pairwise_cons, List.simplexMonoInsert, true_implies]
    by_cases hab : a < b
    · simp_all only [ite_true, List.pairwise_cons, List.mem_cons, forall_eq_or_imp, true_and,
      implies_true, and_self, and_true]
      intro c hc
      exact lt_trans hab (hl.1 c hc)
    · rw [if_neg hab]
      simp_all only [not_lt, List.pairwise_cons, and_true]
      intro c hc
      rcases mem_or_le_of_mem_simplexMonoInsert (a + 1) l c hc with (hleft | hright)
      · exact hl.1 c hleft
      · linarith

theorem simplexMonoSort_sorted (l : List ℕ) :
    (l.simplexMonoSort).Sorted (· < ·) := by
  induction' l with a l ih
  · simp_all only [List.simplexMonoSort, List.sorted_nil]
  · exact idfk a _ ih

theorem order2_sorted {m n : SimplexCategory} (f : m ⟶ n) :
    (order2 f).Sorted (· < ·) := by
  dsimp [order2]
  exact Finset.sort_sorted_lt _

theorem order2_toArrow (l : List ℕ) (hl : l.Sorted (· < ·)) (n : ℕ)
    (H : (toArrowAux simplexThingy l n).isSome) :
    order2 (toArrow _ _ H).hom = l := by
  unfold order2
  have h2 : Finset.sort (· ≤ ·) l.toFinset = l := by
    exact List.sort_toFinset _ hl
  conv_rhs =>
    rw [← h2]
  congr
  rw [rangeCompl_toArrow n l hl H]

theorem toArrowAux_order2_none {m n : SimplexCategory} (f : m ⟶ n)
    (a : ℕ) (l : List ℕ) (H : order2 f = a :: l) {k : ℕ}
    (hl : toArrowAux M l (k + 1) = none) :
    toArrowAux M (order2 f) k = none := by
  simp_all only [toArrowAux, mk_len, Functor.id_obj]

theorem toArrowAux_order2_some {m n : SimplexCategory} (f : m ⟶ n)
    (a : ℕ) (l : List ℕ) (H : order2 f = a :: l) {k : ℕ}
    (hl : (toArrowAux M (order2 f) k).isSome) :
    (toArrowAux M l (k + 1)).isSome := by
  contrapose! hl
  simp_all only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  rw [← H]
  exact toArrowAux_order2_none f a l H hl

theorem fml_cons_cons (l : List ℕ) (a b n : ℕ) (hfml : fml (n + 1) (b :: l))
    (hl : (a :: b :: l).Sorted (· < ·)) :
    fml n (a :: b :: l) := by
  simp_all only [fml, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.sorted_cons, List.mem_cons, forall_eq_or_imp, and_self, decide_True, and_true]
  linarith [hfml.1, hl.1.1]

theorem lt_sub_length_of_cons_lt {l : List ℕ} {a n : ℕ} (hl : (a :: l).Sorted (· < ·))
    (hn : ∀ x ∈ a :: l, x < n) : a < n - l.length := by
  revert a n
  induction' l with b l ih
  · intros a n hn ha
    simp_all only [List.sorted_singleton, List.mem_singleton, forall_eq, List.length_nil, tsub_zero]
  · intros a n hn ha
    simp_all only [List.sorted_cons, List.mem_cons, forall_eq_or_imp, and_imp, List.length_cons,
      true_implies]
    specialize @ih b n hn.2.1 ha.2.1 ha.2.2
    simp_all only [Nat.lt_sub_iff_add_lt]
    linarith

theorem fml_of_forall_lt {l : List ℕ} (hl : l.Sorted (· < ·)) (n : ℕ) (H : ∀ x ∈ l, x < n + l.length - 1) :
    fml n l := by
  revert n
  induction' l with a l ih
  · intro n hn
    simp_all only [List.sorted_nil, List.not_mem_nil, false_implies, implies_true, fml, decide_True]
  · intro n hn
    simp only [fml, List.length_cons, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    have := lt_sub_length_of_cons_lt hl hn
    simp_all only [List.sorted_cons, List.mem_cons, List.length_cons, Nat.add_succ_sub_one,
      forall_eq_or_imp, add_tsub_cancel_right, Nat.succ_add_sub_one, implies_true, and_self]

theorem toArrowAux_some_of_forall_lt {l : List ℕ} (hl : l.Sorted (· < ·)) (n : ℕ) (H : ∀ x ∈ l, x < n + l.length + 1) :
    (toArrowAux M l n).isSome := by
  revert n
  induction' l with a l hal
  · simp_all only [List.sorted_nil, List.not_mem_nil, false_implies, implies_true, toArrowAux,
    Functor.id_obj, Option.isSome_some, imp_self]
  · intro n hn
    have := fml_of_forall_lt hl (n + 2) ?_
    simp_all only [List.sorted_cons, List.mem_cons, List.length_cons, Nat.add_succ_sub_one,
      forall_eq_or_imp, true_implies]
    simp only [fml, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    specialize hal (n + 1) ?_
    · intro x hx
      convert hn.2 x hx using 1
      sorry
    rw [toArrowAux]
    have h432 : toArrowAux M l (n + 1) = some (toArrow _ _ hal) := by
      simp only [toArrow, Option.some_get]
    simp_all only [Functor.id_obj]
    rw [dif_pos]
    · simp only [Option.isSome_some]
    · rw [toArrow_left]
      simp only [and_self]
    · intro x hx
      convert hn x hx using 1
      simp only [List.length_cons, Nat.add_succ_sub_one]
      rw [add_right_comm]
      rfl

theorem order2_length {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    m.len + (order2 f).length = n.len := by
  rw [order2, Finset.length_sort, rangeCompl, Finset.card_image_of_injective, Finset.card_compl, Finset.card_image_of_injective,
      Finset.card_univ]
  simp only [Fintype.card_fin, Nat.reduceSubDiff]
  rw [Nat.add_sub_cancel']
  exact SimplexCategory.len_le_of_mono hf
  · exact SimplexCategory.mono_iff_injective.1 hf
  · exact Fin.val_injective

theorem lt_of_order2_eq_cons {m n : SimplexCategory} (f : m ⟶ n) {a : ℕ} {l : List ℕ} (h : order2 f = a :: l)
    (hf : Mono f) :
    a < m.len + 2 := by
  have : m.len + 2 = n.len + 2 - (a :: l).length := by
    rw [← h, ← order2_length f hf, Nat.add_right_comm, Nat.add_sub_cancel]
  rw [this]
  simp only [List.length_cons, Nat.reduceSubDiff, gt_iff_lt]
  apply lt_sub_length_of_cons_lt
  · rw [← h, order2]
    exact Finset.sort_sorted_lt (rangeCompl f)
  · rw [← h, order2]
    intro x hx
    rw [Finset.mem_sort, rangeCompl, Finset.mem_image] at hx
    rcases hx with ⟨a, ha, rfl⟩
    exact a.2

theorem fml_order2 {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    fml (m.len + 2) (order2 f) := by
  apply fml_of_forall_lt
  · exact Finset.sort_sorted_lt _
  · intro x hx
    rw [order2, Finset.mem_sort, rangeCompl, Finset.mem_image] at hx
    rcases hx with ⟨a, ha, rfl⟩
    have := order2_length f hf
    rw [add_right_comm, this]
    exact a.2

theorem toArrowAux_some_of_mono {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f)
    {k : ℕ} (hk : m.len ≤ k) :
    (toArrowAux M (order2 f) k).isSome := by
  induction' hx : order2 f with a l hal
  · simp_all only [order2, toArrowAux, mk_len, Functor.id_obj, Option.isSome_some]
  · have := toArrowAux_some_of_forall_lt (M := M) (l := (order2 f)) (Finset.sort_sorted_lt _) k ?_
    · rwa [hx] at this
    · intro y hy
      have : y < m.len + (order2 f).length + 1 := by
        rw [order2_length f hf]
        rw [order2, Finset.mem_sort, rangeCompl, Finset.mem_image] at hy
        rcases hy with ⟨a, ha, rfl⟩
        exact a.2
      omega

theorem toArrow_right (l : List ℕ) (n : ℕ) (hl : (toArrowAux M l n).isSome) :
     (toArrow l n hl).right = M.obj (n + l.length) := by
  revert n
  induction' l with a l hal
  · intro n hl
    simp_all only [simplexThingy, List.length_nil, add_zero]
    simp_all only [toArrow, toArrowAux, Functor.id_obj, Option.get_some, List.length_nil, add_zero]
  · intro n hl
    rw [toArrow_cons' hl]
    have := hal (n + 1) (toArrowAux_some_cons _ _ _ hl)
    simp only [List.length_cons]
    erw [this]
    rw [add_right_comm, add_assoc]

theorem toArrow_cons_hom {l : List ℕ} {a n : ℕ} (hal : (toArrowAux M (a :: l) n).isSome) :
    (toArrow (a :: l) n hal).hom
    = eqToHom (toArrow_left _) ≫ M.map ⟨a, (toArrowAux_some_cond (toArrowTail_eq hal) hal).1⟩
      ≫ eqToHom (toArrowAux_some_cond (toArrowTail_eq hal) hal).2
      ≫ (toArrowTail hal).hom ≫ eqToHom (by
      simp only [toArrowTail, Functor.id_obj, toArrow_cons' hal]) := by
  have := Arrow.hom_eq _ _ (toArrow_cons' hal)
  simp only [Functor.id_obj] at this
  rw [← IsIso.eq_inv_comp, ← IsIso.eq_comp_inv] at this
  rw [this]
  simp only [Functor.id_obj, inv_eqToHom, Category.assoc]

theorem order2_comp_eqToHom {m n o : SimplexCategory} (f : m ⟶ n) {h : n = o} :
    order2 (f ≫ eqToHom h) = order2 f := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

theorem order2_eqToHom_comp {m n o : SimplexCategory} (f : m ⟶ n) {h : o = m} :
    order2 (eqToHom h ≫ f) = order2 f := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

lemma card_range_mono {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    Fintype.card (Set.range f.toOrderHom) = m.len := sorry

lemma card_compl_range {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    Fintype.card (Fin.val '' (Set.range f.toOrderHom)ᶜ) = n.len - m.len := sorry

theorem order2_injectiveish {m n : SimplexCategory} (f g : m ⟶ n) (hf : Mono f) (hg : Mono g)
    (h : order2 f = order2 g) : f = g := by
  ext : 2
  have hsmf : StrictMono f.toOrderHom := sorry
  have hsmg : StrictMono g.toOrderHom := by sorry
  apply Fin.strictMono_unique hsmf hsmg
  unfold order2 at h
  apply_fun List.toFinset at h
  simp_all only [rangeCompl, Finset.sort_toFinset]
  replace h := compl_injective <| Finset.image_injective Fin.val_injective h
  apply_fun Finset.toSet at h
  simp_all only [Finset.coe_image, Finset.coe_univ, Set.image_univ]

theorem toArrow_order2 {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    toArrow (order2 f) m.len (toArrowAux_some_of_mono (M := simplexThingy) f hf (le_refl _)) = Arrow.mk f := by
  refine Arrow.ext _ _ ?_ ?_ ?_
  · rw [toArrow_left]
    rfl
  · rw [toArrow_right, order2_length f hf]
    rfl
  · simp only [Functor.id_obj, Arrow.mk_right, Arrow.mk_left, Arrow.mk_hom]
    apply order2_injectiveish
    · letI := toArrow_mono m.len (order2 f) (Finset.sort_sorted_lt _) (toArrowAux_some_of_mono f hf (le_refl _))
        (simplexThingy_mono)
      exact mono_comp _ _
    · letI := hf
      exact mono_comp _ _
    · rw [order2_comp_eqToHom, order2_eqToHom_comp]
      rw [order2_toArrow]
      · exact Finset.sort_sorted_lt _

theorem toArrowAux_some_append {x y : List ℕ} {m n : ℕ} (hx : (toArrowAux M x m).isSome)
    (hy : (toArrowAux M y n).isSome) (h : m + x.length = n) :
    (toArrowAux M (x ++ y) m).isSome := by
  induction' x with a l hal generalizing m
  · simp_all only [List.length_nil, add_zero, List.nil_append]
  · simp_all only [List.length_cons, List.cons_append]
    rw [toArrowAux]
    specialize @hal (m + 1) (toArrowAux_some_cons _ _ _ hx) ?_
    · rw [add_right_comm, add_assoc, h]
    · rw [← Option.some_get hal]
      simp only [Functor.id_obj]
      rw [dif_pos]
      simp only [Option.isSome_some]
      constructor
      · exact (toArrowAux_some_cond' hx).1
      · exact (toArrow_left hal).symm

theorem arrowMk_eq_toArrow_Append {x y : List ℕ} {m n : ℕ} (hx : (toArrowAux M x m).isSome)
    (hy : (toArrowAux M y n).isSome) (h : m + x.length = n) :
    Arrow.mk ((toArrow x m hx).hom ≫ eqToHom (by simp [toArrow_left, toArrow_right, h])
      ≫ (toArrow y n hy).hom)
      = toArrow (x ++ y) m (toArrowAux_some_append hx hy h) := by
  induction' x with a l hal generalizing m
  · refine Arrow.ext _ _ ?_ ?_ ?_
    · simp_all only [Functor.id_obj, Arrow.mk_left, toArrow_left, List.nil_append]
    · simp_all only [Functor.id_obj, Arrow.mk_right, ← h, List.length_nil, add_zero, toArrow_right,
      List.nil_append]
    · simp_all only [toArrow, toArrowAux, Functor.id_obj, Option.get_some, List.length_nil,
      Nat.add_zero, Arrow.mk_left, List.nil_append, Arrow.mk_right, Arrow.mk_hom, Category.id_comp,
      Category.assoc, ← h, add_zero, eqToHom_naturality, eqToHom_trans_assoc]
  · simp_rw [List.cons_append, toArrow_cons']
    refine Arrow.ext _ _ ?_ ?_ ?_
    · simp_all only [Functor.id_obj, Arrow.mk_left, toArrow_left, List.cons_append]
    · simp_all only [← h, List.length_cons, Functor.id_obj, Arrow.mk_right, toArrow_right,
      List.cons_append, List.length_append]
      erw [toArrow_right]
      simp only [List.length_append]
      sorry
    · simp_all only [Functor.id_obj, List.length_cons, Arrow.mk_left, List.cons_append,
      Arrow.mk_right, Arrow.mk_hom, Category.assoc]
      specialize @hal (m + 1) (toArrowAux_some_cons _ _ _ hx) ?_
      · simp only [add_right_comm, add_assoc, ← h, List.length_cons]
      replace hal := Arrow.hom_eq _ _ hal
      simp only [List.length_cons, Functor.id_obj, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
        Category.assoc] at hal
      erw [← hal]
      simp only [← Category.assoc, eqToHom_trans]
      congr 2
      rw [← IsIso.eq_comp_inv]
      simp only [Category.assoc, inv_eqToHom, eqToHom_trans]
      apply_fun Arrow.mk using Arrow.mk_injective _ _
      simp only [Functor.id_obj, Arrow.mk_eq]
      simp_rw [toArrow_cons' hx]
      refine Arrow.ext _ _ ?_ ?_ ?_
      · simp only [Arrow.mk_left, toArrow_left]
      · simp only [Arrow.mk_right]
        erw [toArrow_right, toArrow_right]
        simp only [add_right_comm, add_assoc, List.length_cons]
      · simp only [Functor.id_obj, List.cons_append, id_eq, List.length_cons, Arrow.mk_left,
        Arrow.mk_right, Category.assoc, Arrow.mk_hom, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
        rfl

theorem toArrowAux_simplexMonoInsert_isSome {l : List ℕ} {a m : ℕ} (h : (toArrowAux M l (m + 1)).isSome) (ha : a < m + 2) :
    (toArrowAux M (l.simplexMonoInsert a) m).isSome := by
  induction' l with b l hbl generalizing m a
  · simp only [toArrowAux, Functor.id_obj, and_true, eqToHom_refl, Category.comp_id]
    rw [dif_pos]
    simp only [Option.isSome_some]
    assumption
  · simp_all only [List.simplexMonoInsert]
    split_ifs with hab
    · rw [toArrowAux, ← Option.some_get h]
      simp only [Functor.id_obj]
      rw [dif_pos]
      simp only [Option.isSome_some]
      constructor
      · assumption
      · erw [toArrow_left]
    · specialize @hbl (a + 1) (m + 1) (toArrowAux_some_cons _ _ _ h) (by linarith)
      rw [toArrowAux, ← Option.some_get hbl]
      simp_all only [not_lt, Functor.id_obj]
      rw [dif_pos]
      simp only [Option.isSome_some]
      constructor
      · linarith
      · erw [toArrow_left]

theorem toArrowAux_simplexMonoSort_isSome {l : List ℕ} {m : ℕ} (h : (toArrowAux M l m).isSome) :
    (toArrowAux M l.simplexMonoSort m).isSome := by
  induction' l with b l hbl generalizing m
  · simp only [toArrowAux, Functor.id_obj, Option.isSome_some]
  · simp only [List.simplexMonoSort]
    apply toArrowAux_simplexMonoInsert_isSome
    apply hbl
    exact toArrowAux_some_cons _ _ _ h
    exact (toArrowAux_some_cond' h).1

theorem toArrow_simplexMonoInsert_eq {l : List ℕ} {a m : ℕ} (h : (toArrowAux M l (m + 1)).isSome) (ha : a < m + 2) :
    toArrow (l.simplexMonoInsert a) m (toArrowAux_simplexMonoInsert_isSome h ha)
      = toArrow (a :: l) m (toArrowAux_some_cons' ha h) := by
  induction' l with b l hbl generalizing m a
  · simp_all only [List.simplexMonoInsert]
  · simp_all only [List.simplexMonoInsert]
    split_ifs with hab
    · simp_all only [ite_true]
    · specialize @hbl (a + 1) (m + 1) (toArrowAux_some_cons _ _ _ h) (by linarith)
      refine Arrow.ext _ _ ?_ ?_ ?_
      · rw [toArrow_left, toArrow_left]
      · simp only [toArrow_right, List.length_cons, List.simplexMonoInsert_length]
      · rw [toArrow_cons_hom (toArrowAux_some_cons' ha h)]
        unfold toArrowTail
        simp_rw [toArrow_cons_hom h]
        simp only [Functor.id_obj, inv_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp, eqToHom_trans]
        slice_rhs 2 3 =>
          rw [← M.cond'' (by simp [not_lt.1 hab])]
        rw [toArrow_cons_hom (toArrowAux_some_cons' ?_ ?_)]
        simp only [Functor.id_obj, inv_eqToHom, Category.assoc, eqToHom_trans, Fin.castLT_mk,
          Fin.succ_mk, Nat.succ_eq_add_one]
        · congr 2
          unfold toArrowTail
          have h3 := Arrow.hom_eq _ _ hbl
          rw [← IsIso.eq_inv_comp, ← IsIso.eq_comp_inv] at h3
          simp_rw [h3]
          simp only [Int.reduceNeg, Int.rawCast, Int.cast_id, Nat.rawCast, Nat.cast_id,
            Int.Nat.cast_ofNat_Int, Nat.cast_ofNat, Int.reduceAdd, Int.ofNat_eq_coe, eq_mp_eq_cast,
            id_eq, Functor.id_obj, inv_eqToHom, Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
          rw [toArrow_cons_hom <| toArrowAux_some_cons' ?_ ?_]
          · simp only [Int.reduceNeg, Functor.id_obj, Category.assoc, eqToHom_trans,
            eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
            rfl
          · linarith
          · exact toArrowAux_some_cons _ _ _ h
        · linarith
        · apply toArrowAux_simplexMonoInsert_isSome
          · exact toArrowAux_some_cons _ _ _ h
          · linarith

theorem toArrow_simplexMonoSort_eq {l : List ℕ} {m : ℕ} (h : (toArrowAux M l m).isSome) :
    toArrow l.simplexMonoSort m (toArrowAux_simplexMonoSort_isSome h) = toArrow l m h := by
  induction' l with b l hbl generalizing m
  · simp_all only [List.simplexMonoSort]
  · simp_all only [List.simplexMonoSort]
    rw [toArrow_simplexMonoInsert_eq]
    · rw [toArrow_cons', toArrow_cons']
      refine Arrow.ext _ _ ?_ ?_ ?_
      · rfl
      · simp only [toArrowTail, toArrow_right, List.simplexMonoSort_length]
      · simp only [toArrowTail, Functor.id_obj, Category.assoc, eqToHom_refl, Category.id_comp]
        have := Arrow.hom_eq _ _ (@hbl (m + 1) (toArrowAux_some_cons _ _ _ h))
        rw [← IsIso.eq_inv_comp, ← IsIso.eq_comp_inv] at this
        rw [this]
        simp only [Functor.id_obj, inv_eqToHom, Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id, eqToHom_trans_assoc]
    · apply toArrowAux_simplexMonoSort_isSome
      exact toArrowAux_some_cons _ _ _ h
    · exact (toArrowAux_some_cond' h).1

theorem toArrow_injectiveish {m : ℕ} {l l' : List ℕ} (hl : (toArrowAux simplexThingy l m).isSome)
    (hl' : (toArrowAux simplexThingy l' m).isSome) (h : toArrow _ _ hl = toArrow _ _ hl')
    (hls : l.Sorted (· < ·)) (hls' : l'.Sorted (· < ·)) :
    l = l' := by
  rw [← order2_toArrow _ hls _ hl, ← order2_toArrow _ hls' _ hl']
  congr

theorem simplexMonoSort_order2_append {m n o : SimplexCategory} (f : m ⟶ n) (g : n ⟶ o) (hf : Mono f) (hg : Mono g) :
    (order2 f ++ order2 g).simplexMonoSort = order2 (f ≫ g) := by
  letI : Mono (f ≫ g) := @mono_comp _ _ _ _ _ _ hf _ hg
  refine toArrow_injectiveish (toArrowAux_simplexMonoSort_isSome (toArrowAux_some_append
    (toArrowAux_some_of_mono f hf (le_refl _)) (toArrowAux_some_of_mono g hg (le_refl _)) <| order2_length _ hf))
    (toArrowAux_some_of_mono (f ≫ g) inferInstance (le_refl _)) ?_ ?_ ?_
  dsimp
  have : (toArrowAux simplexThingy (order2 f ++ order2 g).simplexMonoSort m.len).isSome :=
    toArrowAux_simplexMonoSort_isSome (toArrowAux_some_append (toArrowAux_some_of_mono f hf (le_refl _)) (toArrowAux_some_of_mono g hg (le_refl _)) <| order2_length _ hf)
  · rw [toArrow_simplexMonoSort_eq (toArrowAux_some_append (toArrowAux_some_of_mono f hf (le_refl _)) (toArrowAux_some_of_mono g hg (le_refl _)) <| order2_length _ hf)]
    rw [← arrowMk_eq_toArrow_Append (toArrowAux_some_of_mono f hf (le_refl _)) (toArrowAux_some_of_mono g hg (le_refl _)) (order2_length _ hf)]
    simp only [Functor.id_obj]
    simp_rw [toArrow_order2]
    rw [← Arrow.hom_eq _ _ (toArrow_order2 f hf).symm, ← Arrow.hom_eq _ _ (toArrow_order2 g hg).symm]
    refine Arrow.ext _ _ ?_ ?_ ?_
    · simp only [simplexThingy]
      simp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Arrow.mk_hom, eqToHom_trans_assoc,
      Category.assoc, eqToHom_refl, Category.id_comp, toArrow_left, mk_len]
    · simp only [simplexThingy, Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Arrow.mk_hom, eqToHom_trans_assoc,
      Category.assoc, eqToHom_refl, Category.id_comp, toArrow_right, order2_length, mk_len]
    · simp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Arrow.mk_hom, mk_len,
      eqToHom_trans_assoc, Category.assoc, eqToHom_refl, Category.id_comp, eqToHom_trans,
      Category.comp_id]
  · exact simplexMonoSort_sorted (order2 f ++ order2 g)
  · exact order2_sorted (f ≫ g)

theorem toArrowAux_order2_comp_isSome {m n o : SimplexCategory}
    {f : m ⟶ n} {g : n ⟶ o} (hf : Mono f) (hg : Mono g) :
    (toArrowAux M (order2 (f ≫ g)) m.len).isSome := by
  rw [← simplexMonoSort_order2_append _ _ hf hg]
  refine toArrowAux_simplexMonoSort_isSome ?h
  apply toArrowAux_some_append (n := n.len)
  · exact toArrowAux_some_of_mono f hf (le_refl _)
  · exact toArrowAux_some_of_mono g hg (le_refl _)
  · rw [order2_length f hf]

theorem toArrow_comp {m n o : SimplexCategory} {f : m ⟶ n} {g : n ⟶ o}
    (hf : Mono f) (hg : Mono g) :
    toArrow (M := M) (order2 (f ≫ g)) m.len (toArrowAux_order2_comp_isSome hf hg)
      = Arrow.mk ((toArrow (order2 f) m.len (toArrowAux_some_of_mono f hf (le_refl _))).hom
      ≫ eqToHom (by simp [toArrow_right, toArrow_left, order2_length])
      ≫ (toArrow (order2 g) n.len (toArrowAux_some_of_mono g hg (le_refl _))).hom) := by
  simp_rw [← simplexMonoSort_order2_append f g hf hg]
  rw [toArrow_simplexMonoSort_eq (toArrowAux_some_append (toArrowAux_some_of_mono f hf (le_refl _))
    (toArrowAux_some_of_mono g hg (le_refl _)) (order2_length f hf))]
  rw [arrowMk_eq_toArrow_Append]
  rw [order2_length]
  assumption

variable (M)

def toHom {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    M.obj m.len ⟶ M.obj n.len :=
  eqToHom (toArrow_left (toArrowAux_some_of_mono f hf (le_refl _))).symm
  ≫ (toArrow (order2 f) m.len (toArrowAux_some_of_mono f hf (le_refl _))).hom
  ≫ eqToHom (by simp [toArrow_right, order2_length])

variable {M}

@[simp]
theorem order2_id {m : SimplexCategory} : order2 (𝟙 m) = [] := by
  simp only [order2, rangeCompl, id_toOrderHom, OrderHom.id_coe, Finset.image_id, Finset.compl_univ,
    Finset.image_empty, Finset.sort_empty]

theorem toHom_id {m : SimplexCategory} :
    toHom M (𝟙 m) inferInstance = 𝟙 (M.obj m.len) := by
  apply_fun Arrow.mk
  rw [toHom, Arrow.ugh]
  simp only [toArrow, Functor.id_obj, Arrow.mk_eq, order2_id, toArrowAux, mk_len, Option.get_some]
  rfl
  exact Arrow.mk_injective _ _

theorem toHom_comp {m n o : SimplexCategory} (f : m ⟶ n) (g : n ⟶ o)
    (hf : Mono f) (hg : Mono g) :
    toHom M (f ≫ g) (mono_comp' hf hg) = toHom M f hf ≫ toHom M g hg := by
  apply_fun Arrow.mk
  simp only [toHom, Functor.id_obj, Arrow.ugh, Arrow.mk_eq, Category.assoc, eqToHom_trans_assoc]
  rw [toArrow_comp hf hg]
  refine Arrow.ext _ _ ?_ ?_ ?_
  · simp only [Functor.id_obj, Arrow.mk_left, toArrow_left, mk_len]
  · simp only [Functor.id_obj, Arrow.mk_right, toArrow_right, order2_length, mk_len]
  · simp only [Functor.id_obj, mk_len, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · apply Arrow.mk_injective _ _

end monos
