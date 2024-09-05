import Mathlib.AlgebraicTopology.SimplexCategory
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.CommSq
import Mathlib.Data.Set.Image
import Mathlib.Order.SuccPred.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card
import Mathlib.Data.List.Intervals
import Mathlib.AlgebraicTopology.SimplexCatMonos
import Mathlib.Data.Multiset.OrderedMonoid
open CategoryTheory

universe v u

lemma Set.codRestrict_surjective {α β : Type*} (f : α → β) (S : Set β) (hS : Set.univ.SurjOn f S)
    (hs : ∀ x, f x ∈ S) : (S.codRestrict f hs).Surjective := by
  intro x
  rcases hS x.2 with ⟨y, hy, hy'⟩
  use y
  ext
  assumption

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

theorem epi_comp' {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : Epi f) (hg : Epi g) :
    Epi (f ≫ g) := by
  letI := hf
  letI := hg
  apply epi_comp

end CategoryTheory
namespace List

section simplexSort

@[simp]
def simplexInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a ≤ b then a :: b :: l else b :: simplexInsert (a - 1) l

@[simp]
def simplexSort : List ℕ → List ℕ
  | [] => []
  | b :: l => simplexInsert b (simplexSort l)

@[simp]
theorem simplexInsert_nil (a : ℕ) : [].simplexInsert a = [a] :=
  rfl

theorem simplexInsert_length : ∀ (L : List ℕ) (a : ℕ), (L.simplexInsert a).length = L.length + 1
  | [], a => rfl
  | hd :: tl, a => by
    dsimp [simplexInsert]
    split_ifs <;> simp [simplexInsert_length tl]

theorem simplexSort_length : ∀ (L : List ℕ), (L.simplexSort).length = L.length
  | [] => rfl
  | hd :: tl => by
    dsimp [simplexSort]
    rw [simplexInsert_length, simplexSort_length tl]

end simplexSort
end List

def fml : ∀ (_ : ℕ), List ℕ → Bool
| _, [] => True
| m, a :: l => a < m ∧ fml (m - 1) l

instance : BEq SimplexCategory := by
  unfold SimplexCategory
  infer_instance

-- idk
instance (priority := low) : DecidableEq SimplexCategory := by
  unfold SimplexCategory
  infer_instance

variable (m n : SimplexCategory)
instance (m n : SimplexCategory) : Repr (m ⟶ n) where
  reprPrec f _ := repr f.toOrderHom.1
instance : Repr SimplexCategory where
  reprPrec m _ := repr m.len
instance {C : Type*} [Category C] [∀ X Y : C, Repr (X ⟶ Y)] : Repr (Arrow C) where
  reprPrec m _ := repr m.hom

instance {X Y : monos.simplexThingy.C} : Repr (X ⟶ Y) where
  reprPrec f _ := repr f.toOrderHom.1

open SimplexCategory

structure thingy where
  (C : Type u)
  [instCat : Category.{v} C]
  [instDec : DecidableEq C]
  (obj : ℕ → C)
  (epimap : ∀ {n : ℕ} (_ : Fin (n + 1)), obj (n + 1) ⟶ obj n)
  (epicond : ∀ {n : ℕ} (i j : Fin (n + 1)) (_ : i ≤ j),
    epimap i.castSucc ≫ epimap j = epimap j.succ ≫ epimap i)

attribute [instance] thingy.instCat thingy.instDec

def simplexThingy : thingy where
  C := SimplexCategory
  obj := mk
  epimap := σ
  epicond _ _ := σ_comp_σ

variable (a n : ℕ) (l : Arrow SimplexCategory)

def toArrowAux (M : thingy) : ∀ (_ : List ℕ), ℕ → Option (Arrow M.C)
| [], n => some ⟨M.obj n, M.obj n, 𝟙 _⟩
| _ :: _, 0 => none
| a :: l, n + 1 => Option.recOn (toArrowAux M l n) none fun l =>
  if ha : a < n + 1 ∧ M.obj n = l.1 then
  some ⟨M.obj (n + 1), l.2, M.epimap ⟨a, ha.1⟩ ≫ eqToHom ha.2 ≫ l.hom⟩ else none

instance : Repr simplexThingy.C where
  reprPrec m _ := repr m.len
instance {m n : simplexThingy.C} : Repr (m ⟶ n) where
  reprPrec f _ := repr f.toOrderHom.1

variable {M : thingy}

theorem toArrowAux_none_cons (l : List ℕ) (a n : ℕ) (hl : toArrowAux M l n = none) :
    toArrowAux M (a :: l) (n + 1) = none := by
  rw [toArrowAux]
  simp_all only [Functor.id_obj]

theorem toArrowAux_some_nil (n : ℕ) : (toArrowAux M [] n).isSome := by
  simp only [toArrowAux, Functor.id_obj, Option.isSome_some]

theorem toArrowAux_some_cons (l : List ℕ) (a n : ℕ) (hl : (toArrowAux M (a :: l) (n + 1)).isSome) :
    (toArrowAux M l n).isSome := by
  contrapose! hl
  simp_all only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none,
    toArrowAux_none_cons, Option.isSome_none, Bool.false_eq_true, not_false_eq_true]

def toArrow (l : List ℕ) (n : ℕ) (H : (toArrowAux M l n).isSome) :
  Arrow M.C := Option.get _ H

def toArrowTail {l : List ℕ} {a n : ℕ} (H : (toArrowAux M (a :: l) (n + 1)).isSome) :
    Arrow M.C := toArrow _ _ (toArrowAux_some_cons _ _ _ H)

theorem toArrowAux_none_cond {l : List ℕ} {a n : ℕ}
    {f : Arrow M.C}
    (hl : (toArrowAux M l n) = some f)
    (hcond : ¬(a < n + 1 ∧ M.obj n = f.left)) :
    toArrowAux M (a :: l) (n + 1) = none := by
  rw [toArrowAux]
  simp_all only [not_and, Functor.id_obj, dite_eq_right_iff, imp_false, not_false_eq_true,
    implies_true]

theorem toArrowAux_some_cond {l : List ℕ} {a n : ℕ} {f : Arrow M.C}
    (hl : (toArrowAux M l n) = some f)
    (hal : (toArrowAux M (a :: l) (n + 1)).isSome) :
    a < n + 1 ∧ M.obj n = f.left := by
  contrapose hal
  simp_all only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  exact toArrowAux_none_cond hl hal

theorem toArrowAux_some_cond' {l : List ℕ} {a n : ℕ}
    (hal : (toArrowAux M (a :: l) (n + 1)).isSome) :
    a < n + 1 ∧ M.obj n = (toArrowTail hal).left := by
  apply toArrowAux_some_cond (l := l)
  rw [toArrowTail, toArrow]
  simp only [Option.some_get]
  exact hal

theorem toArrow_cons {l : List ℕ} {a n : ℕ} {f : Arrow M.C}
    (hl : toArrowAux M l n = some f)
    (hal : (toArrowAux M (a :: l) (n + 1)).isSome) :
    toArrow (a :: l) (n + 1) hal = ⟨M.obj (n + 1), f.2,
      M.epimap ⟨a, (toArrowAux_some_cond hl hal).1⟩ ≫ eqToHom (toArrowAux_some_cond hl hal).2
      ≫ f.hom⟩ := by
  simp_all only [toArrow, toArrowAux, Functor.id_obj]
  simp_rw [dif_pos (toArrowAux_some_cond hl hal)]
  simp only [Option.get_some]

theorem toArrowTail_eq {l : List ℕ} {a n : ℕ}
    (hal : (toArrowAux M (a :: l) (n + 1)).isSome) :
    toArrowAux M l n = some (toArrowTail hal) := by
  simp_all only [toArrowTail, toArrow, Option.some_get]

theorem toArrow_cons' {l : List ℕ} {a n : ℕ} (hal : (toArrowAux M (a :: l) (n + 1)).isSome) :
    toArrow (a :: l) (n + 1) hal = ⟨M.obj (n + 1), (toArrowTail hal).2,
      M.epimap ⟨a, (toArrowAux_some_cond (toArrowTail_eq hal) hal).1⟩
      ≫ eqToHom (toArrowAux_some_cond (toArrowTail_eq hal) hal).2
      ≫ (toArrowTail hal).hom⟩ :=
  toArrow_cons (toArrowTail_eq hal) _

theorem toArrow_left {l : List ℕ} {n : ℕ}
    (hl : (toArrowAux M l n).isSome) :
    (toArrow l n hl).left = M.obj n := by
  induction' l with a l _
  · simp_all only [toArrow, toArrowAux, Functor.id_obj]
    rfl
  · induction' n with n hn
    · exfalso
      simp_all only [toArrowAux, Option.isSome_none, Bool.false_eq_true]
    · simp only [toArrow_cons', Functor.id_obj]

theorem toArrowAux_some_cons' {l : List ℕ} {a n : ℕ} (h : a < n + 1)
    (hl : (toArrowAux M l n).isSome) : (toArrowAux M (a :: l) (n + 1)).isSome := by
  rw [toArrowAux, ← Option.some_get hl]
  simp only [Functor.id_obj]
  rw [dif_pos]
  simp only [Option.isSome_some]
  constructor
  · assumption
  · erw [toArrow_left]

@[simp]
theorem toArrow_nil (n : ℕ) : toArrow [] n (toArrowAux_some_nil n) = Arrow.mk (𝟙 (M.obj n)) := by
  simp only [toArrow, toArrowAux, Functor.id_obj, Option.get_some]
  rfl

theorem ugh {m n : ℕ} (f : Fin m → Fin n) (hf : f.Surjective) :
    n ≤ m := by
  simpa [Fintype.card_fin] using Fintype.card_le_of_surjective f hf

theorem Fin.map_zero_of_monotone_surjective {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : Monotone f)
    (hs : f.Surjective) : f 0 = 0 := by
  rcases hs 0 with ⟨w, hw⟩
  rw [← Fin.le_zero_iff, ← hw]
  apply hf
  exact zero_le _

theorem Fin.map_last_of_monotone_surjective {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (hf : Monotone f) (hs : f.Surjective) :
    f (Fin.last m) = Fin.last n := by
  apply Fin.eq_last_of_not_lt
  rcases hs (Fin.last n) with ⟨a, ha⟩
  rw [not_lt]
  have := hf (Fin.le_last a)
  rw [ha] at this
  exact this

theorem Fin.succ_le_castSucc_add_one {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : Monotone f)
    (hs : f.Surjective) (x : Fin m) : (f x.succ : ℕ) ≤ f x.castSucc + 1 := by
  by_cases h : (f x.castSucc : ℕ) + 1 < n + 1
  · rcases hs ⟨_, h⟩ with ⟨w, hw⟩
    have : x.succ ≤ w := by
      apply lt_imp_lt_of_le_imp_le (@hf w x.castSucc)
      rw [hw, Fin.lt_iff_val_lt_val]
      simp only [lt_add_iff_pos_right, _root_.zero_lt_one]
    exact Fin.le_iff_val_le_val.1 <| hw.symm ▸ hf this
  · exact le_trans (le_of_lt (Fin.prop _)) <| not_lt.1 h

theorem le_castLE_of_monotone_surjective {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : Monotone f)
    (hs : f.Surjective) (x : Fin (m + 1)) :
    Fin.castLE (by simpa [Fintype.card_fin] using Fintype.card_le_of_surjective f hs) (f x) ≤ x := by
  induction' x using Fin.inductionOn with x hx
  · simp_all only [Fin.map_zero_of_monotone_surjective, Fin.castLE_zero, le_refl]
  · contrapose! hx
    apply lt_of_lt_of_le (Fin.castSucc_lt_succ _)
    · rw [Fin.le_iff_val_le_val] at *
      rw [← Nat.lt_succ_iff]
      exact lt_of_lt_of_le hx (Fin.succ_le_castSucc_add_one f hf hs _)

theorem eq_castLE {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (hf : Monotone f) (hs : f.Surjective)
    (x : Fin (m + 1)) (hx : Set.InjOn f <| Set.Iic x) :
    Fin.castLE sorry (f x) = x := by
  induction' x using Fin.inductionOn with x ih
  · rw [Fin.map_zero_of_monotone_surjective f hf hs]
    simp only [Fin.castLE_zero]
  · specialize ih ?_
    apply Set.InjOn.mono (Set.Iic_subset_Iic.2 (le_of_lt <| Fin.castSucc_lt_succ _)) hx
    apply le_antisymm
    · exact le_castLE_of_monotone_surjective f hf hs x.succ
    · rw [← Fin.castSucc_lt_iff_succ_le]
      rw [← ih, lt_iff_le_and_ne]
      constructor
      · exact hf (le_of_lt <| Fin.castSucc_lt_succ _)
      · have := ne_of_lt <| Fin.castSucc_lt_succ x
        contrapose! this
        apply hx
        · exact le_of_lt <| Fin.castSucc_lt_succ _
        · exact Set.right_mem_Iic
        · exact Fin.castLE_injective _ this

theorem eqOn_castLE' {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (a : Fin (m + 1)) (hf : Function.Surjective f)
    (H : Set.InjOn f <| Set.Iic a) :
    Set.EqOn (Fin.castLE sorry ∘ f) id (Set.Iic a) := by
  intro x hx
  apply eq_castLE f f.monotone hf
  · apply Set.InjOn.mono _ H
    apply Set.Iic_subset_Iic.2 (Set.mem_Iic.1 hx)

theorem eqOn_castLE {m n : SimplexCategory} (f : m ⟶ n)
    (a : Fin (m.len + 1)) (hf : Epi f)
    (H : Set.InjOn f.toOrderHom <| Set.Iic a) :
    Set.EqOn (Fin.castLE sorry ∘ f.toOrderHom : Fin (m.len + 1) → Fin (m.len + 1)) id (Set.Iic a) := by
  intro x hx
  apply eq_castLE f.toOrderHom f.toOrderHom.monotone (epi_iff_surjective.1 hf)
  · apply Set.InjOn.mono _ H
    apply Set.Iic_subset_Iic.2 (Set.mem_Iic.1 hx)

theorem predAbove_zero_comp_succ (m : ℕ) :
    Fin.predAbove (0 : Fin (m + 1)) ∘ Fin.succ = id := by
  ext x
  simp only [Function.comp_apply, Fin.predAbove_zero_succ, id_eq]

abbrev rangeMultiset {m n : SimplexCategory} (f : m ⟶ n) : Multiset ℕ :=
  Multiset.ofList <| List.map (Fin.val ∘ f.toOrderHom) <| List.finRange (m.len + 1)

def toMultiset {m n : SimplexCategory} (f : m ⟶ n) : Multiset ℕ :=
  (rangeMultiset f) - (Multiset.range (n.len + 1))

@[simp]
theorem Multiset.sub_self (l : Multiset ℕ) : l - l = 0 := by
  rw [tsub_eq_zero_of_le]
  simp only [le_refl, tsub_eq_zero_of_le]

theorem Multiset.cons_diff_self (l : Multiset ℕ) (a : ℕ) :
    (a ::ₘ l) - l = {a} := by
  simp only [le_refl, Multiset.cons_sub_of_le, tsub_eq_zero_of_le, Multiset.cons_zero,
    Multiset.coe_singleton]

theorem rangeMultiset_id {m : SimplexCategory} :
    rangeMultiset (𝟙 m) = Multiset.range (m.len + 1) := by
  simp only [rangeMultiset, id_toOrderHom, OrderHom.id_coe, Function.comp_id, List.map_coe_finRange]
  rfl

@[simp]
theorem Multiset.diff_self_erase (l : Multiset ℕ) (a : ℕ) :
    l - (l.erase a) = if a ∈ l then {a} else 0 := by
  sorry
  /-split_ifs with h
  ·
    have := Multiset.cons_sub
    have := cons_diff a l l
    rw [if_pos h] at this
    rw [← this, cons_diff_self]
  · rw [erase_of_not_mem h]
    simp-/

@[simp]
theorem toMultiset_id {m : SimplexCategory} : toMultiset (𝟙 m) = 0 := by
  rw [toMultiset, rangeMultiset]
  simp only [id_toOrderHom, OrderHom.id_coe, Function.comp_id, List.map_coe_finRange,
    Multiset.range, le_refl, tsub_eq_zero_of_le]

@[simp]
theorem rangeMultiset_σ_0 (m : ℕ) :
    rangeMultiset (σ (0 : Fin (m + 1))) = 0 ::ₘ Multiset.range (m + 1) := by
  rw [rangeMultiset, List.finRange_succ_eq_map]
  simp only [len_mk, Nat.succ_eq_add_one, List.map_cons, Function.comp_apply, List.map_map]
  simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk, Fin.predAbove_right_zero, Fin.val_zero,
    Function.comp.assoc, predAbove_zero_comp_succ, Function.comp_id, List.map_coe_finRange]
  rfl

theorem rangeMultiset_σ_succ {m : ℕ} (i : Fin (m + 1)) :
    rangeMultiset (σ i.succ) = 0 ::ₘ Multiset.map (· + 1) (rangeMultiset (σ i)) := by
  rw [rangeMultiset, List.finRange_succ_eq_map]
  simp only [len_mk, σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk, Nat.succ_eq_add_one,
    List.map_cons, Function.comp_apply, Fin.predAbove_right_zero, Fin.val_zero, List.map_map,
    Multiset.map_coe, Multiset.cons_coe]
  congr
  ext x
  simp only [Function.comp_apply, Fin.succ_predAbove_succ, Fin.val_succ]

theorem rangeMultiset_σ_castSucc {m : ℕ} (i : Fin (m + 1)) :
    rangeMultiset (σ i.castSucc) = (m + 1) ::ₘ rangeMultiset (σ i) := by
  simp only [rangeMultiset, len_mk]
  rw [← Multiset.singleton_add, add_comm {m + 1}, ← Multiset.coe_singleton, Multiset.coe_add,
    List.finRange_succ]
  simp_rw [List.concat_eq_append, List.map_append, List.map_map,
    List.map_cons, List.map_nil, Function.comp_apply]
  congr
  · ext x
    simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk, Function.comp_apply,
      Fin.castSucc_predAbove_castSucc, Fin.coe_castSucc]
  · simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk, Fin.predAbove_right_last,
    Fin.val_last]

theorem rangeMultiset_σ {m : ℕ} (i : Fin (m + 1)) :
    rangeMultiset (σ i) = (i : ℕ) ::ₘ Multiset.range (m + 1) := by
  induction' m with m hm
  · simp_all only [Fin.fin_one_eq_zero i, rangeMultiset_σ_0, zero_add, Multiset.range_succ,
    Multiset.range_zero, Multiset.cons_zero, Fin.coe_fin_one]
  · induction' i using Fin.inductionOn with i hi
    · rw [rangeMultiset_σ_0]
      rfl
    · rw [rangeMultiset_σ_succ, hm]
      simp_rw [add_comm (m + 1)]
      nth_rw 2 [Multiset.range_add]
      simp only [Multiset.map_cons, Fin.val_succ]
      rw [Multiset.range_succ 0]
      simp only [Multiset.range_zero, Multiset.cons_zero, Multiset.singleton_add]
      simp_rw [← Multiset.singleton_add]
      rw [add_left_comm]
      simp only [add_comm 1]

/- maybe rangeMultiset should land in Multiset (Fin (n + 1)) or something -/
theorem map_σ_ugh {m : ℕ} (i : Fin (m + 1)) :
    Multiset.map (σ i).toOrderHom (Multiset.ofList <| List.finRange (m + 2))
      = i ::ₘ Multiset.ofList (List.finRange (m + 1)) := by
  apply_fun Multiset.map Fin.val
  · simp only [len_mk, Multiset.map_coe, List.map_map, Multiset.cons_coe, List.map_cons,
      List.map_coe_finRange]
    have := rangeMultiset_σ i
    simp only [rangeMultiset, len_mk] at this
    erw [this]
    rfl
  · refine Multiset.map_injective Fin.val_injective

theorem rangeMultiset_σ_comp {m n : SimplexCategory} (f : m ⟶ n) (i : Fin (m.len + 1)) :
    rangeMultiset (σ i ≫ f) = (f.toOrderHom i : ℕ) ::ₘ (rangeMultiset f) := by
  rw [rangeMultiset]
  simp only [len_mk, mk_len, comp_toOrderHom, OrderHom.comp_coe]
  rw [← Multiset.map_coe, ← Multiset.map_map, ← Multiset.map_map]
  erw [map_σ_ugh]
  simp only [Multiset.cons_coe, Multiset.map_coe, List.map_cons, List.map_map]

theorem toMultiset_σ {m : ℕ} (i : Fin (m + 1)) :
    toMultiset (σ i) = {(i : ℕ)} := by
  rw [toMultiset, rangeMultiset_σ, len_mk]
  rw [Multiset.cons_sub_of_le _ (le_refl _)]
  simp only [Multiset.range_succ, le_refl, tsub_eq_zero_of_le, Multiset.cons_zero]

theorem toMultiset_σ_comp {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) (i : Fin (m.len + 1)) :
    toMultiset (σ i ≫ f) = (f.toOrderHom i : ℕ) ::ₘ toMultiset f := by
  rw [toMultiset, toMultiset, rangeMultiset_σ_comp,
    Multiset.cons_sub_of_le]
  · rw [Multiset.le_iff_subset]
    intro x hx
    rw [rangeMultiset]
    simp only [Multiset.mem_coe, List.mem_map, List.mem_finRange, Function.comp_apply, true_and]
    simp only [Multiset.mem_range] at hx
    rcases (epi_iff_surjective.1 hf) ⟨x, hx⟩ with ⟨w, hw⟩
    use w
    rw [hw]
    · exact Multiset.nodup_range (n.len + 1)

abbrev toList {m n : SimplexCategory} (f : m ⟶ n) : List ℕ := Multiset.sort (· ≤ ·) (toMultiset f)

theorem rangeMultiset_eq_ofFn {m n : SimplexCategory} (f : m ⟶ n) :
    rangeMultiset f = List.ofFn (Fin.val ∘ f.toOrderHom) := by
  rw [List.ofFn_eq_map]

theorem eqToHom_eq_cast {m n : SimplexCategory} {h : m = n} :
    ⇑(eqToHom h).toOrderHom = Fin.cast (h ▸ rfl) := by
  cases h
  rfl

theorem Fin.cast_bijective {m n : ℕ} (h : m = n) : Function.Bijective (Fin.cast h) :=
  (Fin.castOrderIso h).toEquiv.bijective

theorem toArrow_epi (n : ℕ) (l : List ℕ) (hl : l.Sorted (· ≤ ·))
    (H : (toArrowAux M l n).isSome)
    (hmono : ∀ {n : ℕ} (i : Fin (n + 1)), Epi (M.epimap i)) :
    Epi (toArrow _ _ H).hom := by
  revert n
  induction' l with a l ih
  · simp_all only [List.Pairwise.nil, toArrow, toArrowAux, Functor.id_obj, Option.get_some]
    infer_instance
  · intro n h
    induction' n with n _
    · exfalso
      simp_all only [List.sorted_cons, Functor.id_obj, toArrowAux, Option.isSome_none,
        Bool.false_eq_true]
    · specialize ih (List.sorted_cons.1 hl).2 n (toArrowAux_some_cons _ _ _ h)
      rw [toArrow_cons' h]
      simp only [Functor.id_obj]
      letI : Epi (toArrowTail h).hom := ih
      rw [← Category.assoc]
      convert epi_comp _ _
      · exact epi_comp _ _
      · infer_instance

instance simplexThingy_mono {n : ℕ} (i : Fin (n + 1)) : Epi (simplexThingy.epimap i) := by
  simp only [simplexThingy]
  infer_instance

theorem toMultiset_eqToHom_comp {m n o : SimplexCategory} (h : m = n) (f : n ⟶ o) :
    toMultiset (eqToHom h ≫ f) = toMultiset f := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

theorem toArrow_right (l : List ℕ) (n : ℕ) (hl : (toArrowAux M l n).isSome) :
     (toArrow l n hl).right = M.obj (n - l.length) := by
  revert n
  induction' l with a l hal
  · intro n hl
    simp_all only [toArrow_nil, Arrow.mk_right, List.length_nil, tsub_zero]
  · intro n hl
    induction' n with n hn
    · exfalso
      simp_all only [toArrowAux, Option.isSome_none, Bool.false_eq_true]
    · rw [toArrow_cons' hl]
      simp only [List.length_cons]
      erw [hal n (toArrowAux_some_cons _ _ _ hl)]
      simp only [Nat.reduceSubDiff]

theorem toArrow_cons_hom {l : List ℕ} {a n : ℕ} (hal : (toArrowAux M (a :: l) (n + 1)).isSome) :
    (toArrow (a :: l) (n + 1) hal).hom
      = eqToHom (by simp [toArrow_left]) ≫ M.epimap ⟨a, (toArrowAux_some_cond (toArrowTail_eq hal) hal).1⟩
      ≫ eqToHom (toArrowAux_some_cond (toArrowTail_eq hal) hal).2
      ≫ (toArrowTail hal).hom ≫ eqToHom (by simp [toArrow_right, toArrowTail]) := by
  apply_fun Arrow.mk
  slice_rhs 3 6 =>
      simp only [← Category.assoc]
  rw [Arrow.ugh]
  simp only [Functor.id_obj, Arrow.mk_eq, Category.assoc]
  rw [toArrow_cons' hal]
  rfl
  exact Arrow.mk_injective _ _

theorem head_le_sub_length {l : List ℕ} {a n : ℕ} (hal : (a :: l).Sorted (· ≤ ·))
    (H : (toArrowAux M (a :: l) (n + 1)).isSome) :
    a ≤ n - l.length := by
  revert n
  induction' l with b l hbl
  · intro n H
    simp_all only [List.sorted_singleton, List.length_nil, tsub_zero]
    linarith [(toArrowAux_some_cond' H).1]
  · intro n H
    cases' n with n
    · exfalso
      simp_all only [List.sorted_cons, and_imp, List.mem_cons, forall_eq_or_imp, zero_add,
        implies_true, true_implies]
      have := toArrowAux_some_cons _ _ _ H
      simp_all only [toArrowAux, zero_add, Nat.lt_one_iff, Functor.id_obj, Fin.zero_eta,
        Option.isSome_none, Bool.false_eq_true]
    · simp only [List.sorted_cons, and_imp, List.mem_cons, forall_eq_or_imp] at hbl
      simp only [List.sorted_cons, and_imp, List.mem_cons, forall_eq_or_imp] at hal
      specialize @hbl hal.1.2 hal.2.2 n ?_
      · refine toArrowAux_some_cons' ?cons.succ.h ?cons.succ.hl
        · linarith [toArrowAux_some_cond' <| toArrowAux_some_cons _ _ _ H]
        · exact toArrowAux_some_cons _ _ _ (toArrowAux_some_cons _ _ _ H)
      simp_all only [List.length_cons]
      rw [Nat.Simproc.add_sub_add_ge n l.length Nat.le.refl]
      rw [Nat.sub_self, add_zero]
      assumption

theorem some_delete {l : List ℕ} {a b n : ℕ} (habl : (a :: b :: l).Sorted (· ≤ ·))
    (H : (toArrowAux M (a :: b :: l) (n + 2)).isSome) :
    (toArrowAux M (a :: l) (n + 1)).isSome := by
  refine toArrowAux_some_cons' ?h ?hl
  · have := head_le_sub_length (n := n + 1) habl H
    simp_all only [List.sorted_cons, List.mem_cons, forall_eq_or_imp, List.length_cons, gt_iff_lt]
    rw [Nat.lt_succ_iff]
    rw [Nat.add_sub_add_right] at this
    exact le_trans this (Nat.sub_le _ _)
  · apply toArrowAux_some_cons _ _ _ <| toArrowAux_some_cons _ _ _ H

theorem toArrow_head_apply {l : List ℕ} {a n : ℕ} (hal : (a :: l).Sorted (· ≤ ·))
    (H : (toArrowAux simplexThingy (a :: l) (n + 1)).isSome) :
    (toArrow l n <| toArrowAux_some_cons _ _ _ H).hom.toOrderHom ⟨a, by
      simp only [simplexThingy, toArrow_left, Functor.id_obj, len_mk]
      exact (toArrowAux_some_cond' H).1⟩ = ⟨a, by
        simp only [simplexThingy, toArrow_right, Functor.id_obj, len_mk]
        linarith [head_le_sub_length hal H]⟩ := by
  revert n
  induction' l with b l hbl
  · intro n H
    simp_all only [List.sorted_singleton, Functor.id_obj]
    simp only [toArrow, toArrowAux, Functor.id_obj, Option.get_some]
    simp_all only [simplexThingy, len_mk, id_toOrderHom, OrderHom.id_coe, id_eq]
  · intro n H
    induction' n with n hn
    · exfalso
      simp_all only [List.sorted_cons, List.mem_cons, forall_eq_or_imp, implies_true, and_self,
        toArrowAux, zero_add, Nat.lt_one_iff, Functor.id_obj, Fin.zero_eta, forall_true_left,
        Option.isSome_none, Bool.false_eq_true]
    · simp_all only [List.sorted_cons, Functor.id_obj]
      have hmm := hal
      rw [List.sorted_cons, List.sorted_cons] at hal
      specialize @hbl ⟨fun c hc => hal.1 _ <| List.mem_cons.2 (Or.inr hc), hal.2.2⟩ n
      specialize hbl (some_delete hmm H)
      rw [toArrow_cons_hom]
      simp only [simplexThingy, Functor.id_obj, comp_toOrderHom, len_mk, OrderHom.comp_coe,
        Function.comp_apply]
      have : a ≤ b := hal.1 _ <| List.mem_cons.2 (Or.inl rfl)
      simp only [σ, mkHom, Hom.toOrderHom_mk, OrderHom.coe_mk]
      simp only [toArrowTail]
      rw [eqToHom_eq_cast]
      ext
      apply_fun Fin.val at hbl
      simp only at hbl
      dsimp
      convert hbl
      erw [eqToHom_eq_cast]
      simp only [len_mk, Fin.coe_cast]
      erw [eqToHom_eq_cast]
      have hb := (toArrowAux_some_cond' (toArrowAux_some_cons _ _ _ H)).1
      have := Fin.predAbove_castSucc_of_le ⟨b, show b < n + 1 from hb⟩ ⟨a, show a < n + 1 by linarith⟩ ?_
      apply_fun Fin.val at this
      convert this
      · exact this

theorem toMultiset_toArrow (n : ℕ) (l : List ℕ) (hl : l.Sorted (· ≤ ·))
    (H : (toArrowAux simplexThingy l n).isSome) :
    toMultiset (toArrow l n H).hom = l := by
  revert n
  induction' l with a l ih
  · intro n H
    simp only [Functor.id_obj, Multiset.coe_nil]
    rw [← toMultiset_id (m := mk n)]
    congr
  · intro n H
    induction' n with n _
    · exfalso
      simp_all only [Functor.id_obj, List.sorted_cons, toArrowAux, Option.isSome_none,
        Bool.false_eq_true]
    · specialize ih (List.sorted_cons.1 hl).2 n (toArrowAux_some_cons _ _ _ H)
      rw [toArrow_cons']
      dsimp [toList]
      simp only [simplexThingy]
      erw [toMultiset_σ_comp]
      simp only [len_mk, comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
      rw [← Multiset.cons_coe]
      congr
      · simp only [toArrowTail]
        erw [eqToHom_eq_cast, Fin.cast_mk]
        erw [toArrow_head_apply hl H]
      · rw [toMultiset_eqToHom_comp]
        assumption
      · refine epi_comp' inferInstance ?_
        apply toArrow_epi
        exact (List.sorted_cons.1 hl).2
        simp only
        infer_instance

theorem toList_toArrow (n : ℕ) (l : List ℕ) (hl : l.Sorted (· ≤ ·))
    (H : (toArrowAux simplexThingy l n).isSome) :
    toList (toArrow l n H).hom = l := by
  rw [toList, toMultiset_toArrow]
  simp only [Multiset.coe_sort]
  rw [List.mergeSort_eq_self (fun x x_1 ↦ x ≤ x_1) hl]
  assumption

abbrev sorted (l : List ℕ) : Prop := l.simplexSort = l

theorem mem_or_le_of_mem_simplexInsert (a : ℕ) (l : List ℕ) (x : ℕ) (hx : x ∈ l.simplexInsert a) :
    x ∈ l ∨ x ≤ a := by
  revert a
  induction' l with b l ih
  · simp_all only [List.simplexInsert, List.mem_singleton, List.not_mem_nil, le_refl, or_true,
    implies_true]
  · intro a hx
    simp_all only [List.simplexInsert, List.mem_cons]
    by_cases hba : a ≤ b
    · simp_all only [ite_true, List.mem_cons]
      rcases hx with (hl | hr | hrr)
      · simp_all only [le_refl, or_true]
      · simp_all only [true_or, or_self]
      · simp_all only [true_or, implies_true, or_true]
    · simp_all only [ite_false, List.mem_cons, not_le]
      rcases hx with (hl | hr)
      · simp_all only [true_or]
      · have := ih _ hr
        rcases this with (h1 | h2)
        · simp_all only [true_or, implies_true, or_true]
        · right
          exact le_trans h2 (Nat.sub_le _ _)

theorem mem_or_sub_le_of_mem_simplexInsert (a : ℕ) (l : List ℕ) (x : ℕ) (hx : x ∈ l.simplexInsert a) :
    x ∈ l ∨ a - l.length ≤ x := by
  revert a
  induction' l with b l hbl
  · simp_all only [List.simplexInsert, List.mem_singleton, List.not_mem_nil, List.length_nil,
    tsub_zero, le_refl, or_true, implies_true]
  · simp_all only [tsub_le_iff_right, List.simplexInsert, List.mem_cons, List.length_cons]
    intro a hx
    by_cases hab : a ≤ b
    · simp_all only [ite_true, List.mem_cons]
      rcases hx with (h1 | h2 | h3)
      · simp_all only [le_add_iff_nonneg_right, zero_le, or_true]
      · simp_all only [true_or]
      · simp_all only [true_or, implies_true, or_true]
    · simp_all only [ite_false, List.mem_cons, not_le]
      rcases hx with (h1 | h2)
      · simp_all only [true_or]
      · rcases hbl (a - 1) h2 with (h1 | h3)
        · simp_all only [true_or, implies_true, or_true]
        · simp_all only [tsub_le_iff_right]
          right
          omega

theorem ughh (a x : ℕ) (l : List ℕ) (hl : l.Sorted (· ≤ ·)) (hx : x ∈ l.simplexInsert a) :
    x ∈ l ∨ x = a ∨ ∃ b ∈ l, b ≤ x := by
  revert a
  induction' l with b l hbl
  · simp_all only [List.sorted_nil, List.simplexInsert, List.mem_singleton, List.not_mem_nil,
    false_and, exists_const, or_false, or_true, implies_true]
  · simp_all only [List.sorted_cons, List.simplexInsert, List.mem_cons, exists_eq_or_imp,
    true_implies]
    intro a hx
    by_cases hab : a ≤ b
    · simp_all only [ite_true, List.mem_cons]
      tauto
    · simp_all only [ite_false, List.mem_cons, not_le]
      rcases hx with (h1 | h2)
      · tauto
      · specialize hbl (a - 1) h2
        rcases hbl with (h1 | h2 | h3)
        · tauto
        · cases h2
          right
          right
          left
          omega
        · tauto

/-theorem idfk2 (a x : ℕ) (l : List ℕ) (hl : l.Sorted (· ≤ ·)) (hx : x ∈ l.simplexInsert a)
    (ha : x ≤ a) : x = a := by
  revert a
  induction' l with b l ih
  · simp_all only [List.sorted_nil, List.simplexInsert, List.mem_singleton, le_refl, imp_self,
    implies_true]
  · intro c hx hc
    simp_all only [List.sorted_cons, List.simplexInsert, true_implies]
    by_cases hbc : c ≤ b
    · simp_all only [ite_true, List.mem_cons]
      rcases hx with (h1 | h2 | h3)
      · simp_all only [le_refl]
      · linarith
      · linarith [hl.1 x h3]
    · simp_all only [ite_false, List.mem_cons, not_le]
      rcases hx with (h1 | h2)
      · simp_all only
    simp_all only [List.sorted_cons, List.simplexInsert, true_implies]-/

theorem idfk (a : ℕ) (l : List ℕ) (hl : l.Sorted (· ≤ ·)) :
    (l.simplexInsert a).Sorted (· ≤ ·) := by
  revert a
  induction' l with b l ih
  · simp_all only [List.sorted_nil, List.simplexInsert, List.sorted_singleton, implies_true]
  · intro a
    simp_all only [List.sorted_cons, List.simplexInsert, true_implies]
    split_ifs with hab
    · simp_all only [List.sorted_cons, List.mem_cons, forall_eq_or_imp, true_and, implies_true,
      and_self, and_true]
      intro c hc
      exact le_trans hab (hl.1 c hc)
    · simp_all only [not_le, List.sorted_cons, and_true]
      intro c hc
      rcases ughh (a - 1) c l hl.2 hc with (h1 | h2 | h3)
      · exact hl.1 _ h1
      · omega
      · rcases h3 with ⟨d, hd, hd2⟩
        exact le_trans (hl.1 _ hd) hd2

theorem simplexSort_sorted (l : List ℕ) :
    (l.simplexSort).Sorted (· ≤ ·) := by
  induction' l with a l ih
  · simp_all only [List.simplexSort, List.sorted_nil]
  · exact idfk a _ ih

theorem toList_sorted {m n : SimplexCategory} (f : m ⟶ n) :
    (toList f).Sorted (· ≤ ·) := by
  simp only [toList]
  exact Multiset.sort_sorted (fun x x_1 ↦ x ≤ x_1) (toMultiset f)

theorem toArrowAux_toList_none {m n : SimplexCategory} (f : m ⟶ n)
    (a : ℕ) (l : List ℕ) (H : toList f = a :: l) {k : ℕ}
    (hl : toArrowAux M l k = none) :
    toArrowAux M (toList f) (k + 1) = none := by
  simp_all only [toArrowAux, Functor.id_obj]

theorem toArrowAux_toList_some {m n : SimplexCategory} (f : m ⟶ n)
    (a : ℕ) (l : List ℕ) (H : toList f = a :: l) {k : ℕ}
    (hl : (toArrowAux M (toList f) (k + 1)).isSome) :
    (toArrowAux M l k).isSome := by
  contrapose! hl
  simp_all only [ne_eq, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  rw [← H]
  exact toArrowAux_toList_none f a l H hl

theorem fml_cons_cons (l : List ℕ) (a b n : ℕ) (hfml : fml (n - 1) (b :: l))
    (hl : (a :: b :: l).Sorted (· ≤ ·)) :
    fml n (a :: b :: l) := by
  simp_all only [fml, Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.sorted_cons, List.mem_cons, forall_eq_or_imp, and_self, decide_True, and_true]
  omega
/-
theorem lt_sub_length_of_cons_lt {l : List ℕ} {a n : ℕ} (hl : (a :: l).Sorted (· ≤ ·))
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
    omega
    linarith-/
/-
theorem fml_of_forall_lt {l : List ℕ} (hl : l.Sorted (· ≤ ·)) (n : ℕ) (H : ∀ x ∈ l, x < n + 1 - l.length) :
    fml n l := by
  revert n
  induction' l with a l ih
  · intro n hn
    simp_all only [List.sorted_nil, List.not_mem_nil, false_implies, implies_true, fml, decide_True]
  · intro n hn
    simp_all only [List.sorted_cons, List.mem_cons, List.length_cons, forall_eq_or_imp, fml,
      Bool.decide_and, Bool.decide_eq_true, Bool.and_eq_true, decide_eq_true_eq, true_implies]
    constructor
    · omega
    · apply ih
      intro x hx
      apply lt_of_lt_of_eq (hn.2 x hx)
      omega
-/

theorem toArrowAux_some_of_forall_lt {l : List ℕ} (hl : l.Sorted (· ≤ ·)) (n : ℕ)
    (H : ∀ x ∈ l, x < n + 1 - l.length) :
    (toArrowAux M l n).isSome := by
  revert n
  induction' l with a l hal
  · simp_all only [List.sorted_nil, List.not_mem_nil, false_implies, implies_true, toArrowAux,
    Functor.id_obj, Option.isSome_some, imp_self]
  · intro n hn
    induction' n with n ih
    · exfalso
      simp_all only [List.sorted_cons, List.mem_cons, List.length_cons, le_add_iff_nonneg_left,
        zero_le, tsub_eq_zero_of_le, not_lt_zero', imp_false, not_or, false_implies, implies_true,
        true_implies, true_and]
      apply (hn a).1
      rfl
    · simp_all only [List.sorted_cons, List.mem_cons, List.length_cons, forall_eq_or_imp, and_imp,
        true_implies]
      refine toArrowAux_some_cons' ?_ ?_
      · omega
      · apply hal
        intro x hx
        apply lt_of_lt_of_eq (hn.2 x hx)
        omega

theorem toList_length {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    n.len + (toList f).length = m.len := by
  rw [toList]
  simp only [Multiset.length_sort]
  rw [toMultiset, rangeMultiset]
  rw [Multiset.card_sub]
  · simp only [Multiset.coe_card, Multiset.card_range]
    rw [List.length_map]
    simp only [List.length_finRange, Nat.reduceSubDiff]
    have := len_le_of_epi hf
    omega
  · rw [Multiset.le_iff_subset]
    intro x hx
    simp only [Multiset.mem_coe, List.mem_map, List.mem_finRange, Function.comp_apply, true_and]
    simp_all only [Multiset.mem_range]
    rcases SimplexCategory.epi_iff_surjective.1 hf ⟨x, hx⟩ with ⟨w, hw⟩
    use w
    rw [hw]
    · exact Multiset.nodup_range (n.len + 1)

theorem toList_length' {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    m.len - (toList f).length = n.len :=
  Nat.sub_eq_of_eq_add (toList_length f hf).symm

    /-
theorem lt_of_toList_eq_cons {m n : SimplexCategory} (f : m ⟶ n) {a : ℕ} {l : List ℕ} (h : toList f = a :: l) :
    a < n.len + 1 := by
  have : a ∈ toList f := by simp_all only [List.mem_cons, true_or]
  simp only [toList, toMultiset, rangeMultiset] at this
  apply (Multiset.mem_sort _).1 at this
  apply Multiset.subset_of_le tsub_le_self at this
  simp_all only [Multiset.mem_coe, List.mem_map, List.mem_finRange, Function.comp_apply, true_and,
    gt_iff_lt]
  rcases this with ⟨x, hx, rfl⟩
  exact Fin.is_lt _-/

theorem lt_of_toList {m n : SimplexCategory} (f : m ⟶ n) {x : ℕ} (hx : x ∈ toList f) :
    x < n.len + 1 := by
  simp only [toList, toMultiset, rangeMultiset] at hx
  apply (Multiset.mem_sort _).1 at hx
  apply Multiset.subset_of_le tsub_le_self at hx
  simp_all only [Multiset.mem_coe, List.mem_map, List.mem_finRange, Function.comp_apply, true_and,
    gt_iff_lt]
  rcases hx with ⟨x, hx, rfl⟩
  exact Fin.is_lt _

/-
theorem fml_toList {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    fml m.len (toList f) := by
  apply fml_of_forall_lt
  · exact toList_sorted _
  · intro x hx
    rw [← toList_length _ hf]
    abel_nf
    rw [Nat.add_sub_assoc, Nat.add_sub_cancel_left]
    exact lt_of_toList f hx
    · linarith-/

theorem toArrowAux_some_of_epi {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    (toArrowAux M (toList f) m.len).isSome := by
  induction' hx : toList f with a l hal generalizing m
  · simp_all only [toList, toArrowAux, mk_len, Functor.id_obj, Option.isSome_some]
  · induction' m using SimplexCategory.rec with m
    induction' m with m hm
    · exfalso
      have : n = mk 0 := by
        ext
        simp only [len_mk]
        rw [← le_zero_iff]
        exact len_le_of_epi hf
      cases this
      rw [@eq_id_of_epi _ _ hf] at hx
      simp_all only [toList, toMultiset_id, Multiset.sort_zero]
    · have := toArrowAux_some_of_forall_lt (M := M) (l := (toList f)) (toList_sorted _) (m + 1) ?_
      simp_all only [len_mk]
      intro y hy
      have := toList_length f hf
      rw [len_mk] at this
      simp_rw [← this]
      rw [Nat.add_assoc, Nat.add_sub_assoc, Nat.add_sub_cancel_left]
      simp_all only [len_mk, lt_of_toList f hy]
      linarith
/-
theorem toArrow_cons_hom {l : List ℕ} {a n : ℕ} (hal : (toArrowAux M (a :: l) n).isSome) :
    (toArrow (a :: l) n hal).hom
    = eqToHom (toArrow_left _) ≫ M.epimap ⟨a, (toArrowAux_some_cond (toArrowTail_eq hal) hal).1⟩
      ≫ eqToHom (toArrowAux_some_cond (toArrowTail_eq hal) hal).2
      ≫ (toArrowTail hal).hom ≫ eqToHom (by
      simp only [toArrowTail, Functor.id_obj, toArrow_cons' hal]) := by
  have := Arrow.hom_eq _ _ (toArrow_cons' hal)
  simp only [Functor.id_obj] at this
  rw [← IsIso.eq_inv_comp, ← IsIso.eq_comp_inv] at this
  rw [this]
  simp only [Functor.id_obj, inv_eqToHom, Category.assoc]-/

theorem toList_comp_eqToHom {m n o : SimplexCategory} (f : m ⟶ n) {h : n = o} :
    toList (f ≫ eqToHom h) = toList f := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

theorem toList_eqToHom_comp {m n o : SimplexCategory} (f : m ⟶ n) {h : o = m} :
    toList (eqToHom h ≫ f) = toList f := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

lemma card_range_mono {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    Fintype.card (Set.range f.toOrderHom) = m.len := sorry

lemma card_compl_range {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    Fintype.card (Fin.val '' (Set.range f.toOrderHom)ᶜ) = n.len - m.len := sorry

/-
theorem fuckknows (a : ℕ) (l l₁ : List ℕ) (ha : a ∈ l₁) :
    a :: l ≤ l₁ ↔ l ≤ l₁.erase a := by
  induction' l₁ with b l₁ hbl
  · simp_all only [List.not_mem_nil]
  · simp_all only [List.mem_cons]
    by_cases hab : b = a
    · simp_all only [List.erase_cons_head]
      simp only [le_iff_lt_or_eq, List.cons.injEq, true_and]
      show List.Lex _ _ _ ∨ l = l₁ ↔ List.Lex _ _ _ ∨ _
      rw [List.Lex.cons_iff]
    · simp_all only [beq_iff_eq, not_false_eq_true, List.erase_cons_tail]
      specialize hbl (Or.resolve_left ha (ne_comm.1 hab))

      constructor
      · intro hb
        simp_all only [le_iff_lt_or_eq, List.cons.injEq, true_and]
        rcases hb with (fml1 | fml2)
        · left
          rw [List.cons_lt_cons]
        · right
          assumption
      · exact fun a ↦ List.cons_le_cons b a-/

lemma erase_sorted (l : List ℕ) (a : ℕ) (hl : l.Sorted (· ≤ ·)) : (l.erase a).Sorted (· ≤ ·) := by
  induction' l with b l hbl
  · simp_all only [List.sorted_nil, List.erase_nil]
  · simp_all only [List.sorted_cons, true_implies]
    by_cases hab : b = a
    · simp_all only [List.erase_cons_head]
    · simp_all only [beq_iff_eq, not_false_eq_true, List.erase_cons_tail, List.sorted_cons,
      and_true]
      intro c hc
      exact hl.1 c (List.erase_subset _ _ hc)

lemma erase_cancel_of_mem {l₁ l₂ : List ℕ} {a : ℕ} (h1 : a ∈ l₁) (h2 : a ∈ l₂)
    (hl1 : l₁.Sorted (· ≤ ·)) (hl2 : l₂.Sorted (· ≤ ·))
    (h : l₁.erase a = l₂.erase a) : l₁ = l₂ := by
  rw [← List.orderedInsert_erase a l₁ h1 hl1, ← List.orderedInsert_erase a l₂ h2 hl2]
  congr 1
  convert h

lemma diff_cancel {l₁ l₂ l : List ℕ} (h : l.Nodup)
    (h1 : l ⊆ l₁) (h2 : l ⊆ l₂) (h1s : l₁.Sorted (· ≤ ·))
    (h2s : l₂.Sorted (· ≤ ·)) : l₁.diff l = l₂.diff l ↔ l₁ = l₂ := by
  induction' l with a l ih generalizing l₁ l₂
  · simp only [List.diff_nil]
  · simp_all only [List.diff_cons]
    specialize @ih (l₁.erase a) (l₂.erase a)
    simp_all only [List.nodup_cons, List.cons_subset, true_implies]
    specialize ih ?_ ?_ ?_ ?_
    · intro x hx
      by_cases hxa : x = a
      · simp_all only
      · simp_all only [ne_eq, not_false_eq_true, List.mem_erase_of_ne]
        exact h1.2 hx
    · intro x hx
      by_cases hxa : x = a
      · simp_all only
      · simp_all only [ne_eq, not_false_eq_true, List.mem_erase_of_ne]
        exact h2.2 hx
    · apply erase_sorted _ _ h1s
    · apply erase_sorted _ _ h2s
    · rw [ih]
      constructor
      · exact erase_cancel_of_mem h1.1 h2.1 h1s h2s
      · tauto

theorem range_subset_ofFn_shit {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    List.range (n.len + 1) ⊆ List.ofFn (Fin.val ∘ f.toOrderHom) := by
  intro x hx
  simp only [List.mem_range] at hx
  rcases SimplexCategory.epi_iff_surjective.1 hf ⟨x, hx⟩ with ⟨w, hw⟩
  rw [List.mem_ofFn]
  use w
  simp_all only [List.ofFn_succ, Function.comp_apply]

theorem ofFn_shit_sorted {m n : SimplexCategory} (f : m ⟶ n) :
    (List.ofFn (Fin.val ∘ f.toOrderHom)).Sorted (· ≤ ·) :=
  List.sorted_le_ofFn_iff.2 f.toOrderHom.monotone

theorem diff_sorted {l₁ l₂ : List ℕ} (h1 : l₁.Sorted (· ≤ ·)) (h2 : l₂.Sorted (· ≤ ·)) :
    (l₁.diff l₂).Sorted (· ≤ ·) := by
  induction' l₂ with a l hal generalizing l₁
  · simp_all only [List.sorted_nil, List.diff_nil]
  · simp_all only [List.sorted_cons, List.diff_cons, true_implies]
    specialize @hal (l₁.erase a) (erase_sorted _ _ h1)
    assumption

lemma forfucksake (n : ℕ) : List.Sorted (· < ·) (List.range n) := by
  induction' n with n hn
  · simp_all only [List.range_zero, List.sorted_nil]
  · rw [List.range_eq_range', List.range'_succ, List.sorted_cons, List.range'_eq_map_range]
    constructor
    · intro b hb
      simp_all only [zero_add, List.mem_map, List.mem_range]
      rcases hb with ⟨a, ha, rfl⟩
      linarith
    · apply List.Pairwise.map (R := (· < ·))
      intro a b hab
      linarith
      exact hn

theorem toList_injectiveish {m n : SimplexCategory} (f g : m ⟶ n) (hf : Epi f) (hg : Epi g)
    (h : toList f = toList g) : f = g := by
  ext : 2
  simp_rw [toList, toMultiset, rangeMultiset_eq_ofFn] at h
  simp_rw [← Multiset.coe_range] at h
  simp_rw [Multiset.coe_sub] at h
  simp_rw [Multiset.coe_sort] at h
  rw [List.mergeSort_eq_self, List.mergeSort_eq_self] at h
  have := (diff_cancel (List.nodup_range _) (range_subset_ofFn_shit f hf)
    (range_subset_ofFn_shit g hg) (ofFn_shit_sorted f) (ofFn_shit_sorted g)).1 (by convert h)
  apply List.ofFn_injective at this
  ext x
  exact congr_fun this _
  · convert diff_sorted (l₂ := List.range (n.len + 1)) (ofFn_shit_sorted g) ?_
    refine List.Sorted.le_of_lt ?_
    exact forfucksake (n.len + 1)
  · convert diff_sorted (l₂ := List.range (n.len + 1)) (ofFn_shit_sorted f) ?_
    refine List.Sorted.le_of_lt ?_
    exact forfucksake (n.len + 1)

theorem toArrow_toList {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    toArrow (toList f) m.len (toArrowAux_some_of_epi (M := simplexThingy) f hf) = Arrow.mk f := by
  refine Arrow.ext _ _ ?_ ?_ ?_
  · rw [toArrow_left]
    rfl
  · rw [toArrow_right, ← toList_length f hf, Nat.add_sub_cancel]
    rfl
  · simp only [Functor.id_obj, Arrow.mk_right, Arrow.mk_left, Arrow.mk_hom]
    apply toList_injectiveish
    · letI := toArrow_epi m.len (toList f) (toList_sorted _) (toArrowAux_some_of_epi f hf)
        (simplexThingy_mono)
      exact epi_comp _ _
    · letI := hf
      exact epi_comp _ _
    · rw [toList_comp_eqToHom, toList_eqToHom_comp]
      rw [toList_toArrow]
      · exact toList_sorted _

theorem toArrowAux_some_append {x y : List ℕ} {m n : ℕ} (hx : (toArrowAux M x m).isSome)
    (hy : (toArrowAux M y n).isSome) (h : n + x.length = m) :
    (toArrowAux M (x ++ y) m).isSome := by
  induction' x with a l hal generalizing m
  · simp_all only [List.length_nil, add_zero, List.nil_append]
  · induction' m with m hm
    · simp_all only [List.length_cons, add_eq_zero, List.length_eq_zero, one_ne_zero, and_false]
    · simp_all only [List.length_cons, List.cons_append, add_right_eq_self, one_ne_zero,
      false_implies, implies_true]
      apply toArrowAux_some_cons' (toArrowAux_some_cond' hx).1
      specialize @hal m (toArrowAux_some_cons _ _ _ hx) ?_
      · omega
      · assumption

theorem arrowMk_eq_toArrow_Append {x y : List ℕ} {m n : ℕ} (hx : (toArrowAux M x m).isSome)
    (hy : (toArrowAux M y n).isSome) (h : n + x.length = m) :
    Arrow.mk ((toArrow x m hx).hom ≫ eqToHom (by
      simp only [toArrow_right, Functor.id_obj, toArrow_left, ← h, Nat.add_sub_cancel])
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
  · induction' m with m hm
    · exfalso
      simp_all only [Functor.id_obj, List.length_cons, add_eq_zero, List.length_eq_zero,
        one_ne_zero, and_false]
    · simp_rw [List.cons_append, toArrow_cons']
      refine Arrow.ext _ _ ?_ ?_ ?_
      · simp_all only [Functor.id_obj, Arrow.mk_left, toArrow_left, List.cons_append]
      · simp_all only [Functor.id_obj, List.length_cons, List.cons_append, Arrow.mk_right,
        toArrow_right, toArrowTail, List.length_append]
        rw [List.length_cons, ← add_assoc, add_left_inj] at h
        rw [← h, add_comm]
        rw [Nat.add_sub_add_left]
      · simp_all only [Functor.id_obj, List.length_cons, Arrow.mk_left, List.cons_append,
        Arrow.mk_right, Arrow.mk_hom, Category.assoc]
        specialize @hal m (toArrowAux_some_cons _ _ _ hx) ?_
        · rw [List.length_cons] at h
          omega
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
          simp only [List.length_cons, Nat.reduceSubDiff]
        · simp only [Functor.id_obj, List.cons_append, id_eq, List.length_cons, Arrow.mk_left,
          Arrow.mk_right, Category.assoc, Arrow.mk_hom, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
          rfl

theorem toArrowAux_simplexInsert_isSome {l : List ℕ} {a m : ℕ} (h : (toArrowAux M l m).isSome)
    (ha : a < m + 1) :
    (toArrowAux M (l.simplexInsert a) (m + 1)).isSome := by
  induction' l with b l hbl generalizing m a
  · simp_all only [toArrowAux, Functor.id_obj, Option.isSome_some, true_and, eqToHom_refl,
    Category.comp_id, dite_true]
  · simp_all only [List.simplexInsert]
    split_ifs with hab
    · rw [toArrowAux, ← Option.some_get h]
      simp only [Functor.id_obj]
      rw [dif_pos]
      simp only [Option.isSome_some]
      constructor
      · assumption
      · erw [toArrow_left]
    · induction' m with m hm
      · exfalso
        simp_all only [not_le, zero_add, Nat.lt_one_iff, not_lt_zero']
      · simp_all only [not_le]
        specialize @hbl (a - 1) m (toArrowAux_some_cons _ _ _ h) ?_
        · omega
        rw [toArrowAux, ← Option.some_get hbl]
        simp_all only [not_lt, Functor.id_obj]
        rw [dif_pos]
        simp only [Option.isSome_some]
        constructor
        · linarith
        · erw [toArrow_left]

theorem toArrowAux_simplexSort_isSome {l : List ℕ} {m : ℕ} (h : (toArrowAux M l m).isSome) :
    (toArrowAux M l.simplexSort m).isSome := by
  induction' l with b l hbl generalizing m
  · simp only [toArrowAux, Functor.id_obj, Option.isSome_some]
  · induction' m with m hm
    · exfalso
      simp_all only [toArrowAux, Option.isSome_none, Bool.false_eq_true]
    · simp only [List.simplexSort]
      apply toArrowAux_simplexInsert_isSome
      apply hbl
      exact toArrowAux_some_cons _ _ _ h
      exact (toArrowAux_some_cond' h).1

theorem cond'' {n : ℕ} (a : Fin (n + 1)) (b : Fin (n + 2)) (h : (a : ℕ) < (b : ℕ)) :
    M.epimap b ≫ M.epimap a = M.epimap ⟨a, by omega⟩ ≫ M.epimap ⟨b - 1, by omega⟩ := by
  have := M.epicond a ⟨b - 1, by omega⟩
  specialize this ?_
  · rw [Fin.le_iff_val_le_val]
    simp only
    omega
  · convert this.symm using 3
    · ext
      simp only [Fin.succ_mk, Nat.succ_eq_add_one]
      omega

theorem cond' {n : ℕ} (a : Fin (n + 2)) (b : Fin (n + 1)) (h : (a : ℕ) ≤ (b : ℕ)) :
    M.epimap a ≫ M.epimap b = M.epimap ⟨b + 1, by omega⟩ ≫ M.epimap ⟨a, by omega⟩ := by
  have := M.epicond ⟨a, by omega⟩ b
  specialize this ?_
  · rw [Fin.le_iff_val_le_val]
    simp only
    assumption
  · convert this

theorem toArrow_simplexInsert_eq {l : List ℕ} {a m : ℕ} (h : (toArrowAux M l m).isSome) (ha : a < m + 1) :
    toArrow (l.simplexInsert a) (m + 1) (toArrowAux_simplexInsert_isSome h ha)
      = toArrow (a :: l) (m + 1) (toArrowAux_some_cons' ha h) := by
  induction' l with b l hbl generalizing m a
  · simp_all only [List.simplexInsert]
  · simp_all only [List.simplexInsert]
    split_ifs with hab
    · simp_all only [ite_true]
    · induction' m with m hm
      · exfalso
        simp_all only [not_le, zero_add, Nat.lt_one_iff, not_lt_zero']
      · specialize @hbl (a - 1) m (toArrowAux_some_cons _ _ _ h) (by omega)
        refine Arrow.ext _ _ ?_ ?_ ?_
        · rw [toArrow_left, toArrow_left]
        · simp only [toArrow_right, List.length_cons, List.simplexInsert_length]
        · rw [toArrow_cons_hom (toArrowAux_some_cons' ha h)]
          unfold toArrowTail
          simp_rw [toArrow_cons_hom h]
          simp only [Functor.id_obj, inv_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
            Category.id_comp, eqToHom_trans]
          slice_rhs 2 3 =>
            rw [cond'' _ _ (by simp only; exact not_le.1 hab)]
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
            · omega
            · exact toArrowAux_some_cons _ _ _ h
          · linarith
          · apply toArrowAux_simplexInsert_isSome
            · exact toArrowAux_some_cons _ _ _ h
            · omega

theorem toArrow_simplexSort_eq {l : List ℕ} {m : ℕ} (h : (toArrowAux M l m).isSome) :
    toArrow l.simplexSort m (toArrowAux_simplexSort_isSome h) = toArrow l m h := by
  induction' l with b l hbl generalizing m
  · simp_all only [List.simplexSort]
  · induction' m with m hm
    · exfalso
      simp_all only [toArrowAux, Option.isSome_none, Bool.false_eq_true]
    · simp_all only [List.simplexSort]
      rw [toArrow_simplexInsert_eq]
      · rw [toArrow_cons', toArrow_cons']
        refine Arrow.ext _ _ ?_ ?_ ?_
        · rfl
        · simp only [toArrowTail, toArrow_right, List.simplexSort_length]
        · simp only [toArrowTail, Functor.id_obj, Category.assoc, eqToHom_refl, Category.id_comp]
          have := Arrow.hom_eq _ _ (@hbl m (toArrowAux_some_cons _ _ _ h))
          rw [← IsIso.eq_inv_comp, ← IsIso.eq_comp_inv] at this
          rw [this]
          simp only [Functor.id_obj, inv_eqToHom, Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.comp_id, eqToHom_trans_assoc]
      · apply toArrowAux_simplexSort_isSome
        exact toArrowAux_some_cons _ _ _ h
      · exact (toArrowAux_some_cond' h).1

theorem toArrow_injectiveish {m : ℕ} {l l' : List ℕ} (hl : (toArrowAux simplexThingy l m).isSome)
    (hl' : (toArrowAux simplexThingy l' m).isSome) (h : toArrow _ _ hl = toArrow _ _ hl')
    (hls : l.Sorted (· ≤ ·)) (hls' : l'.Sorted (· ≤ ·)) :
    l = l' := by
  rw [← toList_toArrow _ _ hls hl, ← toList_toArrow _ _ hls' hl']
  congr

theorem simplexSort_toList_append {m n o : SimplexCategory} (f : m ⟶ n) (g : n ⟶ o)
    (hf : Epi f) (hg : Epi g) :
    (toList f ++ toList g).simplexSort = toList (f ≫ g) := by
  letI : Epi (f ≫ g) := @epi_comp _ _ _ _ _ _ hf _ hg
  refine toArrow_injectiveish (toArrowAux_simplexSort_isSome (toArrowAux_some_append
    (toArrowAux_some_of_epi f hf) (toArrowAux_some_of_epi g hg) <| toList_length _ hf))
    (toArrowAux_some_of_epi (f ≫ g) inferInstance) ?_ ?_ ?_
  dsimp
  have : (toArrowAux simplexThingy (toList f ++ toList g).simplexSort m.len).isSome :=
    toArrowAux_simplexSort_isSome (toArrowAux_some_append (toArrowAux_some_of_epi f hf) (toArrowAux_some_of_epi g hg) <| toList_length _ hf)
  · rw [toArrow_simplexSort_eq (toArrowAux_some_append (toArrowAux_some_of_epi f hf) (toArrowAux_some_of_epi g hg) <| toList_length _ hf)]
    rw [← arrowMk_eq_toArrow_Append (toArrowAux_some_of_epi f hf) (toArrowAux_some_of_epi g hg) (toList_length _ hf)]
    simp only [Functor.id_obj]
    simp_rw [toArrow_toList]
    rw [← Arrow.hom_eq _ _ (toArrow_toList f hf).symm, ← Arrow.hom_eq _ _ (toArrow_toList g hg).symm]
    refine Arrow.ext _ _ ?_ ?_ ?_
    · simp only [simplexThingy]
      simp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Arrow.mk_hom, eqToHom_trans_assoc,
      Category.assoc, eqToHom_refl, Category.id_comp, toArrow_left, mk_len]
    · simp only [simplexThingy, Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Arrow.mk_hom, eqToHom_trans_assoc,
      Category.assoc, eqToHom_refl, Category.id_comp, toArrow_right, toList_length, mk_len]
      rw [← toList_length g, Nat.add_sub_cancel, mk_len]
      · assumption
    · simp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Arrow.mk_hom, mk_len,
      eqToHom_trans_assoc, Category.assoc, eqToHom_refl, Category.id_comp, eqToHom_trans,
      Category.comp_id]
  · exact simplexSort_sorted (toList f ++ toList g)
  · exact toList_sorted (f ≫ g)

theorem toArrowAux_toList_comp_isSome {m n o : SimplexCategory}
    {f : m ⟶ n} {g : n ⟶ o} (hf : Epi f) (hg : Epi g) :
    (toArrowAux M (toList (f ≫ g)) m.len).isSome := by
  rw [← simplexSort_toList_append _ _ hf hg]
  refine toArrowAux_simplexSort_isSome ?h
  apply toArrowAux_some_append (n := n.len)
  · exact toArrowAux_some_of_epi f hf
  · exact toArrowAux_some_of_epi g hg
  · rw [toList_length f hf]

theorem toArrow_comp {m n o : SimplexCategory} {f : m ⟶ n} {g : n ⟶ o}
    (hf : Epi f) (hg : Epi g) :
    toArrow (M := M) (toList (f ≫ g)) m.len (toArrowAux_toList_comp_isSome hf hg)
      = Arrow.mk ((toArrow (toList f) m.len (toArrowAux_some_of_epi f hf)).hom
      ≫ eqToHom (by simp only [toArrow_right, toArrow_left, toList_length'])
      ≫ (toArrow (toList g) n.len (toArrowAux_some_of_epi g hg)).hom) := by
  simp_rw [← simplexSort_toList_append f g hf hg]
  rw [toArrow_simplexSort_eq (toArrowAux_some_append (toArrowAux_some_of_epi f hf)
    (toArrowAux_some_of_epi g hg) (toList_length f hf))]
  rw [arrowMk_eq_toArrow_Append]
  rw [toList_length]
  assumption

/-
 tᴹₑ(f ≫ g) ≫ tᴹₘ(f ≫ g) vs tᴹₑ(f) ≫ tᴹₘ(f) ≫ tᴹₑ(g) ≫ tᴹₘ(g)

 (toList f ++ toList g).simplexSort = toList (f ≫ g)
also
φ := tₘ(f)≫tₑ(g)
tᴹₘ(f) ≫ tᴹₑ(g) vs tᴹₑ(φ) ≫ tᴹₘ(φ) = tᴹₑ(tₑ(φ) ≫ tₘ(φ)) ≫ tᴹₘ(tₑ(φ) ≫ tₘ(φ))
  = tᴹₑ(tₑ(φ)) ≫ tᴹₘ(tₘ(φ))


want mTAᴹ(Lₘ) ≫ TAᴹ(Lₑ) = TAᴹ(F(Lₘ, Lₑ)ₑ) ≫ mTAᴹ(F(Lₘ, Lₑ)ₘ)
whenever Lₘ is a
whereas tᴹₘ(f) = tᴹₘ(tₘ(f))

tₘ(f) ≫ tₑ(g) = mTA(o(f)) ≫ TA(tLG(g))
claiming that TA(F(f, g)ₑ) ≫ mTA (F(f, g)ₘ) is ^ that
or idk that sort(F(f, g)ₑ) is tLG(tₘ(f) ≫ tₑ(g))


-/
variable (M)

def toHom {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    M.obj m.len ⟶ M.obj n.len :=
  eqToHom (toArrow_left (toArrowAux_some_of_epi f hf)).symm
  ≫ (toArrow (toList f) m.len (toArrowAux_some_of_epi f hf)).hom
  ≫ eqToHom (by simp only [toArrow_right, toList_length', Functor.id_obj])

variable {M}

@[simp]
theorem toList_id {m : SimplexCategory} : toList (𝟙 m) = [] := by
  simp only [toList, toMultiset_id, Multiset.sort_zero]

theorem toHom_id {m : SimplexCategory} :
    toHom M (𝟙 m) inferInstance = 𝟙 (M.obj m.len) := by
  apply_fun Arrow.mk
  rw [toHom, Arrow.ugh]
  simp only [toArrow, Functor.id_obj, Arrow.mk_eq, toList_id, toArrowAux, mk_len, Option.get_some]
  rfl
  exact Arrow.mk_injective _ _

theorem toHom_comp {m n o : SimplexCategory} (f : m ⟶ n) (g : n ⟶ o)
    (hf : Epi f) (hg : Epi g) :
    toHom M (f ≫ g) (epi_comp' hf hg) = toHom M f hf ≫ toHom M g hg := by
  apply_fun Arrow.mk
  simp only [toHom, Functor.id_obj, Arrow.ugh, Arrow.mk_eq, Category.assoc, eqToHom_trans_assoc]
  rw [toArrow_comp hf hg]
  refine Arrow.ext _ _ ?_ ?_ ?_
  · simp only [Functor.id_obj, Arrow.mk_left, toArrow_left, mk_len]
  · simp only [Functor.id_obj, Arrow.mk_right, toArrow_right, toList_length', mk_len]
  · simp only [Functor.id_obj, mk_len, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · apply Arrow.mk_injective _ _


#check monoEquivOfFin

variable {m n : SimplexCategory} (f : m ⟶ n)

abbrev Im := Set.range f.toOrderHom
abbrev rangeList {m n : SimplexCategory}
  (f : m ⟶ n) {k : ℕ} --(hk : Fintype.card (Im f) = k)
  (F : Fin k ≃o Im f) : List ℕ :=
  List.ofFn <| Fin.val ∘ F.symm ∘ (Set.range f.toOrderHom).codRestrict f.toOrderHom Set.mem_range_self

theorem jesusfuckingchrist {α β : Type*} (f : α → β) (hf : f.Surjective) [Fintype β]
    [Fintype (Set.range f)] : Fintype.card (Set.range f) = Fintype.card β := by
  rw [Fintype.card_eq]
  constructor
  exact Equiv.subtypeUnivEquiv hf

theorem card_im_eq {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    Fintype.card (Im f) = n.len + 1 := by
  rw [jesusfuckingchrist, Fintype.card_fin]
  exact SimplexCategory.epi_iff_surjective.1 hf

theorem rangeList_fun_surjective {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    Function.Surjective (F.symm ∘ (Set.range f.toOrderHom).codRestrict f.toOrderHom Set.mem_range_self) :=
  Function.Surjective.comp (Equiv.bijective _).2 <| by
    rintro ⟨x, y, rfl⟩
    use y
    rfl

theorem rangeList_lemma {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) (F : Fin (n.len + 1) ≃o Im f) :
    Fin.val ∘ F.symm
      ∘ (Set.range f.toOrderHom).codRestrict
      f.toOrderHom Set.mem_range_self = Fin.val ∘ f.toOrderHom := by
  let yay : Fin (n.len + 1) ≃o Im f :=
    ((OrderIso.setCongr _ _ (Set.range_iff_surjective.2
      (SimplexCategory.epi_iff_surjective.1 hf))).trans (OrderIso.Set.univ)).symm
  rw [Subsingleton.elim F yay]
  ext x
  rfl

abbrev toMultisetGen {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) : Multiset ℕ :=
  rangeList f F - List.range (Fintype.card <| Im f)

def toListGen {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) : List ℕ :=
  Multiset.sort (· ≤ ·) (toMultisetGen f F)

theorem toListGen_eq_of_epi {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) (F : Fin (n.len + 1) ≃o Im f) :
    toListGen f F = toList f := by
  rw [toListGen, toMultisetGen, rangeList, rangeList_lemma f hf F]
  rw [toList, toMultiset, rangeMultiset_eq_ofFn, card_im_eq f hf]
  rfl

theorem toListGen_sorted {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    (toListGen f F).Sorted (· ≤ ·) := by
  rw [toListGen]
  exact Multiset.sort_sorted (fun x x_1 ↦ x ≤ x_1) (toMultisetGen f F)

theorem k_card {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    Fintype.card (Im f) = k := by
  have := Fintype.card_eq.2 ⟨F.toEquiv⟩
  rw [Fintype.card_fin] at this
  rw [this]

theorem k_le_m_succ {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    k ≤ m.len + 1 := by
  rw [← k_card f F]
  convert Fintype.card_range_le f.toOrderHom
  exact (Fintype.card_fin _).symm

theorem k_le_n_succ {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    k ≤ n.len + 1 := by
  rw [← k_card f F]
  refine le_trans (set_fintype_card_le_univ _) ?_
  simp only [Fintype.card_fin, le_refl]

theorem toListGen_length {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    (toListGen f F).length + k = m.len + 1 := by
  rw [toListGen, Multiset.length_sort, toMultisetGen, Multiset.card_sub, k_card f F]
  simp only [List.ofFn_succ, Function.comp_apply, Multiset.coe_card, List.length_cons,
    List.length_ofFn, List.length_range]
  rw [Nat.sub_add_cancel (k_le_m_succ f F)]
  rw [rangeList]
  rw [Multiset.coe_le]
  apply List.subperm_of_subset
  · exact List.nodup_range (Fintype.card ↑(Im f))
  · intro x hx
    simp_all only [List.mem_range]
    rw [List.mem_ofFn]
    rcases @rangeList_fun_surjective _ _ f k F ⟨x, k_card f F ▸ hx⟩ with ⟨w, hw⟩
    use w
    apply_fun Fin.val at hw
    assumption

/-
theorem kms {k : ℕ} (hk : (Im f).card = k) : Fintype.card (Set.range f.toOrderHom) = k := by
  have := @Fintype.card_ofFinset (Fin (n.len + 1)) (Set.range f.toOrderHom)
    (Finset.univ.image f.toOrderHom) (fun x => by simp)
  rw [← hk]
  convert this
-/

theorem toArrowAux_toListGen_isSome {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    (toArrowAux M (toListGen f F) m.len).isSome := by
  apply toArrowAux_some_of_forall_lt
  · exact toListGen_sorted f F
  · intro x hx
    rw [Nat.eq_sub_of_add_eq (toListGen_length f F)]
    rw [Nat.sub_sub_self]
    rw [toListGen, Multiset.mem_sort, toMultisetGen, Multiset.coe_sub, Multiset.mem_coe] at hx
    have : x ∈ rangeList f F := by
      apply List.diff_subset _ (List.range (Fintype.card ↑(Im f)))
      convert hx
    rw [rangeList, List.mem_ofFn, Set.range_comp] at this
    rcases this with ⟨w, hwl, rfl⟩
    exact w.2
    · exact k_le_m_succ f F

theorem order2_length {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    k + (monos.order2 f).length = n.len + 1 := by
  rw [monos.order2, Finset.length_sort, monos.rangeCompl]
  rw [Finset.card_image_of_injective, Finset.card_compl]
  simp only [← k_card f F, Fintype.card_ofFinset, Fintype.card_fin]
  convert Nat.add_sub_cancel' (k_le_n_succ f F)
  · rw [← k_card f F]
    simp only [Fintype.card_ofFinset]
  · rw [← k_card f F]
    have := Fintype.card_ofFinset (p := Set.range f.toOrderHom) (Finset.univ.image f.toOrderHom) (fun x => by simp)
    convert this.symm
  · exact Fin.val_injective


structure thingys extends thingy, monos.thingy :=
  (condfst : ∀ {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j),
    map (Fin.castSucc i) ≫ epimap j.succ = epimap j ≫ map i)
  (condsnd : ∀ {n} {i : Fin (n + 1)}, map (Fin.castSucc i) ≫ epimap i = 𝟙 (obj n))
  (condsndsnd : ∀ {n} {i : Fin (n + 1)}, map i.succ ≫ epimap i = 𝟙 (obj n))
  (condthrd : ∀ {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i),
    map i.succ ≫ epimap (Fin.castSucc j) = epimap j ≫ map i)

def thingys.tomonothingy (M : thingys) : monos.thingy where
    C := M.C
    obj := M.obj
    map := M.map
    cond := M.cond

def simplexThingys : thingys :=
  { simplexThingy, monos.simplexThingy with
    condfst := δ_comp_σ_of_le
    condsnd := δ_comp_σ_self
    condsndsnd := δ_comp_σ_succ
    condthrd := δ_comp_σ_of_gt }

theorem k_pos {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ}(F : Fin k ≃o Im f)  :
    0 < k := by
  rw [← k_card f F]
  have : 0 < (Finset.univ.image f.toOrderHom).card := by
    simp only [Finset.card_pos, Finset.image_nonempty]
    use 0
    exact Finset.mem_univ 0
  convert this
  convert Fintype.card_ofFinset (p := Set.range (f.toOrderHom)) (Finset.univ.image f.toOrderHom)
    (fun x => by simp)

theorem monos.toArrowAux_order2_isSome {M : monos.thingy} {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F : Fin k ≃o Im f) :
    (toArrowAux M (monos.order2 f) (k - 1)).isSome := by
  apply monos.toArrowAux_some_of_forall_lt
  · exact order2_sorted f
  · rw [Nat.eq_sub_of_add_eq' <| _root_.order2_length f F]
    intro x hx
    have : (k - 1) + (n.len + 1 - k) + 1 = n.len + 1 := by
      have := k_pos f F
      sorry -- fuck thissss
    rw [this]
    rw [order2] at hx
    simp_all only [Fintype.card_ofFinset, rangeCompl, Finset.mem_sort, Finset.mem_image,
      Finset.mem_compl, Finset.mem_univ, true_and, not_exists]
    rcases hx with ⟨y, a, rfl⟩
    linarith [y.2]

variable (B : thingys)

theorem toArrow_right_left {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ}(F : Fin k ≃o Im f) :
    (toArrow (toListGen f F) m.len (toArrowAux_toListGen_isSome (M := B.tothingy) f F)).right
      = (monos.toArrow (monos.order2 f) (k - 1) (monos.toArrowAux_order2_isSome
      (M := B.tomonothingy) f F)).left := by
  rw [toArrow_right, monos.toArrow_left]
  have := Nat.eq_sub_of_add_eq (@toListGen_length m n f k F) -- why does (_ := _) keep not working?
  rw [this]
  sorry

def MAP1 (M : monos.thingy) {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F :  Fin k ≃o Im f) :
    M.obj (k - 1) ⟶ M.obj n.len :=
  eqToHom (monos.toArrow_left ((monos.toArrowAux_order2_isSome f F))).symm ≫
      (monos.toArrow (monos.order2 f) (k - 1) (monos.toArrowAux_order2_isSome f F)).hom
  ≫ eqToHom (by
    simp [monos.toArrow_right]
    rw [Nat.eq_sub_of_add_eq <| order2_length f F]
    rw [Nat.succ_sub_sub_succ]
    simp only [tsub_zero]
    rw [Nat.sub_add_cancel]
    have := k_pos f F
    have h' := order2_length f F
    omega)

theorem fffsss {a b c d : SimplexCategory} (hab : a = b) (hcd : c = d)
    (f : a ⟶ c) (g : b ⟶ d)
    (H : eqToHom hab ≫ g = f ≫ eqToHom hcd) :
    Finset.image Fin.val (Finset.univ.image f.toOrderHom)ᶜ = Finset.image Fin.val (Finset.univ.image g.toOrderHom)ᶜ := by
  cases hab
  cases hcd
  simp_all only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem idfk678 {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F :  Fin k ≃o Im f) :
    monos.rangeCompl (MAP1 monos.simplexThingy f F) = (monos.order2 f).toFinset := by
  have := monos.rangeCompl_toArrow (k - 1) (monos.order2 f) (monos.order2_sorted f) (monos.toArrowAux_order2_isSome f F)
  rw [← this]
  simp only [monos.rangeCompl, len_mk, Functor.id_obj]
  · apply fffsss
    swap
    · simp only [monos.toArrow_left]
    swap
    · simp only [monos.toArrow_right]; rw [Nat.eq_sub_of_add_eq <| order2_length f F]; sorry
    · rw [MAP1]
      simp only [Functor.id_obj, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

def MAP2 (M : thingy) {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F :  Fin k ≃o Im f) :
    M.obj m.len ⟶ M.obj (k - 1) :=
  eqToHom (toArrow_left (toArrowAux_toListGen_isSome f F)).symm
  ≫ (toArrow (toListGen f F) m.len (toArrowAux_toListGen_isSome f F)).hom
  ≫ eqToHom (by simp [toArrow_right]; sorry)

theorem idfk2 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (hg : g.Injective) (hf : f.Surjective) (x : α) :
    Multiset.count (g (f x)) (Multiset.map g Finset.univ.1)
      = Multiset.count (f x) Finset.univ.1 := by
  simp only [Multiset.count_map_eq_count' _ _ hg]

theorem F_comp {α β : Type*} {f : α → β} [Fintype α] [LinearOrder α]
    [Fintype β] [LinearOrder β] {k : ℕ} (H : StrictMono f) (F1 : Fin k ≃o Set.range f)
    (F2 : Fin k ≃o α) :
    F1.symm ∘ (Set.codRestrict f (Set.range f) sorry)
      = F2.symm := by
  ext x : 1
  show ((StrictMono.orderIso f H).trans F1.symm) x
    = F2.symm x
  congr 1
  exact Subsingleton.elim _ _

theorem mono_strictMono {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f) :
    StrictMono f.toOrderHom := sorry

theorem codRestrict_comp {α β γ : Type*} (f : α → β) (g : β → γ) (hf : f.Surjective) :
    Set.codRestrict (g ∘ f) (Set.range (g ∘ f)) sorry
      = Set.codRestrict g (Set.range (g ∘ f)) sorry ∘ f := by
  ext x
  simp only [Set.val_codRestrict_apply, Function.comp_apply]

theorem fuckknows {m k : ℕ} (f : Fin m →o Fin k) (hf : Function.Surjective f)
    (F : Fin k ≃o Set.range f) :
    F.symm ∘ (Set.codRestrict f (Set.range f) sorry)
      = f := by
  let F' : Set.range f ≃o Fin k :=
    (OrderIso.setCongr _ _ (Set.range_iff_surjective.2 hf)).trans OrderIso.Set.univ
  rw [Subsingleton.elim F.symm F']
  ext x
  rfl

theorem toListGen_comp_mono {m n k : SimplexCategory} (f : m ⟶ k) (g : k ⟶ n)
    (hf : Epi f) (hg : Mono g) (F1 : Fin (k.len + 1) ≃o Im (f ≫ g))
    (F2 : Fin (k.len + 1) ≃o Im f) :
    toListGen (f ≫ g) (k := k.len + 1) F1 = toListGen f (k := k.len + 1) F2 := by
  simp only [toListGen, comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, Fintype.card_ofFinset]
  congr 1
  simp_rw [toMultisetGen]
  congr 1
  simp_rw [rangeList]
  congr
  ext x
  congr
  simp only [Im, comp_toOrderHom, OrderHom.comp_coe]
  rw [codRestrict_comp]
  simp only [← Function.comp.assoc]
  rw [fuckknows]
  convert Function.id_comp _
  ext x : 1
  let F3 : Fin (k.len + 1) ≃o Im g :=
    F1.trans <| OrderIso.setCongr _ _ (by
      unfold Im
      simp_all only [comp_toOrderHom, OrderHom.comp_coe, Set.range_comp]
      rw [Set.range_iff_surjective.2 (SimplexCategory.epi_iff_surjective.1 hf)]
      simp only [Set.image_univ])
  have := congr_fun (F_comp (f := g.toOrderHom) (k := k.len + 1) (mono_strictMono g hg) F3 (OrderIso.refl _)) x
  convert this using 1
  · sorry
  · sorry
  · sorry

theorem wtf {n m : ℕ}
    (f g : Fin n → Fin m) (hf : f.Surjective) (hfm : Monotone f)
    (hg : g.Surjective) (hgm : Monotone g) (h : ∀ x : Fin m, Multiset.count x (Multiset.map f Finset.univ.1)
      = Multiset.count x (Multiset.map g Finset.univ.1)) :
    f = g := by
  apply List.ofFn_injective
  rw [← List.mergeSort_eq_self _ (List.sorted_le_ofFn_iff.2 hfm)]
  nth_rw 1 [← List.mergeSort_eq_self _ (List.sorted_le_ofFn_iff.2 hgm)]
  rw [← Multiset.coe_sort, ← Multiset.coe_sort]
  congr 1
  ext x
  simp only [comp_toOrderHom, OrderHom.comp_coe, ← List.map_ofFn, ← Multiset.map_coe, ← Fin.univ_val_map]
  rcases hf x with ⟨y, hy⟩
  rcases hg x with ⟨z, hz⟩
  rw [← hy, h]

theorem idfk500 {m n k : SimplexCategory} (f : m ⟶ n)
    (α : m ⟶ k) (hα : Epi α) (β : k ⟶ n) (hβ : Mono β)
    (hrange : Finset.univ.image β.toOrderHom = Finset.univ.image f.toOrderHom)
    (hcount : ∀ x : Fin (k.len + 1), Multiset.count x
      (Multiset.map α.toOrderHom Finset.univ.1) = Multiset.count (β.toOrderHom x) (Multiset.map f.toOrderHom Finset.univ.1)) :
    α ≫ β = f := by
  ext : 2
  apply List.ofFn_injective
  rw [← List.mergeSort_eq_self _ (List.sorted_le_ofFn_iff.2 (OrderHom.monotone _))]
  nth_rw 2 [← List.mergeSort_eq_self _ (List.sorted_le_ofFn_iff.2 (OrderHom.monotone _))]
  rw [← Multiset.coe_sort, ← Multiset.coe_sort]
  congr 1
  ext x
  simp only [comp_toOrderHom, OrderHom.comp_coe, ← List.map_ofFn, ← Multiset.map_coe, ← Fin.univ_val_map]
  by_cases H : x ∈ Finset.univ.image f.toOrderHom
  · rcases Finset.mem_image.1 H with ⟨y, hy, hy'⟩
    rw [← hrange] at H
    rcases Finset.mem_image.1 H with ⟨z, hz, hz'⟩
    nth_rw 1 [← hz']
    rw [← hy']
    rw [← Finset.image_univ_of_surjective (SimplexCategory.epi_iff_surjective.1 hα)] at hz
    rcases Finset.mem_image.1 hz with ⟨w, hw, hw'⟩
    rw [← hw']
    rw [Multiset.count_map_eq_count']
    rw [Finset.image_univ_of_surjective (SimplexCategory.epi_iff_surjective.1 hα)] at hz
    rw [hy', ← hz', ← hw']
    rw [hcount]
    · exact SimplexCategory.mono_iff_injective.1 hβ
  · rw [Multiset.count_eq_zero_of_not_mem]
    · rw [Multiset.count_eq_zero_of_not_mem]
      · intro hx
        apply H
        show _ ∈ Finset.val _
        rwa [Finset.image_val, Multiset.mem_dedup]
    · intro hx
      apply H
      show _ ∈ Finset.val _
      rw [← hrange]
      rw [Finset.image_val, Multiset.mem_dedup]
      apply Multiset.map_subset_map _ hx
      intro z hz
      exact Finset.mem_univ _

theorem MAP1_mono (M : monos.thingy) {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F :  Fin k ≃o Im f)
    (hM : ∀ {n : ℕ} (i : Fin (n + 2)), Mono (M.map i)) :
    Mono (MAP1 M f F) := by
        apply mono_comp'
        · infer_instance
        · apply mono_comp'
          · apply monos.toArrow_mono
            · exact monos.order2_sorted _
            · assumption
          · infer_instance

theorem MAP2_epi (M : thingy) {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F :  Fin k ≃o Im f)
    (hE : ∀ {n : ℕ} (i : Fin (n + 1)), Epi (M.epimap i)) :
    Epi (MAP2 M f F) := by
  apply epi_comp'
  · infer_instance
  · apply epi_comp'
    · apply toArrow_epi
      · exact toListGen_sorted _ F
      infer_instance
    · infer_instance

theorem strongEpiMonoFactorisation_card {m n : SimplexCategory} (f : m ⟶ n)
    (F : Limits.StrongEpiMonoFactorisation f) : Fintype.card (Im f) = F.I.len + 1 := by
  have : Set.range f.toOrderHom = Set.range F.m.toOrderHom := by
    have := F.1.5
    rw [SimplexCategory.Hom.ext_iff] at this
    rw [← this]
    simp only [comp_toOrderHom, OrderHom.comp_coe]
    have hepi : Epi F.e := sorry
    rw [Set.range_comp, Set.range_iff_surjective.2 (SimplexCategory.epi_iff_surjective.1 hepi)]
    simp only [Set.image_univ]
  have h' := Set.card_range_of_injective (SimplexCategory.mono_iff_injective.1 F.1.3)
  simp only [ Fintype.card_fin] at h'
  rw [← h']
  unfold Im
  apply Fintype.card_congr
  apply Equiv.setCongr _
  rw [this]

theorem idk_mono {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ}
    (F : Fin k ≃o Im f)
    (G : Limits.StrongEpiMonoFactorisation f) :
    Arrow.mk G.m = (monos.toArrow (M := monos.simplexThingy) (monos.order2 f) (k - 1)
      (monos.toArrowAux_order2_isSome f F)) := by
  refine Arrow.ext _ _ ?_ ?_ ?_
  · simp only [Arrow.mk_left, monos.toArrow_left, monos.simplexThingy]
    ext
    apply_fun (· + 1)
    simp only [len_mk]
    rw [← strongEpiMonoFactorisation_card f G]
    rw [k_card f F]
    have := k_pos f F
    omega
    · exact add_left_injective 1
  · simp only [Arrow.mk_right, monos.simplexThingy, monos.toArrow_right]
    ext
    apply_fun (· + 1)
    dsimp
    rw [← order2_length f F]
    have := k_pos f F
    omega
    · exact add_left_injective 1
  · ext : 2
    apply Fin.strictMono_unique
    · simp only [Arrow.mk_left, Functor.id_obj, Arrow.mk_right, Arrow.mk_hom]
      apply mono_strictMono
      exact mono_comp _ _
    · simp only [monos.toArrow_left, monos.toArrow_right, monos.simplexThingy]
      apply mono_strictMono
      apply mono_comp'
      · infer_instance
      · exact monos.toArrow_mono _ _ (monos.order2_sorted _) _ (fun i => by dsimp [simplexThingy]; infer_instance)
    · have := idfk678 f F
      rw [monos.order2] at this
      simp only [Finset.sort_toFinset] at this
      simp_rw [monos.rangeCompl] at this
      apply Finset.image_injective at this
      apply compl_injective at this
      simp only [len_mk, MAP1, Functor.id_obj, comp_toOrderHom, OrderHom.comp_coe] at this
      simp only [Arrow.mk_left, Functor.id_obj, Arrow.mk_right, Arrow.mk_hom, comp_toOrderHom,
        OrderHom.comp_coe]
      nth_rw 2 [Set.range_comp]
      rw [Set.range_iff_surjective.2 (SimplexCategory.epi_iff_surjective.1 _)]
      simp only [Set.image_univ]
      apply_fun Finset.toSet at this
      simp only [Finset.coe_image, Function.comp_apply, Finset.coe_univ, Set.image_univ] at this
      rw [← SimplexCategory.Hom.ext_iff.1 (G.1.5)] at this
      simp only [comp_toOrderHom, OrderHom.comp_coe] at this
      rw [Set.range_comp] at this
      simp only [Set.range_iff_surjective.2 (SimplexCategory.epi_iff_surjective.1 _)] at this
      rw [Set.image_univ] at this
      sorry -- ffs it's fine but I need to sort out my Arrows
      · infer_instance
      · exact Fin.val_injective

theorem toListGen_well_def {m n : SimplexCategory} (f g : m ⟶ n)
    (h1 : f = g) {j k : ℕ} (Ff : Fin j ≃o Im f) (Fg : Fin k ≃o Im g) :
    toListGen f Ff = toListGen g Fg := by
  cases h1
  have : j = k := by
    rw [← k_card f Ff, ← k_card f Fg]
  cases this
  rw [Subsingleton.elim Ff Fg]

theorem toArrow_toListGen_of_epi {m n : SimplexCategory}
    (f : m ⟶ n) (hf : Epi f) {k : ℕ} (F : Fin k ≃o Im f) :
    toArrow (M := simplexThingy) (toListGen f F) m.len (toArrowAux_toListGen_isSome f F) =  Arrow.mk f := by
  have := toArrow_toList f hf
  let F' : Fin (n.len + 1) ≃o Im f :=
    (Fin.castOrderIso <| by
      rw [← k_card f F]
      unfold Im
      have := Fintype.card_fin (n.len + 1)
      have := Set.range_iff_surjective.2 (SimplexCategory.epi_iff_surjective.1 hf)
      apply_fun Fintype.card at this
      rw [this]
      rw [(set_fintype_card_eq_univ_iff _).2 rfl, Fintype.card_fin]).trans F
  have h' := toListGen_eq_of_epi f hf F'
  rw [toListGen_well_def _ _ rfl F' F] at h'
  have h'' := toArrow_toList f hf
  rw [← h'']
  congr

theorem idk_epi {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ}
    (F : Fin k ≃o Im f)
    (G : Limits.StrongEpiMonoFactorisation f) :
    Arrow.mk G.e = (toArrow (M := simplexThingy) (toListGen f F) m.len (toArrowAux_toListGen_isSome f F)) := by
  haveI hepi : Epi G.e := inferInstance
  let X : Fin (G.I.len + 1) ≃o Im (G.e ≫ G.m) :=
    (Fin.castOrderIso (m := k) (by rw [← strongEpiMonoFactorisation_card, k_card f F])).trans
      <| F.trans <| OrderIso.setCongr _ _ <| G.1.5.symm ▸ rfl
  let Y : Fin (G.I.len + 1) ≃o Im G.e :=
    ((OrderIso.setCongr _ _ (Set.range_iff_surjective.2
    (SimplexCategory.epi_iff_surjective.1 inferInstance))).trans (OrderIso.Set.univ)).symm
  have := toListGen_comp_mono G.e G.m inferInstance inferInstance X Y
  rw [toListGen_well_def (G.e ≫ G.m) f G.1.5 X F] at this
  simp_all only [Arrow.mk_left, Functor.id_obj, Arrow.mk_right, Arrow.mk_hom, comp_toOrderHom,
    OrderHom.comp_coe]
  rw [toArrow_toListGen_of_epi G.e inferInstance Y]

theorem idk_total {m n : SimplexCategory} (f : m ⟶ n) {k : ℕ}
    (F : Fin k ≃o Im f) :
    MAP2 simplexThingy f F ≫ MAP1 monos.simplexThingy f F = f := by
  rcases Limits.HasStrongEpiMonoFactorisations.has_fac f with ⟨G⟩
  simp only [MAP2, Functor.id_obj, MAP1, Category.assoc, eqToHom_trans_assoc]
  rw [← Arrow.hom_eq _ _ <| idk_mono f F G]
  rw [← Arrow.hom_eq _ _ <| idk_epi f F G]
  simp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Arrow.mk_hom, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id, eqToHom_trans_assoc, Category.id_comp,
    Limits.MonoFactorisation.fac]

/-/
theorem order2_toFinset {m n : SimplexCategory} (f : m ⟶ n) :
    (monos.order2 f).toFinset = Finset.univ.image f.toOrderHom := by
  have := monos.rangeCompl_toArrow (k - 1) (monos.order2 f) (monos.order2_sorted f) (monos.toArrowAux_order2_isSome f F)
  rw [← this]
  simp only [monos.rangeCompl, len_mk, Functor.id_obj]
  apply fffsss
  · simp only [monos.toArrow_left]; rfl
  · simp only [monos.toArrow_right]; rw [Nat.eq_sub_of_add_eq <| order2_length f F]; sorry-/
def yay {m n : SimplexCategory}
    (f : m ⟶ n) {k : ℕ} (F :  Fin k ≃o Im f) :
    Limits.StrongEpiMonoFactorisation f where
      I := mk (k - 1)
      m := MAP1 monos.simplexThingy f F
      m_mono := MAP1_mono monos.simplexThingy f F (fun i => by dsimp [monos.simplexThingy]; infer_instance)
      e := MAP2 simplexThingy f F
      fac := idk_total f F
      e_strong_epi := by
        convert strongEpi_of_epi (C := SimplexCategory) (MAP2 simplexThingy f F)
        exact MAP2_epi simplexThingy f F (fun i => by dsimp [simplexThingy]; infer_instance)

variable (M)

def ToHom (M : thingys) {m n : SimplexCategory} (f : m ⟶ n)
    {k : ℕ} (F : Fin k ≃o Im f) :
    M.obj m.len ⟶ M.obj n.len :=
  MAP2 M.tothingy f F ≫ MAP1 M.tomonothingy f F

variable {M}

theorem rangeList_id {m : SimplexCategory} (F : Fin (m.len + 1) ≃o Im (𝟙 m)) :
    rangeList (𝟙 m) F = List.range (m.len + 1) := by
  rw [rangeList]
  rw [← List.map_ofFn]
  convert List.map_coe_finRange _
  rw [← List.ofFn_id]
  congr
  let F2 : Fin (m.len + 1) ≃o Im (𝟙 m) :=
    OrderIso.Set.univ.symm.trans <| OrderIso.setCongr _ _ Set.range_id.symm
  rw [Subsingleton.elim F F2]
  ext x
  rfl

@[simp]
theorem toListGen_id {m : SimplexCategory} (F : Fin (m.len + 1) ≃o Im (𝟙 m)) : toListGen (𝟙 m) F = [] := by
  simp only [toListGen]
  rw [toMultisetGen]
  rw [rangeList_id]
  rw [card_im_eq, tsub_self]
  simp only [Multiset.sort_zero]
  infer_instance

abbrev ff : mk 5 ⟶ mk 6 :=
  σ 0 ≫ σ 0 ≫ σ 1 ≫ δ 0 ≫ δ 3 ≫ δ 4 ≫ δ 6

abbrev gg : mk 6 ⟶ mk 4 :=
  σ 0 ≫ σ 0 ≫ σ 0 ≫ σ 1 ≫ δ 0 ≫ δ 3

theorem awshoot : Fintype.card (Im (𝟙 (mk 0))) = 1 := rfl
#eval! MAP1 monos.simplexThingy (𝟙 (mk 0)) (k := 1) (monoEquivOfFin (Im (𝟙 <| mk 0)) awshoot)
#eval Fintype.card (Im ff)
#eval! MAP1 monos.simplexThingy ff (k := 3) (monoEquivOfFin (Im ff) <| rfl)
#eval! MAP2 simplexThingy gg (k := 3) (monoEquivOfFin (Im gg) <| rfl)
#eval! MAP1 monos.simplexThingy ff (k := 3) (monoEquivOfFin (Im ff) <| rfl)
 ≫ MAP2 simplexThingy gg (k := 3) (monoEquivOfFin (Im gg) <| rfl)

instance {X Y : simplexThingys.C} : Repr (X ⟶ Y) where
  reprPrec f _ := repr f.toOrderHom.1

def simplexInsert_δ (a : ℕ) : ∀ l : List ℕ, List ℕ × List ℕ
| [] => ([], [a])
| b :: l =>
  if a < b then ((b - 1) :: (simplexInsert_δ a l).1, (simplexInsert_δ a l).2) else
  if b + 1 < a then (b :: (simplexInsert_δ (a - 1) l).1, (simplexInsert_δ (a - 1) l).2)
  else (l, [])

def simplexSwapAux : ∀ (lm le : List ℕ), List ℕ × List ℕ
| [], le => (le, [])
| a :: lm, le => ((simplexSwapAux lm (simplexInsert_δ a le).1).1,
  (simplexSwapAux lm (simplexInsert_δ a le).1).2 ++ (simplexInsert_δ a le).2)

def simplexSwap (lm le : List ℕ) : List ℕ × List ℕ := ((simplexSwapAux lm.reverse le).1,
  (simplexSwapAux lm.reverse le).2)

theorem rangeList_mono {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f)
    {k : ℕ} (F : Fin k ≃o Im f) :
    rangeList f F = List.range k := by
  rw [rangeList]
  rw [← List.map_ofFn]
  convert List.map_coe_finRange _
  apply_fun List.toFinset
  ext x
  simp only [List.mem_toFinset, List.toFinset_finRange, Finset.mem_univ, iff_true]
  rw [List.mem_ofFn]
  rw [Function.Surjective.range_comp, Set.range_iff_surjective.2]
  trivial
  · exact OrderIso.surjective F.symm
  · rintro ⟨x, ⟨y, rfl⟩⟩
    use y
    ext
    rfl
  · sorry -- lol

theorem toListGen_mono {m n : SimplexCategory} (f : m ⟶ n) (hf : Mono f)
    {k : ℕ} (F : Fin k ≃o Im f) :
    toListGen f F = [] := by
  simp only [toListGen, toMultisetGen, rangeList_mono f hf F, ← k_card f F, tsub_self]
  simp only [Multiset.sort_zero]

theorem mono_of_toListGen_eq_nil {m n : SimplexCategory} (f : m ⟶ n)
    {k : ℕ} (F : Fin k ≃o Im f) (h : toListGen f F = []) : Mono f := sorry

theorem mono_of_toList_eq_nil {m n : SimplexCategory} (f : m ⟶ n)
    (hf : toList f = []) : Mono f := by
  sorry

theorem wither {l h : List ℕ} {b : ℕ} (H : l = h ++ [b]) :
    ∃ (a : ℕ) (t : List ℕ), l = a :: t := by
  induction' l with a t hat
  · simp_all only [List.nil_eq_append, List.cons_ne_self, and_false]
  · use a, t

theorem running {l t : List ℕ} (a : ℕ) (H : l = a :: t) :
    ∃ (b : ℕ) (h : List ℕ), l = h ++ [b] := by
  induction' t with c d hcd generalizing a l
  · simp_all only
    use a, []
    simp only [List.nil_append]
  · specialize hcd c rfl
    rcases hcd with ⟨p, q, hpq⟩
    use p, a :: q
    simp_all only [List.cons_append]

theorem monos.toArrowAux_concat_some {M : monos.thingy}
    (a : ℕ) (l : List ℕ) {k : ℕ}
    (hl : (monos.toArrowAux M (l ++ [a]) k).isSome) :
    (monos.toArrowAux M l k).isSome := by
  induction' l with b l hbl generalizing k
  · simp_all only [toArrowAux, Functor.id_obj, and_true, eqToHom_refl, Category.comp_id,
    Option.isSome_some]
  · have := monos.toArrowAux_some_cons _ _ _ hl
    specialize hbl this
    apply monos.toArrowAux_some_cons'
    · exact (monos.toArrowAux_some_cond' hl).1
    · assumption

theorem monos.toArrowAux_concat_cond {M : monos.thingy} (a : ℕ) (l : List ℕ) {k : ℕ}
    (hl : (monos.toArrowAux M (l ++ [a]) k).isSome) :
    a < k + l.length + 2 := by
  induction' l with b l hbl generalizing k
  · simp_all only [List.nil_append, List.length_nil, add_zero]
    exact (toArrowAux_some_cond' hl).1
  · simp_all only [List.cons_append, List.length_cons]
    specialize hbl (toArrowAux_some_cons _ _ _ hl)
    omega

theorem monos.toArrow_concat {M : monos.thingy} (a : ℕ) (l : List ℕ) {k : ℕ}
    (hl : (monos.toArrowAux M (l ++ [a]) k).isSome) :
    toArrow (l ++ [a]) k hl = Arrow.mk
      ((toArrow l k (toArrowAux_concat_some _ _ hl)).hom
      ≫ eqToHom (monos.toArrow_right _ _ _)
      ≫ M.map ⟨a, monos.toArrowAux_concat_cond _ _ hl⟩) := by
  induction' l with b l hbl generalizing k
  · simp_all only [List.nil_append, toArrow_cons', id_eq, Functor.id_obj, eqToHom_refl,
    Category.id_comp, List.length_nil, Nat.add_zero]
    apply Arrow.ext
    · simp only [toArrowTail, toArrow, toArrowAux, Functor.id_obj, Option.get_some,
      List.nil_append, and_true, eqToHom_refl, id_eq, Arrow.mk_right, Category.comp_id,
      Arrow.mk_left, Arrow.mk_hom, Category.id_comp]
    · simp only [Arrow.mk_left, toArrow_left]
    · simp only [toArrowTail, toArrow_right, List.length_nil, add_zero, Arrow.mk_right]
  · simp_all only [Functor.id_obj, List.cons_append, List.length_cons]
    specialize hbl (toArrowAux_some_cons _ _ _ hl)
    simp only [toArrow_cons', List.cons_append, id_eq, toArrowTail, Functor.id_obj,
      toArrow_cons_hom, Category.assoc, eqToHom_trans_assoc]
    have := Arrow.hom_eq _ _ hbl.symm
    simp only [this.symm, Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Arrow.mk_hom,
      Category.assoc, eqToHom_trans_assoc]
    apply Arrow.ext
    swap
    · simp only [Arrow.mk_left, toArrow_left]
    swap
    · simp only [toArrow_right, List.length_append, List.length_singleton, Arrow.mk_right]
      sorry
    · simp only [List.cons_append, id_eq, Arrow.mk_left, Functor.id_obj, Arrow.mk_right,
      Category.assoc, eqToHom_trans, Arrow.mk_hom, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
      congr 3
      sorry -- go fuck yourself

theorem exists_of_order2_eq_cons {m n : SimplexCategory} (f : m ⟶ mk (n.len + 1))
    {b : ℕ} {l : List ℕ} (h : monos.order2 f = l ++ [b]) (hf : Mono f) :
    ∃ (g : m ⟶ n) (hb : b < n.len + 2), f = g ≫ δ ⟨b, hb⟩ ∧ monos.order2 g = l := by
  have : (monos.toArrowAux monos.simplexThingy (l ++ [b]) m.len).isSome := by
    rw [← h]
    apply monos.toArrowAux_some_of_mono f hf (le_refl _)
  let g : m ⟶ n := eqToHom (monos.toArrow_left (monos.toArrowAux_concat_some b l this)).symm ≫
     (monos.toArrow l m.len (monos.toArrowAux_concat_some b l this)).hom ≫ eqToHom ?_
  swap
  · simp only [Functor.id_obj]
    rw [monos.toArrow_right]
    simp only [monos.simplexThingy]
    have h' := monos.order2_length f hf
    have h'' := monos.toArrow_right _ _ this
    sorry
  · use g, sorry
    constructor
    · sorry
    · sorry

theorem mono_really {m : SimplexCategory} {n : ℕ} (f : m ⟶ mk (n + 1))
    {b : ℕ} {l : List ℕ} (h : monos.order2 f = l ++ [b]) (hf : Mono f) :
    ∃ (g : m ⟶ mk n) (hb : b < n + 2), f = g ≫ δ ⟨b, hb⟩ ∧ monos.order2 g = l := by
  let F : m ⟶ mk ((mk n).len + 1) := f
  convert exists_of_order2_eq_cons F h hf

theorem exists_of_toList_eq_cons {m n : SimplexCategory} (f : mk (m.len + 1) ⟶ n)
    {b : ℕ} {l : List ℕ} (h : toList f = b :: l) (hf : Epi f) :
    ∃ (g : m ⟶ n) (hb : b < m.len + 1), f = σ ⟨b, hb⟩ ≫ g ∧ toList g = l := by
  have := toArrowAux_toList_some (M := simplexThingy) f b l h (toArrowAux_some_of_epi f hf)
  let g : m ⟶ n := eqToHom (by simp [toArrow_left, simplexThingy]) ≫ (toArrow l _ this).hom
    ≫ eqToHom sorry
  use g, sorry
  constructor
  · have lol : toArrow (M := simplexThingy)
      (toList f) (m.len + 1) (toArrowAux_some_of_epi f hf) = toArrow (b :: l) (m.len + 1) (h ▸ toArrowAux_some_of_epi f hf) := by
      simp_rw [← h]
    apply_fun Arrow.mk
    erw [toArrow_toList f hf] at lol
    rw [lol]
    rw [toArrow_cons']
    refine Arrow.ext _ _ ?_ ?_ ?_
    · simp only [mk_len, Arrow.mk_left]; rfl
    · simp only [toArrowTail, toArrow_right, mk_len, Arrow.mk_right]
      sorry
    · simp only [simplexThingy, toArrowTail, Functor.id_obj, mk_len, Arrow.mk_right, Category.assoc,
      Arrow.mk_left, eqToHom_refl, Arrow.mk_hom, Category.id_comp, g]
    · exact Arrow.mk_injective (mk (m.len + 1)) n
  · simp only [Functor.id_obj, toList_eqToHom_comp, toList_comp_eqToHom, g]
    rw [toList_toArrow]
    have := toList_sorted f
    rw [h, List.sorted_cons] at this
    exact this.2

theorem really {m : ℕ} {n : SimplexCategory} (f : mk (m + 1) ⟶ n)
    {b : ℕ} {l : List ℕ} (h : toList f = b :: l) (hf : Epi f) :
    ∃ (g : mk m ⟶ n) (hb : b < m + 1), f = σ ⟨b, hb⟩ ≫ g ∧ toList g = l := by
  let F : mk ((mk m).len + 1) ⟶ n := f
  convert exists_of_toList_eq_cons F h hf

theorem toList_σ_comp {m n : SimplexCategory} {b : Fin (m.len + 1)} {f : m ⟶ n} (hf : Epi f) :
    toList (σ b ≫ f) = List.simplexInsert b (toList f) := by
  have := toArrow_simplexInsert_eq (M := simplexThingy) (toArrowAux_some_of_epi f hf) b.2
  apply toArrow_injectiveish (toArrowAux_some_of_epi _ <| epi_comp' inferInstance hf)
    (toArrowAux_simplexInsert_isSome (toArrowAux_some_of_epi f hf) b.2)
  · --simp only [len_mk, this, toArrow_cons']
    rw [toArrow_toList (σ b ≫ f) (epi_comp' inferInstance hf)]
    simp only [mk_len, len_mk, this]
    rw [toArrow_cons (f := Arrow.mk f)]
    apply Arrow.ext _ _ ?_ ?_ ?_
    · rw [← toArrow_toList f hf]
      simp only [toArrow, Option.some_get]
    · simp only [Arrow.mk_left]; rfl
    · simp only [Arrow.mk_right, toArrowTail, toArrow_right]
    · rfl
  · exact toList_sorted (σ b ≫ f)
  · exact idfk _ _ (by exact toList_sorted f)

theorem toListGen_σ_comp {m n : SimplexCategory} {b : Fin (m.len + 1)} {f : m ⟶ n} {j k : ℕ}
    (F : Fin j ≃o Im f) (G : Fin k ≃o Im (σ b ≫ f)) :
    toListGen (σ b ≫ f) G = List.simplexInsert b (toListGen f F) := by
  have : σ b ≫ ((yay f F).e ≫ (yay f F).m) = σ b ≫ f := (yay f F).fac.symm ▸ rfl
  rw [← toListGen_well_def _ _ (yay f F).fac (monoEquivOfFin _ sorry) F]
  rw [← toListGen_well_def _ _ this (monoEquivOfFin _ sorry) G]
  rw [← Category.assoc]
  rw [toListGen_comp_mono (F2 := monoEquivOfFin _ sorry)]
  rw [toListGen_comp_mono (F2 := monoEquivOfFin _ sorry)]
  rw [toListGen_eq_of_epi, toListGen_eq_of_epi, toList_σ_comp]
  · infer_instance
  · infer_instance
  · apply epi_comp
  · infer_instance
  · infer_instance
  · apply epi_comp
  · infer_instance

theorem List.simplexInsert_of_forall_le {b : ℕ} {l : List ℕ} (hb : ∀ x ∈ l, b ≤ x) :
    l.simplexInsert b = b :: l := by
  induction' l with a l hal
  · simp_all only [simplexInsert]
  · simp_all only [mem_cons, or_true, implies_true, true_implies, forall_eq_or_imp, simplexInsert,
    ite_true]

theorem one {a : ℕ} {l : List ℕ} (hl : l.Sorted (· ≤ ·)) (ha : ∀ x ∈ l, a < x) :
    (simplexInsert_δ a <| l).1 = l.map (· - 1) := by
  induction' l with b l hbl
  · simp_all only [List.sorted_nil, List.not_mem_nil, false_implies, implies_true, simplexInsert_δ,
    List.map_nil]
  · simp only [List.sorted_cons, List.mem_cons, forall_eq_or_imp, List.map_cons] at hl ha ⊢
    simp_all only [simplexInsert_δ, ite_true, List.simplexSort]
    simp only [implies_true, true_implies] at hbl
    rw [hbl]

theorem the_bay {m n : ℕ} {a : Fin (m + 2)} (f : Fin (m + 2) →o Fin (n + 1))
    (ha : (a : ℕ) < n + 1) (hf : Function.Surjective f) (hfa : Set.InjOn f (Set.Iic ⟨a + 1, sorry⟩)) : -- needs extra assumption
    let E : Fin n ≃o Set.range (f ∘ a.succAbove) := StrictMono.orderIsoOfSurjective
      (Set.codRestrict ((Fin.mk a ha).succAbove) (Set.range (f ∘ a.succAbove)) sorry) (StrictMono.codRestrict (Fin.strictMono_succAbove _) _)
      (Set.codRestrict_surjective _ _ sorry _)
    Fin.succ ∘ E.symm ∘ Set.codRestrict (f ∘ a.succAbove) _ sorry
      = f ∘ Fin.succ := by
  set E : Fin n ≃o Set.range (f ∘ a.succAbove) := StrictMono.orderIsoOfSurjective
      (Set.codRestrict ((Fin.mk a ha).succAbove) (Set.range (f ∘ a.succAbove)) sorry) (StrictMono.codRestrict (Fin.strictMono_succAbove _) _)
      (Set.codRestrict_surjective _ _ sorry _)
  ext x : 1
  simp only [Function.comp_apply]
  have hfs : f (Fin.succ x) ≠ 0 := by
    have : f 1 ≠ 0 := by
      rw [← Fin.map_zero_of_monotone_surjective f]
      intro hnot
      specialize @hfa 0 (by simp) 1 (by simp; show (1 : ℕ) ≤ (a : ℕ) + 1; omega) hnot.symm
      simp_all only [zero_ne_one]
      · exact f.monotone
      · exact hf
    have h1 := f.monotone (a := 1) (b := x.succ) (show 1 ≤ (x : ℕ) + 1 by omega)
    intro hnot
    apply this
    rwa [← Fin.le_zero_iff, ← hnot]
  rw [← Fin.pred_inj (ha := Fin.succ_ne_zero _) (hb := hfs)]
  simp only [Fin.pred_succ]
  apply_fun E
  simp only [OrderIso.apply_symm_apply]
  ext
  simp only [Set.val_codRestrict_apply, Function.comp_apply]
  simp only [StrictMono.coe_orderIsoOfSurjective, Set.val_codRestrict_apply, E]
  by_cases hxa : x.castSucc < a
  · rw [Fin.succAbove_of_castSucc_lt]
    have this1 : f x.succ = ⟨(x : ℕ) + 1, sorry⟩ := by
      have := @eqOn_castLE' _ _ f _ hf hfa x.succ sorry
      ext
      apply_fun Fin.val at this
      simp_all only [ne_eq, Function.comp_apply, Fin.coe_castLE, id_eq, Fin.val_succ]
    simp_rw [this1]
    have this2 : f x.castSucc = ⟨x, sorry⟩ := by sorry -- fuck this
    simp_rw [this2]
    rw [Fin.succAbove_of_castSucc_lt]
    simp only [Fin.coe_castSucc, Fin.coe_pred, add_tsub_cancel_right]
    · rw [Fin.lt_iff_val_lt_val]
      simp only [Fin.coe_castSucc, Fin.coe_pred, add_tsub_cancel_right]
      exact Fin.lt_iff_val_lt_val.1 hxa
    · assumption
  · rw [not_lt] at hxa
    rw [Fin.succAbove_of_le_castSucc, Fin.succAbove_of_le_castSucc]
    rw [Fin.succ_pred _ hfs]
    have : f ⟨a + 1, sorry⟩ = ⟨a + 1, sorry⟩ := sorry -- more eqOn_castLE
    show Fin.val _ ≤ Fin.val _
    simp only [Fin.coe_castSucc, Fin.coe_pred]
    rw [← Nat.add_le_add_iff_right (n := 1)]
    apply_fun Fin.val at this
    simp only at this
    have ugh := f.monotone hxa
    sorry -- cbf
    assumption

theorem bending_hectic {l1 l2 : List ℕ} :
    Multiset.map (· + 1) (Multiset.ofList l1 - Multiset.ofList l2)
      = Multiset.ofList (l1.map (· + 1)) - Multiset.ofList (l2.map (· + 1)) := by
  simp only [Multiset.coe_sub, Multiset.map_coe]
  rw [List.map_diff]
  exact add_left_injective 1

theorem two {m : ℕ} (a : Fin (m + 2)) {n : SimplexCategory} (f : mk (m + 1) ⟶ n)
    (hf : Epi f) (ha : ∀ x ∈ toList f, (a : ℕ) < x)
    (F : Fin (n.len + 1) ≃o Im f) (G : Fin n.len ≃o Im (δ a ≫ f)) :
  (toMultisetGen _ G).map (· + 1) = toMultisetGen _ F := by
  simp_rw [toMultisetGen, k_card _ G, rangeList]
  rw [rangeList_lemma f hf F]
  let G' : Fin n.len ≃o Im (δ a ≫ f) := StrictMono.orderIsoOfSurjective
    (Set.codRestrict ((Fin.mk a ?_).succAbove) _ ?_) (StrictMono.codRestrict (Fin.strictMono_succAbove _) _)
    <| Set.codRestrict_surjective _ _ ?_ _
  · simp_all only [Multiset.mem_sort, len_mk, Subsingleton.elim G G', comp_toOrderHom,
    OrderHom.comp_coe]
    rw [k_card _ F, bending_hectic, List.map_ofFn]
    have : Fin.succ ∘ G'.symm ∘ _ = _ := the_bay (a := a) f.toOrderHom sorry (SimplexCategory.epi_iff_surjective.1 hf) sorry -- needs extra lemma meh
    have ugh : Fin.val ∘ Fin.succ (n := n.len) = (· + 1) ∘ Fin.val := by ext; rfl
    simp only [← Function.comp.assoc]
    rw [← ugh]
    simp only [Function.comp.assoc]
    erw [this]
    nth_rw 2 [List.ofFn_succ]
    sorry -- i cbf anymore
  · sorry
  · sorry
  · sorry

theorem Two {m : ℕ} (a : Fin (m + 2)) {n : SimplexCategory} (f : mk (m + 1) ⟶ n)
    (hf : Epi f) (ha : ∀ x ∈ toList f, (a : ℕ) < x)
    (F : Fin (n.len + 1) ≃o Im f) (G : Fin n.len ≃o Im (δ a ≫ f)) :
    (toListGen _ G) = (toListGen _ F).map (· - 1) := by
  simp_rw [toListGen]
  rw [← two a f hf ha F G]
  sorry -- i so cannot be fucked

theorem toList_σ {m : ℕ} (a : Fin (m + 1)) :
    toList (σ a) = [(a : ℕ)] := by
  erw [← Category.comp_id (σ a), toList_σ_comp, toList_id]
  simp only [List.simplexInsert, len_mk]
  · infer_instance

theorem toList_simplexSort {m n : SimplexCategory} (f : m ⟶ n) (hf : Epi f) :
    (toList f).simplexSort = toList f := by
  apply toArrow_injectiveish (m := m.len)
  rw [toArrow_simplexSort_eq]
  · exact simplexSort_sorted (toList f)
  · exact toList_sorted f
  · exact toArrowAux_some_of_epi f hf

theorem three {l : List ℕ} (a b : ℕ) (hl : (b :: l).Sorted (· ≤ ·)) (ha : b + 1 < a)
    (x : ℕ) (hx : x ∈ (simplexInsert_δ (a - 1) l).1) : b ≤ x := by
  induction' l with c l hcl generalizing a
  · simp_all only [List.sorted_singleton, simplexInsert_δ, List.not_mem_nil]
  · simp only [List.sorted_cons, List.mem_cons, forall_eq_or_imp, simplexInsert_δ] at hl hx
    split_ifs at hx with h1 h2
    · simp_all only [List.sorted_cons, implies_true, and_self, true_implies, List.mem_cons]
      rcases hx with (h3 | h4)
      · omega
      · exact hcl a ha h4
    · simp_all only [List.sorted_cons, implies_true, and_self, true_implies, not_lt, List.mem_cons]
      rcases hx with (rfl | h4)
      · exact hl.1.1
      · exact hcl (a - 1) (by omega) h4
    · simp_all

theorem toListGen_δ_comp_epi {m k : ℕ} {n : SimplexCategory} {a : Fin (m + 2)} (f : mk (m + 1) ⟶ n)
    (F : Fin k ≃o Im (δ a ≫ f)) (hf : Epi f) :
    toListGen _ F = (simplexInsert_δ a <| toList f).1 := by
  induction' x : toList f with b l hbl generalizing m f
  · have : mk (m + 1) = n := by
      ext
      apply le_antisymm
      · exact len_le_of_mono (mono_of_toList_eq_nil f x)
      · exact len_le_of_epi hf
    cases this
    have h' : f = 𝟙 _ := by
      apply @eq_id_of_isIso _ _ (isIso_of_bijective _)
      sorry -- obvs
    cases h'
    simp_all only [toList_id, List.simplexSort]
    rw [toListGen_mono]
    simp only [simplexInsert_δ]
    exact mono_comp _ _
  · unfold simplexInsert_δ
    cases' m with m
    · have h1 : n = mk 0 := sorry -- toList is a cons, so it's not id
      cases h1
      have : f = σ 0 := by
        ext x
        simp only [len_mk, Nat.reduceAdd, Fin.coe_fin_one, Fin.isValue]
      cases this
      rw [toList_σ] at x
      simp_all only [len_mk, Fin.coe_fin_one, List.cons.injEq]
      rcases x with ⟨rfl, rfl⟩
      simp only [Nat.reduceAdd, Fin.isValue, not_lt_zero', ↓reduceIte, zero_add]
      rw [if_neg]
      · have : a = 0 ∨ a = 1 := by
          rcases a with ⟨a, ha⟩
          simp_rw [Fin.ext_iff]
          simp_all only [List.simplexSort, Fin.val_zero, Fin.val_one]
          omega
        rcases this with (rfl | rfl)
        · rw [toListGen_well_def _ _ (δ_comp_σ_self' (by simp)) F (monoEquivOfFin _ sorry)]
          rw [toListGen_id]
        · have ffs : δ (1 : Fin 2) ≫ σ 0 = 𝟙 _ := δ_comp_σ_succ' _ _ (by simp)
          rw [toListGen_well_def _ _ ffs F (monoEquivOfFin _ sorry)]
          rw [toListGen_id]
      · rcases a with ⟨a, ha⟩
        simp only [not_lt]
        omega
    · rcases really f x hf with ⟨g, hb, hσ, hg⟩
      cases hσ
      split_ifs with hab h
      · dsimp
        have : δ a ≫ σ ⟨b, hb⟩ ≫ g = σ (Fin.mk (b - 1) sorry) ≫ δ ⟨a, sorry⟩ ≫ g := by
          simp only [← Category.assoc]
          rw [← δ_comp_σ_of_le]
          simp only [Fin.castSucc_mk, Fin.eta, Fin.succ_mk, Nat.succ_eq_add_one]
          congr
          omega
          · simp only [Fin.castSucc_mk, Fin.mk_le_mk]
            omega
        rw [toListGen_well_def (k := k) _ _ this F (monoEquivOfFin _ sorry)]
        erw [toListGen_σ_comp (monoEquivOfFin _ sorry) (monoEquivOfFin _ sorry)]
        have : (b :: l).Sorted (· ≤ ·) := by rw [← x]; exact toList_sorted _
        simp_all only [List.sorted_cons]
        rw [hbl, one this.2, List.simplexInsert_of_forall_le]
        simp_rw [List.mem_map]
        rintro x ⟨y, hy, rfl⟩
        have h' := this.1 y hy
        omega
        · intro x hx
          exact lt_of_lt_of_le hab (this.1 x hx)
        · exact epi_of_epi (σ ⟨b, hb⟩) g
        · assumption
      · dsimp
        have : δ a ≫ σ ⟨b, hb⟩ ≫ g = σ (Fin.mk b sorry) ≫ δ ⟨a - 1, sorry⟩ ≫ g := by
          simp only [← Category.assoc]
          rw [← δ_comp_σ_of_gt]
          simp only [Category.assoc, Fin.succ_mk, Nat.succ_eq_add_one, Fin.castSucc_mk]
          congr
          · ext
            dsimp
            omega
          · simp only [Fin.castSucc_mk, Fin.mk_lt_mk]
            omega
        rw [toListGen_well_def (k := k) _ _ this F (monoEquivOfFin _ sorry)]
        erw [toListGen_σ_comp (monoEquivOfFin _ sorry) (monoEquivOfFin _ sorry)]
        rw [hbl, List.simplexInsert_of_forall_le]
        · apply three
          · dsimp
            rw [← x]
            exact toList_sorted _
          · exact h
        · exact epi_of_epi (σ ⟨b, hb⟩) g
        · assumption
      · dsimp
        have : δ a ≫ σ ⟨b, hb⟩ ≫ g = g := by
          nth_rw 2 [← Category.id_comp g]
          simp only [← Category.assoc]
          have : (a : ℕ) = b ∨ (a : ℕ) = b + 1 := by
            omega
          rcases this with (rfl | h)
          · rw [δ_comp_σ_self']
            simp only [Fin.castSucc_mk, Fin.eta]
          · rw [δ_comp_σ_succ']
            ext
            simp_all only [add_lt_iff_neg_left, not_lt_zero', not_false_eq_true, lt_self_iff_false,
              Fin.succ_mk, Nat.succ_eq_add_one]
        rw [toListGen_well_def (k := k) _ _ this F (monoEquivOfFin _ sorry)]
        rw [← hg]
        exact toListGen_eq_of_epi g (epi_of_epi (σ ⟨b, hb⟩) g) (monoEquivOfFin _ sorry)

theorem simplexInsert_δ_2_subsingleton {a : ℕ} {l : List ℕ} :
    (simplexInsert_δ a l).2 = [] ∨ ∃ b, (simplexInsert_δ a l).2 = [b] := by
  induction' l with b l hbl generalizing a
  · simp_all only [simplexInsert_δ, List.cons_ne_self, List.cons.injEq, and_true, exists_eq',
    or_true]
  · sorry

theorem toListGen_comp_mono' {m n k : SimplexCategory} (f : m ⟶ n) (g : n ⟶ k) (hg : Mono g)
    {j : ℕ} (F : Fin j ≃o Im f) (G : Fin j ≃o Im (f ≫ g)) :
    toListGen _ G = toListGen _ F := by
  have : (yay f F).e ≫ ((yay f F).m ≫ g) = f ≫ g := by
    rw [← Category.assoc, (yay f F).fac]
  rw [← toListGen_well_def _ _ (yay f F).fac (monoEquivOfFin _ sorry) F]
  rw [← toListGen_well_def _ _ this (monoEquivOfFin _ sorry) G]
  rw [toListGen_comp_mono (F2 := monoEquivOfFin _ sorry)]
  rw [toListGen_comp_mono (F2 := monoEquivOfFin _ sorry)]
  · infer_instance
  · infer_instance
  · infer_instance
  · apply mono_comp


theorem swap_e {m n k : SimplexCategory} (f : m ⟶ n) (g : n ⟶ k) (hf : Mono f) (hg : Epi g)
    {j : ℕ} (F : Fin j ≃o Im (f ≫ g)) :
    toListGen _ F = (simplexSwap (monos.order2 f) (toList g)).1 := by
  induction' x : (monos.order2 f).reverse with b l hbl generalizing n f k
  · have : m = n := sorry
    cases this
    have : f = 𝟙 m := sorry
    cases this
    have : j = k.len + 1 := sorry
    cases this
    rw [List.reverse_eq_nil_iff] at x
    rw [toListGen_eq_of_epi _ (epi_comp _ _) F]
    simp_all only [monos.order2_id, Category.id_comp, simplexSwap, List.reverse_nil, simplexSwapAux,
      toList_simplexSort]
  · have : monos.order2 f = l.reverse ++ [b] := by
      apply_fun List.reverse
      simp_all only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.reverse_reverse, List.singleton_append]
      exact List.reverse_injective
    rw [this]
    simp only [simplexSwap, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.reverse_reverse, List.singleton_append, simplexSwapAux]
    induction' n using SimplexCategory.rec with n
    cases' n with n
    · simp_all only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.reverse_reverse, List.singleton_append]
      have : m = mk 0 := sorry
      cases this
      have : f = 𝟙 _ := sorry
      cases this
      exfalso
      simp_all only [monos.order2, monos.rangeCompl, len_mk, id_toOrderHom, OrderHom.id_coe,
        Finset.image_id, Finset.compl_univ, Finset.image_empty, Finset.sort_empty,
        List.nil_eq_append, List.reverse_eq_nil_iff, List.cons_ne_self, and_false]
    · induction' k using SimplexCategory.rec with k
      cases' k with k
      · simp_all only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.reverse_reverse, List.singleton_append]
        sorry -- come back to
      rcases mono_really f this hf with ⟨α, hb, hαb, hl⟩
      have hmm := toListGen_δ_comp_epi (k := n) (a := ⟨b, hb⟩) g (monoEquivOfFin _ sorry) hg

/-
theorem swap_e_insert {a : ℕ} {Le : List ℕ} {m k j : ℕ}
    (hLm : (monos.toArrowAux monos.simplexThingy [a] m).isSome)
    (hLe : (toArrowAux simplexThingy Le k).isSome)
    (h : m + 1 = k)
    (F : Fin j ≃o Im ((monos.toArrow [a] m hLm).hom ≫ eqToHom (by simp [h, monos.toArrow_right,
      toArrow_left, simplexThingy, monos.simplexThingy]) ≫ (toArrow Le k hLe).hom)) :
    toListGen _ F = (simplexInsert_δ a Le).1.simplexSort := by
  induction' Le with b l hbl generalizing k m
  · rw [toListGen_mono]
    simp only [List.simplexSort]
    · apply mono_comp'
      · exact monos.toArrow_mono _ _ (by simp) _ fun i => by dsimp [monos.simplexThingy]; infer_instance
      · simp only [Functor.id_obj, toArrow, toArrowAux, Option.get_some, Category.comp_id]
        infer_instance
  · induction' k with k hk
    · exfalso
      simp only [toArrowAux, Option.isSome_none, Bool.false_eq_true] at hLe
    · simp only [Functor.id_obj, simplexInsert_δ]
      split_ifs with hab hba
      · simp only [Functor.id_obj, List.simplexSort]
        specialize hbl (m := m - 1) (k := k) sorry (toArrowAux_some_cons _ _ _ hLe) sorry (monoEquivOfFin _ sorry)
        rw [← hbl]
      · sorry
      · sorry
-/
theorem swap_e {Lm Le : List ℕ} {m k j : ℕ}
    (hLm : (monos.toArrowAux monos.simplexThingy Lm m).isSome)
    (hLe : (toArrowAux simplexThingy Le k).isSome)
    (h : (monos.toArrow Lm m hLm).right = (toArrow Le k hLe).left)
    (F : Fin j ≃o Im ((monos.toArrow Lm m hLm).hom ≫ eqToHom h ≫ (toArrow Le k hLe).hom)) :
    toListGen _ F = (simplexSwap Lm Le).1.simplexSort := sorry

theorem swap_m_insert {a : ℕ} {Le : List ℕ} {m k j : ℕ}
    (hLm : (monos.toArrowAux monos.simplexThingy [a] m).isSome)
    (hLe : (toArrowAux simplexThingy Le k).isSome)
    (h : (monos.toArrow [a] m hLm).right = (toArrow Le k hLe).left)
    (F : Fin j ≃o Im ((monos.toArrow [a] m hLm).hom ≫ eqToHom h ≫ (toArrow Le k hLe).hom)) :
    monos.order2 ((monos.toArrow [a] m hLm).hom ≫ eqToHom h ≫ (toArrow Le k hLe).hom)
      = (simplexInsert_δ a Le).2.simplexMonoSort := by sorry

theorem swap_m {Lm Le : List ℕ} {m k j : ℕ}
    (hLm : (monos.toArrowAux monos.simplexThingy Lm m).isSome)
    (hLe : (toArrowAux simplexThingy Le k).isSome)
    (h : (monos.toArrow Lm m hLm).right = (toArrow Le k hLe).left)
    (F : Fin j ≃o Im ((monos.toArrow Lm m hLm).hom ≫ eqToHom h ≫ (toArrow Le k hLe).hom)) :
    monos.order2 ((monos.toArrow Lm m hLm).hom ≫ eqToHom h ≫ (toArrow Le k hLe).hom)
      = (simplexSwap Lm Le).2.simplexMonoSort := by sorry

theorem swap_e_isSome {M : thingys} {Lm Le : List ℕ} {m k : ℕ}
    (hLm : (monos.toArrowAux M.tomonothingy Lm m).isSome)
    (hLe : (toArrowAux M.tothingy Le k).isSome) :
    (toArrowAux M.tothingy (simplexSwap Lm Le).1 m).isSome := sorry

theorem monos.isSome_iff {l : List ℕ} {m : ℕ} (M : monos.thingy) :
    (monos.toArrowAux monos.simplexThingy l m).isSome
    ↔ (monos.toArrowAux M l m).isSome := by
  induction' l with a l hal generalizing m
  · simp_all only [monos.toArrowAux, Functor.id_obj, Option.isSome_some]
  · constructor
    · intro h
      apply monos.toArrowAux_some_cons'
      · exact (monos.toArrowAux_some_cond' h).1
      · exact hal.1 (monos.toArrowAux_some_cons _ _ _ h)
    · intro h
      apply monos.toArrowAux_some_cons'
      · exact (monos.toArrowAux_some_cond' h).1
      · exact hal.2 (monos.toArrowAux_some_cons _ _ _ h)

theorem isSome_iff {l : List ℕ} {m : ℕ} (M : thingy) :
    (toArrowAux simplexThingy l m).isSome
    ↔ (toArrowAux M l m).isSome := by
  induction' l with a l hal generalizing m
  · simp_all only [toArrowAux, Functor.id_obj, Option.isSome_some]
  · induction' m with m hm
    · simp_all only [Bool.coe_iff_coe]
      simp_all only [toArrowAux, Option.isSome_none]
    constructor
    · intro h
      apply toArrowAux_some_cons'
      · exact (toArrowAux_some_cond' h).1
      · exact hal.1 (toArrowAux_some_cons _ _ _ h)
    · intro h
      apply toArrowAux_some_cons'
      · exact (toArrowAux_some_cond' h).1
      · exact hal.2 (toArrowAux_some_cons _ _ _ h)

theorem swap_m_isSome {M : thingys} {Lm Le : List ℕ} {m k j : ℕ}
    (hLm : (monos.toArrowAux M.tomonothingy Lm m).isSome)
    (hLe : (toArrowAux M.tothingy Le k).isSome)
    (h : (monos.toArrow Lm m hLm).right = (toArrow Le k hLe).left)
    (F : Fin j ≃o Im ((monos.toArrow Lm m hLm).hom ≫ eqToHom h ≫ (toArrow Le k hLe).hom)) :
    (monos.toArrowAux M.tomonothingy (simplexSwap Lm Le).2 j).isSome := sorry

theorem ToHom_id (M : thingys) {m : SimplexCategory} (F : Fin (m.len + 1) ≃o Im (𝟙 m)) :
    ToHom (M := M) (𝟙 m) F = 𝟙 (M.obj m.len) := by
  apply_fun Arrow.mk
  simp only [ToHom, MAP1, MAP2, Category.assoc]
  simp only [Arrow.ugh_left]
  simp only [← Category.assoc, Arrow.ugh_right]
  simp only [Nat.add_one_sub_one, Functor.id_obj, Category.assoc, eqToHom_trans]
  have := monos.toHom_id (M := M.tomonothingy) (m := m)
  simp only [monos.toHom, Functor.id_obj] at this
  simp only [← eqToIso.hom] at this
  rw [← Iso.eq_inv_comp, ← Iso.eq_comp_inv] at this
  rw [this]
  simp only [eqToIso.inv, Category.comp_id, eqToHom_trans]
  rw [Arrow.ugh_right]
  simp only [Arrow.mk_eq, toListGen_id, toArrow_nil]
  · exact Arrow.mk_injective (M.obj m.len) (M.obj m.len)

theorem ToHom_comp {M : thingys} {m n o : SimplexCategory} (f : m ⟶ n) (g : n ⟶ o)
    {i j k : ℕ} (Ffg : Fin i ≃o Im (f ≫ g)) (Ff : Fin j ≃o Im f) (Fg : Fin k ≃o Im g) :
    ToHom M (f ≫ g) Ffg = ToHom M f Ff ≫ ToHom M g Fg := by
 -- apply_fun Arrow.mk
  unfold ToHom
  simp only [toHom, Functor.id_obj, Arrow.ugh, Arrow.mk_eq, Category.assoc, eqToHom_trans_assoc]
  rw [toArrow_comp hf hg]
  refine Arrow.ext _ _ ?_ ?_ ?_
  · simp only [Functor.id_obj, Arrow.mk_left, toArrow_left, mk_len]
  · simp only [Functor.id_obj, Arrow.mk_right, toArrow_right, toList_length', mk_len]
  · simp only [Functor.id_obj, mk_len, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  · apply Arrow.mk_injective _ _
