import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Data.Countable.Defs

open CategoryTheory Limits Opposite

variable {C : Type*} [Category C] (J : Type*) [Countable J]

namespace CountableLimits

attribute [local instance] IsCofiltered.nonempty

section Category

variable [Category J] [IsCofiltered J]

noncomputable
def obj : ℕ → J := fun
  | .zero => (exists_surjective_nat _).choose 0
  | .succ n => (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
      (obj n)).choose

noncomputable
def map_aux (n : ℕ) : obj J (n + 1) ⟶ obj J n :=
  (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose n)
    (obj J n)).choose_spec.choose_spec.choose

noncomputable
def map {n m : ℕ} (h : n ≤ m) : obj J m ⟶ obj J n :=
  Nat.leRecOn h (fun f ↦ map_aux J _ ≫ f) (𝟙 _)

theorem map_comp {n m : ℕ} (h : n ≤ m) {j : J} (φ : obj J n ⟶ j) :
    map J h ≫ φ = Nat.leRecOn h (fun f ↦ map_aux J _ ≫ f) φ := by
  induction h with
  | refl => simp [map, Nat.leRecOn_self, Nat.leRecOn_self]
  | step h ih => simp [map, Nat.leRecOn_succ h, Nat.leRecOn_succ h, ← ih]

noncomputable
def sequential : ℕᵒᵖ ⥤ J where
  obj n := obj J (unop n)
  map h := map J (leOfHom h.unop)
  map_id X := Nat.leRecOn_self _
  map_comp f g := by
    rw [map_comp]
    simp only [map]
    rw [Nat.leRecOn_trans (leOfHom (g.unop)) (leOfHom f.unop)]

theorem sequential_cofinal :
    ∀ d, ∃ (n : ℕ) (_ : obj J n ⟶ d), True := by
  intro d
  obtain ⟨m, h⟩ := (exists_surjective_nat _).choose_spec d
  refine ⟨m + 1, ?_⟩
  rw [← h]
  use (IsCofilteredOrEmpty.cone_objs ((exists_surjective_nat _).choose m)
      (obj J m)).choose_spec.choose

end Category

section Preorder

-- TODO: show that for every cofiltered category, there is an initial functor from a cofiltered
-- preorder and deduce the more general form of the instance below.

variable [Preorder J] [IsCofiltered J]

instance : (sequential J).Initial  where
  out d := by
    obtain ⟨n, (g : (sequential J).obj ⟨n⟩ ⟶ d), _⟩ := sequential_cofinal J d
    have hn : Nonempty (CostructuredArrow (sequential J) d) := ⟨CostructuredArrow.mk g⟩
    apply isConnected_of_zigzag
    intro i j
    refine ⟨[j], ?_⟩
    simp only [List.chain_cons, Zag, List.Chain.nil, and_true, ne_eq, not_false_eq_true,
      List.getLast_cons, not_true_eq_false, List.getLast_singleton']
    wlog h : (unop i.left) ≤ (unop j.left)
    · exact or_comm.1 (this (C := C) J d n g (by trivial) hn j i (le_of_lt (not_le.mp h)))
    · right
      exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

end Preorder

end CountableLimits
