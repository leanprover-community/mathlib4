import Mathlib.Data.Set.Lattice

theorem Set.iUnion_inter_iUnion {α ι ι' : Type _} (A : ι → Set α) (B : ι' → Set α) :
    (⋃ (i : ι) (j : ι'), A i ∩ B j) = (⋃ (i : ι), A i) ∩ (⋃ (j : ι'), B j) := by
  rw [Set.iUnion_inter]
  apply Set.iUnion_congr
  intro i
  rw [Set.inter_iUnion]

theorem Set.iUnion_equiv {α ι ι' : Type _} (f : ι → Set α) (g : Equiv ι' ι) :
    (⋃ i, (f ∘ g) i) = ⋃ i, f i := Equiv.iSup_congr g (congrFun rfl)

theorem Set.iUnion_prod_dom {α ι ι' : Type _} (f : ι × ι' → Set α) :
    (⋃ (x : ι × ι'), f x) = (⋃ (i : ι) (j : ι'), f (i, j)) := iSup_prod (f := f)
