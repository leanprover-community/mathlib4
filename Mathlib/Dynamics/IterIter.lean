import Mathlib.Topology.Separation

open Set Function Filter
open scoped Topology

section NoTopology

variable {α : Type _} {f g : α → α}

def iterIter (f g : α → α) (n : ℕ) : α → α := f^[n] ∘ g^[n]

theorem iterIter_succ_apply (f g : α → α) (n : ℕ) (x : α) :
    iterIter f g (n + 1) x = f (iterIter f g n (g x)) := by
  simp only [iterIter, comp_apply]
  rw [← Nat.succ_eq_add_one, iterate_succ_apply', iterate_succ_apply]

theorem Function.LeftInverse.iterIter_apply (hf : LeftInverse f g) (n : ℕ) (x : α) :
    iterIter f g n x = x :=
  hf.iterate n x

theorem Function.LeftInverse.iterIter_eq (hf : LeftInverse f g) (n : ℕ) : iterIter f g n = id :=
  funext <| hf.iterIter_apply n

end NoTopology

section CommGroup

variable {G : Type _} [CommGroup G] 

theorem iterIter_mul_left_succ_div (a : G) (g : G → G) (n : ℕ) (x : G) :
    iterIter (a * ·) g (n + 1) x / iterIter (a * ·) g n x = a * g (g^[n] x) / (g^[n] x) := by
  simp only [iterIter, comp_apply, mul_left_iterate, iterate_succ_apply', pow_succ', mul_assoc,
    mul_div_mul_left_eq_div]

end CommGroup

section TopologicalSpace

variable {X : Type _} [TopologicalSpace X] [T2Space X] {f g h : X → X} {x a b : X}
  {s : Set X}

theorem apply_eq_of_tendsto_iterIter (ha : Tendsto (iterIter f g · x) atTop (𝓝 a))
    (hb : Tendsto (iterIter f g · (g x)) atTop (𝓝 b)) (hf : ContinuousAt f b) :
    f b = a := by
  refine tendsto_nhds_unique (hf.tendsto.comp hb) ?_
  simp only [(· ∘ ·), ← iterIter_succ_apply]
  exact ha.comp (tendsto_add_atTop_nat 1)

theorem comp_eqOn_of_tendsto_iterIter (hmapsTo : MapsTo g s s) (hcont : Continuous f)
    (htendsto : ∀ x ∈ s, Tendsto (iterIter f g · x) atTop (𝓝 (h x))) :
    EqOn (f ∘ h ∘ g) h s := fun x hx ↦
  apply_eq_of_tendsto_iterIter (f := f) (g := g) (htendsto x hx) (htendsto (g x) (hmapsTo hx))
    hcont.continuousAt

theorem comp_eqOn_comp_of_tendsto_iterIter (hmapsTo : MapsTo g s s) (hcont : Continuous f)
    (hf' : LeftInverse f' f) (htendsto : ∀ x ∈ s, Tendsto (iterIter f g · x) atTop (𝓝 (h x))) :
    EqOn (h ∘ g) (f' ∘ h) s := fun x hx ↦ by
  simp only [comp_apply, ← comp_eqOn_of_tendsto_iterIter hmapsTo hcont htendsto hx, hf' _]

theorem Function.Semiconj.of_tendsto_iterIter (hcont : Continuous f) (hf' : LeftInverse f' f)
    (htendsto : ∀ x, Tendsto (iterIter f g · x) atTop (𝓝 (h x))) :
    Semiconj h g f' := fun _ ↦
  comp_eqOn_comp_of_tendsto_iterIter (mapsTo_univ _ _) hcont hf' (fun x _ ↦ htendsto x) trivial

end TopologicalSpace
