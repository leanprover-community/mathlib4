/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.FiberBundle.Basic

set_option linter.style.longLine false
set_option linter.style.cdot false

open Function Set

def x := (!₂[1, 0]  : EuclideanSpace ℝ (Fin 2))

theorem h : x ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  have h1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
   exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h5 : (x 0)^2 + (x 1)^2 = 1 := by
    calc
     (x 0)^2 + (x 1)^2 = 1^2 + 0^2 := rfl
     _ = 1 := by simp
  have h6 : x ∈  {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by simp [h5]
  have h7 : x ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
   rw [h1]
   exact h6
  exact h7

def u := (!₂[-1, 0] : EuclideanSpace ℝ (Fin 2))

theorem g : u ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  have h1 : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 = {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
   exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
  have h5 : (u 0)^2 + (u 1)^2 = 1 := by
    calc
     (u 0)^2 + (u 1)^2 = (-1)^2 + 0^2 := rfl
     _ = 1 := by simp
  have h6 : u ∈  {x | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2} := by
    simp [h5]
  have h7 : u ∈  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
   rw [h1]
   exact h6
  exact h7

def xh := ((⟨x, h⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ))
def ug := ((⟨u, g⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ))

noncomputable
def V := chartAt (EuclideanSpace ℝ (Fin 1)) (⟨u, g⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))
noncomputable
def U := chartAt (EuclideanSpace ℝ (Fin 1)) (⟨x, h⟩ : ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)))

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
  ⟨(finrank_euclideanSpace_fin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)⟩

lemma h8 : U.source = { x | x ≠ -xh} := by
    calc U.source = (chartAt (EuclideanSpace ℝ (Fin 1)) xh).source := rfl
         _ = (stereographic' 1 (-xh)).source := rfl
         _ = {-xh}ᶜ := stereographic'_source (-xh)
         _ = { x | x ≠ -xh } := rfl

lemma h9 : V.source = { x | x ≠ -ug} := by
    calc V.source = (chartAt (EuclideanSpace ℝ (Fin 1)) ug).source := rfl
         _ = (stereographic' 1 (-ug)).source := rfl
         _ = {-ug}ᶜ := stereographic'_source (-ug)
         _ = { x | x ≠ -ug } := rfl

noncomputable
def MyCoordChange : Fin 2 → Fin 2 → (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
      | 0, 0, _, α => α
      | 0, 1, x, α => if (x.val 1) > 0 then α else -α
      | 1, 0, x, α => if (x.val 1) > 0 then α else -α
      | 1, 1, _, α => α

theorem MyCoordChange_self : ∀ (i : Fin 2),
    ∀ x ∈ (fun i => if i = 0 then U.source else V.source) i,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange i i x v = v := by
    intro i x h v
    have h : MyCoordChange i i x v = v :=
      match i with
        | 0 => rfl
        | 1 => rfl
    exact h

noncomputable
def f : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
   | x, α => if (x.val 1) > 0 then α else -α

lemma l (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (v : EuclideanSpace ℝ (Fin 1)) : f x (f x v) = v := by
    by_cases h : x.val 1 > 0
    case pos =>
      simp [f, h]
    case neg =>
      simp [f, h]

theorem t1001 (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (v : EuclideanSpace ℝ (Fin 1)) :
 MyCoordChange 1 0 x (MyCoordChange 0 1 x v) = v := by
  have h3 : ∀ v, f x v = MyCoordChange 0 1 x v := by
   intro h
   rfl
  have h4 : ∀ v, f x v = MyCoordChange 1 0 x v := by
    intro h
    rfl
  have h8 : f x (f x v) = MyCoordChange 1 0 x (MyCoordChange 0 1 x v) := by rw [h3 v, h4]
  have h9 : MyCoordChange 1 0 x (MyCoordChange 0 1 x v) = v := by rw [<-h8, l]
  exact h9

theorem t0110 (x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) (v : EuclideanSpace ℝ (Fin 1)) :
 MyCoordChange 0 1 x (MyCoordChange 1 0 x v) = v := by
  have h3 : ∀ v, f x v = MyCoordChange 0 1 x v := by
   intro h
   rfl
  have h4 : ∀ v, f x v = MyCoordChange 1 0 x v := by
    intro h
    rfl
  have h8 : f x (f x v) = MyCoordChange 1 0 x (MyCoordChange 0 1 x v) := by rw [h3 v, h4]
  have h9 : MyCoordChange 1 0 x (MyCoordChange 0 1 x v) = v := by rw [<-h8, l]
  exact h9

theorem MyCoordChange_comp : ∀ (i j k : Fin 2),
  ∀ x ∈ (fun i => if i = 0 then U.source else V.source) i ∩
        (fun i => if i = 0 then U.source else V.source) j ∩
        (fun i => if i = 0 then U.source else V.source) k,
    ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange j k x (MyCoordChange i j x v) = MyCoordChange i k x v := by
    intro i j k x h v
    have h : MyCoordChange j k x (MyCoordChange i j x v) = MyCoordChange i k x v :=
      match i, j, k with
        | 0, 0, 0 => rfl
        | 0, 0, 1 => rfl
        | 0, 1, 0 => t1001 x v
        | 0, 1, 1 => rfl
        | 1, 0, 0 => rfl
        | 1, 0, 1 => t0110 x v
        | 1, 1, 0 => rfl
        | 1, 1, 1 => rfl
    exact h

theorem tOpen : IsOpen { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 > 0 } := by
  let V := { x : EuclideanSpace ℝ (Fin 2) | x 1 > 0 }
  have h1 : Continuous (fun (x: EuclideanSpace ℝ (Fin 2)) ↦ (0 : (fun x => ℝ) 1)) := continuous_const
  have h2 :  ∀ (i : Fin 2), Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x i := continuous_apply
  have h3 : Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x 1 := h2 1
  have h4 : IsOpen V := isOpen_lt h1 h3
  let U := { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 }
  exact isOpen_induced_iff.mpr ⟨V, h4, rfl⟩

theorem tOpen' : IsOpen { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 < 0 } := by
  let V := { x : EuclideanSpace ℝ (Fin 2) | x 1 < 0 }
  have h1 : Continuous (fun (x: EuclideanSpace ℝ (Fin 2)) => (0 : (fun x => ℝ) 1)) := continuous_const
  have h2 :  ∀ (i : Fin 2), Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x i := continuous_apply
  have h3 : Continuous fun (x : EuclideanSpace ℝ (Fin 2)) => x 1 := h2 1
  have h4 : IsOpen V := isOpen_lt h3 h1
  let U := { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 < 0 }
  exact isOpen_induced_iff.mpr ⟨V, h4, rfl⟩

theorem t00 : ContinuousOn (fun p => MyCoordChange 0 0 p.1 p.2) (U.source ×ˢ univ) := by
  have h1 : (fun (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) =>
    MyCoordChange 0 0 p.fst p.snd) = (fun p => p.snd) := by rfl
  rw [h1]
  exact continuousOn_snd

lemma myNeg (a b : ℝ) : -!₂[a, b] = !₂[-a, -b] := by
  let x := ![a, b]
  let y := ![-a, -b]
  have fleeg : -(![a, b]) = ![-a, -b] := by simp
  have flarg : -x = y := by rw [fleeg]
  have flurg : (WithLp.equiv 2 (Fin 2 → ℝ)) (-x) = -(WithLp.equiv 2 (Fin 2 → ℝ)) x := WithLp.equiv_neg 2 x
  have florg : (WithLp.equiv 2 (Fin 2 → ℝ)) y = -(WithLp.equiv 2 (Fin 2 → ℝ)) x := by rw [flarg] at flurg; exact flurg
  have flarq : !₂[-a, -b] = -!₂[a, b] := by exact florg
  exact flarq.symm

theorem SulSource : U.source ∩ V.source = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := by
  let xh := ((⟨x, h⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ))
  let ug := ((⟨u, g⟩ :  Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ))
  ext y

  have h8 : U.source = { x | x ≠ -xh} := h8
  have h9 : V.source = { x | x ≠ -ug} := h9
  have ha : U.source ∩ V.source = { x | x ≠ -xh } ∩ { x | x ≠ -ug } := by rw [h8, h9]

  have h1 : { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } = { x | x.val 1 = 0 }ᶜ := by
    ext y
    simp
    exact not_congr eq_comm

  have h2 : { x | x ≠ -xh } ∩ { x | x ≠ -ug } = { -xh, -ug }ᶜ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact not_or.symm

  have h3 : { x | x.val 1 = 0 } = { -xh, -ug } := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    let A := Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
    let B := { x : EuclideanSpace ℝ (Fin 2) | ∑ i : Fin 2, x i ^ 2 = 1 ^ 2}
    have h31a : A = B := by
      exact EuclideanSpace.sphere_zero_eq 1 (le_of_lt Real.zero_lt_one)
    have h3aa : y.val ∈ A := y.prop
    have h3ba : y.val ∈ B := by
      rw [h31a] at h3aa
      exact h3aa
    have h3ca : ∑ i : Fin 2, y.val i ^ 2 = 1 ^ 2 := by
      simp [Set.mem_setOf_eq] at h3ba
      exact h3ba
    have h3da : (y.val 0) ^ 2 + (y.val 1) ^ 2 = 1 := by
      rwa [Fin.sum_univ_two, one_pow] at h3ca

    have h3de : y.val 1 = 0 ↔ y.val 0 = 1 ∨ y.val 0 = -1 :=
      ⟨ fun h => by
        have ge : (y.val 0) ^ 2 + (y.val 1) ^ 2  = (y.val 0) ^ 2 + 0 ^ 2 := by rw [h]
        have gf : (y.val 0) ^ 2 + 0 ^ 2 = (y.val 0) ^ 2 := by rw [zero_pow two_ne_zero, add_zero]
        have gg : (y.val 0) ^ 2 = 1 ↔ y.val 0 = 1 ∨ y.val 0 = -1 := sq_eq_one_iff
        rw [ge, gf] at h3da
        rwa [gg] at h3da,

      fun h => by
        have : (y.val 0) ^ 2 + (y.val 1) ^ 2 = 1 := h3da
        cases h with
        | inl pos1 => rw [pos1, one_pow, ←sub_eq_zero, add_comm] at this
                      have h1 : (y.val 1 ^ 2 + 1) + (- 1) = 0 := this
                      have h2 : y.val 1 ^ 2 + (1 - 1) = (y.val 1 ^ 2 + 1) + (- 1) := by rw [add_assoc, sub_eq_add_neg]
                      have h3 : y.val 1 ^ 2 + (1 - 1) = y.val 1 ^ 2 := by rw [sub_self, add_zero]
                      have h4 : y.val 1 ^ 2 = 0 := by
                        calc y.val 1 ^ 2 = y.val 1 ^ 2 + (1 - 1) := by rw [h3]
                             _ = (y.val 1 ^ 2 + 1) + (- 1) := by rw [h2]
                             _ = 0 := by rw [h1]
                      exact sq_eq_zero_iff.mp h4
        | inr neg1 => rw [neg1, neg_one_sq, ←sub_eq_zero, add_comm] at this
                      have h1 : (y.val 1 ^ 2 + 1) + (- 1) = 0 := this
                      have h2 : y.val 1 ^ 2 + (1 - 1) = (y.val 1 ^ 2 + 1) + (- 1) := by rw [add_assoc, sub_eq_add_neg]
                      have h3 : y.val 1 ^ 2 + (1 - 1) = y.val 1 ^ 2 := by rw [sub_self, add_zero]
                      have h4 : y.val 1 ^ 2 = 0 := by
                        calc y.val 1 ^ 2 = y.val 1 ^ 2 + (1 - 1) := by rw [h3]
                             _ = (y.val 1 ^ 2 + 1) + (- 1) := by rw [h2]
                             _ = 0 := by rw [h1]
                      exact sq_eq_zero_iff.mp h4⟩

    have bar1 : xh.val = !₂[1, 0]  := rfl
    have bar2 : ug.val = !₂[-1, 0] := rfl
    have bar3 : -!₂[(1 : ℝ), 0] = !₂[-1, 0] := by rw [myNeg 1 0]; simp
    have bar4 : y.val 1 = 0 ↔ y.val 0 = 1 ∨ y.val 0 = -1 := h3de
    have bar5a : y.val 1 = 0 -> y.val = xh.val ∨ y.val = ug.val := by
      intro hy1
      have h1 : y.val 0 = 1 ∨ y.val 0 = -1 := bar4.mp hy1
      cases h1 with
      | inl hpos => have h3 : xh.val 0 = 1 := rfl
                    have h4 : xh.val 1 = 0 := rfl
                    have h5 : y.val = xh.val := by
                      ext i
                      fin_cases i
                      . simp [hpos, h3]
                      . simp [hy1, h4]
                    have h6 : y.val = xh.val ∨ y.val = ug.val := Or.inl h5
                    exact h6
      | inr hneg => have h3 : ug.val 0 = -1 := rfl
                    have h4 : ug.val 1 = 0 := rfl
                    have h5 : y.val = ug.val := by
                      ext i
                      fin_cases i
                      . simp [hneg, h3]
                      . simp [hy1, h4]
                    have h6 : y.val = xh.val ∨ y.val = ug.val := Or.inr h5
                    exact h6

    have bar5b : y.val = xh.val ∨ y.val = ug.val -> y.val 1 = 0 := by
      intro h
      cases h with
      | inl left => have h2 : y.val 1 = xh.val 1 := by rw [left]
                    have h3 : xh.val 1 = 0 :=rfl
                    have h4 : y.val 1 = 0 := by
                      calc y.val 1 = xh.val 1 := h2
                           _ = 0 := h3
                    exact h4
      | inr right => have h2 : y.val 1 = ug.val 1 := by rw [right]
                     have h3 : ug.val 1 = 0 :=rfl
                     have h4 : y.val 1 = 0 := by
                      calc y.val 1 = ug.val 1 := h2
                           _ = 0 := h3
                     exact h4

    have bar5 : y.val 1 = 0 <-> y.val = xh.val ∨ y.val = ug.val := ⟨bar5a, bar5b⟩
    have fooo1 : y.val = (xh).val -> y = xh := Subtype.eq
    have fooo2 : y.val = (ug).val -> y = ug := Subtype.eq
    have barr1 : y = xh -> y.val = (xh).val := by intro h; rw[h]
    have barr2 : y = ug -> y.val = (ug).val := by intro h; rw [h]
    have bar6 : -xh.val = ug.val := by rw [bar1, bar2]; exact bar3
    have bar7 : -xh = ug := Subtype.eq bar6
    have bar8 : xh = -ug := by rw [<-bar7]; simp
    have chat1 : y.val 1 = 0 ↔ y = xh ∨ y = ug := by
      rw [bar5]
      constructor
      · intro h
        cases h with
        | inl hxh => left; exact fooo1 hxh
        | inr hug => right; exact fooo2 hug
      · intro h
        cases h with
        | inl hxh => left; rw [← barr1 hxh]
        | inr hug => right; rw [← barr2 hug]

    have chat2 : y.val 1 = 0 ↔ y = -xh ∨ y = -ug := by
      rw [chat1]
      constructor
      · intro h
        have chit : y = -ug ∨ y = -xh := by cases h with
        | inl hxh => left; rw [bar8] at hxh; exact hxh
        | inr hug => right; rw [<-bar7] at hug; exact hug
        have chot :  y = -xh ∨ y = -ug := or_comm.mp chit
        exact chot
      · intro h
        cases h with
        | inl hxh_neg => right; rw [bar7] at hxh_neg; exact hxh_neg
        | inr hug_neg => left; rw [← bar7, neg_neg] at hug_neg; exact hug_neg

    exact chat2

  have hz : { x | x.val 1 = 0 }ᶜ = { -xh, -ug }ᶜ := by rw [h3]

  have hq : U.source ∩ V.source = { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := by
    calc U.source ∩ V.source = { x | x ≠ -xh } ∩ { x | x ≠ -ug } := ha
         _ = { -xh, -ug }ᶜ := h2
         _ = { x | x.val 1 = 0 }ᶜ := hz.symm
         _ =  { x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := h1.symm
  simp [hq]

lemma continuous_on_union_of_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X → Y) :
  ∀ (s t : Set X), IsOpen s → IsOpen t → ContinuousOn f s → ContinuousOn f t → ContinuousOn f (s ∪ t) := by
  intro s t hso hto hcs hct
  rw [continuousOn_open_iff (IsOpen.union hso hto)]
  intro u hu
  have h1 : ∀ u, IsOpen u → IsOpen (s ∩ f ⁻¹' u) := (continuousOn_open_iff hso).mp hcs
  have h2 : ∀ u, IsOpen u → IsOpen (t ∩ f ⁻¹' u) := (continuousOn_open_iff hto).mp hct
  rw [inter_comm, Set.inter_union_distrib_left, inter_comm]
  have h3 : IsOpen (f ⁻¹' u ∩ t) := by rw [Set.inter_comm]; exact h2 u hu
  exact IsOpen.union (h1 u hu) h3

def s1 : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 < x.1.val 1 }

lemma fooo : {(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 > 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) ⊆ { x | 0 < x.1.val 1 } := by
  intro x hx
  exact hx.1

lemma barr : { x | 0 < x.1.val 1 } ⊆ {(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 > 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) := by
  intro x hx
  exact ⟨hx, trivial⟩

lemma s1_is_open : IsOpen s1 := by
  have h1 : IsOpen { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 > 0 } := tOpen
  have h2 : IsOpen ({ x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 > 0 }×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := IsOpen.prod h1 isOpen_univ
  have h3 : ({(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 > 0} ×ˢ univ) = s1 := HasSubset.Subset.antisymm fooo barr
  rw [h3] at h2
  exact h2

def s2 : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 > x.1.val 1 }

lemma foo' : {(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 < 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) ⊆ { x | 0 > x.1.val 1 } := by
  intro x hx
  exact hx.1

lemma bar' : { x | 0 > x.1.val 1 } ⊆ {(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 < 0} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1))) := by
  intro x hx
  exact ⟨hx, trivial⟩

lemma s2_is_open : IsOpen s2 := by
  have h1 : IsOpen { x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 < 0 } := tOpen'
  have h2 : IsOpen ({ x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) | x.val 1 < 0 }×ˢ (univ : Set (EuclideanSpace ℝ (Fin 1)))) := IsOpen.prod h1 isOpen_univ
  have h3 : ({(x : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) | x.val 1 < 0} ×ˢ univ) = s2 := HasSubset.Subset.antisymm foo' bar'
  rw [h3] at h2
  exact h2

theorem t01 : ContinuousOn (fun p => MyCoordChange 0 1 p.1 p.2) ((U.source ∩ V.source) ×ˢ univ) := by
  have h1 : (U.source ∩ V.source) = { x | x.val 1 > 0 } ∪ { x | x.val 1 < 0 } := SulSource
  let f : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)
  | (x, α) =>if (x.val 1) > 0 then α else -α
  let s1 : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 < x.1.val 1 }
  let s2 : Set ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) := { x | 0 > x.1.val 1 }
  have h6 : (s1 ∪ s2) = (({x | x.val 1 > 0} ∪ {x | x.val 1 < 0}) ×ˢ univ) := by
    ext ⟨p, v⟩
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, Set.mem_setOf_eq]
    exact Iff.rfl

  have hz1 : ContinuousOn f s1 := by
    apply continuous_snd.continuousOn.congr
    intro x hx
    dsimp [f, s1] at hx ⊢
    rw [if_pos hx]

  have hz1' : ContinuousOn (fun p => MyCoordChange 0 1 p.1 p.2) s1 := by
    exact hz1

  have hz2 : ContinuousOn f s2 := by
    apply continuous_snd.neg.continuousOn.congr
    intro x hx
    dsimp [f, s2] at hx ⊢
    rw [if_neg (not_lt_of_gt hx)]

  have hz2' : ContinuousOn (fun p => MyCoordChange 0 1 p.1 p.2) s2 := by
    exact hz2

  have h5 : ContinuousOn (fun p => MyCoordChange 0 1 p.1 p.2) (s1 ∪ s2) := continuous_on_union_of_open (fun p => MyCoordChange 0 1 p.1 p.2) s1 s2 s1_is_open s2_is_open hz1' hz2'
  rw [h1]
  rw [h6] at h5
  exact h5

 theorem t10 : ContinuousOn (fun p => MyCoordChange 1 0 p.1 p.2) ((V.source ∩ U.source) ×ˢ univ) := by
  have h1 : MyCoordChange 1 0 = MyCoordChange 0 1 := rfl
  have h2 : (fun (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) => MyCoordChange 1 0 p.1 p.2) = (fun p => MyCoordChange 0 1 p.1 p.2) :=
    funext (fun x => by rw [h1])
  rw [h2, inter_comm]
  exact t01

theorem t11 : ContinuousOn (fun p => MyCoordChange 0 0 p.1 p.2) (V.source ×ˢ univ) := by
  have h1 : (fun (p : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) × EuclideanSpace ℝ (Fin 1)) =>
    MyCoordChange 0 0 p.fst p.snd) = (fun p => p.snd) := by rfl
  rw [h1]
  exact continuousOn_snd

theorem MyContinuousOn_coordChange : ∀ (i j : Fin 2), ContinuousOn (fun p => MyCoordChange i j p.1 p.2)
  (((fun i => if i = 0 then U.source else V.source) i ∩
      (fun i => if i = 0 then U.source else V.source) j) ×ˢ
    univ) := by
    intro i j
    fin_cases i
    · fin_cases j
      · simp; exact t00
      · exact t01
    · fin_cases j
      · exact t10
      · simp; exact t11

theorem my_mem_baseSet_at : ∀ (x : ↑(Metric.sphere 0 1)),
  x ∈ (fun (i : Fin 2) ↦ if i = 0 then U.source else V.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x):= by
  intro x
  by_cases h : (x.val 0) > 0
  case pos => have h5 : xh.val 0 = 1 := rfl
              have h7 : x ≠ -xh := by
                intro h_eq
                have h_val_eq : x.val = -xh.val := congrArg Subtype.val h_eq
                have h_contra : x.val 0 = -xh.val 0 := congrFun h_val_eq 0
                rw [h5] at h_contra
                linarith
              have h2 : (fun x ↦ if x.val 0 > 0 then (0 : Fin 2) else 1) x = 0 := if_pos h
              have h3 : (fun (i : Fin 2) ↦ if i = 0 then U.source else V.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x) =
                        U.source := by
                          rw [h2]
                          exact if_pos rfl
              have hz : x ∈ (fun (i : Fin 2) ↦ if i = 0 then U.source else V.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x) := by
                rw [h3]
                rw [h8]
                exact h7
              exact hz
  case neg => have h1 : ug.val 0 = -1 := rfl
              have h7 : x ≠ -ug := by
                intro h_eq
                have h_val_eq : x.val = -ug.val := congrArg Subtype.val h_eq
                have h_contra : x.val 0 = -ug.val 0 := congrFun h_val_eq 0
                rw [h1] at h_contra
                linarith
              have h2 : (fun x ↦ if x.val 0 > 0 then (0 : Fin 2) else 1) x = 1 := if_neg h
              have h3 : (fun (i : Fin 2) ↦ if i = 0 then U.source else V.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x) =
                        V.source := by
                          rw [h2]
                          exact if_neg (by exact one_ne_zero)
              have hz : x ∈ (fun (i : Fin 2) ↦ if i = 0 then U.source else V.source) ((fun x ↦ if x.val 0 > 0 then 0 else 1) x) := by
                rw [h3]
                rw [h9]
                exact h7
              exact hz

noncomputable
def Mobius : FiberBundleCore (Fin 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) :=
{
  baseSet := fun i => if i = 0 then U.source
                             else V.source,

  isOpen_baseSet := by
    intro i
    dsimp only
    split
    · exact U.open_source
    · exact V.open_source

  indexAt := fun x => if (x.val 0) > 0 then 0 else 1,

  mem_baseSet_at := my_mem_baseSet_at,

  coordChange := MyCoordChange,

  coordChange_self := MyCoordChange_self,

  continuousOn_coordChange := by
    intro i j
    exact MyContinuousOn_coordChange i j

  coordChange_comp := MyCoordChange_comp
}
