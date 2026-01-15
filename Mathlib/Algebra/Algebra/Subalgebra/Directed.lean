/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.Set.UnionLift

/-!
# Subalgebras and directed Unions of sets

## Main results

* `Subalgebra.coe_iSup_of_directed`: a directed supremum consists of the union of the algebras
* `Subalgebra.iSupLift`: define an algebra homomorphism on a directed supremum of subalgebras by
  defining it on each subalgebra, and proving that it agrees on the intersection of subalgebras.
-/

@[expose] public section

namespace Subalgebra

open Algebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι → Subalgebra R A}

theorem coe_iSup_of_directed (dir : Directed (· ≤ ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A) :=
  let s : Subalgebra R A :=
    { __ := Subsemiring.copy _ _ (Subsemiring.coe_iSup_of_directed dir).symm
      algebraMap_mem' := fun _ ↦ Set.mem_iUnion.2
        ⟨Classical.arbitrary ι, Subalgebra.algebraMap_mem _ _⟩ }
  have : iSup K = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (K i : Set A)) i) (Set.iUnion_subset fun _ ↦ le_iSup K _)
  this.symm ▸ rfl

variable (K)

/-- Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalgebras. -/
noncomputable def iSupLift (dir : Directed (· ≤ ·) K) (f : ∀ i, K i →ₐ[R] B)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
    (T : Subalgebra R A) (hT : T ≤ iSup K) : ↥T →ₐ[R] B :=
  let hT' : (T : Set A) ⊆ ⋃ i, (K i : Set A) := by
    intro x hx
    have hx' : x ∈ (↑(iSup K) : Set A) := hT hx
    simpa [coe_iSup_of_directed (K := K) dir] using hx'
  let compat :
      ∀ (i j) (x : A) (hxi : x ∈ (K i : Set A)) (hxj : x ∈ (K j : Set A)),
        f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases dir i j with ⟨k, hik, hjk⟩
    rw [hf i k hik, hf j k hjk]
    rfl
  { toFun := Set.iUnionLift (fun i => ↑(K i)) (fun i x => f i x) compat
        (T : Set A) hT'
    map_one' := by apply Set.iUnionLift_const _ (fun _ => 1) <;> simp
    map_zero' := by apply Set.iUnionLift_const _ (fun _ => 0) <;> simp
    map_mul' := by
      intro x y
      rcases Set.mem_iUnion.1 (hT' x.prop) with ⟨i, hi⟩
      rcases Set.mem_iUnion.1 (hT' y.prop) with ⟨j, hj⟩
      rcases dir i j with ⟨k, hik, hjk⟩
      have hxk : (x : A) ∈ K k := hik hi
      have hyk : (y : A) ∈ K k := hjk hj
      have hxyk : ((x * y : T) : A) ∈ K k := by
        simpa using (K k).mul_mem hxk hyk
      have hx :
          Set.iUnionLift (fun i => (K i : Set A)) (fun i x => f i x) compat (T : Set A) hT' x =
            f k ⟨x, hxk⟩ :=
        Set.iUnionLift_of_mem (S := fun i => (K i : Set A)) (f := fun i x => f i x)
          (hf := compat) (T := (T : Set A)) (hT := hT') (x := x) (i := k) hxk
      have hy :
          Set.iUnionLift (fun i => (K i : Set A)) (fun i x => f i x) compat (T : Set A) hT' y =
            f k ⟨y, hyk⟩ :=
        Set.iUnionLift_of_mem (S := fun i => (K i : Set A)) (f := fun i x => f i x)
          (hf := compat) (T := (T : Set A)) (hT := hT') (x := y) (i := k) hyk
      have hxy :
          Set.iUnionLift (fun i => (K i : Set A)) (fun i x => f i x) compat (T : Set A) hT'
              (x * y) =
            f k ⟨x * y, hxyk⟩ :=
        Set.iUnionLift_of_mem (S := fun i => (K i : Set A)) (f := fun i x => f i x)
          (hf := compat) (T := (T : Set A)) (hT := hT') (x := x * y) (i := k) hxyk
      rw [hx, hy, hxy]
      have hxyk' :
          (⟨(x * y : A), hxyk⟩ : K k) = (⟨x, hxk⟩ : K k) * ⟨y, hyk⟩ := by
        ext
        rfl
      have hmap :
          f k ⟨x * y, hxyk⟩ = f k ((⟨x, hxk⟩ : K k) * ⟨y, hyk⟩) :=
        congrArg (fun z => f k z) hxyk'
      exact hmap.trans ((f k).map_mul (⟨x, hxk⟩ : K k) ⟨y, hyk⟩)
    map_add' := by
      intro x y
      rcases Set.mem_iUnion.1 (hT' x.prop) with ⟨i, hi⟩
      rcases Set.mem_iUnion.1 (hT' y.prop) with ⟨j, hj⟩
      rcases dir i j with ⟨k, hik, hjk⟩
      have hxk : (x : A) ∈ K k := hik hi
      have hyk : (y : A) ∈ K k := hjk hj
      have hxyk : ((x + y : T) : A) ∈ K k := by
        simpa using (K k).add_mem hxk hyk
      have hx :
          Set.iUnionLift (fun i => (K i : Set A)) (fun i x => f i x) compat (T : Set A) hT' x =
            f k ⟨x, hxk⟩ :=
        Set.iUnionLift_of_mem (S := fun i => (K i : Set A)) (f := fun i x => f i x)
          (hf := compat) (T := (T : Set A)) (hT := hT') (x := x) (i := k) hxk
      have hy :
          Set.iUnionLift (fun i => (K i : Set A)) (fun i x => f i x) compat (T : Set A) hT' y =
            f k ⟨y, hyk⟩ :=
        Set.iUnionLift_of_mem (S := fun i => (K i : Set A)) (f := fun i x => f i x)
          (hf := compat) (T := (T : Set A)) (hT := hT') (x := y) (i := k) hyk
      have hxy :
          Set.iUnionLift (fun i => (K i : Set A)) (fun i x => f i x) compat (T : Set A) hT'
              (x + y) =
            f k ⟨x + y, hxyk⟩ :=
        Set.iUnionLift_of_mem (S := fun i => (K i : Set A)) (f := fun i x => f i x)
          (hf := compat) (T := (T : Set A)) (hT := hT') (x := x + y) (i := k) hxyk
      rw [hx, hy, hxy]
      have hxyk' :
          (⟨(x + y : A), hxyk⟩ : K k) = (⟨x, hxk⟩ : K k) + ⟨y, hyk⟩ := by
        ext
        rfl
      have hmap :
          f k ⟨x + y, hxyk⟩ = f k ((⟨x, hxk⟩ : K k) + ⟨y, hyk⟩) :=
        congrArg (fun z => f k z) hxyk'
      exact hmap.trans ((f k).map_add (⟨x, hxk⟩ : K k) ⟨y, hyk⟩)
    commutes' := fun r => by apply Set.iUnionLift_const _ (fun _ => algebraMap R _ r) <;> simp }


@[simp]
theorem iSupLift_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (inclusion h x) = f i x := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_inclusion]

@[simp]
theorem iSupLift_comp_inclusion {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (inclusion h) = f i := by ext; simp

@[simp]
theorem iSupLift_mk {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : K i) (hx : (x : A) ∈ T) :
    iSupLift K dir f hf T hT ⟨x, hx⟩ = f i x := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_mk]

theorem iSupLift_of_mem {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₐ[R] B}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
    {T : Subalgebra R A} {hT : T ≤ iSup K} {i : ι} (x : T) (hx : (x : A) ∈ K i) :
    iSupLift K dir f hf T hT x = f i ⟨x, hx⟩ := by
  dsimp [iSupLift, inclusion]
  rw [Set.iUnionLift_of_mem]

end Subalgebra
