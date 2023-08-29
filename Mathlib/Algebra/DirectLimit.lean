/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import Mathlib.Data.Finset.Order
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Quotient

#align_import algebra.direct_limit from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Direct limit of modules, abelian groups, rings, and fields.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups, or rings, or fields.

It is constructed as a quotient of the free module (for the module case) or quotient of
the free commutative ring (for the ring case) instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

## Main definitions

* `DirectedSystem f`
* `Module.DirectLimit G f`
* `AddCommGroup.DirectLimit G f`
* `Ring.DirectLimit G f`

-/


universe u v w u₁

open Submodule

variable {R : Type u} [Ring R]

variable {ι : Type v}

variable [dec_ι : DecidableEq ι] [Preorder ι]

variable (G : ι → Type w)

/-- A directed system is a functor from a category (directed poset) to another category. -/
class DirectedSystem (f : ∀ i j, i ≤ j → G i → G j) : Prop where
  map_self' : ∀ i x h, f i i h x = x
  map_map' : ∀ {i j k} (hij hjk x), f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x
#align directed_system DirectedSystem

section

variable {G} (f : ∀ i j, i ≤ j → G i → G j) [DirectedSystem G fun i j h => f i j h]
theorem DirectedSystem.map_self i x h : f i i h x = x :=
  DirectedSystem.map_self' i x h
theorem DirectedSystem.map_map {i j k} (hij hjk x) :
    f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x :=
  DirectedSystem.map_map' hij hjk x

end

namespace Module

variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]

variable {G} (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

/-- A copy of `DirectedSystem.map_self` specialized to linear maps, as otherwise the
`fun i j h ↦ f i j h` can confuse the simplifier. -/
nonrec theorem DirectedSystem.map_self [DirectedSystem G fun i j h => f i j h] (i x h) :
    f i i h x = x :=
  DirectedSystem.map_self (fun i j h => f i j h) i x h
#align module.directed_system.map_self Module.DirectedSystem.map_self

/-- A copy of `DirectedSystem.map_map` specialized to linear maps, as otherwise the
`fun i j h ↦ f i j h` can confuse the simplifier. -/
nonrec theorem DirectedSystem.map_map [DirectedSystem G fun i j h => f i j h] {i j k} (hij hjk x) :
    f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x :=
  DirectedSystem.map_map (fun i j h => f i j h) hij hjk x
#align module.directed_system.map_map Module.DirectedSystem.map_map

variable (G)

/-- The direct limit of a directed system is the modules glued together along the maps. -/
def DirectLimit : Type max v w :=
  DirectSum ι G ⧸
    (span R <|
      { a |
        ∃ (i j : _) (H : i ≤ j) (x : _),
          DirectSum.lof R ι G i x - DirectSum.lof R ι G j (f i j H x) = a })
#align module.direct_limit Module.DirectLimit

namespace DirectLimit

instance addCommGroup : AddCommGroup (DirectLimit G f) :=
  Quotient.addCommGroup _

instance module : Module R (DirectLimit G f) :=
  Quotient.module _

instance inhabited : Inhabited (DirectLimit G f) :=
  ⟨0⟩

variable (R ι)

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[R] DirectLimit G f :=
  (mkQ _).comp <| DirectSum.lof R ι G i
#align module.direct_limit.of Module.DirectLimit.of

variable {R ι G f}

@[simp]
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x :=
  Eq.symm <| (Submodule.Quotient.eq _).2 <| subset_span ⟨i, j, hij, x, rfl⟩
#align module.direct_limit.of_f Module.DirectLimit.of_f

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [Nonempty ι] [IsDirected ι (· ≤ ·)] (z : DirectLimit G f) :
    ∃ i x, of R ι G f i x = z :=
  Nonempty.elim (by infer_instance) fun ind : ι =>
                    -- 🎉 no goals
    Quotient.inductionOn' z fun z =>
      DirectSum.induction_on z ⟨ind, 0, LinearMap.map_zero _⟩ (fun i x => ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
          rw [LinearMap.map_add, of_f, of_f, ihx, ihy]
          -- ⊢ Quotient.mk'' p + Quotient.mk'' q = Quotient.mk'' (p + q)
          -- porting note: was `rfl`
          simp only [Submodule.Quotient.mk''_eq_mk, Quotient.mk_add]⟩
          -- 🎉 no goals
#align module.direct_limit.exists_of Module.DirectLimit.exists_of

@[elab_as_elim]
protected theorem induction_on [Nonempty ι] [IsDirected ι (· ≤ ·)] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of R ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x
#align module.direct_limit.induction_on Module.DirectLimit.induction_on

variable {P : Type u₁} [AddCommGroup P] [Module R P] (g : ∀ i, G i →ₗ[R] P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable (R ι G f)

/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f →ₗ[R] P :=
  liftQ _ (DirectSum.toModule R ι P g)
    (span_le.2 fun a ⟨i, j, hij, x, hx⟩ => by
      rw [← hx, SetLike.mem_coe, LinearMap.sub_mem_ker_iff, DirectSum.toModule_lof,
        DirectSum.toModule_lof, Hg])
#align module.direct_limit.lift Module.DirectLimit.lift

variable {R ι G f}

theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x :=
  DirectSum.toModule_lof R _ _
#align module.direct_limit.lift_of Module.DirectLimit.lift_of

theorem lift_unique [Nonempty ι] [IsDirected ι (· ≤ ·)] (F : DirectLimit G f →ₗ[R] P) (x) :
    F x =
      lift R ι G f (fun i => F.comp <| of R ι G f i)
        (fun i j hij x => by rw [LinearMap.comp_apply, of_f]; rfl) x :=
                             -- ⊢ ↑F (↑(of R ι G f i) x) = ↑((fun i => LinearMap.comp F (of R ι G f i)) i) x
                                                              -- 🎉 no goals
  DirectLimit.induction_on x fun i x => by rw [lift_of]; rfl
                                           -- ⊢ ↑F (↑(of R ι G f i) x) = ↑(LinearMap.comp F (of R ι G f i)) x
                                                         -- 🎉 no goals
#align module.direct_limit.lift_unique Module.DirectLimit.lift_unique

section Totalize

open Classical

variable (G f)

/-- `totalize G f i j` is a linear map from `G i` to `G j`, for *every* `i` and `j`.
If `i ≤ j`, then it is the map `f i j` that comes with the directed system `G`,
and otherwise it is the zero map. -/
noncomputable def totalize (i j) : G i →ₗ[R] G j :=
  if h : i ≤ j then f i j h else 0
#align module.direct_limit.totalize Module.DirectLimit.totalize

variable {G f}

theorem totalize_of_le {i j} (h : i ≤ j) : totalize G f i j = f i j h :=
  dif_pos h
#align module.direct_limit.totalize_of_le Module.DirectLimit.totalize_of_le

theorem totalize_of_not_le {i j} (h : ¬i ≤ j) : totalize G f i j = 0 :=
  dif_neg h
#align module.direct_limit.totalize_of_not_le Module.DirectLimit.totalize_of_not_le

end Totalize

variable [DirectedSystem G fun i j h => f i j h]

open Classical

theorem toModule_totalize_of_le {x : DirectSum ι G} {i j : ι} (hij : i ≤ j)
    (hx : ∀ k ∈ x.support, k ≤ i) :
    DirectSum.toModule R ι (G j) (fun k => totalize G f k j) x =
      f i j hij (DirectSum.toModule R ι (G i) (fun k => totalize G f k i) x) := by
  rw [← @DFinsupp.sum_single ι G _ _ _ x]
  -- ⊢ ↑(DirectSum.toModule R ι (G j) fun k => totalize G f k j) (DFinsupp.sum x DF …
  unfold DFinsupp.sum
  -- ⊢ ↑(DirectSum.toModule R ι (G j) fun k => totalize G f k j) (Finset.sum (DFins …
  simp only [LinearMap.map_sum]
  -- ⊢ (Finset.sum (DFinsupp.support x) fun x_1 => ↑(DirectSum.toModule R ι (G j) f …
  refine' Finset.sum_congr rfl fun k hk => _
  -- ⊢ ↑(DirectSum.toModule R ι (G j) fun k => totalize G f k j) (DFinsupp.single k …
  rw [DirectSum.single_eq_lof R k (x k), DirectSum.toModule_lof, DirectSum.toModule_lof,
    totalize_of_le (hx k hk), totalize_of_le (le_trans (hx k hk) hij), DirectedSystem.map_map]
#align module.direct_limit.to_module_totalize_of_le Module.DirectLimit.toModule_totalize_of_le

theorem of.zero_exact_aux [Nonempty ι] [IsDirected ι (· ≤ ·)] {x : DirectSum ι G}
    (H : (Submodule.Quotient.mk x : DirectLimit G f) = (0 : DirectLimit G f)) :
    ∃ j,
      (∀ k ∈ x.support, k ≤ j) ∧
        DirectSum.toModule R ι (G j) (fun i => totalize G f i j) x = (0 : G j) :=
  Nonempty.elim (by infer_instance) fun ind : ι =>
                    -- 🎉 no goals
    span_induction ((Quotient.mk_eq_zero _).1 H)
      (fun x ⟨i, j, hij, y, hxy⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, by
          subst hxy
          -- ⊢ (∀ (k_1 : ι), k_1 ∈ DFinsupp.support (↑(DirectSum.lof R ι G i) y - ↑(DirectS …
          constructor
          -- ⊢ ∀ (k_1 : ι), k_1 ∈ DFinsupp.support (↑(DirectSum.lof R ι G i) y - ↑(DirectSu …
          · intro i0 hi0
            -- ⊢ i0 ≤ k
            rw [DFinsupp.mem_support_iff, DirectSum.sub_apply, ← DirectSum.single_eq_lof, ←
              DirectSum.single_eq_lof, DFinsupp.single_apply, DFinsupp.single_apply] at hi0
            split_ifs at hi0 with hi hj hj
            · rwa [hi] at hik
              -- 🎉 no goals
            · rwa [hi] at hik
              -- 🎉 no goals
            · rwa [hj] at hjk
              -- 🎉 no goals
            exfalso
            -- ⊢ False
            apply hi0
            -- ⊢ 0 - 0 = 0
            rw [sub_zero]
            -- 🎉 no goals
          simp [LinearMap.map_sub, totalize_of_le, hik, hjk, DirectedSystem.map_map,
            DirectSum.apply_eq_component, DirectSum.component.of]⟩)
      ⟨ind, fun _ h => (Finset.not_mem_empty _ h).elim, LinearMap.map_zero _⟩
      (fun x y ⟨i, hi, hxi⟩ ⟨j, hj, hyj⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, fun l hl =>
          (Finset.mem_union.1 (DFinsupp.support_add hl)).elim (fun hl => le_trans (hi _ hl) hik)
            fun hl => le_trans (hj _ hl) hjk, by
          -- Porting note: this had been
          -- simp [LinearMap.map_add, hxi, hyj, toModule_totalize_of_le hik hi,
          --   toModule_totalize_of_le hjk hj]
          simp only [map_add]
          -- ⊢ ↑(DirectSum.toModule R ι (G k) fun i => totalize G f i k) x + ↑(DirectSum.to …
          rw [toModule_totalize_of_le hik hi, toModule_totalize_of_le hjk hj]
          -- ⊢ ↑(f i k hik) (↑(DirectSum.toModule R ι (G i) fun k => totalize (fun i => G i …
          simp [hxi, hyj]⟩)
          -- 🎉 no goals
      fun a x ⟨i, hi, hxi⟩ =>
      ⟨i, fun k hk => hi k (DirectSum.support_smul _ _ hk), by simp [LinearMap.map_smul, hxi]⟩
                                                               -- 🎉 no goals
#align module.direct_limit.of.zero_exact_aux Module.DirectLimit.of.zero_exact_aux

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact [IsDirected ι (· ≤ ·)] {i x} (H : of R ι G f i x = 0) :
    ∃ j hij, f i j hij x = (0 : G j) :=
  haveI : Nonempty ι := ⟨i⟩
  let ⟨j, hj, hxj⟩ := of.zero_exact_aux H
  if hx0 : x = 0 then ⟨i, le_rfl, by simp [hx0]⟩
                                     -- 🎉 no goals
  else
    have hij : i ≤ j := hj _ <| by simp [DirectSum.apply_eq_component, hx0]
                                   -- 🎉 no goals
    ⟨j, hij, by
      -- porting note: this had been
      -- simpa [totalize_of_le hij] using hxj
      simp only [DirectSum.toModule_lof] at hxj
      -- ⊢ ↑(f i j hij) x = 0
      rwa [totalize_of_le hij] at hxj⟩
      -- 🎉 no goals
#align module.direct_limit.of.zero_exact Module.DirectLimit.of.zero_exact

end DirectLimit

end Module

namespace AddCommGroup

variable [∀ i, AddCommGroup (G i)]

/-- The direct limit of a directed system is the abelian groups glued together along the maps. -/
def DirectLimit (f : ∀ i j, i ≤ j → G i →+ G j) : Type _ :=
  @Module.DirectLimit ℤ _ ι _ _ G _ _ fun i j hij => (f i j hij).toIntLinearMap
#align add_comm_group.direct_limit AddCommGroup.DirectLimit

namespace DirectLimit

variable (f : ∀ i j, i ≤ j → G i →+ G j)

protected theorem directedSystem [h : DirectedSystem G fun i j h => f i j h] :
    DirectedSystem G fun i j hij => (f i j hij).toIntLinearMap :=
  h
#align add_comm_group.direct_limit.directed_system AddCommGroup.DirectLimit.directedSystem

attribute [local instance] DirectLimit.directedSystem

instance : AddCommGroup (DirectLimit G f) :=
  Module.DirectLimit.addCommGroup G fun i j hij => (f i j hij).toIntLinearMap

instance : Inhabited (DirectLimit G f) :=
  ⟨0⟩

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[ℤ] DirectLimit G f :=
  Module.DirectLimit.of ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap) i
#align add_comm_group.direct_limit.of AddCommGroup.DirectLimit.of

variable {G f}

@[simp]
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Module.DirectLimit.of_f
#align add_comm_group.direct_limit.of_f AddCommGroup.DirectLimit.of_f

@[elab_as_elim]
protected theorem induction_on [Nonempty ι] [IsDirected ι (· ≤ ·)] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  Module.DirectLimit.induction_on z ih
#align add_comm_group.direct_limit.induction_on AddCommGroup.DirectLimit.induction_on

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact [IsDirected ι (· ≤ ·)] [DirectedSystem G fun i j h => f i j h] (i x)
    (h : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
  Module.DirectLimit.of.zero_exact h
#align add_comm_group.direct_limit.of.zero_exact AddCommGroup.DirectLimit.of.zero_exact

variable (P : Type u₁) [AddCommGroup P]

variable (g : ∀ i, G i →+ P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variable (G f)

/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f →ₗ[ℤ] P :=
  Module.DirectLimit.lift ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap)
    (fun i => (g i).toIntLinearMap) Hg
#align add_comm_group.direct_limit.lift AddCommGroup.DirectLimit.lift

variable {G f}

@[simp]
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  Module.DirectLimit.lift_of _ _ _
#align add_comm_group.direct_limit.lift_of AddCommGroup.DirectLimit.lift_of

theorem lift_unique [Nonempty ι] [IsDirected ι (· ≤ ·)] (F : DirectLimit G f →+ P) (x) :
    F x = lift G f P (fun i => F.comp (of G f i).toAddMonoidHom) (fun i j hij x => by simp) x :=
                                                                                      -- 🎉 no goals
  DirectLimit.induction_on x fun i x => by simp
                                           -- 🎉 no goals
#align add_comm_group.direct_limit.lift_unique AddCommGroup.DirectLimit.lift_unique

end DirectLimit

end AddCommGroup

namespace Ring

variable [∀ i, CommRing (G i)]

section

variable (f : ∀ i j, i ≤ j → G i → G j)

open FreeCommRing

/-- The direct limit of a directed system is the rings glued together along the maps. -/
def DirectLimit : Type max v w :=
  FreeCommRing (Σi, G i) ⧸
    Ideal.span
      { a |
        (∃ i j H x, of (⟨j, f i j H x⟩ : Σi, G i) - of ⟨i, x⟩ = a) ∨
          (∃ i, of (⟨i, 1⟩ : Σi, G i) - 1 = a) ∨
            (∃ i x y, of (⟨i, x + y⟩ : Σi, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
              ∃ i x y, of (⟨i, x * y⟩ : Σi, G i) - of ⟨i, x⟩ * of ⟨i, y⟩ = a }
#align ring.direct_limit Ring.DirectLimit

namespace DirectLimit

instance commRing : CommRing (DirectLimit G f) :=
  Ideal.Quotient.commRing _

instance ring : Ring (DirectLimit G f) :=
  CommRing.toRing

-- Porting note: Added a `Zero` instance to get rid of `0` errors.
instance zero : Zero (DirectLimit G f) := by
  unfold DirectLimit
  -- ⊢ Zero (FreeCommRing ((i : ι) × G i) ⧸ Ideal.span {a | (∃ i j H x, of { fst := …
  exact ⟨0⟩
  -- 🎉 no goals

instance : Inhabited (DirectLimit G f) :=
  ⟨0⟩

/-- The canonical map from a component to the direct limit. -/
nonrec def of (i) : G i →+* DirectLimit G f :=
  RingHom.mk'
    { toFun := fun x => Ideal.Quotient.mk _ (of (⟨i, x⟩ : Σi, G i))
      map_one' := Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inl ⟨i, rfl⟩
      map_mul' := fun x y =>
        Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inr ⟨i, x, y, rfl⟩ }
    fun x y => Ideal.Quotient.eq.2 <| subset_span <| Or.inr <| Or.inr <| Or.inl ⟨i, x, y, rfl⟩
#align ring.direct_limit.of Ring.DirectLimit.of

variable {G f}

-- porting note: the @[simp] attribute would trigger a `simpNF` linter error:
-- failed to synthesize CommMonoidWithZero (Ring.DirectLimit G f)
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Ideal.Quotient.eq.2 <| subset_span <| Or.inl ⟨i, j, hij, x, rfl⟩
#align ring.direct_limit.of_f Ring.DirectLimit.of_f

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [Nonempty ι] [IsDirected ι (· ≤ ·)] (z : DirectLimit G f) :
    ∃ i x, of G f i x = z :=
  Nonempty.elim (by infer_instance) fun ind : ι =>
                    -- 🎉 no goals
    Quotient.inductionOn' z fun x =>
      FreeAbelianGroup.induction_on x ⟨ind, 0, (of _ _ ind).map_zero⟩
        (fun s =>
          Multiset.induction_on s ⟨ind, 1, (of _ _ ind).map_one⟩ fun a s ih =>
            let ⟨i, x⟩ := a
            let ⟨j, y, hs⟩ := ih
            let ⟨k, hik, hjk⟩ := exists_ge_ge i j
            ⟨k, f i k hik x * f j k hjk y, by
              rw [(of G f k).map_mul, of_f, of_f, hs]
              -- ⊢ ↑(of G f i) x * Quotient.mk'' (FreeAbelianGroup.of s) = Quotient.mk'' (FreeA …
              /- porting note: In Lean3, from here, this was `by refl`. I have added
              the lemma `FreeCommRing.of_cons` to fix this proof. -/
              apply congr_arg Quotient.mk''
              -- ⊢ (fun x x_1 => x * x_1) (FreeCommRing.of { fst := i, snd := x }) (FreeAbelian …
              symm
              -- ⊢ FreeAbelianGroup.of ({ fst := i, snd := x } ::ₘ s) = (fun x x_1 => x * x_1)  …
              apply FreeCommRing.of_cons⟩)
              -- 🎉 no goals
        (fun s ⟨i, x, ih⟩ => ⟨i, -x, by
          -- porting note: Lean 3 was `of _ _ _`; Lean 4 is not as good at unification
          -- here as Lean 3 is, for some reason.
          rw [(of G f i).map_neg, ih]
          -- ⊢ -Quotient.mk'' (FreeAbelianGroup.of s) = Quotient.mk'' (-FreeAbelianGroup.of …
          rfl⟩)
          -- 🎉 no goals
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by rw [(of _ _ _).map_add, of_f, of_f, ihx, ihy]; rfl⟩
                                          -- ⊢ Quotient.mk'' p + Quotient.mk'' q = Quotient.mk'' (p + q)
                                                                                         -- 🎉 no goals
#align ring.direct_limit.exists_of Ring.DirectLimit.exists_of

section

open Classical

open Polynomial

variable {f' : ∀ i j, i ≤ j → G i →+* G j}

nonrec theorem Polynomial.exists_of [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (q : Polynomial (DirectLimit G fun i j h => f' i j h)) :
    ∃ i p, Polynomial.map (of G (fun i j h => f' i j h) i) p = q :=
  Polynomial.induction_on q
    (fun z =>
      let ⟨i, x, h⟩ := exists_of z
      ⟨i, C x, by rw [map_C, h]⟩)
                  -- 🎉 no goals
    (fun q₁ q₂ ⟨i₁, p₁, ih₁⟩ ⟨i₂, p₂, ih₂⟩ =>
      let ⟨i, h1, h2⟩ := exists_ge_ge i₁ i₂
      ⟨i, p₁.map (f' i₁ i h1) + p₂.map (f' i₂ i h2), by
        rw [Polynomial.map_add, map_map, map_map, ← ih₁, ← ih₂]
        -- ⊢ Polynomial.map (RingHom.comp (of G (fun i j h => ↑(f' i j h)) i) (f' i₁ i h1 …
        congr 2 <;> ext x <;> simp_rw [RingHom.comp_apply, of_f]⟩)
        -- ⊢ RingHom.comp (of G (fun i j h => ↑(f' i j h)) i) (f' i₁ i h1) = of G (fun i  …
                    -- ⊢ ↑(RingHom.comp (of G (fun i j h => ↑(f' i j h)) i) (f' i₁ i h1)) x = ↑(of G  …
                    -- ⊢ ↑(RingHom.comp (of G (fun i j h => ↑(f' i j h)) i) (f' i₂ i h2)) x = ↑(of G  …
                              -- 🎉 no goals
                              -- 🎉 no goals
    fun n z _ =>
    let ⟨i, x, h⟩ := exists_of z
    ⟨i, C x * X ^ (n + 1), by rw [Polynomial.map_mul, map_C, h, Polynomial.map_pow, map_X]⟩
                              -- 🎉 no goals
#align ring.direct_limit.polynomial.exists_of Ring.DirectLimit.Polynomial.exists_of

end

@[elab_as_elim]
theorem induction_on [Nonempty ι] [IsDirected ι (· ≤ ·)] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  let ⟨i, x, hx⟩ := exists_of z
  hx ▸ ih i x
#align ring.direct_limit.induction_on Ring.DirectLimit.induction_on

section OfZeroExact

open Classical

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

variable [DirectedSystem G fun i j h => f' i j h]

variable (G f)

theorem of.zero_exact_aux2 {x : FreeCommRing (Σi, G i)} {s t} (hxs : IsSupported x s) {j k}
    (hj : ∀ z : Σi, G i, z ∈ s → z.1 ≤ j) (hk : ∀ z : Σi, G i, z ∈ t → z.1 ≤ k) (hjk : j ≤ k)
    (hst : s ⊆ t) :
    f' j k hjk (lift (fun ix : s => f' ix.1.1 j (hj ix ix.2) ix.1.2) (restriction s x)) =
      lift (fun ix : t => f' ix.1.1 k (hk ix ix.2) ix.1.2) (restriction t x) := by
  refine' Subring.InClosure.recOn hxs _ _ _ _
  · rw [(restriction _).map_one, (FreeCommRing.lift _).map_one, (f' j k hjk).map_one,
      (restriction _).map_one, (FreeCommRing.lift _).map_one]
  · -- porting note: Lean 3 had `(FreeCommRing.lift _).map_neg` but I needed to replace it with
  -- `RingHom.map_neg` to get the rewrite to compile
    rw [(restriction _).map_neg, (restriction _).map_one, RingHom.map_neg,
      (FreeCommRing.lift _).map_one, (f' j k hjk).map_neg, (f' j k hjk).map_one,
      -- porting note: similarly here I give strictly less information
      (restriction _).map_neg, (restriction _).map_one, RingHom.map_neg,
      (FreeCommRing.lift _).map_one]
  · rintro _ ⟨p, hps, rfl⟩ n ih
    -- ⊢ ↑(f' j k hjk) (↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑ix).fst ≤ j)) (↑ix) …
    rw [(restriction _).map_mul, (FreeCommRing.lift _).map_mul, (f' j k hjk).map_mul, ih,
      (restriction _).map_mul, (FreeCommRing.lift _).map_mul, restriction_of, dif_pos hps, lift_of,
      restriction_of, dif_pos (hst hps), lift_of]
    dsimp only
    -- ⊢ ↑(f' j k hjk) (↑(f' p.fst j (_ : p.fst ≤ j)) p.snd) * ↑(↑lift fun ix => ↑(f' …
    -- porting note: Lean 3 could get away with far fewer hints for inputs in the line below
    have := DirectedSystem.map_map (fun i j h => f' i j h) (hj p hps) hjk
    -- ⊢ ↑(f' j k hjk) (↑(f' p.fst j (_ : p.fst ≤ j)) p.snd) * ↑(↑lift fun ix => ↑(f' …
    dsimp only at this
    -- ⊢ ↑(f' j k hjk) (↑(f' p.fst j (_ : p.fst ≤ j)) p.snd) * ↑(↑lift fun ix => ↑(f' …
    rw [this]
    -- 🎉 no goals
  · rintro x y ihx ihy
    -- ⊢ ↑(f' j k hjk) (↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑ix).fst ≤ j)) (↑ix) …
    rw [(restriction _).map_add, (FreeCommRing.lift _).map_add, (f' j k hjk).map_add, ihx, ihy,
      (restriction _).map_add, (FreeCommRing.lift _).map_add]
#align ring.direct_limit.of.zero_exact_aux2 Ring.DirectLimit.of.zero_exact_aux2

variable {G f f'}

theorem of.zero_exact_aux [Nonempty ι] [IsDirected ι (· ≤ ·)] {x : FreeCommRing (Σi, G i)}
    (H : (Ideal.Quotient.mk _ x : DirectLimit G fun i j h => f' i j h)
        = (0 : DirectLimit G fun i j h => f' i j h)) :
    ∃ j s,
      ∃ H : ∀ k : Σi, G i, k ∈ s → k.1 ≤ j,
        IsSupported x s ∧
          lift (fun ix : s => f' ix.1.1 j (H ix ix.2) ix.1.2) (restriction s x) = (0 : G j) := by
  refine' span_induction (Ideal.Quotient.eq_zero_iff_mem.1 H) _ _ _ _
  · rintro x (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩)
    · refine'
        ⟨j, {⟨i, x⟩, ⟨j, f' i j hij x⟩}, _,
          isSupported_sub (isSupported_of.2 <| Or.inr rfl) (isSupported_of.2 <| Or.inl rfl), _⟩
      · rintro k (rfl | ⟨rfl | _⟩)
        -- ⊢ { fst := i, snd := x }.fst ≤ j
        exact hij
        -- ⊢ { fst := j, snd := (fun i j h => ↑(f' i j h)) i j hij x }.fst ≤ j
        rfl
        -- 🎉 no goals
      · rw [(restriction _).map_sub, RingHom.map_sub, restriction_of, dif_pos,
          restriction_of, dif_pos, lift_of, lift_of]
        dsimp only
        have := DirectedSystem.map_map (fun i j h => f' i j h) hij (le_refl j : j ≤ j)
        dsimp only at this
        rw [this]
        exact sub_self _
        exacts [Or.inr rfl, Or.inl rfl]
        -- 🎉 no goals
    · refine' ⟨i, {⟨i, 1⟩}, _, isSupported_sub (isSupported_of.2 rfl) isSupported_one, _⟩
      -- ⊢ ∀ (k : (i : ι) × G i), k ∈ {{ fst := i, snd := 1 }} → k.fst ≤ i
      · rintro k (rfl | h)
        -- ⊢ { fst := i, snd := 1 }.fst ≤ i
        rfl
        -- 🎉 no goals
        -- porting note: the Lean3 proof contained `rw [restriction_of]`, but this
        -- lemma does not seem to work here
      · rw [RingHom.map_sub, RingHom.map_sub]
        -- ⊢ ↑(↑lift fun ix => ↑(f' (↑ix).fst i (_ : (↑ix).fst ≤ i)) (↑ix).snd) (↑(restri …
        erw [lift_of, dif_pos rfl, RingHom.map_one, RingHom.map_one, lift_of,
          RingHom.map_one, sub_self]
    · refine'
        ⟨i, {⟨i, x + y⟩, ⟨i, x⟩, ⟨i, y⟩}, _,
          isSupported_sub (isSupported_of.2 <| Or.inl rfl)
            (isSupported_add (isSupported_of.2 <| Or.inr <| Or.inl rfl)
              (isSupported_of.2 <| Or.inr <| Or.inr rfl)),
          _⟩
      · rintro k (rfl | ⟨rfl | ⟨rfl | hk⟩⟩) <;> rfl
                                                -- 🎉 no goals
                                                -- 🎉 no goals
                                                -- 🎉 no goals
      · rw [(restriction _).map_sub, (restriction _).map_add, restriction_of, restriction_of,
          restriction_of, dif_pos, dif_pos, dif_pos, RingHom.map_sub,
          (FreeCommRing.lift _).map_add, lift_of, lift_of, lift_of]
        dsimp only
        rw [(f' i i _).map_add]
        exact sub_self _
        all_goals tauto
        -- 🎉 no goals
    · refine'
        ⟨i, {⟨i, x * y⟩, ⟨i, x⟩, ⟨i, y⟩}, _,
          isSupported_sub (isSupported_of.2 <| Or.inl rfl)
            (isSupported_mul (isSupported_of.2 <| Or.inr <| Or.inl rfl)
              (isSupported_of.2 <| Or.inr <| Or.inr rfl)), _⟩
      · rintro k (rfl | ⟨rfl | ⟨rfl | hk⟩⟩) <;> rfl
                                                -- 🎉 no goals
                                                -- 🎉 no goals
                                                -- 🎉 no goals
      · rw [(restriction _).map_sub, (restriction _).map_mul, restriction_of, restriction_of,
          restriction_of, dif_pos, dif_pos, dif_pos, RingHom.map_sub,
          (FreeCommRing.lift _).map_mul, lift_of, lift_of, lift_of]
        dsimp only
        rw [(f' i i _).map_mul]
        exact sub_self _
        all_goals tauto
        -- 🎉 no goals
        -- porting note: was
        --exacts [sub_self _, Or.inl rfl, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)]
  · refine' Nonempty.elim (by infer_instance) fun ind : ι => _
    -- ⊢ ∃ j s H, IsSupported 0 s ∧ ↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑ix).fst …
    refine' ⟨ind, ∅, fun _ => False.elim, isSupported_zero, _⟩
    -- ⊢ ↑(↑lift fun ix => ↑(f' (↑ix).fst ind (_ : (↑ix).fst ≤ ind)) (↑ix).snd) (↑(re …
    -- porting note: `RingHom.map_zero` was `(restriction _).map_zero`
    rw [RingHom.map_zero, (FreeCommRing.lift _).map_zero]
    -- 🎉 no goals
  · rintro x y ⟨i, s, hi, hxs, ihs⟩ ⟨j, t, hj, hyt, iht⟩
    -- ⊢ ∃ j s H, IsSupported (x + y) s ∧ ↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑i …
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    -- ⊢ ∃ j s H, IsSupported (x + y) s ∧ ↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑i …
    have : ∀ z : Σi, G i, z ∈ s ∪ t → z.1 ≤ k := by
      rintro z (hz | hz)
      exact le_trans (hi z hz) hik
      exact le_trans (hj z hz) hjk
    refine'
      ⟨k, s ∪ t, this,
        isSupported_add (isSupported_upwards hxs <| Set.subset_union_left s t)
          (isSupported_upwards hyt <| Set.subset_union_right s t), _⟩
    · -- porting note: was `(restriction _).map_add`
      rw [RingHom.map_add, (FreeCommRing.lift _).map_add, ←
        of.zero_exact_aux2 G f' hxs hi this hik (Set.subset_union_left s t), ←
        of.zero_exact_aux2 G f' hyt hj this hjk (Set.subset_union_right s t), ihs,
        (f' i k hik).map_zero, iht, (f' j k hjk).map_zero, zero_add]
  · rintro x y ⟨j, t, hj, hyt, iht⟩
    -- ⊢ ∃ j s H, IsSupported (x • y) s ∧ ↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑i …
    rw [smul_eq_mul]
    -- ⊢ ∃ j s H, IsSupported (x * y) s ∧ ↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑i …
    rcases exists_finset_support x with ⟨s, hxs⟩
    -- ⊢ ∃ j s H, IsSupported (x * y) s ∧ ↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑i …
    rcases(s.image Sigma.fst).exists_le with ⟨i, hi⟩
    -- ⊢ ∃ j s H, IsSupported (x * y) s ∧ ↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑i …
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    -- ⊢ ∃ j s H, IsSupported (x * y) s ∧ ↑(↑lift fun ix => ↑(f' (↑ix).fst j (_ : (↑i …
    have : ∀ z : Σi, G i, z ∈ ↑s ∪ t → z.1 ≤ k := by
      rintro z (hz | hz)
      exacts [(hi z.1 <| Finset.mem_image.2 ⟨z, hz, rfl⟩).trans hik, (hj z hz).trans hjk]
    refine'
      ⟨k, ↑s ∪ t, this,
        isSupported_mul (isSupported_upwards hxs <| Set.subset_union_left (↑s) t)
          (isSupported_upwards hyt <| Set.subset_union_right (↑s) t), _⟩
    -- porting note: RingHom.map_mul was `(restriction _).map_mul`
    rw [RingHom.map_mul, (FreeCommRing.lift _).map_mul, ←
      of.zero_exact_aux2 G f' hyt hj this hjk (Set.subset_union_right (↑s) t), iht,
      (f' j k hjk).map_zero, mul_zero]
#align ring.direct_limit.of.zero_exact_aux Ring.DirectLimit.of.zero_exact_aux

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact [IsDirected ι (· ≤ ·)] {i x} (hix : of G (fun i j h => f' i j h) i x = 0) :
    ∃ (j : _) (hij : i ≤ j), f' i j hij x = 0 :=
  haveI : Nonempty ι := ⟨i⟩
  let ⟨j, s, H, hxs, hx⟩ := of.zero_exact_aux hix
  have hixs : (⟨i, x⟩ : Σi, G i) ∈ s := isSupported_of.1 hxs
  ⟨j, H ⟨i, x⟩ hixs, by rw [restriction_of, dif_pos hixs, lift_of] at hx; exact hx⟩
                        -- ⊢ ↑(f' i j (_ : { fst := i, snd := x }.fst ≤ j)) x = 0
                                                                          -- 🎉 no goals
#align ring.direct_limit.of.zero_exact Ring.DirectLimit.of.zero_exact

end OfZeroExact

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

/-- If the maps in the directed system are injective, then the canonical maps
from the components to the direct limits are injective. -/
theorem of_injective [IsDirected ι (· ≤ ·)] [DirectedSystem G fun i j h => f' i j h]
    (hf : ∀ i j hij, Function.Injective (f' i j hij)) (i) :
    Function.Injective (of G (fun i j h => f' i j h) i) := by
  suffices ∀ x, of G (fun i j h => f' i j h) i x = 0 → x = 0 by
    intro x y hxy
    rw [← sub_eq_zero]
    apply this
    rw [(of G _ i).map_sub, hxy, sub_self]
  intro x hx
  -- ⊢ x = 0
  rcases of.zero_exact hx with ⟨j, hij, hfx⟩
  -- ⊢ x = 0
  apply hf i j hij
  -- ⊢ ↑(f' i j hij) x = ↑(f' i j hij) 0
  rw [hfx, (f' i j hij).map_zero]
  -- 🎉 no goals
#align ring.direct_limit.of_injective Ring.DirectLimit.of_injective

variable (P : Type u₁) [CommRing P]

variable (g : ∀ i, G i →+* P)

variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

open FreeCommRing

variable (G f)

/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
def lift : DirectLimit G f →+* P :=
  Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σi, G i => g x.1 x.2)
    (by
      suffices Ideal.span _ ≤
          Ideal.comap (FreeCommRing.lift fun x : Σi : ι, G i => g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      -- ⊢ {a | (∃ i j H x, FreeCommRing.of { fst := j, snd := f i j H x } - FreeCommRi …
      intro x hx
      -- ⊢ x ∈ ↑(Ideal.comap (↑FreeCommRing.lift fun x => ↑(g x.fst) x.snd) ⊥)
      rw [SetLike.mem_coe, Ideal.mem_comap, mem_bot]
      -- ⊢ ↑(↑FreeCommRing.lift fun x => ↑(g x.fst) x.snd) x = 0
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [RingHom.map_sub, lift_of, Hg, RingHom.map_one, RingHom.map_add, RingHom.map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])
#align ring.direct_limit.lift Ring.DirectLimit.lift

variable {G f}

-- porting note: the @[simp] attribute would trigger a `simpNF` linter error:
-- failed to synthesize CommMonoidWithZero (Ring.DirectLimit G f)
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  FreeCommRing.lift_of _ _
#align ring.direct_limit.lift_of Ring.DirectLimit.lift_of

theorem lift_unique [Nonempty ι] [IsDirected ι (· ≤ ·)] (F : DirectLimit G f →+* P) (x) :
    F x = lift G f P (fun i => F.comp <| of G f i) (fun i j hij x => by simp [of_f]) x :=
                                                                        -- 🎉 no goals
  DirectLimit.induction_on x fun i x => by simp [lift_of]
                                           -- 🎉 no goals
#align ring.direct_limit.lift_unique Ring.DirectLimit.lift_unique

end DirectLimit

end

end Ring

namespace Field

variable [Nonempty ι] [IsDirected ι (· ≤ ·)] [∀ i, Field (G i)]

variable (f : ∀ i j, i ≤ j → G i → G j)

variable (f' : ∀ i j, i ≤ j → G i →+* G j)

namespace DirectLimit

instance nontrivial [DirectedSystem G fun i j h => f' i j h] :
    Nontrivial (Ring.DirectLimit G fun i j h => f' i j h) :=
  ⟨⟨0, 1,
      Nonempty.elim (by infer_instance) fun i : ι => by
                        -- 🎉 no goals
        change (0 : Ring.DirectLimit G fun i j h => f' i j h) ≠ 1
        -- ⊢ 0 ≠ 1
        rw [← (Ring.DirectLimit.of _ _ _).map_one]
        -- ⊢ 0 ≠ ↑(Ring.DirectLimit.of G (fun i j h => ↑(f' i j h)) ?m.2568314) 1
        intro H; rcases Ring.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
        -- ⊢ False
                 -- ⊢ False
        rw [(f' i j hij).map_one] at hf
        -- ⊢ False
        exact one_ne_zero hf⟩⟩
        -- 🎉 no goals
#align field.direct_limit.nontrivial Field.DirectLimit.nontrivial

theorem exists_inv {p : Ring.DirectLimit G f} : p ≠ 0 → ∃ y, p * y = 1 :=
  Ring.DirectLimit.induction_on p fun i x H =>
    ⟨Ring.DirectLimit.of G f i x⁻¹, by
      erw [← (Ring.DirectLimit.of _ _ _).map_mul,
        mul_inv_cancel fun h : x = 0 => H <| by rw [h, (Ring.DirectLimit.of _ _ _).map_zero],
        (Ring.DirectLimit.of _ _ _).map_one]⟩
#align field.direct_limit.exists_inv Field.DirectLimit.exists_inv

section

open Classical

/-- Noncomputable multiplicative inverse in a direct limit of fields. -/
noncomputable def inv (p : Ring.DirectLimit G f) : Ring.DirectLimit G f :=
  if H : p = 0 then 0 else Classical.choose (DirectLimit.exists_inv G f H)
#align field.direct_limit.inv Field.DirectLimit.inv

protected theorem mul_inv_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : p * inv G f p = 1 := by
  rw [inv, dif_neg hp, Classical.choose_spec (DirectLimit.exists_inv G f hp)]
  -- 🎉 no goals
#align field.direct_limit.mul_inv_cancel Field.DirectLimit.mul_inv_cancel

protected theorem inv_mul_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : inv G f p * p = 1 := by
  rw [_root_.mul_comm, DirectLimit.mul_inv_cancel G f hp]
  -- 🎉 no goals
#align field.direct_limit.inv_mul_cancel Field.DirectLimit.inv_mul_cancel

-- porting note: this takes some time, had to increase heartbeats
set_option maxHeartbeats 1000000 in
/-- Noncomputable field structure on the direct limit of fields.
See note [reducible non-instances]. -/
@[reducible]
protected noncomputable def field [DirectedSystem G fun i j h => f' i j h] :
    Field (Ring.DirectLimit G fun i j h => f' i j h) :=
  { Ring.DirectLimit.commRing G fun i j h => f' i j h,
    DirectLimit.nontrivial G fun i j h =>
      f' i j h with
    inv := inv G fun i j h => f' i j h
    mul_inv_cancel := fun p => DirectLimit.mul_inv_cancel G fun i j h => f' i j h
    inv_zero := dif_pos rfl }
#align field.direct_limit.field Field.DirectLimit.field

end

end DirectLimit

end Field
