/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Jujian Zhang
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.Finset.Order
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of modules, abelian groups, rings, and fields.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups, or rings, or fields.

It is constructed as a quotient of the free module (for the module case) or quotient of
the free commutative ring (for the ring case) instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

## Main definitions

* `Module.DirectLimit G f`
* `AddCommGroup.DirectLimit G f`
* `Ring.DirectLimit G f`

-/

suppress_compilation

universe u v v' v'' w u₁

open Submodule

variable {R : Type u} [Ring R]
variable {ι : Type v}
variable [Preorder ι]
variable (G : ι → Type w)

namespace Module

variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable {G}
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

alias DirectedSystem.map_self := DirectedSystem.map_self'
alias DirectedSystem.map_map := DirectedSystem.map_map'

variable (G)

/-- The direct limit of a directed system is the modules glued together along the maps. -/
def DirectLimit [DecidableEq ι] : Type max v w :=
  DirectSum ι G ⧸
    (span R <|
      { a |
        ∃ (i j : _) (H : i ≤ j) (x : _),
          DirectSum.lof R ι G i x - DirectSum.lof R ι G j (f i j H x) = a })

namespace DirectLimit

section Basic

variable [DecidableEq ι]

instance addCommGroup : AddCommGroup (DirectLimit G f) :=
  Quotient.addCommGroup _

instance module : Module R (DirectLimit G f) :=
  Quotient.module _

instance inhabited : Inhabited (DirectLimit G f) :=
  ⟨0⟩

instance unique [IsEmpty ι] : Unique (DirectLimit G f) :=
  inferInstanceAs <| Unique (Quotient _)

variable (R ι)

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[R] DirectLimit G f :=
  (mkQ _).comp <| DirectSum.lof R ι G i

variable {R ι G f}

@[simp]
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x :=
  Eq.symm <| (Submodule.Quotient.eq _).2 <| subset_span ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [Nonempty ι] [IsDirected ι (· ≤ ·)] (z : DirectLimit G f) :
    ∃ i x, of R ι G f i x = z :=
  Nonempty.elim (by infer_instance) fun ind : ι =>
    Quotient.inductionOn' z fun z =>
      DirectSum.induction_on z ⟨ind, 0, LinearMap.map_zero _⟩ (fun i x => ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
          rw [LinearMap.map_add, of_f, of_f, ihx, ihy]
          rfl ⟩

@[elab_as_elim]
protected theorem induction_on [Nonempty ι] [IsDirected ι (· ≤ ·)] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of R ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

variable {P : Type u₁} [AddCommGroup P] [Module R P]

variable (R ι G f) in
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₗ[R] P :=
  liftQ _ (DirectSum.toModule R ι P g)
    (span_le.2 fun a ⟨i, j, hij, x, hx⟩ => by
      rw [← hx, SetLike.mem_coe, LinearMap.sub_mem_ker_iff, DirectSum.toModule_lof,
        DirectSum.toModule_lof, Hg])

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp] theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x :=
  DirectSum.toModule_lof R _ _

theorem lift_unique [IsDirected ι (· ≤ ·)] (F : DirectLimit G f →ₗ[R] P) (x) :
    F x =
      lift R ι G f (fun i => F.comp <| of R ι G f i)
        (fun i j hij x => by rw [LinearMap.comp_apply, of_f]; rfl) x := by
  cases isEmpty_or_nonempty ι
  · simp_rw [Subsingleton.elim x 0, _root_.map_zero]
  · exact DirectLimit.induction_on x fun i x => by rw [lift_of]; rfl

lemma lift_injective [IsDirected ι (· ≤ ·)]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift R ι G f g Hg) := by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intros z hz
  induction z using DirectLimit.induction_on with
  | ih _ g =>
    rw [lift_of] at hz
    rw [injective _ g hz, _root_.map_zero]

section functorial

variable {G' : ι → Type v'} [∀ i, AddCommGroup (G' i)] [∀ i, Module R (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j}
variable {G'' : ι → Type v''} [∀ i, AddCommGroup (G'' i)] [∀ i, Module R (G'' i)]
variable {f'' : ∀ i j, i ≤ j → G'' i →ₗ[R] G'' j}

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of linear maps `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a linear map
`lim G ⟶ lim G'`.
-/
def map (g : (i : ι) → G i →ₗ[R] G' i) (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i) :
    DirectLimit G f →ₗ[R] DirectLimit G' f' :=
  lift _ _ _ _ (fun i ↦ of _ _ _ _ _ ∘ₗ g i) fun i j h g ↦ by
    cases isEmpty_or_nonempty ι
    · subsingleton
    · have eq1 := LinearMap.congr_fun (hg i j h) g
      simp only [LinearMap.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1, of_f]

@[simp] lemma map_apply_of (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    {i : ι} (x : G i) :
    map g hg (of _ _ G f _ x) = of R ι G' f' i (g i x) :=
  lift_of _ _ _

@[simp] lemma map_id [IsDirected ι (· ≤ ·)] :
    map (fun _ ↦ LinearMap.id) (fun _ _ _ ↦ rfl) = LinearMap.id (R := R) (M := DirectLimit G f) :=
  DFunLike.ext _ _ fun x ↦ (isEmpty_or_nonempty ι).elim (by subsingleton) fun _ ↦
    x.induction_on fun i g ↦ by simp

lemma map_comp [IsDirected ι (· ≤ ·)]
    (g₁ : (i : ι) → G i →ₗ[R] G' i) (g₂ : (i : ι) → G' i →ₗ[R] G'' i)
    (hg₁ : ∀ i j h, g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i)
    (hg₂ : ∀ i j h, g₂ j ∘ₗ f' i j h = f'' i j h ∘ₗ g₂ i) :
    (map g₂ hg₂ ∘ₗ map g₁ hg₁ :
      DirectLimit G f →ₗ[R] DirectLimit G'' f'') =
    (map (fun i ↦ g₂ i ∘ₗ g₁ i) fun i j h ↦ by
        rw [LinearMap.comp_assoc, hg₁ i, ← LinearMap.comp_assoc, hg₂ i, LinearMap.comp_assoc] :
      DirectLimit G f →ₗ[R] DirectLimit G'' f'') :=
  DFunLike.ext _ _ fun x ↦ (isEmpty_or_nonempty ι).elim (by subsingleton) fun _ ↦
    x.induction_on fun i g ↦ by simp

open LinearEquiv LinearMap in
/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ≅ lim G'`.
-/
def congr [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) :
    DirectLimit G f ≃ₗ[R] DirectLimit G' f' :=
  LinearEquiv.ofLinear (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ by
      rw [toLinearMap_symm_comp_eq, ← comp_assoc, he i, comp_assoc, comp_coe, symm_trans_self,
        refl_toLinearMap, comp_id])
    (by simp [map_comp]) (by simp [map_comp])

lemma congr_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
    {i : ι} (g : G i) :
    congr e he (of _ _ G f i g) = of _ _ G' f' i (e i g) :=
  map_apply_of _ he _

open LinearEquiv LinearMap in
lemma congr_symm_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
    {i : ι} (g : G' i) :
    (congr e he).symm (of _ _ G' f' i g) = of _ _ G f i ((e i).symm g) :=
  map_apply_of _ (fun i j h ↦ by
    rw [toLinearMap_symm_comp_eq, ← comp_assoc, he i, comp_assoc, comp_coe, symm_trans_self,
      refl_toLinearMap, comp_id]) _

end functorial

end Basic

section equiv

variable [Nonempty ι] [IsDirected ι (· ≤ ·)] [DecidableEq ι] [DirectedSystem G (f · · ·)]
open _root_.DirectLimit

/-- The direct limit constructed as a quotient of the direct sum is isomorphic to
the direct limit constructed as a quotient of the disjoint union. -/
def linearEquiv : DirectLimit G f ≃ₗ[R] _root_.DirectLimit G f :=
  .ofLinear (lift _ _ _ _ (Module.of _ _ _ _) fun _ _ _ _ ↦ .symm <| eq_of_le ..)
    (Module.lift _ _ _ _ (of _ _ _ _) fun _ _ _ _ ↦ of_f ..)
    (by ext ⟨_⟩; rw [← Quotient.mk]; simp [Module.lift, _root_.DirectLimit.lift_def]; rfl)
    (by ext x; refine x.induction_on fun i x ↦ ?_; simp; rfl)

theorem linearEquiv_of {i g} : linearEquiv _ _ (of _ _ G f i g) = ⟦⟨i, g⟩⟧ := by
  simp [linearEquiv]; rfl

theorem linearEquiv_symm_mk {g} : (linearEquiv _ _).symm ⟦g⟧ = of _ _ G f g.1 g.2 := rfl

end equiv

variable {G f}

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact [DirectedSystem G (f · · ·)] [IsDirected ι (· ≤ ·)] [DecidableEq ι]
    {i x} (H : of R ι G f i x = 0) :
    ∃ j hij, f i j hij x = (0 : G j) := by
  haveI : Nonempty ι := ⟨i⟩
  apply_fun linearEquiv _ _ at H
  rwa [map_zero, linearEquiv_of, DirectLimit.exists_eq_zero] at H

end DirectLimit

end Module

namespace AddCommGroup

variable [∀ i, AddCommGroup (G i)]

/-- The direct limit of a directed system is the abelian groups glued together along the maps. -/
def DirectLimit [DecidableEq ι] (f : ∀ i j, i ≤ j → G i →+ G j) : Type _ :=
  @Module.DirectLimit ℤ _ ι _ G _ _ (fun i j hij => (f i j hij).toIntLinearMap) _

namespace DirectLimit

variable (f : ∀ i j, i ≤ j → G i →+ G j)

protected theorem directedSystem [h : DirectedSystem G fun i j h => f i j h] :
    DirectedSystem G fun i j hij => (f i j hij).toIntLinearMap :=
  h

attribute [local instance] DirectLimit.directedSystem

variable [DecidableEq ι]

instance : AddCommGroup (DirectLimit G f) :=
  Module.DirectLimit.addCommGroup G fun i j hij => (f i j hij).toIntLinearMap

instance : Inhabited (DirectLimit G f) :=
  ⟨0⟩

instance [IsEmpty ι] : Unique (DirectLimit G f) := Module.DirectLimit.unique _ _

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →+ DirectLimit G f :=
  (Module.DirectLimit.of ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap) i).toAddMonoidHom

variable {G f}

@[simp]
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Module.DirectLimit.of_f

@[elab_as_elim]
protected theorem induction_on [Nonempty ι] [IsDirected ι (· ≤ ·)] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  Module.DirectLimit.induction_on z ih

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact [IsDirected ι (· ≤ ·)] [DirectedSystem G fun i j h => f i j h] (i x)
    (h : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
  Module.DirectLimit.of.zero_exact h

variable (P : Type u₁) [AddCommGroup P]
variable (g : ∀ i, G i →+ P)
variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variable (G f)

/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f →+ P :=
  (Module.DirectLimit.lift ℤ ι G (fun i j hij => (f i j hij).toIntLinearMap)
    (fun i => (g i).toIntLinearMap) Hg).toAddMonoidHom

variable {G f}

@[simp]
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  Module.DirectLimit.lift_of
    -- Note: had to make these arguments explicit https://github.com/leanprover-community/mathlib4/pull/8386
    (f := (fun i j hij => (f i j hij).toIntLinearMap))
    (fun i => (g i).toIntLinearMap)
    Hg
    x

theorem lift_unique [IsDirected ι (· ≤ ·)] (F : DirectLimit G f →+ P) (x) :
    F x = lift G f P (fun i => F.comp (of G f i)) (fun i j hij x => by simp) x := by
  cases isEmpty_or_nonempty ι
  · simp_rw [Subsingleton.elim x 0, _root_.map_zero]
  · exact DirectLimit.induction_on x fun i x => by simp

lemma lift_injective [IsDirected ι (· ≤ ·)]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) := by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intros z hz
  induction z using DirectLimit.induction_on with
  | ih _ g => rw [lift_of] at hz; rw [injective _ g hz, _root_.map_zero]

section functorial

variable {G' : ι → Type v'} [∀ i, AddCommGroup (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →+ G' j}
variable {G'' : ι → Type v''} [∀ i, AddCommGroup (G'' i)]
variable {f'' : ∀ i j, i ≤ j → G'' i →+ G'' j}

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of group homomorphisms `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a group
homomorphism `lim G ⟶ lim G'`.
-/
def map (g : (i : ι) → G i →+ G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G f →+ DirectLimit G' f' :=
  lift _ _ _ (fun i ↦ (of _ _ _).comp (g i)) fun i j h g ↦ by
    cases isEmpty_or_nonempty ι
    · subsingleton
    · have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [AddMonoidHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1, of_f]

@[simp] lemma map_apply_of (g : (i : ι) → G i →+ G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G f _ x) = of G' f' i (g i x) :=
  lift_of _ _ _ _ _

@[simp] lemma map_id [IsDirected ι (· ≤ ·)] :
    map (fun _ ↦ AddMonoidHom.id _) (fun _ _ _ ↦ rfl) = AddMonoidHom.id (DirectLimit G f) :=
  DFunLike.ext _ _ fun x ↦ (isEmpty_or_nonempty ι).elim (by subsingleton) fun _ ↦
    x.induction_on fun i g ↦ by simp

lemma map_comp [IsDirected ι (· ≤ ·)]
    (g₁ : (i : ι) → G i →+ G' i) (g₂ : (i : ι) → G' i →+ G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G f →+ DirectLimit G'' f'') =
    (map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [AddMonoidHom.comp_assoc, hg₁ i, ← AddMonoidHom.comp_assoc, hg₂ i,
        AddMonoidHom.comp_assoc] :
      DirectLimit G f →+ DirectLimit G'' f'') :=
  DFunLike.ext _ _ fun x ↦ (isEmpty_or_nonempty ι).elim (by subsingleton) fun _ ↦
    x.induction_on fun i g ↦ by simp

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ⟶ lim G'`.
-/
def congr [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G f ≃+ DirectLimit G' f' :=
  AddMonoidHom.toAddEquiv (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ DFunLike.ext _ _ fun x ↦ by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
        AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1, of_f])
    (by rw [map_comp]; convert map_id <;> aesop)
    (by rw [map_comp]; convert map_id <;> aesop)

lemma congr_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G f i g) = of G' f' i (e i g) :=
  map_apply_of _ he _

lemma congr_symm_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' f' i g) = of G f i ((e i).symm g) := by
  simp only [congr, AddMonoidHom.toAddEquiv_symm_apply, map_apply_of, AddMonoidHom.coe_coe]

end functorial

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

namespace DirectLimit

instance commRing : CommRing (DirectLimit G f) :=
  Ideal.Quotient.commRing _

instance ring : Ring (DirectLimit G f) :=
  CommRing.toRing

-- Porting note: Added a `Zero` instance to get rid of `0` errors.
instance zero : Zero (DirectLimit G f) := by
  unfold DirectLimit
  exact ⟨0⟩

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

variable {G f}

@[simp] theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
  Ideal.Quotient.eq.2 <| subset_span <| Or.inl ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [Nonempty ι] [IsDirected ι (· ≤ ·)] (z : DirectLimit G f) :
    ∃ i x, of G f i x = z :=
  Nonempty.elim (by infer_instance) fun ind : ι =>
    Quotient.inductionOn' z fun x =>
      FreeAbelianGroup.induction_on x ⟨ind, 0, (of _ _ ind).map_zero⟩
        (fun s =>
          Multiset.induction_on s ⟨ind, 1, (of _ _ ind).map_one⟩ fun a s ih =>
            let ⟨i, x⟩ := a
            let ⟨j, y, hs⟩ := ih
            let ⟨k, hik, hjk⟩ := exists_ge_ge i j
            ⟨k, f i k hik x * f j k hjk y, by
              rw [(of G f k).map_mul, of_f, of_f, hs]
              /- porting note: In Lean3, from here, this was `by refl`. I have added
              the lemma `FreeCommRing.of_cons` to fix this proof. -/
              apply congr_arg Quotient.mk''
              symm
              apply FreeCommRing.of_cons⟩)
        (fun s ⟨i, x, ih⟩ => ⟨i, -x, by
          rw [(of G _ _).map_neg, ih]
          rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ =>
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by rw [(of _ _ _).map_add, of_f, of_f, ihx, ihy]; rfl⟩

section

open Polynomial

variable {f' : ∀ i j, i ≤ j → G i →+* G j}

nonrec theorem Polynomial.exists_of [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (q : Polynomial (DirectLimit G fun i j h => f' i j h)) :
    ∃ i p, Polynomial.map (of G (fun i j h => f' i j h) i) p = q :=
  Polynomial.induction_on q
    (fun z =>
      let ⟨i, x, h⟩ := exists_of z
      ⟨i, C x, by rw [map_C, h]⟩)
    (fun q₁ q₂ ⟨i₁, p₁, ih₁⟩ ⟨i₂, p₂, ih₂⟩ =>
      let ⟨i, h1, h2⟩ := exists_ge_ge i₁ i₂
      ⟨i, p₁.map (f' i₁ i h1) + p₂.map (f' i₂ i h2), by
        rw [Polynomial.map_add, map_map, map_map, ← ih₁, ← ih₂]
        congr 2 <;> ext x <;> simp_rw [RingHom.comp_apply, of_f]⟩)
    fun n z _ =>
    let ⟨i, x, h⟩ := exists_of z
    ⟨i, C x * X ^ (n + 1), by rw [Polynomial.map_mul, map_C, h, Polynomial.map_pow, map_X]⟩

end

@[elab_as_elim]
theorem induction_on [Nonempty ι] [IsDirected ι (· ≤ ·)] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
  let ⟨i, x, hx⟩ := exists_of z
  hx ▸ ih i x

variable (P : Type u₁) [CommRing P]

open FreeCommRing

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →+* P :=
  Ideal.Quotient.lift _ (FreeCommRing.lift fun x : Σi, G i => g x.1 x.2)
    (by
      suffices Ideal.span _ ≤
          Ideal.comap (FreeCommRing.lift fun x : Σi : ι, G i => g x.fst x.snd) ⊥ by
        intro x hx
        exact (mem_bot P).1 (this hx)
      rw [Ideal.span_le]
      intro x hx
      rw [SetLike.mem_coe, Ideal.mem_comap, mem_bot]
      rcases hx with (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩) <;>
        simp only [RingHom.map_sub, lift_of, Hg, RingHom.map_one, RingHom.map_add, RingHom.map_mul,
          (g i).map_one, (g i).map_add, (g i).map_mul, sub_self])

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp] theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  FreeCommRing.lift_of _ _

theorem lift_unique [IsDirected ι (· ≤ ·)] (F : DirectLimit G f →+* P) (x) :
    F x = lift G f P (fun i => F.comp <| of G f i) (fun i j hij x => by simp [of_f]) x := by
  cases isEmpty_or_nonempty ι
  · apply DFunLike.congr_fun
    apply Ideal.Quotient.ringHom_ext
    refine FreeCommRing.hom_ext fun ⟨i, _⟩ ↦ ?_
    exact IsEmpty.elim' inferInstance i
  · exact DirectLimit.induction_on x fun i x => by simp

lemma lift_injective [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) := by
  simp_rw [injective_iff_map_eq_zero] at injective ⊢
  intros z hz
  induction z using DirectLimit.induction_on with
  | ih _ g => rw [lift_of] at hz; rw [injective _ g hz, _root_.map_zero]

section OfZeroExact

variable (f' : ∀ i j, i ≤ j → G i →+* G j)
variable [DirectedSystem G fun i j h => f' i j h] [IsDirected ι (· ≤ ·)]
variable (G f)

open _root_.DirectLimit in
/-- The direct limit constructed as a quotient of the free commutative ring is isomorphic to
the direct limit constructed as a quotient of the disjoint union. -/
def ringEquiv [Nonempty ι] : DirectLimit G (f' · · ·) ≃+* _root_.DirectLimit G f' :=
  .ofRingHom (lift _ _ _ (Ring.of _ _) fun _ _ _ _ ↦ .symm <| eq_of_le ..)
    (Ring.lift _ _ _ (of _ _) fun _ _ _ _ ↦ of_f ..)
    (by ext ⟨_⟩; rw [← Quotient.mk]; simp [Ring.lift, _root_.DirectLimit.lift_def]; rfl)
    (by ext x; exact x.induction_on fun i x ↦ by simp)

theorem ringEquiv_of [Nonempty ι] {i g} : ringEquiv G f' (of _ _ i g) = ⟦⟨i, g⟩⟧ := by
  simp [ringEquiv]; rfl

theorem ringEquiv_symm_mk [Nonempty ι] {g} : (ringEquiv G f').symm ⟦g⟧ = of _ _ g.1 g.2 := rfl

variable {G f'}
/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact {i x} (hix : of G (f' · · ·) i x = 0) :
    ∃ (j : _) (hij : i ≤ j), f' i j hij x = 0 := by
  haveI : Nonempty ι := ⟨i⟩
  apply_fun ringEquiv _ _ at hix
  rwa [map_zero, ringEquiv_of, DirectLimit.exists_eq_zero] at hix

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
  rcases of.zero_exact hx with ⟨j, hij, hfx⟩
  apply hf i j hij
  rw [hfx, (f' i j hij).map_zero]

section functorial

variable {f : ∀ i j, i ≤ j → G i →+* G j}
variable {G' : ι → Type v'} [∀ i, CommRing (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →+* G' j}
variable {G'' : ι → Type v''} [∀ i, CommRing (G'' i)]
variable {f'' : ∀ i j, i ≤ j → G'' i →+* G'' j}

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of ring homomorphisms `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a ring
homomorphism `lim G ⟶ lim G'`.
-/
def map (g : (i : ι) → G i →+* G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i)) :
    DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G' fun _ _ h ↦ f' _ _ h :=
  lift _ _ _ (fun i ↦ (of _ _ _).comp (g i)) fun i j h g ↦ by
      have eq1 := DFunLike.congr_fun (hg i j h) g
      simp only [RingHom.coe_comp, Function.comp_apply] at eq1 ⊢
      rw [eq1, of_f]

@[simp] lemma map_apply_of (g : (i : ι) → G i →+* G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G _ _ x) = of G' (fun _ _ h ↦ f' _ _ h) i (g i x) :=
  lift_of _ _ _ _ _

variable [Nonempty ι]

@[simp] lemma map_id [IsDirected ι (· ≤ ·)] :
    map (fun _ ↦ RingHom.id _) (fun _ _ _ ↦ rfl) =
    RingHom.id (DirectLimit G fun _ _ h ↦ f _ _ h) :=
  DFunLike.ext _ _ fun x ↦ x.induction_on fun i g ↦ by simp

lemma map_comp [IsDirected ι (· ≤ ·)]
    (g₁ : (i : ι) → G i →+* G' i) (g₂ : (i : ι) → G' i →+* G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G'' fun _ _ h ↦ f'' _ _ h) =
    (map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [RingHom.comp_assoc, hg₁ i, ← RingHom.comp_assoc, hg₂ i, RingHom.comp_assoc] :
      DirectLimit G (fun _ _ h ↦ f _ _ h) →+* DirectLimit G'' fun _ _ h ↦ f'' _ _ h) :=
  DFunLike.ext _ _ fun x ↦ x.induction_on fun i g ↦ by simp

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ⟶ lim G'`.
-/
def congr [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G (fun _ _ h ↦ f _ _ h) ≃+* DirectLimit G' fun _ _ h ↦ f' _ _ h :=
  RingEquiv.ofHomInv
    (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ DFunLike.ext _ _ fun x ↦ by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1, of_f])
    (DFunLike.ext _ _ fun x ↦ x.induction_on <| by simp)
    (DFunLike.ext _ _ fun x ↦ x.induction_on <| by simp)

lemma congr_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G _ i g) = of G' (fun _ _ h ↦ f' _ _ h) i (e i g) :=
  map_apply_of _ he _

lemma congr_symm_apply_of [IsDirected ι (· ≤ ·)]
    (e : (i : ι) → G i ≃+* G' i)
    (he : ∀ i j h, (e j).toRingHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' _ i g) = of G (fun _ _ h ↦ f _ _ h) i ((e i).symm g) := by
  simp only [congr, RingEquiv.ofHomInv_symm_apply, map_apply_of, RingHom.coe_coe]

end functorial

end DirectLimit

end

end Ring

namespace Field

variable [Nonempty ι] [IsDirected ι (· ≤ ·)] [∀ i, Field (G i)]
variable (f : ∀ i j, i ≤ j → G i → G j)
variable (f' : ∀ i j, i ≤ j → G i →+* G j)

namespace DirectLimit

instance nontrivial [DirectedSystem G (f' · · ·)] :
    Nontrivial (Ring.DirectLimit G (f' · · ·)) :=
  ⟨⟨0, 1,
      Nonempty.elim (by infer_instance) fun i : ι => by
        change (0 : Ring.DirectLimit G (f' · · ·)) ≠ 1
        rw [← (Ring.DirectLimit.of _ _ _).map_one]
        · intro H; rcases Ring.DirectLimit.of.zero_exact H.symm with ⟨j, hij, hf⟩
          rw [(f' i j hij).map_one] at hf
          exact one_ne_zero hf⟩⟩

theorem exists_inv {p : Ring.DirectLimit G f} : p ≠ 0 → ∃ y, p * y = 1 :=
  Ring.DirectLimit.induction_on p fun i x H =>
    ⟨Ring.DirectLimit.of G f i x⁻¹, by
      rw [← (Ring.DirectLimit.of _ _ _).map_mul,
        mul_inv_cancel₀ fun h : x = 0 => H <| by rw [h, (Ring.DirectLimit.of _ _ _).map_zero],
        (Ring.DirectLimit.of _ _ _).map_one]⟩

section


open Classical in
/-- Noncomputable multiplicative inverse in a direct limit of fields. -/
noncomputable def inv (p : Ring.DirectLimit G f) : Ring.DirectLimit G f :=
  if H : p = 0 then 0 else Classical.choose (DirectLimit.exists_inv G f H)

protected theorem mul_inv_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : p * inv G f p = 1 := by
  rw [inv, dif_neg hp, Classical.choose_spec (DirectLimit.exists_inv G f hp)]

protected theorem inv_mul_cancel {p : Ring.DirectLimit G f} (hp : p ≠ 0) : inv G f p * p = 1 := by
  rw [_root_.mul_comm, DirectLimit.mul_inv_cancel G f hp]

/-- Noncomputable field structure on the direct limit of fields.
See note [reducible non-instances]. -/
protected noncomputable abbrev field [DirectedSystem G (f' · · ·)] :
    Field (Ring.DirectLimit G (f' · · ·)) where
  -- This used to include the parent CommRing and Nontrivial instances,
  -- but leaving them implicit avoids a very expensive (2-3 minutes!) eta expansion.
  inv := inv G (f' · · ·)
  mul_inv_cancel := fun _ => DirectLimit.mul_inv_cancel G (f' · · ·)
  inv_zero := dif_pos rfl
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end

end DirectLimit

end Field
