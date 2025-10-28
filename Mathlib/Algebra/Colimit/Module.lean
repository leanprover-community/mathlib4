/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Jujian Zhang
-/
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Congruence.Defs
import Mathlib.Data.Finset.Order
import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of modules and abelian groups

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups.

It is constructed as a quotient of the free module instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

## Main definitions

* `Module.DirectLimit G f`
* `AddCommGroup.DirectLimit G f`

-/

suppress_compilation

variable {R : Type*} [Semiring R] {ι : Type*} [Preorder ι] {G : ι → Type*}

open Submodule

namespace Module

alias DirectedSystem.map_self := DirectedSystem.map_self'
alias DirectedSystem.map_map := DirectedSystem.map_map'

variable [DecidableEq ι]
variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)] (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

/-- The relation on the direct sum that generates the additive congruence that defines the
colimit as a quotient. -/
inductive DirectLimit.Eqv : DirectSum ι G → DirectSum ι G → Prop
  | of_map {i j} (h : i ≤ j) (x : G i) :
    Eqv (DirectSum.lof R ι G i x) (DirectSum.lof R ι G j <| f i j h x)

/-- The congruence relation to quotient the direct sum by to obtain the direct limit. -/
def DirectLimit.moduleCon [DecidableEq ι] : ModuleCon R (DirectSum ι G) where
  toAddCon := addConGen (Eqv f)
  smul r _ _ h := by
    refine ((addConGen (Eqv f)).comap (smulAddHom R _ r) <| by simp).addConGen_le ?_ h
    rintro _ _ ⟨⟩
    simpa only [smulAddHom_apply, AddCon.comap_rel, ← map_smul] using .of _ _ (.of_map ..)

variable (G)

/-- The direct limit of a directed system is the modules glued together along the maps. -/
def DirectLimit [DecidableEq ι] : Type _ := (DirectLimit.moduleCon f).Quotient

namespace DirectLimit

section Basic

instance addCommMonoid : AddCommMonoid (DirectLimit G f) :=
  inferInstanceAs (AddCommMonoid (moduleCon f).Quotient)

instance module : Module R (DirectLimit G f) := inferInstanceAs (Module R (moduleCon f).Quotient)

instance addCommGroup (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) : AddCommGroup (DirectLimit G f) :=
  inferInstanceAs (AddCommGroup (moduleCon f).Quotient)

instance inhabited : Inhabited (DirectLimit G f) :=
  ⟨0⟩

instance unique [IsEmpty ι] : Unique (DirectLimit G f) :=
  inferInstanceAs <| Unique (Quotient _)

variable (R ι)

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[R] DirectLimit G f :=
  .comp { __ := AddCon.mk' _, map_smul' := fun _ _ ↦ rfl } <| DirectSum.lof R ι G i

variable {R ι G f}

theorem quotMk_of (i x) : Quot.mk _ (.of G i x) = of R ι G f i x := rfl

@[simp]
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x :=
  (AddCon.eq _).mpr <| .symm <| .of _ _ (.of_map _ _)

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [Nonempty ι] [IsDirected ι (· ≤ ·)] (z : DirectLimit G f) :
    ∃ i x, of R ι G f i x = z :=
  Nonempty.elim (by infer_instance) fun ind : ι ↦
    Quotient.inductionOn' z fun z ↦
      DirectSum.induction_on z ⟨ind, 0, LinearMap.map_zero _⟩ (fun i x ↦ ⟨i, x, rfl⟩)
        fun p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩ ↦
        let ⟨k, hik, hjk⟩ := exists_ge_ge i j
        ⟨k, f i k hik x + f j k hjk y, by
          rw [LinearMap.map_add, of_f, of_f, ihx, ihy]
          rfl ⟩

theorem exists_of₂ [Nonempty ι] [IsDirected ι (· ≤ ·)] (z w : DirectLimit G f) :
    ∃ i x y, of R ι G f i x = z ∧ of R ι G f i y = w :=
  have ⟨i, x, hx⟩ := exists_of z
  have ⟨j, y, hy⟩ := exists_of w
  have ⟨k, hik, hjk⟩ := exists_ge_ge i j
  ⟨k, f i k hik x, f j k hjk y, by rw [of_f, hx], by rw [of_f, hy]⟩

@[elab_as_elim]
protected theorem induction_on [Nonempty ι] [IsDirected ι (· ≤ ·)] {C : DirectLimit G f → Prop}
    (z : DirectLimit G f) (ih : ∀ i x, C (of R ι G f i x)) : C z :=
  let ⟨i, x, h⟩ := exists_of z
  h ▸ ih i x

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (R ι G f) in
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₗ[R] P where
  __ := AddCon.lift _ (DirectSum.toModule R ι P g) <|
    AddCon.addConGen_le fun _ _ ⟨_, _⟩ ↦ by simpa using (Hg _ _ _ _).symm
  map_smul' r := by rintro ⟨x⟩; exact map_smul (DirectSum.toModule R ι P g) r x

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp] theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x :=
  DirectSum.toModule_lof R _ _

@[ext]
theorem hom_ext {g₁ g₂ : DirectLimit G f →ₗ[R] P}
    (h : ∀ i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) :
    g₁ = g₂ :=
  LinearMap.toAddMonoidHom_injective <| AddCon.hom_ext <| DirectSum.addHom_ext' fun i =>
    congr($(h i).toAddMonoidHom)

@[simp]
theorem lift_comp_of (F : DirectLimit G f →ₗ[R] P) :
    lift R ι G f (fun i ↦ F.comp <| of R ι G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

@[deprecated lift_comp_of (since := "2025-08-11")]
theorem lift_unique (F : DirectLimit G f →ₗ[R] P) (x) :
    F x = lift R ι G f (fun i ↦ F.comp <| of R ι G f i) (fun i j hij x ↦ by simp) x := by
  rw [lift_comp_of]

@[simp]
theorem lift_of' : lift R ι G f (of R ι G f) (fun i j hij x ↦ by simp) = .id := by
  ext; simp

lemma lift_injective [IsDirected ι (· ≤ ·)]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift R ι G f g Hg) := by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  intro z w eq
  obtain ⟨i, x, y, rfl, rfl⟩ := exists_of₂ z w
  simp_rw [lift_of] at eq
  rw [injective _ eq]

section functorial

variable {G' : ι → Type*} [∀ i, AddCommMonoid (G' i)] [∀ i, Module R (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j}
variable {G'' : ι → Type*} [∀ i, AddCommMonoid (G'' i)] [∀ i, Module R (G'' i)]
variable {f'' : ∀ i j, i ≤ j → G'' i →ₗ[R] G'' j}

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of linear maps `gᵢ : Gᵢ ⟶ G'ᵢ` such that `g ∘ f = f' ∘ g` induces a linear map
`lim G ⟶ lim G'`.
-/
def map (g : (i : ι) → G i →ₗ[R] G' i) (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i) :
    DirectLimit G f →ₗ[R] DirectLimit G' f' :=
  lift _ _ _ _ (fun i ↦ of _ _ _ _ _ ∘ₗ g i) fun i j h g ↦ by
    have eq1 := LinearMap.congr_fun (hg i j h) g
    simp only [LinearMap.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1, of_f]

@[simp] lemma map_apply_of (g : (i : ι) → G i →ₗ[R] G' i)
    (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    {i : ι} (x : G i) :
    map g hg (of _ _ G f _ x) = of R ι G' f' i (g i x) :=
  lift_of _ _ _

@[simp] lemma map_id :
    map (fun _ ↦ LinearMap.id) (fun _ _ _ ↦ rfl) = LinearMap.id (M := DirectLimit G f) := by
  ext; simp

lemma map_comp (g₁ : (i : ι) → G i →ₗ[R] G' i) (g₂ : (i : ι) → G' i →ₗ[R] G'' i)
    (hg₁ : ∀ i j h, g₁ j ∘ₗ f i j h = f' i j h ∘ₗ g₁ i)
    (hg₂ : ∀ i j h, g₂ j ∘ₗ f' i j h = f'' i j h ∘ₗ g₂ i) :
    (map g₂ hg₂ ∘ₗ map g₁ hg₁ :
      DirectLimit G f →ₗ[R] DirectLimit G'' f'') =
    (map (fun i ↦ g₂ i ∘ₗ g₁ i) fun i j h ↦ by
        rw [LinearMap.comp_assoc, hg₁ i, ← LinearMap.comp_assoc, hg₂ i, LinearMap.comp_assoc] :
      DirectLimit G f →ₗ[R] DirectLimit G'' f'') := by
  ext; simp

open LinearEquiv LinearMap in
/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ≅ lim G'`.
-/
def congr (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) :
    DirectLimit G f ≃ₗ[R] DirectLimit G' f' :=
  LinearEquiv.ofLinear (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ by
      rw [toLinearMap_symm_comp_eq, ← comp_assoc, he i, comp_assoc, comp_coe, symm_trans_self,
        refl_toLinearMap, comp_id])
    (by simp [map_comp]) (by simp [map_comp])

lemma congr_apply_of (e : (i : ι) → G i ≃ₗ[R] G' i) (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i)
    {i : ι} (g : G i) :
    congr e he (of _ _ G f i g) = of _ _ G' f' i (e i g) :=
  map_apply_of _ he _

open LinearEquiv LinearMap in
lemma congr_symm_apply_of (e : (i : ι) → G i ≃ₗ[R] G' i)
    (he : ∀ i j h, e j ∘ₗ f i j h = f' i j h ∘ₗ e i) {i : ι} (g : G' i) :
    (congr e he).symm (of _ _ G' f' i g) = of _ _ G f i ((e i).symm g) :=
  map_apply_of _ (fun i j h ↦ by
    rw [toLinearMap_symm_comp_eq, ← comp_assoc, he i, comp_assoc, comp_coe, symm_trans_self,
      refl_toLinearMap, comp_id]) _

end functorial

end Basic

section equiv

variable [Nonempty ι] [IsDirected ι (· ≤ ·)] [DirectedSystem G (f · · ·)]
open _root_.DirectLimit

/-- The direct limit constructed as a quotient of the direct sum is isomorphic to
the direct limit constructed as a quotient of the disjoint union. -/
def linearEquiv : DirectLimit G f ≃ₗ[R] _root_.DirectLimit G f :=
  .ofLinear
    (lift _ _ _ _ (Module.of _ _ _ _) fun _ _ _ _ ↦ .symm <| eq_of_le ..)
    (Module.lift _ _ _ _ (of _ _ _ _) fun _ _ _ _ ↦ of_f ..)
    (by ext; simp)
    (by ext; simp)

theorem linearEquiv_of {i g} : linearEquiv _ _ (of _ _ G f i g) = ⟦⟨i, g⟩⟧ := by
  simp [linearEquiv]; rfl

theorem linearEquiv_symm_mk {g} : (linearEquiv _ _).symm ⟦g⟧ = of _ _ G f g.1 g.2 := rfl

end equiv

variable {G f} [DirectedSystem G (f · · ·)] [IsDirected ι (· ≤ ·)]

theorem exists_eq_of_of_eq {i x y} (h : of R ι G f i x = of R ι G f i y) :
    ∃ j hij, f i j hij x = f i j hij y := by
  have := Nonempty.intro i
  apply_fun linearEquiv _ _ at h
  simp_rw [linearEquiv_of] at h
  have ⟨j, h⟩ := Quotient.exact h
  exact ⟨j, h.1, h.2.2⟩

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact {i x} (H : of R ι G f i x = 0) :
    ∃ j hij, f i j hij x = (0 : G j) := by
  convert exists_eq_of_of_eq (H.trans (map_zero <| _).symm)
  rw [map_zero]

end DirectLimit

end Module

namespace AddCommGroup

variable (G) [∀ i, AddCommMonoid (G i)]

/-- The direct limit of a directed system is the abelian groups glued together along the maps. -/
def DirectLimit [DecidableEq ι] (f : ∀ i j, i ≤ j → G i →+ G j) : Type _ :=
  @Module.DirectLimit ℕ _ ι _ G _ _ (fun i j hij ↦ (f i j hij).toNatLinearMap) _

namespace DirectLimit

variable (f : ∀ i j, i ≤ j → G i →+ G j)

local instance directedSystem [h : DirectedSystem G fun i j h ↦ f i j h] :
    DirectedSystem G fun i j hij ↦ (f i j hij).toNatLinearMap :=
  h

variable [DecidableEq ι]

instance : AddCommMonoid (DirectLimit G f) :=
  Module.DirectLimit.addCommMonoid G fun i j hij ↦ (f i j hij).toNatLinearMap

instance addCommGroup (G : ι → Type*) [∀ i, AddCommGroup (G i)]
    (f : ∀ i j, i ≤ j → G i →+ G j) : AddCommGroup (DirectLimit G f) :=
  Module.DirectLimit.addCommGroup G fun i j hij ↦ (f i j hij).toNatLinearMap

instance : Inhabited (DirectLimit G f) :=
  ⟨0⟩

instance [IsEmpty ι] : Unique (DirectLimit G f) := Module.DirectLimit.unique _ _

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →+ DirectLimit G f :=
  (Module.DirectLimit.of ℕ ι G _ i).toAddMonoidHom

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
theorem of.zero_exact [IsDirected ι (· ≤ ·)] [DirectedSystem G fun i j h ↦ f i j h] (i x)
    (h : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
  Module.DirectLimit.of.zero_exact h

variable (P : Type*) [AddCommMonoid P]
variable (g : ∀ i, G i →+ P)
variable (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
variable (G f)

/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : DirectLimit G f →+ P :=
  (Module.DirectLimit.lift ℕ ι G (fun i j hij ↦ (f i j hij).toNatLinearMap)
    (fun i ↦ (g i).toNatLinearMap) Hg).toAddMonoidHom

variable {G f}

@[simp]
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
  Module.DirectLimit.lift_of
    -- Note: had to make these arguments explicit https://github.com/leanprover-community/mathlib4/pull/8386
    (f := fun i j hij ↦ (f i j hij).toNatLinearMap)
    (fun i ↦ (g i).toNatLinearMap)
    Hg
    x

@[ext]
theorem hom_ext {g₁ g₂ : DirectLimit G f →+ P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ :=
  AddCon.hom_ext <| DirectSum.addHom_ext' h

@[simp]
theorem lift_comp_of (F : DirectLimit G f →+ P) :
    lift G f _ (fun i ↦ F.comp <| of G f i) (fun i j hij x ↦ by simp) = F := by
  ext; simp

@[deprecated lift_comp_of (since := "2025-08-11")]
theorem lift_unique (F : DirectLimit G f →+ P) (x) :
    F x = lift G f P (fun i ↦ F.comp (of G f i)) (fun i j hij x ↦ by simp) x := by
  rw [lift_comp_of]

@[simp]
theorem lift_of' : lift G f _ (of G f) (fun i j hij x ↦ by simp) = .id _ := by
  ext; simp

lemma lift_injective [IsDirected ι (· ≤ ·)]
    (injective : ∀ i, Function.Injective <| g i) :
    Function.Injective (lift G f P g Hg) :=
  Module.DirectLimit.lift_injective (f := fun i j hij ↦ (f i j hij).toNatLinearMap) _ Hg injective

section functorial

variable {G' : ι → Type*} [∀ i, AddCommMonoid (G' i)]
variable {f' : ∀ i j, i ≤ j → G' i →+ G' j}
variable {G'' : ι → Type*} [∀ i, AddCommMonoid (G'' i)]
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
    have eq1 := DFunLike.congr_fun (hg i j h) g
    simp only [AddMonoidHom.coe_comp, Function.comp_apply] at eq1 ⊢
    rw [eq1, of_f]

@[simp] lemma map_apply_of (g : (i : ι) → G i →+ G' i)
    (hg : ∀ i j h, (g j).comp (f i j h) = (f' i j h).comp (g i))
    {i : ι} (x : G i) :
    map g hg (of G f _ x) = of G' f' i (g i x) :=
  lift_of _ _ _ _ _

@[simp] lemma map_id :
    map (fun _ ↦ AddMonoidHom.id _) (fun _ _ _ ↦ rfl) = AddMonoidHom.id (DirectLimit G f) := by
  ext; simp

lemma map_comp (g₁ : (i : ι) → G i →+ G' i) (g₂ : (i : ι) → G' i →+ G'' i)
    (hg₁ : ∀ i j h, (g₁ j).comp (f i j h) = (f' i j h).comp (g₁ i))
    (hg₂ : ∀ i j h, (g₂ j).comp (f' i j h) = (f'' i j h).comp (g₂ i)) :
    ((map g₂ hg₂).comp (map g₁ hg₁) :
      DirectLimit G f →+ DirectLimit G'' f'') =
    (map (fun i ↦ (g₂ i).comp (g₁ i)) fun i j h ↦ by
      rw [AddMonoidHom.comp_assoc, hg₁ i, ← AddMonoidHom.comp_assoc, hg₂ i,
        AddMonoidHom.comp_assoc] :
      DirectLimit G f →+ DirectLimit G'' f'') := by
  ext; simp

/--
Consider direct limits `lim G` and `lim G'` with direct system `f` and `f'` respectively, any
family of equivalences `eᵢ : Gᵢ ≅ G'ᵢ` such that `e ∘ f = f' ∘ e` induces an equivalence
`lim G ⟶ lim G'`.
-/
def congr (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i)) :
    DirectLimit G f ≃+ DirectLimit G' f' :=
  AddMonoidHom.toAddEquiv (map (e ·) he)
    (map (fun i ↦ (e i).symm) fun i j h ↦ DFunLike.ext _ _ fun x ↦ by
      have eq1 := DFunLike.congr_fun (he i j h) ((e i).symm x)
      simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
        AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] at eq1 ⊢
      simp [← eq1])
    (by simp [map_comp]) (by simp [map_comp])

lemma congr_apply_of (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G i) :
    congr e he (of G f i g) = of G' f' i (e i g) :=
  map_apply_of _ he _

lemma congr_symm_apply_of (e : (i : ι) → G i ≃+ G' i)
    (he : ∀ i j h, (e j).toAddMonoidHom.comp (f i j h) = (f' i j h).comp (e i))
    {i : ι} (g : G' i) :
    (congr e he).symm (of G' f' i g) = of G f i ((e i).symm g) := by
  simp only [congr, AddMonoidHom.toAddEquiv_symm_apply, map_apply_of, AddMonoidHom.coe_coe]

end functorial

end DirectLimit

end AddCommGroup
