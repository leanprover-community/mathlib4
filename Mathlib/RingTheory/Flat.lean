/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.CategoryTheory.ShortExactSequence
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Character
import Mathlib.Algebra.DirectLimitAndTensorProduct
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Homology.Homology

#align_import ring_theory.flat from "leanprover-community/mathlib"@"62c0a4ef1441edb463095ea02a06e87f3dfe135c"

/-!
# Flat modules

A module `M` over a commutative ring `R` is *flat*
if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective.

This is equivalent to the claim that for all injective `R`-linear maps `f : M₁ → M₂`
the induced map `M₁ ⊗ M → M₂ ⊗ M` is injective.
See <https://stacks.math.columbia.edu/tag/00HD>.
This result is not yet formalised.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## TODO

* Show that tensoring with a flat module preserves injective morphisms.
  Show that this is equivalent to be flat.
  See <https://stacks.math.columbia.edu/tag/00HD>.
  To do this, it is probably a good idea to think about a suitable
  categorical induction principle that should be applied to the category of `R`-modules,
  and that will take care of the administrative side of the proof.
* Define flat `R`-algebras
* Define flat ring homomorphisms
  - Show that the identity is flat
  - Show that composition of flat morphisms is flat
* Show that flatness is stable under base change (aka extension of scalars)
  For base change, it will be very useful to have a "characteristic predicate"
  instead of relying on the construction `A ⊗ B`.
  Indeed, such a predicate should allow us to treat both
  `A[X]` and `A ⊗ R[X]` as the base change of `R[X]` to `A`.
  (Similar examples exist with `Fin n → R`, `R × R`, `ℤ[i] ⊗ ℝ`, etc...)
* Generalize flatness to noncommutative rings.

-/

universe u v

namespace Module

open CategoryTheory Functor MonoidalCategory Limits

open LinearMap (lsmul)

variable (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

open TensorProduct

def Flat.preserves_ses : Prop :=
  (tensorRight <| ModuleCat.of R M).PreservesSESs

def Flat.preserves_exactness : Prop :=
∀ ⦃N1 N2 N3 : ModuleCat.{u} R⦄ (l12 : N1 ⟶ N2) (l23 : N2 ⟶ N3)
  (_ : Exact l12 l23),
  Exact ((tensorRight <| ModuleCat.of R M).map l12)
    ((tensorRight <| ModuleCat.of R M).map l23)

def Flat.injective : Prop :=
∀ ⦃N N' : ModuleCat.{u} R⦄ (L : N ⟶ N'),
  Function.Injective L → Function.Injective ((tensorRight (ModuleCat.of R M)).map L)

def Flat.ideal : Prop :=
  ∀ (I : Ideal R), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))

def Flat.fg_ideal : Prop :=
  ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
class Flat  : Prop where
  out : ∀ ⦃I : Ideal R⦄ (_ : I.FG),
    Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))
#align module.flat Module.Flat

namespace Flat

open TensorProduct LinearMap Submodule BigOperators

instance self (R : Type u) [CommRing R] : Flat R R := ⟨by
  intro I _
  rw [← Equiv.injective_comp (TensorProduct.rid R I).symm.toEquiv]
  convert Subtype.coe_injective using 1
  ext x
  simp⟩
#align module.flat.self Module.Flat.self

lemma fg_ideal_of_ideal (H : Flat.ideal R M) : Flat.fg_ideal R M := fun I _ => H I

namespace injective_of_ideal

lemma baer_iff_surjective :
    Module.Baer.{u, u} R M ↔
    ∀ (I : Ideal R), Function.Surjective <| LinearMap.domRestrict' (M₂ := M) I := by
fconstructor
· intro H I g
  obtain ⟨L, H⟩:= H I g
  refine ⟨L, LinearMap.ext fun x => H x.1 x.2⟩
· intro H I g
  obtain ⟨L, H⟩ := H I g
  refine ⟨L, fun x hx => by convert FunLike.congr_fun H ⟨x, hx⟩⟩

lemma lambek [h : CategoryTheory.Injective (ModuleCat.of R <| CharacterModule M)] :
    Flat.injective R M := by
  intros A B L hL
  have m1 : Mono L
  · rwa [ConcreteCategory.mono_iff_injective_of_preservesPullback]
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro z (hz : _ = 0)
  simp only [tensorRight_obj, tensorRight_map] at hz
  show z = 0
  by_contra rid
  obtain ⟨g, hg⟩ := exists_character_apply_ne_zero_of_ne_zero _ rid
  let f : A →ₗ[R] (CharacterModule M) :=
  { toFun := fun a =>
    { toFun := fun m => g (a ⊗ₜ m)
      map_add' := ?_
      map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }
  pick_goal 2
  · intros
    simp only [tensorRight_obj, tmul_add]
    rw [g.map_add]
  pick_goal 2
  · intros
    simp only [tensorRight_obj, tmul_smul, eq_intCast, Int.cast_id]
    rw [g.map_smul]
  pick_goal 2
  · intros
    refine LinearMap.ext fun _ => ?_
    simp only [tensorRight_obj, LinearMap.coe_mk, AddHom.coe_mk]
    rw [LinearMap.add_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [add_tmul, g.map_add]
  pick_goal 2
  · intros
    refine LinearMap.ext fun _ => ?_
    simp only [tensorRight_obj, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    rw [LinearMap.bimodule_smul_apply]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, tmul_smul]
    rw [smul_tmul']
  obtain ⟨f', hf'⟩ := h.factors (f : A ⟶ ModuleCat.of R (CharacterModule M)) L
  obtain ⟨ι, a, m, s, rfl⟩ := TensorProduct.exists_rep _ z
  let g' : (CharacterModule <| B ⊗[R] M) := CharacterModule.homEquiv _ _ _ f'
  have EQ : g' (∑ i in s, L (a i) ⊗ₜ m i) = 0
  · rw [LinearMap.map_sum] at hz
    change ∑ i in s, (L (a i) ⊗ₜ m i) = 0 at hz
    rw [hz, g'.map_zero]
  refine hg ?_
  rw [g.map_sum]
  rw [g'.map_sum] at EQ
  simp_rw [CharacterModule.homEquiv_apply, CharacterModule.uncurry_apply,
    toAddCommGroup'_apply_tmul] at EQ
  replace hf' : ∀ x, f' (L x) = f x := FunLike.congr_fun hf'
  replace EQ : ∑ i in s, f (a i) (m i) = 0
  · rw [← EQ]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [hf']
  convert EQ

lemma injective_of_baer (h : Module.Baer.{u, u} R <| CharacterModule M) :
    Flat.injective R M :=
  lambek (h := (Module.injective_iff_injective_object _ _).mp <| Module.Baer.injective h)

lemma injective_of_surjective
    (h : ∀ (I : Ideal R), Function.Surjective <|
      LinearMap.domRestrict' (M₂ := CharacterModule M) I) :
    Flat.injective R M :=
  injective_of_baer _ _ <| (baer_iff_surjective _ _).mpr h

lemma characterfy_surj_of_inj (I : Ideal R)
    (inj : Function.Injective <| (TensorProduct.lift ((lsmul R M).comp I.subtype))) :
    Function.Surjective <|
      (LinearMap.characterfy (R := R) (M := I ⊗[R] M) (N := M)
        (TensorProduct.lift ((lsmul R M).comp I.subtype))) := by
  apply LinearMap.charaterfy_surjective_of_injective
  assumption

lemma baer_characterModule_of_injective
    (inj : ∀ (I : Ideal R), Function.Injective <|
      (TensorProduct.lift ((lsmul R M).comp I.subtype))) :
    Module.Baer.{u, u} R (CharacterModule M) := by
  rw [baer_iff_surjective]
  intro I L
  obtain ⟨F, hF⟩ := characterfy_surj_of_inj R _ I (inj I) <| CharacterModule.uncurry R _ _ L
  refine ⟨CharacterModule.curry _ _ _ <|
    (CharacterModule.cong R (R ⊗[R] M) M (TensorProduct.lid _ _)).symm F,
    FunLike.ext _ _ fun i => FunLike.ext _ _ fun m => ?_⟩
  simp only [CharacterModule.cong_symm_apply, characterfy_apply, domRestrict'_apply]
  rw [CharacterModule.curry_apply_apply, LinearMap.comp_apply]
  simp only [AddMonoidHom.coe_toIntLinearMap, toAddMonoidHom_coe, LinearEquiv.coe_coe, lid_tmul]
  have EQ := FunLike.congr_fun hF (i ⊗ₜ m)
  simp only [characterfy_apply] at EQ
  rw [LinearMap.comp_apply] at EQ
  simp only [AddMonoidHom.coe_toIntLinearMap, toAddMonoidHom_coe, lift.tmul, LinearMap.coe_comp,
    coeSubtype, Function.comp_apply, lsmul_apply] at EQ
  exact EQ

lemma main (ideal : Flat.ideal R M) : Flat.injective R M := by
  apply injective_of_baer
  apply baer_characterModule_of_injective
  exact ideal

end injective_of_ideal

lemma injective_of_ideal (ideal : Flat.ideal R M) : Flat.injective R M :=
  injective_of_ideal.main R M ideal

namespace ideal_of_fg_ideal

variable {R M}
variable (m : Submodule R M)

@[ext]
structure _root_.Submodule.fgSubmodule :=
(asSubmodule : Submodule R M)
(le : asSubmodule ≤ m)
(fg : Submodule.FG asSubmodule)

instance : PartialOrder m.fgSubmodule :=
PartialOrder.lift fgSubmodule.asSubmodule fun _ _ h => Submodule.fgSubmodule.ext _ _ h

instance : Sup m.fgSubmodule where
  sup a b := ⟨a.1 ⊔ b.1, sup_le a.2 b.2, Submodule.FG.sup a.3 b.3⟩

instance : SemilatticeSup m.fgSubmodule where
  le_sup_left a _ := le_sup_left (a := a.1)
  le_sup_right _ b := le_sup_right (b := b.1)
  sup_le a _ _ := sup_le (a := a.1)

instance : IsDirected m.fgSubmodule (. ≤ .) where
  directed a b := ⟨a ⊔ b, le_sup_left, le_sup_right⟩

instance : Inhabited m.fgSubmodule where
  default := ⟨⊥, bot_le, Submodule.fg_bot⟩

instance : SetLike m.fgSubmodule M where
  coe a := a.1
  coe_injective' := by intro a b h; simp only [SetLike.coe_set_eq] at h; ext1; exact h

@[simps]
def _root_.Submodule.principalSubmodule (i : m) : m.fgSubmodule where
  asSubmodule := Submodule.span R {i.1}
  le := Submodule.span_le.mpr <| Set.singleton_subset_iff.mpr i.2
  fg := Submodule.fg_span_singleton _

lemma _root_.Submodule.principalSubmodule_smul_le (r : R) (i : m) :
    m.principalSubmodule (r • i) ≤ m.principalSubmodule i :=
  Submodule.span_le.mpr <| Set.singleton_subset_iff.mpr <| Submodule.mem_span_singleton.mpr ⟨r, rfl⟩

lemma _root_.Submodule.mem_principalSubmodule_self (i : m) : (i : M) ∈ m.principalSubmodule i :=
  Submodule.mem_span_singleton_self _

@[simps]
def _root_.Submodule.doubletonSubmodule (i j : m) : m.fgSubmodule where
  asSubmodule := Submodule.span R {i.1, j.1}
  le := Submodule.span_le.mpr <| fun x hx => by aesop
  fg := Submodule.fg_span <| by aesop

lemma _root_.Submodule.mem_self_doubletonSubmodule_left (i j : m) :
    i.1 ∈ m.doubletonSubmodule i j :=
  Submodule.subset_span <| by aesop

lemma _root_.Submodule.mem_self_doubletonSubmodule_right (i j : m) :
    j.1 ∈ m.doubletonSubmodule i j :=
  Submodule.subset_span <| by aesop

lemma _root_.Submodule.principalSubmodule_le_doubletonSubmodule_left (i j : m) :
    m.principalSubmodule i ≤ m.doubletonSubmodule i j :=
  Submodule.span_mono <| by aesop

lemma _root_.Submodule.principalSubmodule_le_doubletonSubmodule_right (i j : m) :
    m.principalSubmodule j ≤ m.doubletonSubmodule i j :=
  Submodule.span_mono <| by aesop

lemma _root_.Submodule.principalSubmodule_add_le_doubletonSubmodule (i j : m) :
    m.principalSubmodule (i + j) ≤ m.doubletonSubmodule i j :=
  Submodule.span_le.mpr <| Set.singleton_subset_iff.mpr <| Submodule.add_mem _
    (m.mem_self_doubletonSubmodule_left _ _) (m.mem_self_doubletonSubmodule_right _ _)

variable [DecidableEq m.fgSubmodule]

def _root_.Submodule.asDirectLimit : Type _ :=
  DirectLimit (R := R) (ι := m.fgSubmodule)
    (fun (a : m.fgSubmodule) => a.asSubmodule) <| fun _ _ h => Submodule.ofLe h

instance : AddCommGroup m.asDirectLimit := by
  delta asDirectLimit
  infer_instance

instance : Module R m.asDirectLimit := by
  delta asDirectLimit
  infer_instance

def _root_.Submodule.asDirectLimitToSelf : m.asDirectLimit →ₗ[R] m :=
DirectLimit.lift _ _ _ _ (fun i => Submodule.ofLe i.le) <| fun _ _ _ _ => Subtype.ext rfl

@[simp] lemma _root_.Submodule.asDirectLimitToSelf_apply_of (a : m.fgSubmodule) (i : a) :
    m.asDirectLimitToSelf (DirectLimit.of _ _ _ _ a i) = Submodule.ofLe a.le i := by
  delta asDirectLimitToSelf
  erw [DirectLimit.lift_of]

@[simps]
def _root_.Submodule.toAsDirectLimit : m →ₗ[R] m.asDirectLimit where
  toFun x := DirectLimit.of _ _ _ _ (m.principalSubmodule x) <| ⟨_, m.mem_principalSubmodule_self _⟩
  map_add' x y := by
    simp only [principalSubmodule_asSubmodule, AddSubmonoid.coe_add, coe_toAddSubmonoid]
    let n : m.fgSubmodule := m.doubletonSubmodule x y
    have le1 : m.principalSubmodule x ≤ n := m.principalSubmodule_le_doubletonSubmodule_left _ _
    have le2 : m.principalSubmodule y ≤ n := m.principalSubmodule_le_doubletonSubmodule_right _ _
    have le3 : m.principalSubmodule (x + y) ≤ n :=
      m.principalSubmodule_add_le_doubletonSubmodule _ _
    have eq1 := DirectLimit.of_f (R := R) (ι := m.fgSubmodule) (G := fun a => a.asSubmodule)
      (f := fun _ _ h => Submodule.ofLe h) (i := m.principalSubmodule x)
      (j := n) (hij := le1) (x := ⟨x, m.mem_principalSubmodule_self _⟩)
    have eq2 := DirectLimit.of_f (R := R) (ι := m.fgSubmodule) (G := fun a => a.asSubmodule)
      (f := fun _ _ h => Submodule.ofLe h) (i := m.principalSubmodule y)
      (j := n) (hij := le2) (x := ⟨y, m.mem_principalSubmodule_self _⟩)
    have eq3 := DirectLimit.of_f (R := R) (ι := m.fgSubmodule) (G := fun a => a.asSubmodule)
      (f := fun _ _ h => Submodule.ofLe h) (i := m.principalSubmodule (x + y))
      (j := n) (hij := le3) (x := ⟨x.1 + y.1, ?will_be_automatic⟩)
    simp only [doubletonSubmodule_asSubmodule, principalSubmodule_asSubmodule] at eq1 eq2 eq3
    rw [← eq1, ← eq2, ← _root_.map_add]
    exact eq3.symm
  map_smul' r x := by
    simp only [principalSubmodule_asSubmodule, SetLike.val_smul, RingHom.id_apply]
    have le1 : m.principalSubmodule (r • x) ≤ m.principalSubmodule x
    · exact m.principalSubmodule_smul_le _ _
    have eq1 := DirectLimit.of_f (R := R) (ι := m.fgSubmodule) (G := fun a => a.asSubmodule)
      (f := fun _ _ h => Submodule.ofLe h) (i := m.principalSubmodule <| r • x)
      (j := m.principalSubmodule x) (hij := le1) (x := ⟨r • x, m.mem_principalSubmodule_self _⟩)
    simp only [principalSubmodule_asSubmodule, SetLike.val_smul] at eq1
    rw [← eq1, ← LinearMap.map_smul]
    congr

@[simps!]
def _root_.Submodule.equivAsDirectLimit : m ≃ₗ[R] m.asDirectLimit :=
LinearEquiv.ofLinear m.toAsDirectLimit m.asDirectLimitToSelf
  (FunLike.ext _ _ fun x => x.induction_on fun i x => by
    rw [LinearMap.comp_apply, LinearMap.id_apply, toAsDirectLimit_apply,
      asDirectLimitToSelf_apply_of]
    exact Eq.symm <| DirectLimit.of_f (R := R) (ι := m.fgSubmodule) (G := fun a => a.asSubmodule)
      (f := fun _ _ h => Submodule.ofLe h) (i := m.principalSubmodule ⟨x.1, i.le x.2⟩) (j := i)
      (hij := Submodule.span_le.mpr <| Set.singleton_subset_iff.mpr <| x.2)
      (x := ⟨x.1, m.mem_principalSubmodule_self _⟩))
  (FunLike.ext _ _ fun _ => by
    rw [LinearMap.comp_apply, LinearMap.id_apply, toAsDirectLimit_apply,
      asDirectLimitToSelf_apply_of]
    rfl)

section

variable (N : Type u) [AddCommGroup N] [Module R N]

def _root_.Submodule.tensorProductAsDirectLimit  : Type u :=
Module.DirectLimit (R := R) (ι := m.fgSubmodule) (fun i => i.asSubmodule ⊗[R] N) <| fun _ _ h =>
  TensorProduct.map (Submodule.ofLe h) LinearMap.id

instance : AddCommGroup (m.tensorProductAsDirectLimit N) := by
  delta tensorProductAsDirectLimit
  infer_instance

instance : Module R (m.tensorProductAsDirectLimit N) := by
  delta tensorProductAsDirectLimit
  infer_instance

def _root_.Submodule.tensorProductEquiv :
    m ⊗[R] N ≃ₗ[R] m.asDirectLimit ⊗[R] N :=
  TensorProduct.congr m.equivAsDirectLimit <| LinearEquiv.refl _ _

@[simp] lemma _root_.Submodule.tensorProductEquiv_apply_tmul (x : m) (n : N) :
    m.tensorProductEquiv N (x ⊗ₜ n) =
    DirectLimit.of _ _ _ _ (m.principalSubmodule x) ⟨x, m.mem_principalSubmodule_self _⟩ ⊗ₜ n := by
  delta tensorProductEquiv
  rw [TensorProduct.congr_tmul, equivAsDirectLimit_apply]
  rfl

@[simp] lemma _root_.Submodule.tensorProductEquiv_symm_apply_tmul_of {a : m.fgSubmodule} (x : a) (n : N) :
    (m.tensorProductEquiv N).symm (DirectLimit.of _ _ _ _ a x ⊗ₜ n) =
    ⟨x, a.le x.2⟩ ⊗ₜ n := by
  delta tensorProductEquiv
  rw [TensorProduct.congr_symm_tmul, equivAsDirectLimit_symm_apply, asDirectLimitToSelf_apply_of]
  rfl

set_option maxHeartbeats 1000000 in
def _root_.Submodule.asDirectLimitTensorEquiv :
    m.asDirectLimit ⊗[R] N ≃ₗ[R]
    m.tensorProductAsDirectLimit N :=
  (Module.directLimitCommutesTensorProduct (R := R) (ι := m.fgSubmodule)
    (G := fun a => a.asSubmodule) (f := fun _ _ h => Submodule.ofLe h) N).symm

example : true := rfl

set_option maxHeartbeats 1000000 in
lemma _root_.Submodule.asDirectLimitTensorEquiv_apply_of_tmul {a : m.fgSubmodule} (x : a) (n : N) :
    m.asDirectLimitTensorEquiv N (DirectLimit.of _ _ _ _ a x ⊗ₜ n) =
    DirectLimit.of _ _ _ _ a (x ⊗ₜ n) := by
  have EQ1 : _ = _ :=
    Module.directLimitCommutesTensorProduct_symm_apply (R := R) (ι := m.fgSubmodule)
      (G := fun a => a.asSubmodule) (f := fun _ _ h => Submodule.ofLe h) N
      (DirectLimit.of _ _ _ _ a x ⊗ₜ n)
  rw [tensorProductWithDirectLimitToDirectLimitOfTensorProduct_apply_of_tmul] at EQ1
  exact EQ1

example : true := rfl

set_option maxHeartbeats 1000000 in
lemma _root_.Submodule.asDirectLimitTensorEquiv_symm_apply_of_tmul {a : m.fgSubmodule}
    (x : a) (n : N) :
    (m.asDirectLimitTensorEquiv N).symm (DirectLimit.of _ _ _ _ a (x ⊗ₜ n)) =
    DirectLimit.of _ _ _ _ a x ⊗ₜ n := by
  have EQ1 : _ = _ :=
    Module.directLimitOfTensorProductToTensorProductWithDirectLimit_apply_of_tmul
      (R := R) (ι := m.fgSubmodule) (G := fun a => a.asSubmodule)
      (f := fun _ _ h => Submodule.ofLe h) (g := x) (m := n)
  exact EQ1

example : true := rfl

def _root_.Submodule.tensorProductEquivDirectLimit :
    m ⊗[R] N ≃ₗ[R] m.tensorProductAsDirectLimit N :=
  m.tensorProductEquiv N ≪≫ₗ m.asDirectLimitTensorEquiv N

example : true := rfl

lemma _root_.Submodule.tensorProductEquivDirectLimit_apply_tmul (x : m) (n : N) :
    m.tensorProductEquivDirectLimit N (x ⊗ₜ n) =
    DirectLimit.of _ _ _ _ (m.principalSubmodule x)
      (⟨x, m.mem_principalSubmodule_self _⟩ ⊗ₜ n) := by
  delta tensorProductEquivDirectLimit
  rw [LinearEquiv.trans_apply, tensorProductEquiv_apply_tmul,
    asDirectLimitTensorEquiv_apply_of_tmul]

lemma _root_.Submodule.tensorProductEquivDirectLimit_symm_apply_of {a : m.fgSubmodule}
    (x : a) (n : N) :
    (m.tensorProductEquivDirectLimit N).symm (DirectLimit.of _ _ _ _ a (x ⊗ₜ n)) =
    ⟨_, a.le x.2⟩ ⊗ₜ n := by
  delta tensorProductEquivDirectLimit
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    asDirectLimitTensorEquiv_symm_apply_of_tmul,
    tensorProductEquiv_symm_apply_tmul_of]

end

lemma key_identity (I : Ideal R) [DecidableEq I.fgSubmodule] :
    TensorProduct.lift ((lsmul R M).comp I.subtype) =
    DirectLimit.lift _ _ _ _
      (fun i => TensorProduct.lift <| (lsmul R M).comp i.asSubmodule.subtype) (fun i j h x =>
        x.induction_on
          (by simp only [LinearMap.map_zero])
          (fun a m => by
            simp only [TensorProduct.map_tmul, TensorProduct.lift.tmul,
              LinearMap.comp_apply]
            congr)
          (fun _ _ hx hy => by
            dsimp only at hx hy ⊢
            simp only [_root_.map_add, hx, hy])) ∘ₗ
    (I.tensorProductEquivDirectLimit M).toLinearMap :=
  TensorProduct.ext <| FunLike.ext _ _ fun a => FunLike.ext _ _ fun m => by
    simp only [compr₂_apply, mk_apply, lift.tmul, LinearMap.coe_comp, coeSubtype,
      Function.comp_apply, lsmul_apply]
    erw [tensorProductEquivDirectLimit_apply_tmul]
    simp_rw [DirectLimit.lift_of]
    rw [TensorProduct.lift.tmul]
    rfl

lemma main (fg_ideal : Flat.fg_ideal R M) : Flat.ideal R M := by
  intro I
  classical
  rw [key_identity, LinearMap.coe_comp]
  exact Function.Injective.comp
    (hf:= LinearEquiv.injective _)
    (hg := Module.lift_inj _ _ _ _ _ _ fun i => fg_ideal i.fg)

end ideal_of_fg_ideal

lemma ideal_of_fg_ideal (fg_ideal : Flat.fg_ideal R M) : Flat.ideal R M :=
  ideal_of_fg_ideal.main fg_ideal

lemma tfae : List.TFAE
    [ Flat.injective R M,
      Flat.ideal R M,
      Flat.fg_ideal R M ] := by
  tfae_have 2 → 1
  · apply injective_of_ideal
  tfae_have 1 → 2
  · intro H I
    specialize H (ModuleCat.ofHom (R := R) (X := I) (Y := R) <| Submodule.subtype _)
      (Submodule.injective_subtype _)
    intro x y h
    apply H
    simp only [tensorRight_obj, tensorRight_map]
    change TensorProduct.map _ LinearMap.id _ =
      TensorProduct.map _ LinearMap.id _
    apply_fun TensorProduct.lid R M using LinearEquiv.injective _
    change ((TensorProduct.lid _ _).toLinearMap ∘ₗ _) x =
      ((TensorProduct.lid _ _).toLinearMap ∘ₗ _) _
    convert h <;>
    · refine TensorProduct.ext ?_
      ext i m : 2
      simp only [compr₂_apply, mk_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, lift.tmul, coeSubtype, lsmul_apply]
      rfl
  tfae_have 2 → 3
  · intro H I _
    exact H I
  tfae_have 3 → 2
  · apply Module.Flat.ideal_of_fg_ideal
  tfae_finish

end Flat

end Module
