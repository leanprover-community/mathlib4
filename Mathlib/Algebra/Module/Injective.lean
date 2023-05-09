/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebra.module.injective
! leanprover-community/mathlib commit f8d8465c3c392a93b9ed226956e26dee00975946
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Preadditive.Injective
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.LinearAlgebra.LinearPmap

/-!
# Injective modules

## Main definitions

* `module.injective`: an `R`-module `Q` is injective if and only if every injective `R`-linear
  map descends to a linear map to `Q`, i.e. in the following diagram, if `f` is injective then there
  is an `R`-linear map `h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
* `module.Baer`: an `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an
  `ideal R` extends to an `R`-linear map `R ⟶ Q`

## Main statements

* `module.Baer.criterion`: an `R`-module is injective if it is Baer.

-/


noncomputable section

universe u v

variable (R : Type u) [Ring R] (Q : Type max u v) [AddCommGroup Q] [Module R Q]

/--
An `R`-module `Q` is injective if and only if every injective `R`-linear map descends to a linear
map to `Q`, i.e. in the following diagram, if `f` is injective then there is an `R`-linear map
`h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
-/
class Module.Injective : Prop where
  out :
    ∀ (X Y : Type max u v) [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
      (f : X →ₗ[R] Y) (hf : Function.Injective f) (g : X →ₗ[R] Q),
      ∃ h : Y →ₗ[R] Q, ∀ x, h (f x) = g x
#align module.injective Module.Injective

theorem Module.injective_object_of_injective_module [Module.Injective.{u, v} R Q] :
    CategoryTheory.Injective.{max u v} (⟨Q⟩ : ModuleCat.{max u v} R) :=
  {
    Factors := fun X Y g f mn =>
      by
      rcases Module.Injective.out X Y f ((ModuleCat.mono_iff_injective f).mp mn) g with ⟨h, eq1⟩
      exact ⟨h, LinearMap.ext eq1⟩ }
#align module.injective_object_of_injective_module Module.injective_object_of_injective_module

theorem Module.injective_module_of_injective_object
    [CategoryTheory.Injective.{max u v} (⟨Q⟩ : ModuleCat.{max u v} R)] :
    Module.Injective.{u, v} R Q :=
  {
    out := fun X Y ins1 ins2 ins3 ins4 f hf g => by
      skip
      rcases@CategoryTheory.Injective.factors (ModuleCat R) _ ⟨Q⟩ _ ⟨X⟩ ⟨Y⟩ g f
          ((ModuleCat.mono_iff_injective _).mpr hf) with
        ⟨h, rfl⟩
      exact ⟨h, fun x => rfl⟩ }
#align module.injective_module_of_injective_object Module.injective_module_of_injective_object

theorem Module.injective_iff_injective_object :
    Module.Injective.{u, v} R Q ↔
      CategoryTheory.Injective.{max u v} (⟨Q⟩ : ModuleCat.{max u v} R) :=
  ⟨fun h => @Module.injective_object_of_injective_module R _ Q _ _ h, fun h =>
    @Module.injective_module_of_injective_object R _ Q _ _ h⟩
#align module.injective_iff_injective_object Module.injective_iff_injective_object

/-- An `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `ideal R` extends to
an `R`-linear map `R ⟶ Q`-/
def Module.Baer : Prop :=
  ∀ (I : Ideal R) (g : I →ₗ[R] Q), ∃ g' : R →ₗ[R] Q, ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩
#align module.Baer Module.Baer

namespace Module.Baer

variable {R Q} {M N : Type max u v} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

/-- If we view `M` as a submodule of `N` via the injective linear map `i : M ↪ N`, then a submodule
between `M` and `N` is a submodule `N'` of `N`. To prove Baer's criterion, we need to consider
pairs of `(N', f')` such that `M ≤ N' ≤ N` and `f'` extends `f`. -/
structure ExtensionOf extends LinearPMap R N Q where
  le : i.range ≤ domain
  is_extension : ∀ m : M, f m = to_linear_pmap ⟨i m, le ⟨m, rfl⟩⟩
#align module.Baer.extension_of Module.Baer.ExtensionOf

section Ext

variable {i f}

@[ext]
theorem ExtensionOf.ext {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
    (to_fun_eq :
      ∀ ⦃x : a.domain⦄ ⦃y : b.domain⦄, (x : N) = y → a.toLinearPMap x = b.toLinearPMap y) :
    a = b := by
  rcases a with ⟨a, a_le, e1⟩
  rcases b with ⟨b, b_le, e2⟩
  congr
  exact LinearPMap.ext domain_eq to_fun_eq
#align module.Baer.extension_of.ext Module.Baer.ExtensionOf.ext

theorem ExtensionOf.ext_iff {a b : ExtensionOf i f} :
    a = b ↔
      ∃ domain_eq : a.domain = b.domain,
        ∀ ⦃x : a.domain⦄ ⦃y : b.domain⦄, (x : N) = y → a.toLinearPMap x = b.toLinearPMap y :=
  ⟨fun r => r ▸ ⟨rfl, fun x y h => congr_arg a.toFun <| by exact_mod_cast h⟩, fun ⟨h1, h2⟩ =>
    ExtensionOf.ext h1 h2⟩
#align module.Baer.extension_of.ext_iff Module.Baer.ExtensionOf.ext_iff

end Ext

instance : Inf (ExtensionOf i f)
    where inf X1 X2 :=
    {
      X1.toLinearPMap ⊓
        X2.toLinearPMap with
      le := fun x hx =>
        (by
          rcases hx with ⟨x, rfl⟩
          refine' ⟨X1.le (Set.mem_range_self _), X2.le (Set.mem_range_self _), _⟩
          rw [← X1.is_extension x, ← X2.is_extension x] :
          x ∈ X1.toLinearPMap.eqLocus X2.toLinearPMap)
      is_extension := fun m => X1.is_extension _ }

instance : SemilatticeInf (ExtensionOf i f) :=
  Function.Injective.semilatticeInf ExtensionOf.toLinearPmap
    (fun X Y h =>
      ExtensionOf.ext (by rw [h]) fun x y h' =>
        by
        induction h
        congr
        exact_mod_cast h')
    fun X Y =>
    LinearPMap.ext rfl fun x y h => by
      congr
      exact_mod_cast h

variable {R i f}

theorem chain_linearPMap_of_chain_extensionOf {c : Set (ExtensionOf i f)}
    (hchain : IsChain (· ≤ ·) c) :
    IsChain (· ≤ ·) <| (fun x : ExtensionOf i f => x.toLinearPMap) '' c :=
  by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ neq
  exact hchain a_mem b_mem (ne_of_apply_ne _ neq)
#align module.Baer.chain_linear_pmap_of_chain_extension_of Module.Baer.chain_linearPMap_of_chain_extensionOf

/-- The maximal element of every nonempty chain of `extension_of i f`. -/
def ExtensionOf.max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) : ExtensionOf i f :=
  {
    LinearPMap.supₛ _
      (IsChain.directedOn <|
        chain_linearPMap_of_chain_extensionOf
          hchain) with
    le :=
      le_trans hnonempty.some.le <|
        (LinearPMap.le_supₛ _ <|
            (Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩).1
    is_extension := fun m =>
      by
      refine' Eq.trans (hnonempty.some.is_extension m) _
      symm
      generalize_proofs _ h0 h1
      exact
        LinearPMap.supₛ_apply (IsChain.directedOn <| chain_linear_pmap_of_chain_extension_of hchain)
          ((Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.some_spec, rfl⟩) ⟨i m, h1⟩ }
#align module.Baer.extension_of.max Module.Baer.ExtensionOf.max

theorem ExtensionOf.le_max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) (a : ExtensionOf i f) (ha : a ∈ c) :
    a ≤ ExtensionOf.max hchain hnonempty :=
  LinearPMap.le_supₛ (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) <|
    (Set.mem_image _ _ _).mpr ⟨a, ha, rfl⟩
#align module.Baer.extension_of.le_max Module.Baer.ExtensionOf.le_max

variable (i f) [Fact <| Function.Injective i]

instance ExtensionOf.inhabited : Inhabited (ExtensionOf i f)
    where default :=
    { domain := i.range
      toFun :=
        { toFun := fun x => f x.2.some
          map_add' := fun x y =>
            by
            have eq1 : _ + _ = (x + y).1 := congr_arg₂ (· + ·) x.2.choose_spec y.2.choose_spec
            rw [← map_add, ← (x + y).2.choose_spec] at eq1
            rw [← Fact.out (Function.Injective i) eq1, map_add]
          map_smul' := fun r x =>
            by
            have eq1 : r • _ = (r • x).1 := congr_arg ((· • ·) r) x.2.choose_spec
            rw [← LinearMap.map_smul, ← (r • x).2.choose_spec] at eq1
            rw [RingHom.id_apply, ← Fact.out (Function.Injective i) eq1, LinearMap.map_smul] }
      le := le_refl _
      is_extension := fun m =>
        by
        simp only [LinearPMap.mk_apply, LinearMap.coe_mk]
        congr
        exact Fact.out (Function.Injective i) (⟨i m, ⟨_, rfl⟩⟩ : i.range).2.choose_spec.symm }
#align module.Baer.extension_of.inhabited Module.Baer.ExtensionOf.inhabited

/-- Since every nonempty chain has a maximal element, by Zorn's lemma, there is a maximal
`extension_of i f`. -/
def extensionOfMax : ExtensionOf i f :=
  (@zorn_nonempty_partialOrder (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun c hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).some
#align module.Baer.extension_of_max Module.Baer.extensionOfMax

theorem extensionOfMax_is_max :
    ∀ a : ExtensionOf i f, extensionOfMax i f ≤ a → a = extensionOfMax i f :=
  (@zorn_nonempty_partialOrder (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun c hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose_spec
#align module.Baer.extension_of_max_is_max Module.Baer.extensionOfMax_is_max

variable {f}

private theorem extension_of_max_adjoin.aux1 {y : N}
    (x : (extensionOfMax i f).domain ⊔ Submodule.span R {y}) :
    ∃ (a : (extensionOfMax i f).domain)(b : R), x.1 = a.1 + b • y :=
  by
  have mem1 : x.1 ∈ (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, b, a_mem, b_mem : b ∈ (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩
#align module.Baer.extension_of_max_adjoin.aux1 module.Baer.extension_of_max_adjoin.aux1

/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `fst` pick an arbitrary such `m`.-/
def ExtensionOfMaxAdjoin.fst {y : N} (x : (extensionOfMax i f).domain ⊔ Submodule.span R {y}) :
    (extensionOfMax i f).domain :=
  (ExtensionOfMaxAdjoin.aux1 i x).some
#align module.Baer.extension_of_max_adjoin.fst Module.Baer.ExtensionOfMaxAdjoin.fst

/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `snd` pick an arbitrary such `r`.-/
def ExtensionOfMaxAdjoin.snd {y : N} (x : (extensionOfMax i f).domain ⊔ Submodule.span R {y}) : R :=
  (ExtensionOfMaxAdjoin.aux1 i x).choose_spec.some
#align module.Baer.extension_of_max_adjoin.snd Module.Baer.ExtensionOfMaxAdjoin.snd

theorem ExtensionOfMaxAdjoin.eqn {y : N} (x : (extensionOfMax i f).domain ⊔ Submodule.span R {y}) :
    ↑x = ↑(ExtensionOfMaxAdjoin.fst i x) + ExtensionOfMaxAdjoin.snd i x • y :=
  (ExtensionOfMaxAdjoin.aux1 i x).choose_spec.choose_spec
#align module.Baer.extension_of_max_adjoin.eqn Module.Baer.ExtensionOfMaxAdjoin.eqn

variable (f)

/-- the ideal `I = {r | r • y ∈ N}`-/
def ExtensionOfMaxAdjoin.ideal (y : N) : Ideal R :=
  (extensionOfMax i f).domain.comap ((LinearMap.id : R →ₗ[R] R).smul_right y)
#align module.Baer.extension_of_max_adjoin.ideal Module.Baer.ExtensionOfMaxAdjoin.ideal

/-- A linear map `I ⟶ Q` by `x ↦ f' (x • y)` where `f'` is the maximal extension-/
def ExtensionOfMaxAdjoin.idealTo (y : N) : ExtensionOfMaxAdjoin.ideal i f y →ₗ[R] Q
    where
  toFun z := (extensionOfMax i f).toLinearPMap ⟨(↑z : R) • y, z.Prop⟩
  map_add' z1 z2 := by simp [← (extension_of_max i f).toLinearPMap.map_add, add_smul]
  map_smul' z1 z2 := by simp [← (extension_of_max i f).toLinearPMap.map_smul, mul_smul] <;> rfl
#align module.Baer.extension_of_max_adjoin.ideal_to Module.Baer.ExtensionOfMaxAdjoin.idealTo

/-- Since we assumed `Q` being Baer, the linear map `x ↦ f' (x • y) : I ⟶ Q` extends to `R ⟶ Q`,
call this extended map `φ`-/
def ExtensionOfMaxAdjoin.extendIdealTo (h : Module.Baer R Q) (y : N) : R →ₗ[R] Q :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).some
#align module.Baer.extension_of_max_adjoin.extend_ideal_to Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo

theorem ExtensionOfMaxAdjoin.extendIdealTo_is_extension (h : Module.Baer R Q) (y : N) :
    ∀ (x : R) (mem : x ∈ ExtensionOfMaxAdjoin.ideal i f y),
      ExtensionOfMaxAdjoin.extendIdealTo i f h y x = ExtensionOfMaxAdjoin.idealTo i f y ⟨x, mem⟩ :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose_spec
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_is_extension Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_is_extension

theorem ExtensionOfMaxAdjoin.extendIdealTo_wd' (h : Module.Baer R Q) {y : N} (r : R)
    (eq1 : r • y = 0) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r = 0 :=
  by
  rw [extension_of_max_adjoin.extend_ideal_to_is_extension i f h y r
      (by rw [eq1] <;> exact Submodule.zero_mem _ : r • y ∈ _)]
  simp only [extension_of_max_adjoin.ideal_to, LinearMap.coe_mk, eq1, Subtype.coe_mk, ←
    ZeroMemClass.zero_def, (extension_of_max i f).toLinearPMap.map_zero]
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_wd' Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd'

theorem ExtensionOfMaxAdjoin.extendIdealTo_wd (h : Module.Baer R Q) {y : N} (r r' : R)
    (eq1 : r • y = r' • y) :
    ExtensionOfMaxAdjoin.extendIdealTo i f h y r = ExtensionOfMaxAdjoin.extendIdealTo i f h y r' :=
  by
  rw [← sub_eq_zero, ← map_sub]
  convert extension_of_max_adjoin.extend_ideal_to_wd' i f h (r - r') _
  rw [sub_smul, sub_eq_zero, eq1]
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_wd Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd

theorem ExtensionOfMaxAdjoin.extendIdealTo_eq (h : Module.Baer R Q) {y : N} (r : R)
    (hr : r • y ∈ (extensionOfMax i f).domain) :
    ExtensionOfMaxAdjoin.extendIdealTo i f h y r = (extensionOfMax i f).toLinearPMap ⟨r • y, hr⟩ :=
  by
  simp only [extension_of_max_adjoin.extend_ideal_to_is_extension i f h _ _ hr,
    extension_of_max_adjoin.ideal_to, LinearMap.coe_mk, Subtype.coe_mk]
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_eq Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_eq

/-- We can finally define a linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r`
-/
def ExtensionOfMaxAdjoin.extensionToFun (h : Module.Baer R Q) {y : N} :
    (extensionOfMax i f).domain ⊔ Submodule.span R {y} → Q := fun x =>
  (extensionOfMax i f).toLinearPMap (ExtensionOfMaxAdjoin.fst i x) +
    ExtensionOfMaxAdjoin.extendIdealTo i f h y (ExtensionOfMaxAdjoin.snd i x)
#align module.Baer.extension_of_max_adjoin.extension_to_fun Module.Baer.ExtensionOfMaxAdjoin.extensionToFun

theorem ExtensionOfMaxAdjoin.extensionToFun_wd (h : Module.Baer R Q) {y : N}
    (x : (extensionOfMax i f).domain ⊔ Submodule.span R {y}) (a : (extensionOfMax i f).domain)
    (r : R) (eq1 : ↑x = ↑a + r • y) :
    ExtensionOfMaxAdjoin.extensionToFun i f h x =
      (extensionOfMax i f).toLinearPMap a + ExtensionOfMaxAdjoin.extendIdealTo i f h y r :=
  by
  cases' a with a ha
  rw [Subtype.coe_mk] at eq1
  have eq2 :
    (extension_of_max_adjoin.fst i x - a : N) = (r - extension_of_max_adjoin.snd i x) • y := by
    rwa [extension_of_max_adjoin.eqn, ← sub_eq_zero, ← sub_sub_sub_eq, sub_eq_zero, ← sub_smul] at
      eq1
  have eq3 :=
    extension_of_max_adjoin.extend_ideal_to_eq i f h (r - extension_of_max_adjoin.snd i x)
      (by rw [← eq2] <;> exact Submodule.sub_mem _ (extension_of_max_adjoin.fst i x).2 ha)
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3
  unfold extension_of_max_adjoin.extension_to_fun
  rw [eq3, ← add_assoc, ← (extension_of_max i f).toLinearPMap.map_add, AddMemClass.mk_add_mk]
  congr
  ext
  rw [Subtype.coe_mk, add_sub, ← eq1]
  exact eq_sub_of_add_eq (extension_of_max_adjoin.eqn _ _).symm
#align module.Baer.extension_of_max_adjoin.extension_to_fun_wd Module.Baer.ExtensionOfMaxAdjoin.extensionToFun_wd

/-- The linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r` is an extension of `f`-/
def extensionOfMaxAdjoin (h : Module.Baer R Q) (y : N) : ExtensionOf i f
    where
  domain := (extensionOfMax i f).domain ⊔ Submodule.span R {y}
  le := le_trans (extensionOfMax i f).le le_sup_left
  toFun :=
    { toFun := ExtensionOfMaxAdjoin.extensionToFun i f h
      map_add' := fun a b =>
        by
        have eq1 :
          ↑a + ↑b =
            ↑(extension_of_max_adjoin.fst i a + extension_of_max_adjoin.fst i b) +
              (extension_of_max_adjoin.snd i a + extension_of_max_adjoin.snd i b) • y :=
          by
          rw [extension_of_max_adjoin.eqn, extension_of_max_adjoin.eqn, add_smul]
          abel
        rw [extension_of_max_adjoin.extension_to_fun_wd i f h (a + b) _ _ eq1, LinearPMap.map_add,
          map_add]
        unfold extension_of_max_adjoin.extension_to_fun
        abel
      map_smul' := fun r a => by
        rw [RingHom.id_apply]
        have eq1 :
          r • ↑a =
            ↑(r • extension_of_max_adjoin.fst i a) + (r • extension_of_max_adjoin.snd i a) • y :=
          by
          rw [extension_of_max_adjoin.eqn, smul_add, smul_eq_mul, mul_smul]
          rfl
        rw [extension_of_max_adjoin.extension_to_fun_wd i f h (r • a) _ _ eq1, LinearMap.map_smul,
          LinearPMap.map_smul, ← smul_add]
        congr }
  is_extension m := by
    simp only [LinearPMap.mk_apply, LinearMap.coe_mk]
    rw [(extension_of_max i f).is_extension,
      extension_of_max_adjoin.extension_to_fun_wd i f h _ ⟨i m, _⟩ 0 _, map_zero, add_zero]
    simp
#align module.Baer.extension_of_max_adjoin Module.Baer.extensionOfMaxAdjoin

theorem extensionOfMax_le (h : Module.Baer R Q) {y : N} :
    extensionOfMax i f ≤ extensionOfMaxAdjoin i f h y :=
  ⟨le_sup_left, fun x x' EQ => by
    symm
    change extension_of_max_adjoin.extension_to_fun i f h _ = _
    rw [extension_of_max_adjoin.extension_to_fun_wd i f h x' x 0 (by simp [EQ]), map_zero,
      add_zero]⟩
#align module.Baer.extension_of_max_le Module.Baer.extensionOfMax_le

theorem extensionOfMax_to_submodule_eq_top (h : Module.Baer R Q) :
    (extensionOfMax i f).domain = ⊤ :=
  by
  refine' submodule.eq_top_iff'.mpr fun y => _
  rw [← extension_of_max_is_max i f _ (extension_of_max_le i f h), extension_of_max_adjoin,
    Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩
#align module.Baer.extension_of_max_to_submodule_eq_top Module.Baer.extensionOfMax_to_submodule_eq_top

/-- **Baer's criterion** for injective module : a Baer module is an injective module, i.e. if every
linear map from an ideal can be extended, then the module is injective.-/
protected theorem injective (h : Module.Baer R Q) : Module.Injective R Q :=
  {
    out := fun X Y ins1 ins2 ins3 ins4 i hi f =>
      haveI : Fact (Function.Injective i) := ⟨hi⟩
      ⟨{  toFun := fun y =>
            (extension_of_max i f).toLinearPMap
              ⟨y, (extension_of_max_to_submodule_eq_top i f h).symm ▸ trivial⟩
          map_add' := fun x y => by
            rw [← LinearPMap.map_add]
            congr
          map_smul' := fun r x => by
            rw [← LinearPMap.map_smul]
            congr },
        fun x => ((extension_of_max i f).is_extension x).symm⟩ }
#align module.Baer.injective Module.Baer.injective

end Module.Baer

