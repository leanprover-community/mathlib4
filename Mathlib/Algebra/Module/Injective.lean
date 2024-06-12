/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Logic.Equiv.TransferInstance

#align_import algebra.module.injective from "leanprover-community/mathlib"@"f8d8465c3c392a93b9ed226956e26dee00975946"

/-!
# Injective modules

## Main definitions

* `Module.Injective`: an `R`-module `Q` is injective if and only if every injective `R`-linear
  map descends to a linear map to `Q`, i.e. in the following diagram, if `f` is injective then there
  is an `R`-linear map `h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
* `Module.Baer`: an `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an
  `Ideal R` extends to an `R`-linear map `R ⟶ Q`

## Main statements

* `Module.Baer.injective`: an `R`-module is injective if it is Baer.

-/


noncomputable section

universe u v v'

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

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
@[mk_iff] class Module.Injective : Prop where
  out : ∀ ⦃X Y : Type v⦄ [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (f : X →ₗ[R] Y) (_ : Function.Injective f) (g : X →ₗ[R] Q),
    ∃ h : Y →ₗ[R] Q, ∀ x, h (f x) = g x
#align module.injective Module.Injective

theorem Module.injective_object_of_injective_module [inj : Module.Injective R Q] :
    CategoryTheory.Injective (ModuleCat.of R Q) where
  factors g f m :=
    have ⟨l, h⟩ := inj.out f ((ModuleCat.mono_iff_injective f).mp m) g
    ⟨l, LinearMap.ext h⟩
#align module.injective_object_of_injective_module Module.injective_object_of_injective_module

theorem Module.injective_module_of_injective_object
    [inj : CategoryTheory.Injective <| ModuleCat.of R Q] :
    Module.Injective R Q where
  out X Y _ _ _ _ f hf g := by
    have : CategoryTheory.Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
    obtain ⟨l, rfl⟩ := inj.factors (ModuleCat.ofHom g) (ModuleCat.ofHom f)
    exact ⟨l, fun _ ↦ rfl⟩
#align module.injective_module_of_injective_object Module.injective_module_of_injective_object

theorem Module.injective_iff_injective_object :
    Module.Injective R Q ↔
    CategoryTheory.Injective (ModuleCat.of R Q) :=
  ⟨fun _ => injective_object_of_injective_module R Q,
   fun _ => injective_module_of_injective_object R Q⟩
#align module.injective_iff_injective_object Module.injective_iff_injective_object

/-- An `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `Ideal R` extends to
an `R`-linear map `R ⟶ Q`-/
def Module.Baer : Prop :=
  ∀ (I : Ideal R) (g : I →ₗ[R] Q), ∃ g' : R →ₗ[R] Q, ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩
set_option linter.uppercaseLean3 false in
#align module.Baer Module.Baer

namespace Module.Baer

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

/-- If we view `M` as a submodule of `N` via the injective linear map `i : M ↪ N`, then a submodule
between `M` and `N` is a submodule `N'` of `N`. To prove Baer's criterion, we need to consider
pairs of `(N', f')` such that `M ≤ N' ≤ N` and `f'` extends `f`. -/
structure ExtensionOf extends LinearPMap R N Q where
  le : LinearMap.range i ≤ domain
  is_extension : ∀ m : M, f m = toLinearPMap ⟨i m, le ⟨m, rfl⟩⟩
set_option linter.uppercaseLean3 false in
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
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of.ext Module.Baer.ExtensionOf.ext

theorem ExtensionOf.ext_iff {a b : ExtensionOf i f} :
    a = b ↔ ∃ _ : a.domain = b.domain, ∀ ⦃x : a.domain⦄ ⦃y : b.domain⦄,
    (x : N) = y → a.toLinearPMap x = b.toLinearPMap y :=
  ⟨fun r => r ▸ ⟨rfl, fun _ _ h => congr_arg a.toFun <| mod_cast h⟩, fun ⟨h1, h2⟩ =>
    ExtensionOf.ext h1 h2⟩
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of.ext_iff Module.Baer.ExtensionOf.ext_iff

end Ext

instance : Inf (ExtensionOf i f) where
  inf X1 X2 :=
    { X1.toLinearPMap ⊓
        X2.toLinearPMap with
      le := fun x hx =>
        (by
          rcases hx with ⟨x, rfl⟩
          refine ⟨X1.le (Set.mem_range_self _), X2.le (Set.mem_range_self _), ?_⟩
          rw [← X1.is_extension x, ← X2.is_extension x] :
          x ∈ X1.toLinearPMap.eqLocus X2.toLinearPMap)
      is_extension := fun m => X1.is_extension _ }

instance : SemilatticeInf (ExtensionOf i f) :=
  Function.Injective.semilatticeInf ExtensionOf.toLinearPMap
    (fun X Y h =>
      ExtensionOf.ext (by rw [h]) fun x y h' => by
        -- Porting note: induction didn't handle dependent rw like in Lean 3
        have : {x y : N} → (h'' : x = y) → (hx : x ∈ X.toLinearPMap.domain) →
          (hy : y ∈ Y.toLinearPMap.domain) → X.toLinearPMap ⟨x,hx⟩ = Y.toLinearPMap ⟨y,hy⟩ := by
            rw [h]
            intro _ _ h _ _
            congr
        apply this h' _ _)
    fun X Y =>
    LinearPMap.ext rfl fun x y h => by
      congr
      exact mod_cast h

variable {i f}

theorem chain_linearPMap_of_chain_extensionOf {c : Set (ExtensionOf i f)}
    (hchain : IsChain (· ≤ ·) c) :
    IsChain (· ≤ ·) <| (fun x : ExtensionOf i f => x.toLinearPMap) '' c := by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ neq
  exact hchain a_mem b_mem (ne_of_apply_ne _ neq)
set_option linter.uppercaseLean3 false in
#align module.Baer.chain_linear_pmap_of_chain_extension_of Module.Baer.chain_linearPMap_of_chain_extensionOf

/-- The maximal element of every nonempty chain of `extension_of i f`. -/
def ExtensionOf.max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) : ExtensionOf i f :=
  { LinearPMap.sSup _
      (IsChain.directedOn <|
        chain_linearPMap_of_chain_extensionOf
          hchain) with
    le := by
      refine le_trans hnonempty.some.le <|
        (LinearPMap.le_sSup _ <|
            (Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩).1
    is_extension := fun m => by
      refine Eq.trans (hnonempty.some.is_extension m) ?_
      symm
      generalize_proofs _ h1
      exact
        LinearPMap.sSup_apply (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain)
          ((Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩) ⟨i m, h1⟩ }
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of.max Module.Baer.ExtensionOf.max

theorem ExtensionOf.le_max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) (a : ExtensionOf i f) (ha : a ∈ c) :
    a ≤ ExtensionOf.max hchain hnonempty :=
  LinearPMap.le_sSup (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) <|
    (Set.mem_image _ _ _).mpr ⟨a, ha, rfl⟩
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of.le_max Module.Baer.ExtensionOf.le_max

variable (i f) [Fact <| Function.Injective i]

instance ExtensionOf.inhabited : Inhabited (ExtensionOf i f) where
  default :=
    { domain := LinearMap.range i
      toFun :=
        { toFun := fun x => f x.2.choose
          map_add' := fun x y => by
            have eq1 : _ + _ = (x + y).1 := congr_arg₂ (· + ·) x.2.choose_spec y.2.choose_spec
            rw [← map_add, ← (x + y).2.choose_spec] at eq1
            dsimp
            rw [← Fact.out (p := Function.Injective i) eq1, map_add]
          map_smul' := fun r x => by
            have eq1 : r • _ = (r • x).1 := congr_arg (r • ·) x.2.choose_spec
            rw [← LinearMap.map_smul, ← (r • x).2.choose_spec] at eq1
            dsimp
            rw [← Fact.out (p := Function.Injective i) eq1, LinearMap.map_smul] }
      le := le_refl _
      is_extension := fun m => by
        simp only [LinearPMap.mk_apply, LinearMap.coe_mk]
        dsimp
        apply congrArg
        exact Fact.out (p := Function.Injective i)
          (⟨i m, ⟨_, rfl⟩⟩ : LinearMap.range i).2.choose_spec.symm }
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of.inhabited Module.Baer.ExtensionOf.inhabited

/-- Since every nonempty chain has a maximal element, by Zorn's lemma, there is a maximal
`extension_of i f`. -/
def extensionOfMax : ExtensionOf i f :=
  (@zorn_nonempty_partialOrder (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max Module.Baer.extensionOfMax

theorem extensionOfMax_is_max :
    ∀ a : ExtensionOf i f, extensionOfMax i f ≤ a → a = extensionOfMax i f :=
  (@zorn_nonempty_partialOrder (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose_spec
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_is_max Module.Baer.extensionOfMax_is_max

-- Porting note: helper function. Lean looks for an instance of `Sup (Type u)` when the
-- right hand side is substituted in directly
abbrev supExtensionOfMaxSingleton (y : N) : Submodule R N :=
  (extensionOfMax i f).domain ⊔ (Submodule.span R {y})

variable {f}

private theorem extensionOfMax_adjoin.aux1 {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ∃ (a : (extensionOfMax i f).domain) (b : R), x.1 = a.1 + b • y := by
  have mem1 : x.1 ∈ (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b ∈ (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩
set_option align.precheck false in
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.aux1 Module.Baer.extensionOfMax_adjoin.aux1

/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `fst` pick an arbitrary such `m`. -/
def ExtensionOfMaxAdjoin.fst {y : N} (x : supExtensionOfMaxSingleton i f y) :
    (extensionOfMax i f).domain :=
  (extensionOfMax_adjoin.aux1 i x).choose
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.fst Module.Baer.ExtensionOfMaxAdjoin.fst

/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `snd` pick an arbitrary such `r`. -/
def ExtensionOfMaxAdjoin.snd {y : N} (x : supExtensionOfMaxSingleton i f y) : R :=
  (extensionOfMax_adjoin.aux1 i x).choose_spec.choose
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.snd Module.Baer.ExtensionOfMaxAdjoin.snd

theorem ExtensionOfMaxAdjoin.eqn {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ↑x = ↑(ExtensionOfMaxAdjoin.fst i x) + ExtensionOfMaxAdjoin.snd i x • y :=
  (extensionOfMax_adjoin.aux1 i x).choose_spec.choose_spec
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.eqn Module.Baer.ExtensionOfMaxAdjoin.eqn

variable (f)

-- TODO: refactor to use colon ideals?
/-- The ideal `I = {r | r • y ∈ N}`-/
def ExtensionOfMaxAdjoin.ideal (y : N) : Ideal R :=
  (extensionOfMax i f).domain.comap ((LinearMap.id : R →ₗ[R] R).smulRight y)
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.ideal Module.Baer.ExtensionOfMaxAdjoin.ideal

/-- A linear map `I ⟶ Q` by `x ↦ f' (x • y)` where `f'` is the maximal extension-/
def ExtensionOfMaxAdjoin.idealTo (y : N) : ExtensionOfMaxAdjoin.ideal i f y →ₗ[R] Q where
  toFun (z : { x // x ∈ ideal i f y }) := (extensionOfMax i f).toLinearPMap ⟨(↑z : R) • y, z.prop⟩
  map_add' (z1 z2 : { x // x ∈ ideal i f y }) := by
    -- Porting note: a single simp took care of the goal before reenableeta
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_add]
    congr
    apply add_smul
  map_smul' z1 (z2 : {x // x ∈ ideal i f y}) := by
    -- Porting note: a single simp took care of the goal before reenableeta
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_smul]
    congr 2
    apply mul_smul
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.ideal_to Module.Baer.ExtensionOfMaxAdjoin.idealTo

/-- Since we assumed `Q` being Baer, the linear map `x ↦ f' (x • y) : I ⟶ Q` extends to `R ⟶ Q`,
call this extended map `φ`-/
def ExtensionOfMaxAdjoin.extendIdealTo (h : Module.Baer R Q) (y : N) : R →ₗ[R] Q :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extend_ideal_to Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo

theorem ExtensionOfMaxAdjoin.extendIdealTo_is_extension (h : Module.Baer R Q) (y : N) :
    ∀ (x : R) (mem : x ∈ ExtensionOfMaxAdjoin.ideal i f y),
      ExtensionOfMaxAdjoin.extendIdealTo i f h y x = ExtensionOfMaxAdjoin.idealTo i f y ⟨x, mem⟩ :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose_spec
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_is_extension Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_is_extension

theorem ExtensionOfMaxAdjoin.extendIdealTo_wd' (h : Module.Baer R Q) {y : N} (r : R)
    (eq1 : r • y = 0) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r = 0 := by
  have : r ∈ ideal i f y := by
    change (r • y) ∈ (extensionOfMax i f).toLinearPMap.domain
    rw [eq1]
    apply Submodule.zero_mem _
  rw [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h y r this]
  dsimp [ExtensionOfMaxAdjoin.idealTo]
  simp only [LinearMap.coe_mk, eq1, Subtype.coe_mk, ← ZeroMemClass.zero_def,
    (extensionOfMax i f).toLinearPMap.map_zero]
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_wd' Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd'

theorem ExtensionOfMaxAdjoin.extendIdealTo_wd (h : Module.Baer R Q) {y : N} (r r' : R)
    (eq1 : r • y = r' • y) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    ExtensionOfMaxAdjoin.extendIdealTo i f h y r' := by
  rw [← sub_eq_zero, ← map_sub]
  convert ExtensionOfMaxAdjoin.extendIdealTo_wd' i f h (r - r') _
  rw [sub_smul, sub_eq_zero, eq1]
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_wd Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd

theorem ExtensionOfMaxAdjoin.extendIdealTo_eq (h : Module.Baer R Q) {y : N} (r : R)
    (hr : r • y ∈ (extensionOfMax i f).domain) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    (extensionOfMax i f).toLinearPMap ⟨r • y, hr⟩ := by
    -- Porting note: in mathlib3 `AddHom.coe_mk` was not needed
  simp only [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h _ _ hr,
    ExtensionOfMaxAdjoin.idealTo, LinearMap.coe_mk, Subtype.coe_mk, AddHom.coe_mk]
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_eq Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_eq

/-- We can finally define a linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r`
-/
def ExtensionOfMaxAdjoin.extensionToFun (h : Module.Baer R Q) {y : N} :
    supExtensionOfMaxSingleton i f y → Q := fun x =>
  (extensionOfMax i f).toLinearPMap (ExtensionOfMaxAdjoin.fst i x) +
    ExtensionOfMaxAdjoin.extendIdealTo i f h y (ExtensionOfMaxAdjoin.snd i x)
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extension_to_fun Module.Baer.ExtensionOfMaxAdjoin.extensionToFun

theorem ExtensionOfMaxAdjoin.extensionToFun_wd (h : Module.Baer R Q) {y : N}
    (x : supExtensionOfMaxSingleton i f y) (a : (extensionOfMax i f).domain)
    (r : R) (eq1 : ↑x = ↑a + r • y) :
    ExtensionOfMaxAdjoin.extensionToFun i f h x =
      (extensionOfMax i f).toLinearPMap a + ExtensionOfMaxAdjoin.extendIdealTo i f h y r := by
  cases' a with a ha
  have eq2 :
    (ExtensionOfMaxAdjoin.fst i x - a : N) = (r - ExtensionOfMaxAdjoin.snd i x) • y := by
    change x = a + r • y at eq1
    rwa [ExtensionOfMaxAdjoin.eqn, ← sub_eq_zero, ← sub_sub_sub_eq, sub_eq_zero, ← sub_smul]
      at eq1
  have eq3 :=
    ExtensionOfMaxAdjoin.extendIdealTo_eq i f h (r - ExtensionOfMaxAdjoin.snd i x)
      (by rw [← eq2]; exact Submodule.sub_mem _ (ExtensionOfMaxAdjoin.fst i x).2 ha)
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3
  unfold ExtensionOfMaxAdjoin.extensionToFun
  rw [eq3, ← add_assoc, ← (extensionOfMax i f).toLinearPMap.map_add, AddMemClass.mk_add_mk]
  congr
  ext
  dsimp
  rw [Subtype.coe_mk, add_sub, ← eq1]
  exact eq_sub_of_add_eq (ExtensionOfMaxAdjoin.eqn i x).symm
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extension_to_fun_wd Module.Baer.ExtensionOfMaxAdjoin.extensionToFun_wd

/-- The linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r` is an extension of `f`-/
def extensionOfMaxAdjoin (h : Module.Baer R Q) (y : N) : ExtensionOf i f where
  domain := supExtensionOfMaxSingleton i f y -- (extensionOfMax i f).domain ⊔ Submodule.span R {y}
  le := le_trans (extensionOfMax i f).le le_sup_left
  toFun :=
    { toFun := ExtensionOfMaxAdjoin.extensionToFun i f h
      map_add' := fun a b => by
        have eq1 :
          ↑a + ↑b =
            ↑(ExtensionOfMaxAdjoin.fst i a + ExtensionOfMaxAdjoin.fst i b) +
              (ExtensionOfMaxAdjoin.snd i a + ExtensionOfMaxAdjoin.snd i b) • y := by
          rw [ExtensionOfMaxAdjoin.eqn, ExtensionOfMaxAdjoin.eqn, add_smul, Submodule.coe_add]
          ac_rfl
        rw [ExtensionOfMaxAdjoin.extensionToFun_wd (y := y) i f h (a + b) _ _ eq1,
          LinearPMap.map_add, map_add]
        unfold ExtensionOfMaxAdjoin.extensionToFun
        abel
      map_smul' := fun r a => by
        dsimp
        have eq1 :
          r • (a : N) =
            ↑(r • ExtensionOfMaxAdjoin.fst i a) + (r • ExtensionOfMaxAdjoin.snd i a) • y := by
          rw [ExtensionOfMaxAdjoin.eqn, smul_add, smul_eq_mul, mul_smul]
          rfl
        rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h (r • a :) _ _ eq1, LinearMap.map_smul,
          LinearPMap.map_smul, ← smul_add]
        congr }
  is_extension m := by
    dsimp
    rw [(extensionOfMax i f).is_extension,
      ExtensionOfMaxAdjoin.extensionToFun_wd i f h _ ⟨i m, _⟩ 0 _, map_zero, add_zero]
    simp
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin Module.Baer.extensionOfMaxAdjoin

theorem extensionOfMax_le (h : Module.Baer R Q) {y : N} :
    extensionOfMax i f ≤ extensionOfMaxAdjoin i f h y :=
  ⟨le_sup_left, fun x x' EQ => by
    symm
    change ExtensionOfMaxAdjoin.extensionToFun i f h _ = _
    rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h x' x 0 (by simp [EQ]), map_zero,
      add_zero]⟩
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_le Module.Baer.extensionOfMax_le

theorem extensionOfMax_to_submodule_eq_top (h : Module.Baer R Q) :
    (extensionOfMax i f).domain = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  dsimp
  rw [← extensionOfMax_is_max i f _ (extensionOfMax_le i f h), extensionOfMaxAdjoin,
    Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_to_submodule_eq_top Module.Baer.extensionOfMax_to_submodule_eq_top

protected theorem extension_property (h : Module.Baer R Q)
    (f : M →ₗ[R] N) (hf : Function.Injective f) (g : M →ₗ[R] Q) : ∃ h, h ∘ₗ f = g :=
  haveI : Fact (Function.Injective f) := ⟨hf⟩
  Exists.intro
    { toFun := ((extensionOfMax f g).toLinearPMap
        ⟨·, (extensionOfMax_to_submodule_eq_top f g h).symm ▸ ⟨⟩⟩)
      map_add' := fun x y ↦ by rw [← LinearPMap.map_add]; congr
      map_smul' := fun r x ↦ by rw [← LinearPMap.map_smul]; dsimp } <|
    LinearMap.ext fun x ↦ ((extensionOfMax f g).is_extension x).symm

theorem extension_property_addMonoidHom (h : Module.Baer ℤ Q)
    (f : M →+ N) (hf : Function.Injective f) (g : M →+ Q) : ∃ h : N →+ Q, h.comp f = g :=
  have ⟨g', hg'⟩ := h.extension_property f.toIntLinearMap hf g.toIntLinearMap
  ⟨g', congr(LinearMap.toAddMonoidHom $hg')⟩

/-- **Baer's criterion** for injective module : a Baer module is an injective module, i.e. if every
linear map from an ideal can be extended, then the module is injective. -/
protected theorem injective (h : Module.Baer R Q) : Module.Injective R Q where
  out X Y _ _ _ _ i hi f := by
    obtain ⟨h, H⟩ := Module.Baer.extension_property h i hi f
    exact ⟨h, DFunLike.congr_fun H⟩
set_option linter.uppercaseLean3 false in
#align module.Baer.injective Module.Baer.injective

protected theorem of_injective [Small.{v} R] (inj : Module.Injective R Q) : Module.Baer R Q := by
  intro I g
  let eI := Shrink.linearEquiv I R
  let eR := Shrink.linearEquiv R R
  obtain ⟨g', hg'⟩ := Module.Injective.out (eR.symm.toLinearMap ∘ₗ I.subtype ∘ₗ eI.toLinearMap)
    (eR.symm.injective.comp <| Subtype.val_injective.comp eI.injective) (g ∘ₗ eI.toLinearMap)
  exact ⟨g' ∘ₗ eR.symm.toLinearMap, fun x mx ↦ by simpa [eI, eR] using hg' (equivShrink I ⟨x, mx⟩)⟩

protected theorem iff_injective [Small.{v} R] : Module.Baer R Q ↔ Module.Injective R Q :=
  ⟨Module.Baer.injective, Module.Baer.of_injective⟩

end Module.Baer

section ULift

variable {M : Type v} [AddCommGroup M] [Module R M]

lemma Module.ulift_injective_of_injective [Small.{v} R]
    (inj : Module.Injective R M) :
    Module.Injective R (ULift.{v'} M) := Module.Baer.injective fun I g ↦
  have ⟨g', hg'⟩ := Module.Baer.iff_injective.mpr inj I (ULift.moduleEquiv.toLinearMap ∘ₗ g)
  ⟨ULift.moduleEquiv.symm.toLinearMap ∘ₗ g', fun r hr ↦ ULift.ext _ _ <| hg' r hr⟩

lemma Module.injective_of_ulift_injective
    (inj : Module.Injective R (ULift.{v'} M)) :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g :=
    let eX := ULift.moduleEquiv.{_,_,v'} (R := R) (M := X)
    have ⟨g', hg'⟩ := inj.out (ULift.moduleEquiv.{_,_,v'}.symm.toLinearMap ∘ₗ f ∘ₗ eX.toLinearMap)
      (by exact ULift.moduleEquiv.symm.injective.comp <| hf.comp eX.injective)
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ eX.toLinearMap)
    ⟨ULift.moduleEquiv.toLinearMap ∘ₗ g' ∘ₗ ULift.moduleEquiv.symm.toLinearMap,
      fun x ↦ by exact congr(ULift.down $(hg' ⟨x⟩))⟩

variable (M) [Small.{v} R]

lemma Module.injective_iff_ulift_injective :
    Module.Injective R M ↔ Module.Injective R (ULift.{v'} M) :=
  ⟨Module.ulift_injective_of_injective R,
   Module.injective_of_ulift_injective R⟩

instance ModuleCat.ulift_injective_of_injective
    [inj : CategoryTheory.Injective <| ModuleCat.of R M] :
    CategoryTheory.Injective <| ModuleCat.of R (ULift.{v'} M) :=
  Module.injective_object_of_injective_module
    (inj := Module.ulift_injective_of_injective
      (inj := Module.injective_module_of_injective_object (inj := inj)))

end ULift

section lifting_property

universe uR uM uP uP'

variable (R : Type uR) [Ring R] [Small.{uM} R]
variable (M : Type uM) [AddCommGroup M] [Module R M] [inj : Module.Injective R M]
variable (P : Type uP) [AddCommGroup P] [Module R P]
variable (P' : Type uP') [AddCommGroup P'] [Module R P']

lemma Module.Injective.extension_property
    (f : P →ₗ[R] P') (hf : Function.Injective f)
    (g : P →ₗ[R] M) : ∃ h : P' →ₗ[R] M, h ∘ₗ f = g :=
  (Module.Baer.of_injective inj).extension_property f hf g

end lifting_property
