/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Data.TypeMax -- Porting note: added for universe issues

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

universe u v

variable (R : Type u) [Ring R] (Q : TypeMax.{v,u}) [AddCommGroup Q] [Module R Q]

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
  out : ∀ (X Y : TypeMax.{v,u}) [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]
    (f : X →ₗ[R] Y) (_ : Function.Injective f) (g : X →ₗ[R] Q),
    ∃ h : Y →ₗ[R] Q, ∀ x, h (f x) = g x
#align module.injective Module.Injective

-- Porting note: egregious max u v abuse
theorem Module.injective_object_of_injective_module [Module.Injective.{u, v} R Q] :
    CategoryTheory.Injective.{max u v} (⟨Q⟩ : ModuleCat.{max u v} R) :=
  { factors := fun g f mn => by
      rcases Module.Injective.out _ _ f ((ModuleCat.mono_iff_injective f).mp mn) g with ⟨h, eq1⟩
      -- ⊢ ∃ h, CategoryTheory.CategoryStruct.comp f h = g
      exact ⟨h, LinearMap.ext eq1⟩ }
      -- 🎉 no goals
#align module.injective_object_of_injective_module Module.injective_object_of_injective_module

theorem Module.injective_module_of_injective_object
    [CategoryTheory.Injective.{max u v} (⟨Q⟩ : ModuleCat.{max u v} R)] :
    Module.Injective.{u, v} R Q :=
  { out := fun X Y ins1 ins2 ins3 ins4 f hf g => by
      skip
      -- ⊢ ∃ h, ∀ (x : X), ↑h (↑f x) = ↑g x
      rcases@CategoryTheory.Injective.factors (ModuleCat R) _ ⟨Q⟩ _ ⟨X⟩ ⟨Y⟩ g f
          ((ModuleCat.mono_iff_injective _).mpr hf) with
        ⟨h, rfl⟩
      exact ⟨h, fun x => rfl⟩ }
      -- 🎉 no goals
#align module.injective_module_of_injective_object Module.injective_module_of_injective_object

theorem Module.injective_iff_injective_object :
    Module.Injective.{u, v} R Q ↔
      CategoryTheory.Injective.{max u v} (⟨Q⟩ : ModuleCat.{max u v} R) :=
  ⟨fun h => @Module.injective_object_of_injective_module R _ Q _ _ h, fun h =>
    @Module.injective_module_of_injective_object R _ Q _ _ h⟩
#align module.injective_iff_injective_object Module.injective_iff_injective_object

/-- An `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `Ideal R` extends to
an `R`-linear map `R ⟶ Q`-/
def Module.Baer : Prop :=
  ∀ (I : Ideal R) (g : I →ₗ[R] Q), ∃ g' : R →ₗ[R] Q, ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩
set_option linter.uppercaseLean3 false in
#align module.Baer Module.Baer

namespace Module.Baer

variable {R Q} {M N : Type max u v} [AddCommGroup M] [AddCommGroup N]

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
  -- ⊢ { toLinearPMap := a, le := a_le, is_extension := e1 } = b
  rcases b with ⟨b, b_le, e2⟩
  -- ⊢ { toLinearPMap := a, le := a_le, is_extension := e1 } = { toLinearPMap := b, …
  congr
  -- ⊢ a = b
  exact LinearPMap.ext domain_eq to_fun_eq
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of.ext Module.Baer.ExtensionOf.ext

theorem ExtensionOf.ext_iff {a b : ExtensionOf i f} :
    a = b ↔ ∃ _ : a.domain = b.domain, ∀ ⦃x : a.domain⦄ ⦃y : b.domain⦄,
    (x : N) = y → a.toLinearPMap x = b.toLinearPMap y :=
  ⟨fun r => r ▸ ⟨rfl, fun x y h => congr_arg a.toFun <| by exact_mod_cast h⟩, fun ⟨h1, h2⟩ =>
                                                           -- 🎉 no goals
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
          -- ⊢ ↑i x ∈ LinearPMap.eqLocus X1.toLinearPMap X2.toLinearPMap
          refine' ⟨X1.le (Set.mem_range_self _), X2.le (Set.mem_range_self _), _⟩
          -- ⊢ ↑X1.toLinearPMap { val := ↑i x, property := (_ : ↑i x ∈ X1.domain) } = ↑X2.t …
          rw [← X1.is_extension x, ← X2.is_extension x] :
          -- 🎉 no goals
          x ∈ X1.toLinearPMap.eqLocus X2.toLinearPMap)
      is_extension := fun m => X1.is_extension _ }

instance : SemilatticeInf (ExtensionOf i f) :=
  Function.Injective.semilatticeInf ExtensionOf.toLinearPMap
    (fun X Y h =>
      ExtensionOf.ext (by rw [h]) fun x y h' => by
                          -- 🎉 no goals
        -- Porting note: induction didn't handle dependent rw like in Lean 3
        have : {x y : N} → (h'' : x = y) → (hx : x ∈ X.toLinearPMap.domain) →
          (hy : y ∈ Y.toLinearPMap.domain) → X.toLinearPMap ⟨x,hx⟩ = Y.toLinearPMap ⟨y,hy⟩ := by
            rw [h]
            intro _ _ h _ _
            congr
        apply this h' _ _)
        -- 🎉 no goals
    fun X Y =>
    LinearPMap.ext rfl fun x y h => by
      congr
      -- ⊢ x = y
      exact_mod_cast h
      -- 🎉 no goals

variable {i f}

theorem chain_linearPMap_of_chain_extensionOf {c : Set (ExtensionOf i f)}
    (hchain : IsChain (· ≤ ·) c) :
    IsChain (· ≤ ·) <| (fun x : ExtensionOf i f => x.toLinearPMap) '' c := by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ neq
  -- ⊢ (fun x x_1 => x ≤ x_1) ((fun x => x.toLinearPMap) a) ((fun x => x.toLinearPM …
  exact hchain a_mem b_mem (ne_of_apply_ne _ neq)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align module.Baer.chain_linear_pmap_of_chain_extension_of Module.Baer.chain_linearPMap_of_chain_extensionOf

/-- The maximal element of every nonempty chain of `extension_of i f`. -/
def ExtensionOf.max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) : ExtensionOf i f :=
  {
    LinearPMap.sSup _
      (IsChain.directedOn <|
        chain_linearPMap_of_chain_extensionOf
          hchain) with
    le :=
      le_trans hnonempty.some.le <|
        (LinearPMap.le_sSup _ <|
            (Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩).1
    is_extension := fun m => by
      refine' Eq.trans (hnonempty.some.is_extension m) _
      -- ⊢ ∀ {c : Set (ExtensionOf i f)} (hchain : IsChain (fun x x_1 => x ≤ x_1) c),
      · -- porting note: this subgoal didn't exist before the reenableeta branch
        intros c hchain _
        -- ⊢ let src := LinearPMap.sSup ((fun x => x.toLinearPMap) '' c) (_ : DirectedOn  …
        exact (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain)
        -- 🎉 no goals
      symm
      -- ⊢ ↑{ domain := src✝.domain, toFun := src✝.toFun } { val := ↑i m, property := ( …
      generalize_proofs _ h1
      -- ⊢ ↑{ domain := src✝.domain, toFun := src✝.toFun } { val := ↑i m, property := h …
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
            -- ⊢ (fun x => ↑f (Exists.choose (_ : ↑x ∈ LinearMap.range i))) (x + y) = (fun x  …
            rw [← map_add, ← (x + y).2.choose_spec] at eq1
            -- ⊢ (fun x => ↑f (Exists.choose (_ : ↑x ∈ LinearMap.range i))) (x + y) = (fun x  …
            dsimp
            -- ⊢ ↑f (Exists.choose (_ : ↑(x + y) ∈ LinearMap.range i)) = ↑f (Exists.choose (_ …
            rw [← Fact.out (p := Function.Injective i) eq1, map_add]
            -- 🎉 no goals
          map_smul' := fun r x => by
            have eq1 : r • _ = (r • x).1 := congr_arg ((· • ·) r) x.2.choose_spec
            -- ⊢ AddHom.toFun { toFun := fun x => ↑f (Exists.choose (_ : ↑x ∈ LinearMap.range …
            rw [← LinearMap.map_smul, ← (r • x).2.choose_spec] at eq1
            -- ⊢ AddHom.toFun { toFun := fun x => ↑f (Exists.choose (_ : ↑x ∈ LinearMap.range …
            dsimp
            -- ⊢ ↑f (Exists.choose (_ : ↑(r • x) ∈ LinearMap.range i)) = r • ↑f (Exists.choos …
            rw [← Fact.out (p := Function.Injective i) eq1, LinearMap.map_smul] }
            -- 🎉 no goals
      le := le_refl _
      is_extension := fun m => by
        simp only [LinearPMap.mk_apply, LinearMap.coe_mk]
        -- ⊢ ↑f m = ↑{ toFun := fun x => ↑f (Exists.choose (_ : ↑x ∈ LinearMap.range i)), …
        dsimp
        -- ⊢ ↑f m = ↑f (Exists.choose (_ : ↑i m ∈ LinearMap.range i))
        apply congrArg
        -- ⊢ m = Exists.choose (_ : ↑i m ∈ LinearMap.range i)
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
@[reducible]
def supExtensionOfMaxSingleton (y : N) : Submodule R N :=
  (extensionOfMax i f).domain ⊔ (Submodule.span R {y})

variable {f}

private theorem extensionOfMax_adjoin.aux1 {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ∃ (a : (extensionOfMax i f).domain) (b : R), x.1 = a.1 + b • y := by
  have mem1 : x.1 ∈ (_ : Set _) := x.2
  -- ⊢ ∃ a b, ↑x = ↑a + b • y
  rw [Submodule.coe_sup] at mem1
  -- ⊢ ∃ a b, ↑x = ↑a + b • y
  rcases mem1 with ⟨a, b, a_mem, b_mem : b ∈ (Submodule.span R _ : Submodule R N), eq1⟩
  -- ⊢ ∃ a b, ↑x = ↑a + b • y
  rw [Submodule.mem_span_singleton] at b_mem
  -- ⊢ ∃ a b, ↑x = ↑a + b • y
  rcases b_mem with ⟨z, eq2⟩
  -- ⊢ ∃ a b, ↑x = ↑a + b • y
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩
  -- 🎉 no goals
set_option align.precheck false in
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.aux1 Module.Baer.extensionOfMax_adjoin.aux1

/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `fst` pick an arbitrary such `m`.-/
def ExtensionOfMaxAdjoin.fst {y : N} (x : supExtensionOfMaxSingleton i f y) :
    (extensionOfMax i f).domain :=
  (extensionOfMax_adjoin.aux1 i x).choose
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.fst Module.Baer.ExtensionOfMaxAdjoin.fst

/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `snd` pick an arbitrary such `r`.-/
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
    -- porting note: a single simp took care of the goal before reenableeta
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_add]
    -- ⊢ ↑(extensionOfMax i f).toLinearPMap { val := ↑(z1 + z2) • y, property := (_ : …
    congr
    -- ⊢ ↑(z1 + z2) • y = ↑{ val := ↑z1 • y, property := (_ : ↑z1 ∈ ideal i f y) } +  …
    apply add_smul
    -- 🎉 no goals
  map_smul' z1 (z2 : {x // x ∈ ideal i f y}) := by
    -- porting note: a single simp took care of the goal before reenableeta
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_smul]
    -- ⊢ ↑(extensionOfMax i f).toLinearPMap { val := ↑(z1 • z2) • y, property := (_ : …
    congr 2
    -- ⊢ ↑(z1 • z2) • y = ↑(RingHom.id R) z1 • ↑{ val := ↑z2 • y, property := (_ : ↑z …
    apply mul_smul
    -- 🎉 no goals
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
  -- ⊢ ↑(idealTo i f y) { val := r, property := this } = 0
  dsimp [ExtensionOfMaxAdjoin.idealTo]
  -- ⊢ ↑(extensionOfMax i f).toLinearPMap { val := r • y, property := (_ : ↑{ val : …
  simp only [LinearMap.coe_mk, eq1, Subtype.coe_mk, ← ZeroMemClass.zero_def,
    (extensionOfMax i f).toLinearPMap.map_zero]
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_wd' Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd'

theorem ExtensionOfMaxAdjoin.extendIdealTo_wd (h : Module.Baer R Q) {y : N} (r r' : R)
    (eq1 : r • y = r' • y) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    ExtensionOfMaxAdjoin.extendIdealTo i f h y r' := by
  rw [← sub_eq_zero, ← map_sub]
  -- ⊢ ↑(extendIdealTo i f h y) (r - r') = 0
  convert ExtensionOfMaxAdjoin.extendIdealTo_wd' i f h (r - r') _
  -- ⊢ (r - r') • y = 0
  rw [sub_smul, sub_eq_zero, eq1]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin.extend_ideal_to_wd Module.Baer.ExtensionOfMaxAdjoin.extendIdealTo_wd

theorem ExtensionOfMaxAdjoin.extendIdealTo_eq (h : Module.Baer R Q) {y : N} (r : R)
    (hr : r • y ∈ (extensionOfMax i f).domain) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    (extensionOfMax i f).toLinearPMap ⟨r • y, hr⟩ := by
    -- porting note: in mathlib3 `AddHom.coe_mk` was not needed
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
  -- ⊢ extensionToFun i f h x = ↑(extensionOfMax i f).toLinearPMap { val := a, prop …
  have eq2 :
    (ExtensionOfMaxAdjoin.fst i x - a : N) = (r - ExtensionOfMaxAdjoin.snd i x) • y := by
    change x = a + r • y at eq1
    rwa [ExtensionOfMaxAdjoin.eqn, ← sub_eq_zero, ← sub_sub_sub_eq, sub_eq_zero, ← sub_smul]
      at eq1
  have eq3 :=
    ExtensionOfMaxAdjoin.extendIdealTo_eq i f h (r - ExtensionOfMaxAdjoin.snd i x)
      (by rw [← eq2]; exact Submodule.sub_mem _ (ExtensionOfMaxAdjoin.fst i x).2 ha)
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3
  -- ⊢ extensionToFun i f h x = ↑(extensionOfMax i f).toLinearPMap { val := a, prop …
  unfold ExtensionOfMaxAdjoin.extensionToFun
  -- ⊢ ↑(extensionOfMax i f).toLinearPMap (fst i x) + ↑(extendIdealTo i f h y) (snd …
  rw [eq3, ← add_assoc, ← (extensionOfMax i f).toLinearPMap.map_add, AddMemClass.mk_add_mk]
  -- ⊢ ↑(extensionOfMax i f).toLinearPMap (fst i x) + ↑(extendIdealTo i f h y) (snd …
  congr
  -- ⊢ fst i x = { val := a + (r • y - snd i x • y), property := (_ : a + (r • y -  …
  ext
  -- ⊢ ↑(fst i x) = ↑{ val := a + (r • y - snd i x • y), property := (_ : a + (r •  …
  dsimp
  -- ⊢ ↑(fst i x) = a + (r • y - snd i x • y)
  rw [Subtype.coe_mk, add_sub, ← eq1]
  -- ⊢ ↑(fst i x) = ↑x - snd i x • y
  exact eq_sub_of_add_eq (ExtensionOfMaxAdjoin.eqn i x).symm
  -- 🎉 no goals
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
        -- ⊢ ↑(extensionOfMax i f).toLinearPMap (ExtensionOfMaxAdjoin.fst i a) + ↑(extens …
        abel
        -- 🎉 no goals
        -- 🎉 no goals
      map_smul' := fun r a => by
        dsimp
        -- ⊢ ExtensionOfMaxAdjoin.extensionToFun i f h (r • a) = r • ExtensionOfMaxAdjoin …
        have eq1 :
          r • (a : N) =
            ↑(r • ExtensionOfMaxAdjoin.fst i a) + (r • ExtensionOfMaxAdjoin.snd i a) • y := by
          rw [ExtensionOfMaxAdjoin.eqn, smul_add, smul_eq_mul, mul_smul]
          rfl
        rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h (r • a) _ _ eq1, LinearMap.map_smul,
          LinearPMap.map_smul, ← smul_add]
        congr }
        -- 🎉 no goals
  is_extension m := by
    dsimp
    -- ⊢ ↑f m = ExtensionOfMaxAdjoin.extensionToFun i f h { val := ↑i m, property :=  …
    rw [(extensionOfMax i f).is_extension,
      ExtensionOfMaxAdjoin.extensionToFun_wd i f h _ ⟨i m, _⟩ 0 _, map_zero, add_zero]
    simp
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_adjoin Module.Baer.extensionOfMaxAdjoin

theorem extensionOfMax_le (h : Module.Baer R Q) {y : N} :
    extensionOfMax i f ≤ extensionOfMaxAdjoin i f h y :=
  ⟨le_sup_left, fun x x' EQ => by
    symm
    -- ⊢ ↑(extensionOfMaxAdjoin i f h y).toLinearPMap x' = ↑(extensionOfMax i f).toLi …
    change ExtensionOfMaxAdjoin.extensionToFun i f h _ = _
    -- ⊢ ExtensionOfMaxAdjoin.extensionToFun i f h x' = ↑(extensionOfMax i f).toLinea …
    rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h x' x 0 (by simp [EQ]), map_zero,
      add_zero]⟩
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_le Module.Baer.extensionOfMax_le

theorem extensionOfMax_to_submodule_eq_top (h : Module.Baer R Q) :
    (extensionOfMax i f).domain = ⊤ := by
  refine' Submodule.eq_top_iff'.mpr fun y => _
  -- ⊢ y ∈ (extensionOfMax i f).toLinearPMap.domain
  dsimp
  -- ⊢ y ∈ (extensionOfMax i f).toLinearPMap.domain
  rw [← extensionOfMax_is_max i f _ (extensionOfMax_le i f h), extensionOfMaxAdjoin,
    Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align module.Baer.extension_of_max_to_submodule_eq_top Module.Baer.extensionOfMax_to_submodule_eq_top

/-- **Baer's criterion** for injective module : a Baer module is an injective module, i.e. if every
linear map from an ideal can be extended, then the module is injective.-/
protected theorem injective (h : Module.Baer R Q) : Module.Injective R Q :=
  { out := fun X Y ins1 ins2 ins3 ins4 i hi f =>
      haveI : Fact (Function.Injective i) := ⟨hi⟩
      ⟨{  toFun := fun y =>
            (extensionOfMax i f).toLinearPMap
              ⟨y, (extensionOfMax_to_submodule_eq_top i f h).symm ▸ trivial⟩
          map_add' := fun x y => by
            rw [← LinearPMap.map_add]
            -- ⊢ (fun y => ↑(extensionOfMax i f).toLinearPMap { val := y, property := (_ : y  …
            congr
            -- 🎉 no goals
          map_smul' := fun r x => by
            rw [← LinearPMap.map_smul]
            -- ⊢ AddHom.toFun { toFun := fun y => ↑(extensionOfMax i f).toLinearPMap { val := …
            -- Porting note: used to be congr
            dsimp },
            -- 🎉 no goals
        fun x => ((extensionOfMax i f).is_extension x).symm⟩ }
set_option linter.uppercaseLean3 false in
#align module.Baer.injective Module.Baer.injective

end Module.Baer
