/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Logic.Small.Defs
import Mathlib.Algebra.Module.Shrink
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ULift
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Small.Basic
import Mathlib.Order.Zorn
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

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

@[expose] public section

assert_not_exists ModuleCat

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

/-- An `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `Ideal R` extends to
an `R`-linear map `R ⟶ Q` -/
def Module.Baer : Prop :=
  ∀ (I : Ideal R) (g : I →ₗ[R] Q), ∃ g' : R →ₗ[R] Q, ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩

namespace Module.Baer

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

lemma of_equiv (e : Q ≃ₗ[R] M) (h : Module.Baer R Q) : Module.Baer R M := fun I g ↦
  have ⟨g', h'⟩ := h I (e.symm ∘ₗ g)
  ⟨e ∘ₗ g', by simpa [LinearEquiv.eq_symm_apply] using h'⟩

lemma congr (e : Q ≃ₗ[R] M) : Module.Baer R Q ↔ Module.Baer R M := ⟨of_equiv e, of_equiv e.symm⟩

lemma iff_surjective {R : Type u} [CommRing R] [Module R M] : Module.Baer R M ↔
    ∀ (I : Ideal R), Function.Surjective (LinearMap.lcomp R M I.subtype) := by
  refine ⟨fun h I g ↦ ?_, fun h I g ↦ ?_⟩
  · rcases h I g with ⟨g', hg'⟩
    use g'
    ext x
    simp [hg']
  · rcases h I g with ⟨g', hg'⟩
    use g'
    intro x hx
    simp [← hg']

/-- If we view `M` as a submodule of `N` via the injective linear map `i : M ↪ N`, then a submodule
between `M` and `N` is a submodule `N'` of `N`. To prove Baer's criterion, we need to consider
pairs of `(N', f')` such that `M ≤ N' ≤ N` and `f'` extends `f`. -/
structure ExtensionOf extends N →ₗ.[R] Q where
  le : LinearMap.range i ≤ domain
  is_extension : ∀ m : M, f m = toLinearPMap ⟨i m, le ⟨m, rfl⟩⟩

section Ext

variable {i f}

@[ext (iff := false)]
theorem ExtensionOf.ext {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
    (to_fun_eq : ∀ ⦃x : N⦄ ⦃ha : x ∈ a.domain⦄ ⦃hb : x ∈ b.domain⦄,
      a.toLinearPMap ⟨x, ha⟩ = b.toLinearPMap ⟨x, hb⟩) :
    a = b := by
  rcases a with ⟨a, a_le, e1⟩
  congr
  exact LinearPMap.ext domain_eq to_fun_eq

/-- A dependent version of `ExtensionOf.ext` -/
theorem ExtensionOf.dExt {a b : ExtensionOf i f} (domain_eq : a.domain = b.domain)
    (to_fun_eq :
      ∀ ⦃x : a.domain⦄ ⦃y : b.domain⦄, (x : N) = y → a.toLinearPMap x = b.toLinearPMap y) :
    a = b :=
  ext domain_eq fun _ _ _ ↦ to_fun_eq rfl

theorem ExtensionOf.dExt_iff {a b : ExtensionOf i f} :
    a = b ↔ ∃ _ : a.domain = b.domain, ∀ ⦃x : a.domain⦄ ⦃y : b.domain⦄,
    (x : N) = y → a.toLinearPMap x = b.toLinearPMap y :=
  ⟨fun r => r ▸ ⟨rfl, fun _ _ h => congr_arg a.toFun <| mod_cast h⟩, fun ⟨h1, h2⟩ =>
    ExtensionOf.dExt h1 h2⟩

theorem ExtensionOf.toLinearPMap_injective :
    Function.Injective (α := ExtensionOf i f) ExtensionOf.toLinearPMap :=
  fun _ _ _ ↦ by ext <;> congr!

end Ext

instance : Min (ExtensionOf i f) where
  min X1 X2 :=
    { X1.toLinearPMap ⊓ X2.toLinearPMap with
      le := fun x hx =>
        (by
          rcases hx with ⟨x, rfl⟩
          refine ⟨X1.le (Set.mem_range_self _), X2.le (Set.mem_range_self _), ?_⟩
          rw [← X1.is_extension x, ← X2.is_extension x] :
          x ∈ X1.toLinearPMap.eqLocus X2.toLinearPMap)
      is_extension := fun _ => X1.is_extension _ }

instance : PartialOrder (ExtensionOf i f) :=
  PartialOrder.lift _ ExtensionOf.toLinearPMap_injective

instance : SemilatticeInf (ExtensionOf i f) :=
  ExtensionOf.toLinearPMap_injective.semilatticeInf _
    .rfl .rfl fun X Y ↦ LinearPMap.ext rfl fun x y h ↦ by congr

variable {i f}

theorem chain_linearPMap_of_chain_extensionOf {c : Set (ExtensionOf i f)}
    (hchain : IsChain (· ≤ ·) c) :
    IsChain (· ≤ ·) <| (fun x : ExtensionOf i f => x.toLinearPMap) '' c := by
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ ne
  exact hchain a_mem b_mem (ne_of_apply_ne _ ne)

/-- The maximal element of every nonempty chain of `extension_of i f`. -/
def ExtensionOf.max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) : ExtensionOf i f :=
  { LinearPMap.sSup _
      (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) with
    le := by
      refine le_trans hnonempty.some.le <|
        (LinearPMap.le_sSup _ <|
            (Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩).1
    is_extension := fun m => by
      refine Eq.trans (hnonempty.some.is_extension m) ?_
      symm
      generalize_proofs _ _ h1
      exact
        LinearPMap.sSup_apply (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain)
          ((Set.mem_image _ _ _).mpr ⟨hnonempty.some, hnonempty.choose_spec, rfl⟩) ⟨i m, h1⟩ }

theorem ExtensionOf.le_max {c : Set (ExtensionOf i f)} (hchain : IsChain (· ≤ ·) c)
    (hnonempty : c.Nonempty) (a : ExtensionOf i f) (ha : a ∈ c) :
    a ≤ ExtensionOf.max hchain hnonempty :=
  LinearPMap.le_sSup (IsChain.directedOn <| chain_linearPMap_of_chain_extensionOf hchain) <|
    (Set.mem_image _ _ _).mpr ⟨a, ha, rfl⟩

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
            rw [← map_smul, ← (r • x).2.choose_spec] at eq1
            dsimp
            rw [← Fact.out (p := Function.Injective i) eq1, map_smul] }
      le := le_refl _
      is_extension := fun m => by
        simp only [LinearPMap.mk_apply, LinearMap.coe_mk]
        dsimp
        apply congrArg
        exact Fact.out (p := Function.Injective i)
          (⟨i m, ⟨_, rfl⟩⟩ : LinearMap.range i).2.choose_spec.symm }

/-- Since every nonempty chain has a maximal element, by Zorn's lemma, there is a maximal
`extension_of i f`. -/
def extensionOfMax : ExtensionOf i f :=
  (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
      ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose

theorem extensionOfMax_is_max :
    ∀ (a : ExtensionOf i f), extensionOfMax i f ≤ a → a = extensionOfMax i f :=
  fun _ ↦ (@zorn_le_nonempty (ExtensionOf i f) _ ⟨Inhabited.default⟩ fun _ hchain hnonempty =>
    ⟨ExtensionOf.max hchain hnonempty, ExtensionOf.le_max hchain hnonempty⟩).choose_spec.eq_of_ge

-- Auxiliary definition: Lean looks for an instance of `Max (Type u)` if we would write
-- `(x : (extensionOfMax i f).domain ⊔ (Submodule.span R {y}))`, so we encapsulate the cast instead.
abbrev supExtensionOfMaxSingleton (y : N) : Submodule R N :=
  (extensionOfMax i f).domain ⊔ (Submodule.span R {y})

variable {f}

set_option backward.privateInPublic true in
private theorem extensionOfMax_adjoin.aux1 {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ∃ (a : (extensionOfMax i f).domain) (b : R), x.1 = a.1 + b • y := by
  have mem1 : x.1 ∈ (_ : Set _) := x.2
  rw [Submodule.coe_sup] at mem1
  rcases mem1 with ⟨a, a_mem, b, b_mem : b ∈ (Submodule.span R _ : Submodule R N), eq1⟩
  rw [Submodule.mem_span_singleton] at b_mem
  rcases b_mem with ⟨z, eq2⟩
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `fst` pick an arbitrary such `m`. -/
def ExtensionOfMaxAdjoin.fst {y : N} (x : supExtensionOfMaxSingleton i f y) :
    (extensionOfMax i f).domain :=
  (extensionOfMax_adjoin.aux1 i x).choose

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `snd` pick an arbitrary such `r`. -/
def ExtensionOfMaxAdjoin.snd {y : N} (x : supExtensionOfMaxSingleton i f y) : R :=
  (extensionOfMax_adjoin.aux1 i x).choose_spec.choose

theorem ExtensionOfMaxAdjoin.eqn {y : N} (x : supExtensionOfMaxSingleton i f y) :
    ↑x = ↑(ExtensionOfMaxAdjoin.fst i x) + ExtensionOfMaxAdjoin.snd i x • y :=
  (extensionOfMax_adjoin.aux1 i x).choose_spec.choose_spec

variable (f)

-- TODO: refactor to use colon ideals?
/-- The ideal `I = {r | r • y ∈ N}` -/
def ExtensionOfMaxAdjoin.ideal (y : N) : Ideal R :=
  (extensionOfMax i f).domain.comap ((LinearMap.id : R →ₗ[R] R).smulRight y)

/-- A linear map `I ⟶ Q` by `x ↦ f' (x • y)` where `f'` is the maximal extension -/
def ExtensionOfMaxAdjoin.idealTo (y : N) : ExtensionOfMaxAdjoin.ideal i f y →ₗ[R] Q where
  toFun (z : { x // x ∈ ideal i f y }) := (extensionOfMax i f).toLinearPMap ⟨(↑z : R) • y, z.prop⟩
  map_add' (z1 z2 : { x // x ∈ ideal i f y }) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_add]
    congr
    apply add_smul
  map_smul' z1 (z2 : {x // x ∈ ideal i f y}) := by
    simp_rw [← (extensionOfMax i f).toLinearPMap.map_smul]
    congr 2
    apply mul_smul

/-- Since we assumed `Q` being Baer, the linear map `x ↦ f' (x • y) : I ⟶ Q` extends to `R ⟶ Q`,
call this extended map `φ` -/
def ExtensionOfMaxAdjoin.extendIdealTo (h : Module.Baer R Q) (y : N) : R →ₗ[R] Q :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose

theorem ExtensionOfMaxAdjoin.extendIdealTo_is_extension (h : Module.Baer R Q) (y : N) :
    ∀ (x : R) (mem : x ∈ ExtensionOfMaxAdjoin.ideal i f y),
      ExtensionOfMaxAdjoin.extendIdealTo i f h y x = ExtensionOfMaxAdjoin.idealTo i f y ⟨x, mem⟩ :=
  (h (ExtensionOfMaxAdjoin.ideal i f y) (ExtensionOfMaxAdjoin.idealTo i f y)).choose_spec

theorem ExtensionOfMaxAdjoin.extendIdealTo_wd' (h : Module.Baer R Q) {y : N} (r : R)
    (eq1 : r • y = 0) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r = 0 := by
  have : r ∈ ideal i f y := by
    change (r • y) ∈ (extensionOfMax i f).toLinearPMap.domain
    rw [eq1]
    apply Submodule.zero_mem _
  rw [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h y r this]
  dsimp [ExtensionOfMaxAdjoin.idealTo]
  simp only [eq1, ← ZeroMemClass.zero_def, (extensionOfMax i f).toLinearPMap.map_zero]

theorem ExtensionOfMaxAdjoin.extendIdealTo_wd (h : Module.Baer R Q) {y : N} (r r' : R)
    (eq1 : r • y = r' • y) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    ExtensionOfMaxAdjoin.extendIdealTo i f h y r' := by
  rw [← sub_eq_zero, ← map_sub]
  convert ExtensionOfMaxAdjoin.extendIdealTo_wd' i f h (r - r') _
  rw [sub_smul, sub_eq_zero, eq1]

theorem ExtensionOfMaxAdjoin.extendIdealTo_eq (h : Module.Baer R Q) {y : N} (r : R)
    (hr : r • y ∈ (extensionOfMax i f).domain) : ExtensionOfMaxAdjoin.extendIdealTo i f h y r =
    (extensionOfMax i f).toLinearPMap ⟨r • y, hr⟩ := by
  simp only [ExtensionOfMaxAdjoin.extendIdealTo_is_extension i f h _ _ hr,
    ExtensionOfMaxAdjoin.idealTo, LinearMap.coe_mk, AddHom.coe_mk]

/-- We can finally define a linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r`
-/
def ExtensionOfMaxAdjoin.extensionToFun (h : Module.Baer R Q) {y : N} :
    supExtensionOfMaxSingleton i f y → Q := fun x =>
  (extensionOfMax i f).toLinearPMap (ExtensionOfMaxAdjoin.fst i x) +
    ExtensionOfMaxAdjoin.extendIdealTo i f h y (ExtensionOfMaxAdjoin.snd i x)

theorem ExtensionOfMaxAdjoin.extensionToFun_wd (h : Module.Baer R Q) {y : N}
    (x : supExtensionOfMaxSingleton i f y) (a : (extensionOfMax i f).domain)
    (r : R) (eq1 : ↑x = ↑a + r • y) :
    ExtensionOfMaxAdjoin.extensionToFun i f h x =
      (extensionOfMax i f).toLinearPMap a + ExtensionOfMaxAdjoin.extendIdealTo i f h y r := by
  obtain ⟨a, ha⟩ := a
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

/-- The linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r` is an extension of `f` -/
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
        rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h (r • a :) _ _ eq1, map_smul,
          LinearPMap.map_smul, ← smul_add]
        congr }
  is_extension m := by
    dsimp
    rw [(extensionOfMax i f).is_extension,
      ExtensionOfMaxAdjoin.extensionToFun_wd i f h _ ⟨i m, _⟩ 0 _, map_zero, add_zero]
    simp

theorem extensionOfMax_le (h : Module.Baer R Q) {y : N} :
    extensionOfMax i f ≤ extensionOfMaxAdjoin i f h y :=
  ⟨le_sup_left, fun x x' EQ => by
    symm
    change ExtensionOfMaxAdjoin.extensionToFun i f h _ = _
    rw [ExtensionOfMaxAdjoin.extensionToFun_wd i f h x' x 0 (by simp [EQ]), map_zero,
      add_zero]⟩

theorem extensionOfMax_to_submodule_eq_top (h : Module.Baer R Q) :
    (extensionOfMax i f).domain = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  dsimp
  rw [← extensionOfMax_is_max i f _ (extensionOfMax_le i f h), extensionOfMaxAdjoin,
    Submodule.mem_sup]
  exact ⟨0, Submodule.zero_mem _, y, Submodule.mem_span_singleton_self _, zero_add _⟩

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

protected theorem of_injective [Small.{v} R] (inj : Module.Injective R Q) : Module.Baer R Q := by
  intro I g
  let eI := Shrink.linearEquiv R I
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
    let eX := ULift.moduleEquiv.{_, _, v'} (R := R) (M := X)
    have ⟨g', hg'⟩ := inj.out (ULift.moduleEquiv.{_, _, v'}.symm.toLinearMap ∘ₗ f ∘ₗ eX.toLinearMap)
      (by exact ULift.moduleEquiv.symm.injective.comp <| hf.comp eX.injective)
      (ULift.moduleEquiv.symm.toLinearMap ∘ₗ g ∘ₗ eX.toLinearMap)
    ⟨ULift.moduleEquiv.toLinearMap ∘ₗ g' ∘ₗ ULift.moduleEquiv.symm.toLinearMap,
      fun x ↦ by exact congr(ULift.down $(hg' ⟨x⟩))⟩

variable (M) [Small.{v} R]

lemma Module.injective_iff_ulift_injective :
    Module.Injective R M ↔ Module.Injective R (ULift.{v'} M) :=
  ⟨Module.ulift_injective_of_injective R,
   Module.injective_of_ulift_injective R⟩

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


universe w in
instance Module.Injective.pi
    (R : Type u) [Ring R] {ι : Type w} (M : ι → Type v) [Small.{v} R]
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Injective R (M i)] :
    Module.Injective R (∀ i, M i) :=
  ⟨fun X Y _ _ _ _ f hf g ↦ by
    choose l hl using fun i ↦ extension_property R _ _ _ f hf ((LinearMap.proj i).comp g)
    refine ⟨LinearMap.pi l, fun x ↦ ?_⟩
    ext i
    exact DFunLike.congr_fun (hl i) x⟩

universe u' in
attribute [local instance] RingHomInvPair.of_ringEquiv in
theorem Module.Injective.of_ringEquiv {R : Type u} [Ring R] [Small.{v} R] {S : Type u'} [Ring S]
    {M : Type v} {N : Type v'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[RingHomClass.toRingHom e₁] N)
    [inj : Module.Injective R M] : Module.Injective S N := by
  apply Module.Baer.injective (fun I g ↦ ?_)
  let I' := Submodule.map e₁.symm.toSemilinearEquiv.toLinearMap I
  let e : I' ≃ₛₗ[RingHomClass.toRingHom e₁] I := (e₁.symm.toSemilinearEquiv.submoduleMap I).symm
  let f : I' →ₗ[R] M := e₂.symm.toLinearMap.comp (g.comp e.toLinearMap)
  have hf (x) (hx : x ∈ I') : f ⟨x, hx⟩ = e₂.symm (g ⟨e₁ x, by simp_all [I']⟩) := rfl
  obtain ⟨f', hf'⟩ := Module.Baer.of_injective ‹_› I' f
  exact ⟨e₂.toLinearMap ∘ₛₗ f' ∘ₛₗ e₁.toSemilinearEquiv.symm.toLinearMap, by simp_all [I']⟩
