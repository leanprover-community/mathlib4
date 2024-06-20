/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Moritz Doll
-/
import Mathlib.LinearAlgebra.Prod

#align_import linear_algebra.linear_pmap from "leanprover-community/mathlib"@"8b981918a93bc45a8600de608cde7944a80d92b9"

/-!
# Partially defined linear maps

A `LinearPMap R E F` or `E →ₗ.[R] F` is a linear map from a submodule of `E` to `F`.
We define a `SemilatticeInf` with `OrderBot` instance on this, and define three operations:

* `mkSpanSingleton` defines a partial linear map defined on the span of a singleton.
* `sup` takes two partial linear maps `f`, `g` that agree on the intersection of their
  domains, and returns the unique partial linear map on `f.domain ⊔ g.domain` that
  extends both `f` and `g`.
* `sSup` takes a `DirectedOn (· ≤ ·)` set of partial linear maps, and returns the unique
  partial linear map on the `sSup` of their domains that extends all these maps.

Moreover, we define
* `LinearPMap.graph` is the graph of the partial linear map viewed as a submodule of `E × F`.

Partially defined maps are currently used in `Mathlib` to prove Hahn-Banach theorem
and its variations. Namely, `LinearPMap.sSup` implies that every chain of `LinearPMap`s
is bounded above.
They are also the basis for the theory of unbounded operators.

-/

universe u v w

/-- A `LinearPMap R E F` or `E →ₗ.[R] F` is a linear map from a submodule of `E` to `F`. -/
structure LinearPMap (R : Type u) [Ring R] (E : Type v) [AddCommGroup E] [Module R E] (F : Type w)
  [AddCommGroup F] [Module R F] where
  domain : Submodule R E
  toFun : domain →ₗ[R] F
#align linear_pmap LinearPMap

@[inherit_doc] notation:25 E " →ₗ.[" R:25 "] " F:0 => LinearPMap R E F

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E] {F : Type*}
  [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G]

namespace LinearPMap

open Submodule

-- Porting note: A new definition underlying a coercion `↑`.
@[coe]
def toFun' (f : E →ₗ.[R] F) : f.domain → F := f.toFun

instance : CoeFun (E →ₗ.[R] F) fun f : E →ₗ.[R] F => f.domain → F :=
  ⟨toFun'⟩

@[simp]
theorem toFun_eq_coe (f : E →ₗ.[R] F) (x : f.domain) : f.toFun x = f x :=
  rfl
#align linear_pmap.to_fun_eq_coe LinearPMap.toFun_eq_coe

@[ext]
theorem ext {f g : E →ₗ.[R] F} (h : f.domain = g.domain)
    (h' : ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y) : f = g := by
  rcases f with ⟨f_dom, f⟩
  rcases g with ⟨g_dom, g⟩
  obtain rfl : f_dom = g_dom := h
  obtain rfl : f = g := LinearMap.ext fun x => h' rfl
  rfl
#align linear_pmap.ext LinearPMap.ext

@[simp]
theorem map_zero (f : E →ₗ.[R] F) : f 0 = 0 :=
  f.toFun.map_zero
#align linear_pmap.map_zero LinearPMap.map_zero

theorem ext_iff {f g : E →ₗ.[R] F} :
    f = g ↔
      ∃ _domain_eq : f.domain = g.domain,
        ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y :=
  ⟨fun EQ =>
    EQ ▸
      ⟨rfl, fun x y h => by
        congr
        exact mod_cast h⟩,
    fun ⟨deq, feq⟩ => ext deq feq⟩
#align linear_pmap.ext_iff LinearPMap.ext_iff

theorem ext' {s : Submodule R E} {f g : s →ₗ[R] F} (h : f = g) : mk s f = mk s g :=
  h ▸ rfl
#align linear_pmap.ext' LinearPMap.ext'

theorem map_add (f : E →ₗ.[R] F) (x y : f.domain) : f (x + y) = f x + f y :=
  f.toFun.map_add x y
#align linear_pmap.map_add LinearPMap.map_add

theorem map_neg (f : E →ₗ.[R] F) (x : f.domain) : f (-x) = -f x :=
  f.toFun.map_neg x
#align linear_pmap.map_neg LinearPMap.map_neg

theorem map_sub (f : E →ₗ.[R] F) (x y : f.domain) : f (x - y) = f x - f y :=
  f.toFun.map_sub x y
#align linear_pmap.map_sub LinearPMap.map_sub

theorem map_smul (f : E →ₗ.[R] F) (c : R) (x : f.domain) : f (c • x) = c • f x :=
  f.toFun.map_smul c x
#align linear_pmap.map_smul LinearPMap.map_smul

@[simp]
theorem mk_apply (p : Submodule R E) (f : p →ₗ[R] F) (x : p) : mk p f x = f x :=
  rfl
#align linear_pmap.mk_apply LinearPMap.mk_apply

/-- The unique `LinearPMap` on `R ∙ x` that sends `x` to `y`. This version works for modules
over rings, and requires a proof of `∀ c, c • x = 0 → c • y = 0`. -/
noncomputable def mkSpanSingleton' (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) :
    E →ₗ.[R] F where
  domain := R ∙ x
  toFun :=
    have H : ∀ c₁ c₂ : R, c₁ • x = c₂ • x → c₁ • y = c₂ • y := by
      intro c₁ c₂ h
      rw [← sub_eq_zero, ← sub_smul] at h ⊢
      exact H _ h
    { toFun := fun z => Classical.choose (mem_span_singleton.1 z.prop) • y
      -- Porting note(#12129): additional beta reduction needed
      -- Porting note: Were `Classical.choose_spec (mem_span_singleton.1 _)`.
      map_add' := fun y z => by
        beta_reduce
        rw [← add_smul]
        apply H
        simp only [add_smul, sub_smul,
          fun w : R ∙ x => Classical.choose_spec (mem_span_singleton.1 w.prop)]
        apply coe_add
      map_smul' := fun c z => by
        beta_reduce
        rw [smul_smul]
        apply H
        simp only [mul_smul,
          fun w : R ∙ x => Classical.choose_spec (mem_span_singleton.1 w.prop)]
        apply coe_smul }
#align linear_pmap.mk_span_singleton' LinearPMap.mkSpanSingleton'

@[simp]
theorem domain_mkSpanSingleton (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) :
    (mkSpanSingleton' x y H).domain = R ∙ x :=
  rfl
#align linear_pmap.domain_mk_span_singleton LinearPMap.domain_mkSpanSingleton

@[simp]
theorem mkSpanSingleton'_apply (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) (c : R) (h) :
    mkSpanSingleton' x y H ⟨c • x, h⟩ = c • y := by
  dsimp [mkSpanSingleton']
  rw [← sub_eq_zero, ← sub_smul]
  apply H
  simp only [sub_smul, one_smul, sub_eq_zero]
  apply Classical.choose_spec (mem_span_singleton.1 h)
#align linear_pmap.mk_span_singleton'_apply LinearPMap.mkSpanSingleton'_apply

@[simp]
theorem mkSpanSingleton'_apply_self (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) (h) :
    mkSpanSingleton' x y H ⟨x, h⟩ = y := by
  -- Porting note: A placeholder should be specified before `convert`.
  have := by refine mkSpanSingleton'_apply x y H 1 ?_; rwa [one_smul]
  convert this <;> rw [one_smul]
#align linear_pmap.mk_span_singleton'_apply_self LinearPMap.mkSpanSingleton'_apply_self

/-- The unique `LinearPMap` on `span R {x}` that sends a non-zero vector `x` to `y`.
This version works for modules over division rings. -/
noncomputable abbrev mkSpanSingleton {K E F : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (x : E) (y : F) (hx : x ≠ 0) : E →ₗ.[K] F :=
  mkSpanSingleton' x y fun c hc =>
    (smul_eq_zero.1 hc).elim (fun hc => by rw [hc, zero_smul]) fun hx' => absurd hx' hx
#align linear_pmap.mk_span_singleton LinearPMap.mkSpanSingleton

theorem mkSpanSingleton_apply (K : Type*) {E F : Type*} [DivisionRing K] [AddCommGroup E]
    [Module K E] [AddCommGroup F] [Module K F] {x : E} (hx : x ≠ 0) (y : F) :
    mkSpanSingleton x y hx ⟨x, (Submodule.mem_span_singleton_self x : x ∈ Submodule.span K {x})⟩ =
      y :=
  LinearPMap.mkSpanSingleton'_apply_self _ _ _ _
#align linear_pmap.mk_span_singleton_apply LinearPMap.mkSpanSingleton_apply

/-- Projection to the first coordinate as a `LinearPMap` -/
protected def fst (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] E where
  domain := p.prod p'
  toFun := (LinearMap.fst R E F).comp (p.prod p').subtype
#align linear_pmap.fst LinearPMap.fst

@[simp]
theorem fst_apply (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') :
    LinearPMap.fst p p' x = (x : E × F).1 :=
  rfl
#align linear_pmap.fst_apply LinearPMap.fst_apply

/-- Projection to the second coordinate as a `LinearPMap` -/
protected def snd (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] F where
  domain := p.prod p'
  toFun := (LinearMap.snd R E F).comp (p.prod p').subtype
#align linear_pmap.snd LinearPMap.snd

@[simp]
theorem snd_apply (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') :
    LinearPMap.snd p p' x = (x : E × F).2 :=
  rfl
#align linear_pmap.snd_apply LinearPMap.snd_apply

instance le : LE (E →ₗ.[R] F) :=
  ⟨fun f g => f.domain ≤ g.domain ∧ ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y⟩
#align linear_pmap.has_le LinearPMap.le

theorem apply_comp_inclusion {T S : E →ₗ.[R] F} (h : T ≤ S) (x : T.domain) :
    T x = S (Submodule.inclusion h.1 x) :=
  h.2 rfl
#align linear_pmap.apply_comp_of_le LinearPMap.apply_comp_inclusion

theorem exists_of_le {T S : E →ₗ.[R] F} (h : T ≤ S) (x : T.domain) :
    ∃ y : S.domain, (x : E) = y ∧ T x = S y :=
  ⟨⟨x.1, h.1 x.2⟩, ⟨rfl, h.2 rfl⟩⟩
#align linear_pmap.exists_of_le LinearPMap.exists_of_le

theorem eq_of_le_of_domain_eq {f g : E →ₗ.[R] F} (hle : f ≤ g) (heq : f.domain = g.domain) :
    f = g :=
  ext heq hle.2
#align linear_pmap.eq_of_le_of_domain_eq LinearPMap.eq_of_le_of_domain_eq

/-- Given two partial linear maps `f`, `g`, the set of points `x` such that
both `f` and `g` are defined at `x` and `f x = g x` form a submodule. -/
def eqLocus (f g : E →ₗ.[R] F) : Submodule R E where
  carrier := { x | ∃ (hf : x ∈ f.domain) (hg : x ∈ g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ }
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩
  add_mem' := fun {x y} ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ =>
    ⟨add_mem hfx hfy, add_mem hgx hgy, by
      erw [f.map_add ⟨x, hfx⟩ ⟨y, hfy⟩, g.map_add ⟨x, hgx⟩ ⟨y, hgy⟩, hx, hy]⟩
  -- Porting note: `by rintro` is required, or error of a free variable happens.
  smul_mem' := by
    rintro c x ⟨hfx, hgx, hx⟩
    exact
      ⟨smul_mem _ c hfx, smul_mem _ c hgx,
        by erw [f.map_smul c ⟨x, hfx⟩, g.map_smul c ⟨x, hgx⟩, hx]⟩
#align linear_pmap.eq_locus LinearPMap.eqLocus

instance inf : Inf (E →ₗ.[R] F) :=
  ⟨fun f g => ⟨f.eqLocus g, f.toFun.comp <| inclusion fun _x hx => hx.fst⟩⟩
#align linear_pmap.has_inf LinearPMap.inf

instance bot : Bot (E →ₗ.[R] F) :=
  ⟨⟨⊥, 0⟩⟩
#align linear_pmap.has_bot LinearPMap.bot

instance inhabited : Inhabited (E →ₗ.[R] F) :=
  ⟨⊥⟩
#align linear_pmap.inhabited LinearPMap.inhabited

instance semilatticeInf : SemilatticeInf (E →ₗ.[R] F) where
  le := (· ≤ ·)
  le_refl f := ⟨le_refl f.domain, fun x y h => Subtype.eq h ▸ rfl⟩
  le_trans := fun f g h ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩ =>
    ⟨le_trans fg_le gh_le, fun x z hxz =>
      have hxy : (x : E) = inclusion fg_le x := rfl
      (fg_eq hxy).trans (gh_eq <| hxy.symm.trans hxz)⟩
  le_antisymm f g fg gf := eq_of_le_of_domain_eq fg (le_antisymm fg.1 gf.1)
  inf := (· ⊓ ·)
  -- Porting note: `by rintro` is required, or error of a metavariable happens.
  le_inf := by
    rintro f g h ⟨fg_le, fg_eq⟩ ⟨fh_le, fh_eq⟩
    exact ⟨fun x hx =>
      ⟨fg_le hx, fh_le hx, by
        -- Porting note: `[exact ⟨x, hx⟩, rfl, rfl]` → `[skip, exact ⟨x, hx⟩, skip] <;> rfl`
        convert (fg_eq _).symm.trans (fh_eq _) <;> [skip; exact ⟨x, hx⟩; skip] <;> rfl⟩,
      fun x ⟨y, yg, hy⟩ h => by
        apply fg_eq
        exact h⟩
  inf_le_left f g := ⟨fun x hx => hx.fst, fun x y h => congr_arg f <| Subtype.eq <| h⟩
  inf_le_right f g :=
    ⟨fun x hx => hx.snd.fst, fun ⟨x, xf, xg, hx⟩ y h => hx.trans <| congr_arg g <| Subtype.eq <| h⟩
#align linear_pmap.semilattice_inf LinearPMap.semilatticeInf

instance orderBot : OrderBot (E →ₗ.[R] F) where
  bot := ⊥
  bot_le f :=
    ⟨bot_le, fun x y h => by
      have hx : x = 0 := Subtype.eq ((mem_bot R).1 x.2)
      have hy : y = 0 := Subtype.eq (h.symm.trans (congr_arg _ hx))
      rw [hx, hy, map_zero, map_zero]⟩
#align linear_pmap.order_bot LinearPMap.orderBot

theorem le_of_eqLocus_ge {f g : E →ₗ.[R] F} (H : f.domain ≤ f.eqLocus g) : f ≤ g :=
  suffices f ≤ f ⊓ g from le_trans this inf_le_right
  ⟨H, fun _x _y hxy => ((inf_le_left : f ⊓ g ≤ f).2 hxy.symm).symm⟩
#align linear_pmap.le_of_eq_locus_ge LinearPMap.le_of_eqLocus_ge

theorem domain_mono : StrictMono (@domain R _ E _ _ F _ _) := fun _f _g hlt =>
  lt_of_le_of_ne hlt.1.1 fun heq => ne_of_lt hlt <| eq_of_le_of_domain_eq (le_of_lt hlt) heq
#align linear_pmap.domain_mono LinearPMap.domain_mono

private theorem sup_aux (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    ∃ fg : ↥(f.domain ⊔ g.domain) →ₗ[R] F,
      ∀ (x : f.domain) (y : g.domain) (z : ↥(f.domain ⊔ g.domain)),
        (x : E) + y = ↑z → fg z = f x + g y := by
  choose x hx y hy hxy using fun z : ↥(f.domain ⊔ g.domain) => mem_sup.1 z.prop
  set fg := fun z => f ⟨x z, hx z⟩ + g ⟨y z, hy z⟩
  have fg_eq : ∀ (x' : f.domain) (y' : g.domain) (z' : ↥(f.domain ⊔ g.domain))
      (_H : (x' : E) + y' = z'), fg z' = f x' + g y' := by
    intro x' y' z' H
    dsimp [fg]
    rw [add_comm, ← sub_eq_sub_iff_add_eq_add, eq_comm, ← map_sub, ← map_sub]
    apply h
    simp only [← eq_sub_iff_add_eq] at hxy
    simp only [AddSubgroupClass.coe_sub, coe_mk, coe_mk, hxy, ← sub_add, ← sub_sub, sub_self,
      zero_sub, ← H]
    apply neg_add_eq_sub
  use { toFun := fg, map_add' := ?_, map_smul' := ?_ }, fg_eq
  · rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    rw [← add_assoc, add_right_comm (f _), ← map_add, add_assoc, ← map_add]
    apply fg_eq
    simp only [coe_add, coe_mk, ← add_assoc]
    rw [add_right_comm (x _), hxy, add_assoc, hxy, coe_mk, coe_mk]
  · intro c z
    rw [smul_add, ← map_smul, ← map_smul]
    apply fg_eq
    simp only [coe_smul, coe_mk, ← smul_add, hxy, RingHom.id_apply]

/-- Given two partial linear maps that agree on the intersection of their domains,
`f.sup g h` is the unique partial linear map on `f.domain ⊔ g.domain` that agrees
with `f` and `g`. -/
protected noncomputable def sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : E →ₗ.[R] F :=
  ⟨_, Classical.choose (sup_aux f g h)⟩
#align linear_pmap.sup LinearPMap.sup

@[simp]
theorem domain_sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    (f.sup g h).domain = f.domain ⊔ g.domain :=
  rfl
#align linear_pmap.domain_sup LinearPMap.domain_sup

theorem sup_apply {f g : E →ₗ.[R] F} (H : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y)
    (x : f.domain) (y : g.domain) (z : ↥(f.domain ⊔ g.domain)) (hz : (↑x : E) + ↑y = ↑z) :
    f.sup g H z = f x + g y :=
  Classical.choose_spec (sup_aux f g H) x y z hz
#align linear_pmap.sup_apply LinearPMap.sup_apply

protected theorem left_le_sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : f ≤ f.sup g h := by
  refine ⟨le_sup_left, fun z₁ z₂ hz => ?_⟩
  rw [← add_zero (f _), ← g.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa
#align linear_pmap.left_le_sup LinearPMap.left_le_sup

protected theorem right_le_sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : g ≤ f.sup g h := by
  refine ⟨le_sup_right, fun z₁ z₂ hz => ?_⟩
  rw [← zero_add (g _), ← f.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa
#align linear_pmap.right_le_sup LinearPMap.right_le_sup

protected theorem sup_le {f g h : E →ₗ.[R] F}
    (H : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) (fh : f ≤ h) (gh : g ≤ h) :
    f.sup g H ≤ h :=
  have Hf : f ≤ f.sup g H ⊓ h := le_inf (f.left_le_sup g H) fh
  have Hg : g ≤ f.sup g H ⊓ h := le_inf (f.right_le_sup g H) gh
  le_of_eqLocus_ge <| sup_le Hf.1 Hg.1
#align linear_pmap.sup_le LinearPMap.sup_le

/-- Hypothesis for `LinearPMap.sup` holds, if `f.domain` is disjoint with `g.domain`. -/
theorem sup_h_of_disjoint (f g : E →ₗ.[R] F) (h : Disjoint f.domain g.domain) (x : f.domain)
    (y : g.domain) (hxy : (x : E) = y) : f x = g y := by
  rw [disjoint_def] at h
  have hy : y = 0 := Subtype.eq (h y (hxy ▸ x.2) y.2)
  have hx : x = 0 := Subtype.eq (hxy.trans <| congr_arg _ hy)
  simp [*]
#align linear_pmap.sup_h_of_disjoint LinearPMap.sup_h_of_disjoint

/-! ### Algebraic operations -/


section Zero

instance instZero : Zero (E →ₗ.[R] F) := ⟨⊤, 0⟩

@[simp]
theorem zero_domain : (0 : E →ₗ.[R] F).domain = ⊤ := rfl

@[simp]
theorem zero_apply (x : (⊤ : Submodule R E)) : (0 : E →ₗ.[R] F) x = 0 := rfl

end Zero

section SMul

variable {M N : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass R M F]
variable [Monoid N] [DistribMulAction N F] [SMulCommClass R N F]

instance instSMul : SMul M (E →ₗ.[R] F) :=
  ⟨fun a f =>
    { domain := f.domain
      toFun := a • f.toFun }⟩
#align linear_pmap.has_smul LinearPMap.instSMul

@[simp]
theorem smul_domain (a : M) (f : E →ₗ.[R] F) : (a • f).domain = f.domain :=
  rfl
#align linear_pmap.smul_domain LinearPMap.smul_domain

theorem smul_apply (a : M) (f : E →ₗ.[R] F) (x : (a • f).domain) : (a • f) x = a • f x :=
  rfl
#align linear_pmap.smul_apply LinearPMap.smul_apply

@[simp]
theorem coe_smul (a : M) (f : E →ₗ.[R] F) : ⇑(a • f) = a • ⇑f :=
  rfl
#align linear_pmap.coe_smul LinearPMap.coe_smul

instance instSMulCommClass [SMulCommClass M N F] : SMulCommClass M N (E →ₗ.[R] F) :=
  ⟨fun a b f => ext' <| smul_comm a b f.toFun⟩
#align linear_pmap.smul_comm_class LinearPMap.instSMulCommClass

instance instIsScalarTower [SMul M N] [IsScalarTower M N F] : IsScalarTower M N (E →ₗ.[R] F) :=
  ⟨fun a b f => ext' <| smul_assoc a b f.toFun⟩
#align linear_pmap.is_scalar_tower LinearPMap.instIsScalarTower

instance instMulAction : MulAction M (E →ₗ.[R] F) where
  smul := (· • ·)
  one_smul := fun ⟨_s, f⟩ => ext' <| one_smul M f
  mul_smul a b f := ext' <| mul_smul a b f.toFun
#align linear_pmap.mul_action LinearPMap.instMulAction

end SMul

instance instNeg : Neg (E →ₗ.[R] F) :=
  ⟨fun f => ⟨f.domain, -f.toFun⟩⟩
#align linear_pmap.has_neg LinearPMap.instNeg

@[simp]
theorem neg_domain (f : E →ₗ.[R] F) : (-f).domain = f.domain := rfl

@[simp]
theorem neg_apply (f : E →ₗ.[R] F) (x) : (-f) x = -f x :=
  rfl
#align linear_pmap.neg_apply LinearPMap.neg_apply

instance instInvolutiveNeg : InvolutiveNeg (E →ₗ.[R] F) :=
  ⟨fun f => by
    ext x y hxy
    · rfl
    · simp only [neg_apply, neg_neg]
      cases x
      congr⟩

section Add

instance instAdd : Add (E →ₗ.[R] F) :=
  ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain ≤ _))
        + g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain ≤ _)) }⟩

theorem add_domain (f g : E →ₗ.[R] F) : (f + g).domain = f.domain ⊓ g.domain := rfl

theorem add_apply (f g : E →ₗ.[R] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
    (f + g) x = f ⟨x, x.prop.1⟩ + g ⟨x, x.prop.2⟩ := rfl

instance instAddSemigroup : AddSemigroup (E →ₗ.[R] F) :=
  ⟨fun f g h => by
    ext x y hxy
    · simp only [add_domain, inf_assoc]
    · simp only [add_apply, hxy, add_assoc]⟩

instance instAddZeroClass : AddZeroClass (E →ₗ.[R] F) :=
  ⟨fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp only [add_apply, hxy, zero_apply, zero_add],
  fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp only [add_apply, hxy, zero_apply, add_zero]⟩

instance instAddMonoid : AddMonoid (E →ₗ.[R] F) where
  zero_add f := by
    simp
  add_zero := by
    simp
  nsmul := nsmulRec

instance instAddCommMonoid : AddCommMonoid (E →ₗ.[R] F) :=
  ⟨fun f g => by
    ext x y hxy
    · simp only [add_domain, inf_comm]
    · simp only [add_apply, hxy, add_comm]⟩

end Add

section VAdd

instance instVAdd : VAdd (E →ₗ[R] F) (E →ₗ.[R] F) :=
  ⟨fun f g =>
    { domain := g.domain
      toFun := f.comp g.domain.subtype + g.toFun }⟩
#align linear_pmap.has_vadd LinearPMap.instVAdd

@[simp]
theorem vadd_domain (f : E →ₗ[R] F) (g : E →ₗ.[R] F) : (f +ᵥ g).domain = g.domain :=
  rfl
#align linear_pmap.vadd_domain LinearPMap.vadd_domain

theorem vadd_apply (f : E →ₗ[R] F) (g : E →ₗ.[R] F) (x : (f +ᵥ g).domain) :
    (f +ᵥ g) x = f x + g x :=
  rfl
#align linear_pmap.vadd_apply LinearPMap.vadd_apply

@[simp]
theorem coe_vadd (f : E →ₗ[R] F) (g : E →ₗ.[R] F) : ⇑(f +ᵥ g) = ⇑(f.comp g.domain.subtype) + ⇑g :=
  rfl
#align linear_pmap.coe_vadd LinearPMap.coe_vadd

instance instAddAction : AddAction (E →ₗ[R] F) (E →ₗ.[R] F) where
  vadd := (· +ᵥ ·)
  zero_vadd := fun ⟨_s, _f⟩ => ext' <| zero_add _
  add_vadd := fun _f₁ _f₂ ⟨_s, _g⟩ => ext' <| LinearMap.ext fun _x => add_assoc _ _ _
#align linear_pmap.add_action LinearPMap.instAddAction

end VAdd

section Sub

instance instSub : Sub (E →ₗ.[R] F) :=
  ⟨fun f g =>
    { domain := f.domain ⊓ g.domain
      toFun := f.toFun.comp (inclusion (inf_le_left : f.domain ⊓ g.domain ≤ _))
        - g.toFun.comp (inclusion (inf_le_right : f.domain ⊓ g.domain ≤ _)) }⟩

theorem sub_domain (f g : E →ₗ.[R] F) : (f - g).domain = f.domain ⊓ g.domain := rfl

theorem sub_apply (f g : E →ₗ.[R] F) (x : (f.domain ⊓ g.domain : Submodule R E)) :
    (f - g) x = f ⟨x, x.prop.1⟩ - g ⟨x, x.prop.2⟩ := rfl

instance instSubtractionCommMonoid : SubtractionCommMonoid (E →ₗ.[R] F) where
  add_comm := add_comm
  sub_eq_add_neg f g := by
    ext x y h
    · rfl
    simp [sub_apply, add_apply, neg_apply, ← sub_eq_add_neg, h]
  neg_neg := neg_neg
  neg_add_rev f g := by
    ext x y h
    · simp [add_domain, sub_domain, neg_domain, And.comm]
    simp [sub_apply, add_apply, neg_apply, ← sub_eq_add_neg, h]
  neg_eq_of_add f g h' := by
    ext x y h
    · have : (0 : E →ₗ.[R] F).domain = ⊤ := zero_domain
      simp only [← h', add_domain, ge_iff_le, inf_eq_top_iff] at this
      rw [neg_domain, this.1, this.2]
    simp only [inf_coe, neg_domain, Eq.ndrec, Int.ofNat_eq_coe, neg_apply]
    rw [ext_iff] at h'
    rcases h' with ⟨hdom, h'⟩
    rw [zero_domain] at hdom
    simp only [inf_coe, neg_domain, Eq.ndrec, Int.ofNat_eq_coe, zero_domain, top_coe, zero_apply,
      Subtype.forall, mem_top, forall_true_left, forall_eq'] at h'
    specialize h' x.1 (by simp [hdom])
    simp only [inf_coe, neg_domain, Eq.ndrec, Int.ofNat_eq_coe, add_apply, Subtype.coe_eta,
      ← neg_eq_iff_add_eq_zero] at h'
    rw [h', h]
  zsmul := zsmulRec

end Sub

section

variable {K : Type*} [DivisionRing K] [Module K E] [Module K F]

/-- Extend a `LinearPMap` to `f.domain ⊔ K ∙ x`. -/
noncomputable def supSpanSingleton (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    E →ₗ.[K] F :=
  -- Porting note: `simpa [..]` → `simp [..]; exact ..`
  f.sup (mkSpanSingleton x y fun h₀ => hx <| h₀.symm ▸ f.domain.zero_mem) <|
    sup_h_of_disjoint _ _ <| by simp [disjoint_span_singleton]; exact fun h => False.elim <| hx h
#align linear_pmap.sup_span_singleton LinearPMap.supSpanSingleton

@[simp]
theorem domain_supSpanSingleton (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    (f.supSpanSingleton x y hx).domain = f.domain ⊔ K ∙ x :=
  rfl
#align linear_pmap.domain_sup_span_singleton LinearPMap.domain_supSpanSingleton

@[simp] -- Porting note: Left-hand side does not simplify.
theorem supSpanSingleton_apply_mk (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E)
    (hx' : x' ∈ f.domain) (c : K) :
    f.supSpanSingleton x y hx
        ⟨x' + c • x, mem_sup.2 ⟨x', hx', _, mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩⟩ =
      f ⟨x', hx'⟩ + c • y := by
  -- Porting note: `erw [..]; rfl; exact ..` → `erw [..]; exact ..; rfl`
  -- That is, the order of the side goals generated by `erw` changed.
  erw [sup_apply _ ⟨x', hx'⟩ ⟨c • x, _⟩, mkSpanSingleton'_apply]
  · exact mem_span_singleton.2 ⟨c, rfl⟩
  · rfl
#align linear_pmap.sup_span_singleton_apply_mk LinearPMap.supSpanSingleton_apply_mk

end

private theorem sSup_aux (c : Set (E →ₗ.[R] F)) (hc : DirectedOn (· ≤ ·) c) :
    ∃ f : ↥(sSup (domain '' c)) →ₗ[R] F, (⟨_, f⟩ : E →ₗ.[R] F) ∈ upperBounds c := by
  rcases c.eq_empty_or_nonempty with ceq | cne
  · subst c
    simp
  have hdir : DirectedOn (· ≤ ·) (domain '' c) :=
    directedOn_image.2 (hc.mono @(domain_mono.monotone))
  have P : ∀ x : ↥(sSup (domain '' c)), { p : c // (x : E) ∈ p.val.domain } := by
    rintro x
    apply Classical.indefiniteDescription
    have := (mem_sSup_of_directed (cne.image _) hdir).1 x.2
    -- Porting note: + `← bex_def`
    rwa [Set.exists_mem_image, ← bex_def, SetCoe.exists'] at this
  set f : ↥(sSup (domain '' c)) → F := fun x => (P x).val.val ⟨x, (P x).property⟩
  have f_eq : ∀ (p : c) (x : ↥(sSup (domain '' c))) (y : p.1.1) (_hxy : (x : E) = y),
      f x = p.1 y := by
    intro p x y hxy
    rcases hc (P x).1.1 (P x).1.2 p.1 p.2 with ⟨q, _hqc, hxq, hpq⟩
    -- Porting note: `refine' ..; exacts [inclusion hpq.1 y, hxy, rfl]`
    --               → `refine' .. <;> [skip; exact inclusion hpq.1 y; rfl]; exact hxy`
    convert (hxq.2 _).trans (hpq.2 _).symm <;> [skip; exact inclusion hpq.1 y; rfl]; exact hxy
  use { toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_
  · intro x y
    rcases hc (P x).1.1 (P x).1.2 (P y).1.1 (P y).1.2 with ⟨p, hpc, hpx, hpy⟩
    set x' := inclusion hpx.1 ⟨x, (P x).2⟩
    set y' := inclusion hpy.1 ⟨y, (P y).2⟩
    rw [f_eq ⟨p, hpc⟩ x x' rfl, f_eq ⟨p, hpc⟩ y y' rfl, f_eq ⟨p, hpc⟩ (x + y) (x' + y') rfl,
      map_add]
  · intro c x
    simp only [RingHom.id_apply]
    rw [f_eq (P x).1 (c • x) (c • ⟨x, (P x).2⟩) rfl, ← map_smul]
  · intro p hpc
    refine ⟨le_sSup <| Set.mem_image_of_mem domain hpc, fun x y hxy => Eq.symm ?_⟩
    exact f_eq ⟨p, hpc⟩ _ _ hxy.symm

protected noncomputable def sSup (c : Set (E →ₗ.[R] F)) (hc : DirectedOn (· ≤ ·) c) : E →ₗ.[R] F :=
  ⟨_, Classical.choose <| sSup_aux c hc⟩
#align linear_pmap.Sup LinearPMap.sSup

protected theorem le_sSup {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {f : E →ₗ.[R] F}
    (hf : f ∈ c) : f ≤ LinearPMap.sSup c hc :=
  Classical.choose_spec (sSup_aux c hc) hf
#align linear_pmap.le_Sup LinearPMap.le_sSup

protected theorem sSup_le {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {g : E →ₗ.[R] F}
    (hg : ∀ f ∈ c, f ≤ g) : LinearPMap.sSup c hc ≤ g :=
  le_of_eqLocus_ge <|
    sSup_le fun _ ⟨f, hf, Eq⟩ =>
      Eq ▸
        have : f ≤ LinearPMap.sSup c hc ⊓ g := le_inf (LinearPMap.le_sSup _ hf) (hg f hf)
        this.1
#align linear_pmap.Sup_le LinearPMap.sSup_le

protected theorem sSup_apply {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {l : E →ₗ.[R] F}
    (hl : l ∈ c) (x : l.domain) :
    (LinearPMap.sSup c hc) ⟨x, (LinearPMap.le_sSup hc hl).1 x.2⟩ = l x := by
  symm
  apply (Classical.choose_spec (sSup_aux c hc) hl).2
  rfl
#align linear_pmap.Sup_apply LinearPMap.sSup_apply

end LinearPMap

namespace LinearMap

/-- Restrict a linear map to a submodule, reinterpreting the result as a `LinearPMap`. -/
def toPMap (f : E →ₗ[R] F) (p : Submodule R E) : E →ₗ.[R] F :=
  ⟨p, f.comp p.subtype⟩
#align linear_map.to_pmap LinearMap.toPMap

@[simp]
theorem toPMap_apply (f : E →ₗ[R] F) (p : Submodule R E) (x : p) : f.toPMap p x = f x :=
  rfl
#align linear_map.to_pmap_apply LinearMap.toPMap_apply

@[simp]
theorem toPMap_domain (f : E →ₗ[R] F) (p : Submodule R E) : (f.toPMap p).domain = p :=
  rfl
#align linear_map.to_pmap_domain LinearMap.toPMap_domain

/-- Compose a linear map with a `LinearPMap` -/
def compPMap (g : F →ₗ[R] G) (f : E →ₗ.[R] F) : E →ₗ.[R] G where
  domain := f.domain
  toFun := g.comp f.toFun
#align linear_map.comp_pmap LinearMap.compPMap

@[simp]
theorem compPMap_apply (g : F →ₗ[R] G) (f : E →ₗ.[R] F) (x) : g.compPMap f x = g (f x) :=
  rfl
#align linear_map.comp_pmap_apply LinearMap.compPMap_apply

end LinearMap

namespace LinearPMap

/-- Restrict codomain of a `LinearPMap` -/
def codRestrict (f : E →ₗ.[R] F) (p : Submodule R F) (H : ∀ x, f x ∈ p) : E →ₗ.[R] p where
  domain := f.domain
  toFun := f.toFun.codRestrict p H
#align linear_pmap.cod_restrict LinearPMap.codRestrict

/-- Compose two `LinearPMap`s -/
def comp (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) (H : ∀ x : f.domain, f x ∈ g.domain) : E →ₗ.[R] G :=
  g.toFun.compPMap <| f.codRestrict _ H
#align linear_pmap.comp LinearPMap.comp

/-- `f.coprod g` is the partially defined linear map defined on `f.domain × g.domain`,
and sending `p` to `f p.1 + g p.2`. -/
def coprod (f : E →ₗ.[R] G) (g : F →ₗ.[R] G) : E × F →ₗ.[R] G where
  domain := f.domain.prod g.domain
  toFun :=
    -- Porting note: This is just
    -- `(f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun +`
    -- `  (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun`,
    HAdd.hAdd
      (α := f.domain.prod g.domain →ₗ[R] G)
      (β := f.domain.prod g.domain →ₗ[R] G)
      (f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun
      (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun
#align linear_pmap.coprod LinearPMap.coprod

@[simp]
theorem coprod_apply (f : E →ₗ.[R] G) (g : F →ₗ.[R] G) (x) :
    f.coprod g x = f ⟨(x : E × F).1, x.2.1⟩ + g ⟨(x : E × F).2, x.2.2⟩ :=
  rfl
#align linear_pmap.coprod_apply LinearPMap.coprod_apply

/-- Restrict a partially defined linear map to a submodule of `E` contained in `f.domain`. -/
def domRestrict (f : E →ₗ.[R] F) (S : Submodule R E) : E →ₗ.[R] F :=
  ⟨S ⊓ f.domain, f.toFun.comp (Submodule.inclusion (by simp))⟩
#align linear_pmap.dom_restrict LinearPMap.domRestrict

@[simp]
theorem domRestrict_domain (f : E →ₗ.[R] F) {S : Submodule R E} :
    (f.domRestrict S).domain = S ⊓ f.domain :=
  rfl
#align linear_pmap.dom_restrict_domain LinearPMap.domRestrict_domain

theorem domRestrict_apply {f : E →ₗ.[R] F} {S : Submodule R E} ⦃x : ↥(S ⊓ f.domain)⦄ ⦃y : f.domain⦄
    (h : (x : E) = y) : f.domRestrict S x = f y := by
  have : Submodule.inclusion (by simp) x = y := by
    ext
    simp [h]
  rw [← this]
  exact LinearPMap.mk_apply _ _ _
#align linear_pmap.dom_restrict_apply LinearPMap.domRestrict_apply

theorem domRestrict_le {f : E →ₗ.[R] F} {S : Submodule R E} : f.domRestrict S ≤ f :=
  ⟨by simp, fun x y hxy => domRestrict_apply hxy⟩
#align linear_pmap.dom_restrict_le LinearPMap.domRestrict_le

/-! ### Graph -/


section Graph

/-- The graph of a `LinearPMap` viewed as a submodule on `E × F`. -/
def graph (f : E →ₗ.[R] F) : Submodule R (E × F) :=
  f.toFun.graph.map (f.domain.subtype.prodMap (LinearMap.id : F →ₗ[R] F))
#align linear_pmap.graph LinearPMap.graph

theorem mem_graph_iff' (f : E →ₗ.[R] F) {x : E × F} :
    x ∈ f.graph ↔ ∃ y : f.domain, (↑y, f y) = x := by simp [graph]
#align linear_pmap.mem_graph_iff' LinearPMap.mem_graph_iff'

@[simp]
theorem mem_graph_iff (f : E →ₗ.[R] F) {x : E × F} :
    x ∈ f.graph ↔ ∃ y : f.domain, (↑y : E) = x.1 ∧ f y = x.2 := by
  cases x
  simp_rw [mem_graph_iff', Prod.mk.inj_iff]
#align linear_pmap.mem_graph_iff LinearPMap.mem_graph_iff

/-- The tuple `(x, f x)` is contained in the graph of `f`. -/
theorem mem_graph (f : E →ₗ.[R] F) (x : domain f) : ((x : E), f x) ∈ f.graph := by simp
#align linear_pmap.mem_graph LinearPMap.mem_graph

theorem graph_map_fst_eq_domain (f : E →ₗ.[R] F) :
    f.graph.map (LinearMap.fst R E F) = f.domain := by
  ext x
  simp only [Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left,
    LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
  constructor <;> intro h
  · rcases h with ⟨x, hx, _⟩
    exact hx
  · use f ⟨x, h⟩
    simp only [h, exists_const]

theorem graph_map_snd_eq_range (f : E →ₗ.[R] F) :
    f.graph.map (LinearMap.snd R E F) = LinearMap.range f.toFun := by ext; simp

variable {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass R M F] (y : M)

/-- The graph of `z • f` as a pushforward. -/
theorem smul_graph (f : E →ₗ.[R] F) (z : M) :
    (z • f).graph =
      f.graph.map ((LinearMap.id : E →ₗ[R] E).prodMap (z • (LinearMap.id : F →ₗ[R] F))) := by
  ext x; cases' x with x_fst x_snd
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.smul_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.smul_apply, Prod.mk.inj_iff, Prod.exists, exists_exists_and_eq_and]
    use x_fst, y, hy
  rw [Submodule.mem_map] at h
  rcases h with ⟨x', hx', h⟩
  cases x'
  simp only [LinearMap.prodMap_apply, LinearMap.id_coe, id, LinearMap.smul_apply,
    Prod.mk.inj_iff] at h
  rw [mem_graph_iff] at hx' ⊢
  rcases hx' with ⟨y, hy, hx'⟩
  use y
  rw [← h.1, ← h.2]
  simp [hy, hx']
#align linear_pmap.smul_graph LinearPMap.smul_graph

/-- The graph of `-f` as a pushforward. -/
theorem neg_graph (f : E →ₗ.[R] F) :
    (-f).graph =
    f.graph.map ((LinearMap.id : E →ₗ[R] E).prodMap (-(LinearMap.id : F →ₗ[R] F))) := by
  ext x; cases' x with x_fst x_snd
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.neg_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.neg_apply, Prod.mk.inj_iff, Prod.exists, exists_exists_and_eq_and]
    use x_fst, y, hy
  rw [Submodule.mem_map] at h
  rcases h with ⟨x', hx', h⟩
  cases x'
  simp only [LinearMap.prodMap_apply, LinearMap.id_coe, id, LinearMap.neg_apply,
    Prod.mk.inj_iff] at h
  rw [mem_graph_iff] at hx' ⊢
  rcases hx' with ⟨y, hy, hx'⟩
  use y
  rw [← h.1, ← h.2]
  simp [hy, hx']
#align linear_pmap.neg_graph LinearPMap.neg_graph

theorem mem_graph_snd_inj (f : E →ₗ.[R] F) {x y : E} {x' y' : F} (hx : (x, x') ∈ f.graph)
    (hy : (y, y') ∈ f.graph) (hxy : x = y) : x' = y' := by
  rw [mem_graph_iff] at hx hy
  rcases hx with ⟨x'', hx1, hx2⟩
  rcases hy with ⟨y'', hy1, hy2⟩
  simp only at hx1 hx2 hy1 hy2
  rw [← hx1, ← hy1, SetLike.coe_eq_coe] at hxy
  rw [← hx2, ← hy2, hxy]
#align linear_pmap.mem_graph_snd_inj LinearPMap.mem_graph_snd_inj

theorem mem_graph_snd_inj' (f : E →ₗ.[R] F) {x y : E × F} (hx : x ∈ f.graph) (hy : y ∈ f.graph)
    (hxy : x.1 = y.1) : x.2 = y.2 := by
  cases x
  cases y
  exact f.mem_graph_snd_inj hx hy hxy
#align linear_pmap.mem_graph_snd_inj' LinearPMap.mem_graph_snd_inj'

/-- The property that `f 0 = 0` in terms of the graph. -/
theorem graph_fst_eq_zero_snd (f : E →ₗ.[R] F) {x : E} {x' : F} (h : (x, x') ∈ f.graph)
    (hx : x = 0) : x' = 0 :=
  f.mem_graph_snd_inj h f.graph.zero_mem hx
#align linear_pmap.graph_fst_eq_zero_snd LinearPMap.graph_fst_eq_zero_snd

theorem mem_domain_iff {f : E →ₗ.[R] F} {x : E} : x ∈ f.domain ↔ ∃ y : F, (x, y) ∈ f.graph := by
  constructor <;> intro h
  · use f ⟨x, h⟩
    exact f.mem_graph ⟨x, h⟩
  cases' h with y h
  rw [mem_graph_iff] at h
  cases' h with x' h
  simp only at h
  rw [← h.1]
  simp
#align linear_pmap.mem_domain_iff LinearPMap.mem_domain_iff

theorem mem_domain_of_mem_graph {f : E →ₗ.[R] F} {x : E} {y : F} (h : (x, y) ∈ f.graph) :
    x ∈ f.domain := by
  rw [mem_domain_iff]
  exact ⟨y, h⟩
#align linear_pmap.mem_domain_of_mem_graph LinearPMap.mem_domain_of_mem_graph

theorem image_iff {f : E →ₗ.[R] F} {x : E} {y : F} (hx : x ∈ f.domain) :
    y = f ⟨x, hx⟩ ↔ (x, y) ∈ f.graph := by
  rw [mem_graph_iff]
  constructor <;> intro h
  · use ⟨x, hx⟩
    simp [h]
  rcases h with ⟨⟨x', hx'⟩, ⟨h1, h2⟩⟩
  simp only [Submodule.coe_mk] at h1 h2
  simp only [← h2, h1]
#align linear_pmap.image_iff LinearPMap.image_iff

theorem mem_range_iff {f : E →ₗ.[R] F} {y : F} : y ∈ Set.range f ↔ ∃ x : E, (x, y) ∈ f.graph := by
  constructor <;> intro h
  · rw [Set.mem_range] at h
    rcases h with ⟨⟨x, hx⟩, h⟩
    use x
    rw [← h]
    exact f.mem_graph ⟨x, hx⟩
  cases' h with x h
  rw [mem_graph_iff] at h
  cases' h with x h
  rw [Set.mem_range]
  use x
  simp only at h
  rw [h.2]
#align linear_pmap.mem_range_iff LinearPMap.mem_range_iff

theorem mem_domain_iff_of_eq_graph {f g : E →ₗ.[R] F} (h : f.graph = g.graph) {x : E} :
    x ∈ f.domain ↔ x ∈ g.domain := by simp_rw [mem_domain_iff, h]
#align linear_pmap.mem_domain_iff_of_eq_graph LinearPMap.mem_domain_iff_of_eq_graph

theorem le_of_le_graph {f g : E →ₗ.[R] F} (h : f.graph ≤ g.graph) : f ≤ g := by
  constructor
  · intro x hx
    rw [mem_domain_iff] at hx ⊢
    cases' hx with y hx
    use y
    exact h hx
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [image_iff]
  refine h ?_
  simp only [Submodule.coe_mk] at hxy
  rw [hxy] at hx
  rw [← image_iff hx]
  simp [hxy]
#align linear_pmap.le_of_le_graph LinearPMap.le_of_le_graph

theorem le_graph_of_le {f g : E →ₗ.[R] F} (h : f ≤ g) : f.graph ≤ g.graph := by
  intro x hx
  rw [mem_graph_iff] at hx ⊢
  cases' hx with y hx
  use ⟨y, h.1 y.2⟩
  simp only [hx, Submodule.coe_mk, eq_self_iff_true, true_and_iff]
  convert hx.2 using 1
  refine (h.2 ?_).symm
  simp only [hx.1, Submodule.coe_mk]
#align linear_pmap.le_graph_of_le LinearPMap.le_graph_of_le

theorem le_graph_iff {f g : E →ₗ.[R] F} : f.graph ≤ g.graph ↔ f ≤ g :=
  ⟨le_of_le_graph, le_graph_of_le⟩
#align linear_pmap.le_graph_iff LinearPMap.le_graph_iff

theorem eq_of_eq_graph {f g : E →ₗ.[R] F} (h : f.graph = g.graph) : f = g := by
  -- Porting note: `ext` → `refine ext ..`
  refine ext (Submodule.ext fun x => ?_) (fun x y h' => ?_)
  · exact mem_domain_iff_of_eq_graph h
  · exact (le_of_le_graph h.le).2 h'
#align linear_pmap.eq_of_eq_graph LinearPMap.eq_of_eq_graph

end Graph

end LinearPMap

namespace Submodule

section SubmoduleToLinearPMap

theorem existsUnique_from_graph {g : Submodule R (E × F)}
    (hg : ∀ {x : E × F} (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : ∃! b : F, (a, b) ∈ g := by
  refine exists_unique_of_exists_of_unique ?_ ?_
  · convert ha
    simp
  intro y₁ y₂ hy₁ hy₂
  have hy : ((0 : E), y₁ - y₂) ∈ g := by
    convert g.sub_mem hy₁ hy₂
    exact (sub_self _).symm
  exact sub_eq_zero.mp (hg hy (by simp))
#align submodule.exists_unique_from_graph Submodule.existsUnique_from_graph

/-- Auxiliary definition to unfold the existential quantifier. -/
noncomputable def valFromGraph {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : F :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose
#align submodule.val_from_graph Submodule.valFromGraph

theorem valFromGraph_mem {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : (a, valFromGraph hg ha) ∈ g :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose_spec
#align submodule.val_from_graph_mem Submodule.valFromGraph_mem

/-- Define a `LinearMap` from its graph.

Helper definition for `LinearPMap`. -/
noncomputable def toLinearPMapAux (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) :
    g.map (LinearMap.fst R E F) →ₗ[R] F where
  toFun := fun x => valFromGraph hg x.2
  map_add' := fun v w => by
    have hadd := (g.map (LinearMap.fst R E F)).add_mem v.2 w.2
    have hvw := valFromGraph_mem hg hadd
    have hvw' := g.add_mem (valFromGraph_mem hg v.2) (valFromGraph_mem hg w.2)
    rw [Prod.mk_add_mk] at hvw'
    exact (existsUnique_from_graph @hg hadd).unique hvw hvw'
  map_smul' := fun a v => by
    have hsmul := (g.map (LinearMap.fst R E F)).smul_mem a v.2
    have hav := valFromGraph_mem hg hsmul
    have hav' := g.smul_mem a (valFromGraph_mem hg v.2)
    rw [Prod.smul_mk] at hav'
    exact (existsUnique_from_graph @hg hsmul).unique hav hav'

open scoped Classical in
/-- Define a `LinearPMap` from its graph.

In the case that the submodule is not a graph of a `LinearPMap` then the underlying linear map
is just the zero map. -/
noncomputable def toLinearPMap (g : Submodule R (E × F)) : E →ₗ.[R] F where
  domain := g.map (LinearMap.fst R E F)
  toFun := if hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0 then
    g.toLinearPMapAux hg else 0
#align submodule.to_linear_pmap Submodule.toLinearPMap

theorem toLinearPMap_domain (g : Submodule R (E × F)) :
    g.toLinearPMap.domain = g.map (LinearMap.fst R E F) := rfl

theorem toLinearPMap_apply_aux {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0)
    (x : g.map (LinearMap.fst R E F)) :
    g.toLinearPMap x = valFromGraph hg x.2 := by
  classical
  change (if hg : _ then g.toLinearPMapAux hg else 0) x = _
  rw [dif_pos]
  · rfl
  · exact hg

theorem mem_graph_toLinearPMap {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0)
    (x : g.map (LinearMap.fst R E F)) : (x.val, g.toLinearPMap x) ∈ g := by
  rw [toLinearPMap_apply_aux hg]
  exact valFromGraph_mem hg x.2
#align submodule.mem_graph_to_linear_pmap Submodule.mem_graph_toLinearPMap

@[simp]
theorem toLinearPMap_graph_eq (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) :
    g.toLinearPMap.graph = g := by
  ext x
  constructor <;> intro hx
  · rw [LinearPMap.mem_graph_iff] at hx
    rcases hx with ⟨y, hx1, hx2⟩
    convert g.mem_graph_toLinearPMap hg y using 1
    exact Prod.ext hx1.symm hx2.symm
  rw [LinearPMap.mem_graph_iff]
  cases' x with x_fst x_snd
  have hx_fst : x_fst ∈ g.map (LinearMap.fst R E F) := by
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨x_snd, hx⟩
  refine ⟨⟨x_fst, hx_fst⟩, Subtype.coe_mk x_fst hx_fst, ?_⟩
  rw [toLinearPMap_apply_aux hg]
  exact (existsUnique_from_graph @hg hx_fst).unique (valFromGraph_mem hg hx_fst) hx
#align submodule.to_linear_pmap_graph_eq Submodule.toLinearPMap_graph_eq

theorem toLinearPMap_range (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) :
    LinearMap.range g.toLinearPMap.toFun = g.map (LinearMap.snd R E F) := by
  rwa [← LinearPMap.graph_map_snd_eq_range, toLinearPMap_graph_eq]

end SubmoduleToLinearPMap

end Submodule

namespace LinearPMap

section inverse

/-- The inverse of a `LinearPMap`. -/
noncomputable def inverse (f : E →ₗ.[R] F) : F →ₗ.[R] E :=
  (f.graph.map (LinearEquiv.prodComm R E F)).toLinearPMap

variable {f : E →ₗ.[R] F}

theorem inverse_domain : (inverse f).domain = LinearMap.range f.toFun := by
  rw [inverse, Submodule.toLinearPMap_domain, ← graph_map_snd_eq_range,
    ← LinearEquiv.fst_comp_prodComm, Submodule.map_comp]
  rfl

variable (hf : LinearMap.ker f.toFun = ⊥)

/-- The graph of the inverse generates a `LinearPMap`. -/
theorem mem_inverse_graph_snd_eq_zero (x : F × E)
    (hv : x ∈ (graph f).map (LinearEquiv.prodComm R E F))
    (hv' : x.fst = 0) : x.snd = 0 := by
  simp only [Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left,
    LinearEquiv.prodComm_apply, Prod.exists, Prod.swap_prod_mk] at hv
  rcases hv with ⟨a, b, ⟨ha, h1⟩, ⟨h2, h3⟩⟩
  simp only at hv' ⊢
  rw [hv'] at h1
  rw [LinearMap.ker_eq_bot'] at hf
  specialize hf ⟨a, ha⟩ h1
  simp only [Submodule.mk_eq_zero] at hf
  exact hf

theorem inverse_graph : (inverse f).graph = f.graph.map (LinearEquiv.prodComm R E F) := by
  rw [inverse, Submodule.toLinearPMap_graph_eq _ (mem_inverse_graph_snd_eq_zero hf)]

theorem inverse_range : LinearMap.range (inverse f).toFun = f.domain := by
  rw [inverse, Submodule.toLinearPMap_range _ (mem_inverse_graph_snd_eq_zero hf),
    ← graph_map_fst_eq_domain, ← LinearEquiv.snd_comp_prodComm, Submodule.map_comp]
  rfl

theorem mem_inverse_graph (x : f.domain) : (f x, (x : E)) ∈ (inverse f).graph := by
  simp only [inverse_graph hf, Submodule.mem_map, mem_graph_iff, Subtype.exists, exists_and_left,
    exists_eq_left, LinearEquiv.prodComm_apply, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  exact ⟨(x : E), f x, ⟨x.2, Eq.refl _⟩, Eq.refl _, Eq.refl _⟩

theorem inverse_apply_eq {y : (inverse f).domain} {x : f.domain} (hxy : f x = y) :
    (inverse f) y = x := by
  have := mem_inverse_graph hf x
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left] at this
  rcases this with ⟨hx, h⟩
  rw [← h]
  congr
  simp only [hxy, Subtype.coe_eta]

end inverse

end LinearPMap
