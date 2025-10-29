/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Moritz Doll
-/
import Mathlib.LinearAlgebra.Prod

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

@[inherit_doc] notation:25 E " →ₗ.[" R:25 "] " F:0 => LinearPMap R E F

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E] {F : Type*}
  [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G]

namespace LinearPMap

open Submodule

@[coe]
def toFun' (f : E →ₗ.[R] F) : f.domain → F := f.toFun

instance : CoeFun (E →ₗ.[R] F) fun f : E →ₗ.[R] F => f.domain → F :=
  ⟨toFun'⟩

@[simp]
theorem toFun_eq_coe (f : E →ₗ.[R] F) (x : f.domain) : f.toFun x = f x :=
  rfl

@[ext (iff := false)]
theorem ext {f g : E →ₗ.[R] F} (h : f.domain = g.domain)
    (h' : ∀ ⦃x : E⦄ ⦃hf : x ∈ f.domain⦄ ⦃hg : x ∈ g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩) : f = g := by
  rcases f with ⟨f_dom, f⟩
  rcases g with ⟨g_dom, g⟩
  obtain rfl : f_dom = g_dom := h
  congr
  apply LinearMap.ext
  intro x
  apply h'

/-- A dependent version of `ext`. -/
theorem dExt {f g : E →ₗ.[R] F} (h : f.domain = g.domain)
    (h' : ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y) : f = g :=
  ext h fun _ _ _ ↦ h' rfl

@[simp]
theorem map_zero (f : E →ₗ.[R] F) : f 0 = 0 :=
  f.toFun.map_zero

theorem ext_iff {f g : E →ₗ.[R] F} :
    f = g ↔
      f.domain = g.domain ∧
        ∀ ⦃x : E⦄ ⦃hf : x ∈ f.domain⦄ ⦃hg : x ∈ g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩ :=
  ⟨by rintro rfl; simp, fun ⟨deq, feq⟩ ↦ ext deq feq⟩

theorem dExt_iff {f g : E →ₗ.[R] F} :
    f = g ↔
      ∃ _domain_eq : f.domain = g.domain,
        ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y :=
  ⟨fun EQ =>
    EQ ▸
      ⟨rfl, fun x y h => by
        congr
        exact mod_cast h⟩,
    fun ⟨deq, feq⟩ => dExt deq feq⟩

theorem ext' {s : Submodule R E} {f g : s →ₗ[R] F} (h : f = g) : mk s f = mk s g :=
  h ▸ rfl

theorem map_add (f : E →ₗ.[R] F) (x y : f.domain) : f (x + y) = f x + f y :=
  f.toFun.map_add x y

theorem map_neg (f : E →ₗ.[R] F) (x : f.domain) : f (-x) = -f x :=
  f.toFun.map_neg x

theorem map_sub (f : E →ₗ.[R] F) (x y : f.domain) : f (x - y) = f x - f y :=
  f.toFun.map_sub x y

theorem map_smul (f : E →ₗ.[R] F) (c : R) (x : f.domain) : f (c • x) = c • f x :=
  f.toFun.map_smul c x

@[simp]
theorem mk_apply (p : Submodule R E) (f : p →ₗ[R] F) (x : p) : mk p f x = f x :=
  rfl

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
    { toFun z := Classical.choose (mem_span_singleton.1 z.prop) • y
      map_add' y z := by
        rw [← add_smul, H]
        have (w : R ∙ x) := Classical.choose_spec (mem_span_singleton.1 w.prop)
        simp only [add_smul, this, ← coe_add]
      map_smul' c z := by
        rw [smul_smul, H]
        have (w : R ∙ x) := Classical.choose_spec (mem_span_singleton.1 w.prop)
        simp only [mul_smul, this]
        apply coe_smul }

@[simp]
theorem domain_mkSpanSingleton (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) :
    (mkSpanSingleton' x y H).domain = R ∙ x :=
  rfl

@[simp]
theorem mkSpanSingleton'_apply (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) (c : R) (h) :
    mkSpanSingleton' x y H ⟨c • x, h⟩ = c • y := by
  dsimp [mkSpanSingleton']
  rw [← sub_eq_zero, ← sub_smul]
  apply H
  simp only [sub_smul, sub_eq_zero]
  apply Classical.choose_spec (mem_span_singleton.1 h)

@[simp]
theorem mkSpanSingleton'_apply_self (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) (h) :
    mkSpanSingleton' x y H ⟨x, h⟩ = y := by
  conv_rhs => rw [← one_smul R y]
  rw [← mkSpanSingleton'_apply x y H 1 ?_]
  · congr
    rw [one_smul]
  · rwa [one_smul]

/-- The unique `LinearPMap` on `span R {x}` that sends a non-zero vector `x` to `y`.
This version works for modules over division rings. -/
noncomputable abbrev mkSpanSingleton {K E F : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (x : E) (y : F) (hx : x ≠ 0) : E →ₗ.[K] F :=
  mkSpanSingleton' x y fun c hc =>
    (smul_eq_zero.1 hc).elim (fun hc => by rw [hc, zero_smul]) fun hx' => absurd hx' hx

theorem mkSpanSingleton_apply (K : Type*) {E F : Type*} [DivisionRing K] [AddCommGroup E]
    [Module K E] [AddCommGroup F] [Module K F] {x : E} (hx : x ≠ 0) (y : F) :
    mkSpanSingleton x y hx ⟨x, (Submodule.mem_span_singleton_self x : x ∈ Submodule.span K {x})⟩ =
      y :=
  LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

/-- Projection to the first coordinate as a `LinearPMap` -/
protected def fst (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] E where
  domain := p.prod p'
  toFun := (LinearMap.fst R E F).comp (p.prod p').subtype

@[simp]
theorem fst_apply (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') :
    LinearPMap.fst p p' x = (x : E × F).1 :=
  rfl

/-- Projection to the second coordinate as a `LinearPMap` -/
protected def snd (p : Submodule R E) (p' : Submodule R F) : E × F →ₗ.[R] F where
  domain := p.prod p'
  toFun := (LinearMap.snd R E F).comp (p.prod p').subtype

@[simp]
theorem snd_apply (p : Submodule R E) (p' : Submodule R F) (x : p.prod p') :
    LinearPMap.snd p p' x = (x : E × F).2 :=
  rfl

instance le : LE (E →ₗ.[R] F) :=
  ⟨fun f g => f.domain ≤ g.domain ∧ ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (_h : (x : E) = y), f x = g y⟩

theorem apply_comp_inclusion {T S : E →ₗ.[R] F} (h : T ≤ S) (x : T.domain) :
    T x = S (Submodule.inclusion h.1 x) :=
  h.2 rfl

theorem exists_of_le {T S : E →ₗ.[R] F} (h : T ≤ S) (x : T.domain) :
    ∃ y : S.domain, (x : E) = y ∧ T x = S y :=
  ⟨⟨x.1, h.1 x.2⟩, ⟨rfl, h.2 rfl⟩⟩

theorem eq_of_le_of_domain_eq {f g : E →ₗ.[R] F} (hle : f ≤ g) (heq : f.domain = g.domain) :
    f = g :=
  dExt heq hle.2

/-- Given two partial linear maps `f`, `g`, the set of points `x` such that
both `f` and `g` are defined at `x` and `f x = g x` form a submodule. -/
def eqLocus (f g : E →ₗ.[R] F) : Submodule R E where
  carrier := { x | ∃ (hf : x ∈ f.domain) (hg : x ∈ g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩ }
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩
  add_mem' {x y} := fun ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩ ↦
    ⟨add_mem hfx hfy, add_mem hgx hgy, by
      simp_all [← AddMemClass.mk_add_mk, f.map_add, g.map_add]⟩
  smul_mem' c x := fun ⟨hfx, hgx, hx⟩ ↦
    ⟨smul_mem _ c hfx, smul_mem _ c hgx, by
      have {f : E →ₗ.[R] F} (hfx) : (⟨c • x, smul_mem _ c hfx⟩ : f.domain) = c • ⟨x, hfx⟩ := by simp
      rw [this hfx, this hgx, f.map_smul, g.map_smul, hx]⟩

instance bot : Bot (E →ₗ.[R] F) :=
  ⟨⟨⊥, 0⟩⟩

instance inhabited : Inhabited (E →ₗ.[R] F) :=
  ⟨⊥⟩

instance semilatticeInf : SemilatticeInf (E →ₗ.[R] F) where
  le := (· ≤ ·)
  le_refl f := ⟨le_refl f.domain, fun _ _ h => Subtype.ext h ▸ rfl⟩
  le_trans := fun _ _ _ ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩ =>
    ⟨le_trans fg_le gh_le, fun x _ hxz =>
      have hxy : (x : E) = inclusion fg_le x := rfl
      (fg_eq hxy).trans (gh_eq <| hxy.symm.trans hxz)⟩
  le_antisymm _ _ fg gf := eq_of_le_of_domain_eq fg (le_antisymm fg.1 gf.1)
  inf f g := ⟨f.eqLocus g, f.toFun.comp <| inclusion fun _x hx => hx.fst⟩
  le_inf := by
    intro f g h ⟨fg_le, fg_eq⟩ ⟨fh_le, fh_eq⟩
    exact ⟨fun x hx =>
      ⟨fg_le hx, fh_le hx,
      (fg_eq (x := ⟨x, hx⟩) rfl).symm.trans (fh_eq rfl)⟩,
      fun x ⟨y, yg, hy⟩ h => fg_eq h⟩
  inf_le_left f _ := ⟨fun _ hx => hx.fst, fun _ _ h => congr_arg f <| Subtype.ext <| h⟩
  inf_le_right _ g :=
    ⟨fun _ hx => hx.snd.fst, fun ⟨_, _, _, hx⟩ _ h => hx.trans <| congr_arg g <| Subtype.ext <| h⟩

instance orderBot : OrderBot (E →ₗ.[R] F) where
  bot := ⊥
  bot_le f :=
    ⟨bot_le, fun x y h => by
      have hx : x = 0 := Subtype.ext ((mem_bot R).1 x.2)
      have hy : y = 0 := Subtype.ext (h.symm.trans (congr_arg _ hx))
      rw [hx, hy, map_zero, map_zero]⟩

theorem le_of_eqLocus_ge {f g : E →ₗ.[R] F} (H : f.domain ≤ f.eqLocus g) : f ≤ g :=
  suffices f ≤ f ⊓ g from le_trans this inf_le_right
  ⟨H, fun _x _y hxy => ((inf_le_left : f ⊓ g ≤ f).2 hxy.symm).symm⟩

theorem domain_mono : StrictMono (@domain R _ E _ _ F _ _) := fun _f _g hlt =>
  lt_of_le_of_ne hlt.1.1 fun heq => ne_of_lt hlt <| eq_of_le_of_domain_eq (le_of_lt hlt) heq

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
    simp only [AddSubgroupClass.coe_sub, hxy, ← sub_add, ← sub_sub, sub_self,
      zero_sub, ← H]
    apply neg_add_eq_sub
  use { toFun := fg, map_add' := ?_, map_smul' := ?_ }, fg_eq
  · rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    rw [← add_assoc, add_right_comm (f _), ← map_add, add_assoc, ← map_add]
    apply fg_eq
    simp only [coe_add, ← add_assoc]
    rw [add_right_comm (x _), hxy, add_assoc, hxy, coe_mk, coe_mk]
  · intro c z
    rw [smul_add, ← map_smul, ← map_smul]
    apply fg_eq
    simp only [coe_smul, ← smul_add, hxy, RingHom.id_apply]

/-- Given two partial linear maps that agree on the intersection of their domains,
`f.sup g h` is the unique partial linear map on `f.domain ⊔ g.domain` that agrees
with `f` and `g`. -/
protected noncomputable def sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : E →ₗ.[R] F :=
  ⟨_, Classical.choose (sup_aux f g h)⟩

@[simp]
theorem domain_sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) :
    (f.sup g h).domain = f.domain ⊔ g.domain :=
  rfl

theorem sup_apply {f g : E →ₗ.[R] F} (H : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y)
    (x : f.domain) (y : g.domain) (z : ↥(f.domain ⊔ g.domain)) (hz : (↑x : E) + ↑y = ↑z) :
    f.sup g H z = f x + g y :=
  Classical.choose_spec (sup_aux f g H) x y z hz

protected theorem left_le_sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : f ≤ f.sup g h := by
  refine ⟨le_sup_left, fun z₁ z₂ hz => ?_⟩
  rw [← add_zero (f _), ← g.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa

protected theorem right_le_sup (f g : E →ₗ.[R] F)
    (h : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) : g ≤ f.sup g h := by
  refine ⟨le_sup_right, fun z₁ z₂ hz => ?_⟩
  rw [← zero_add (g _), ← f.map_zero]
  refine (sup_apply h _ _ _ ?_).symm
  simpa

protected theorem sup_le {f g h : E →ₗ.[R] F}
    (H : ∀ (x : f.domain) (y : g.domain), (x : E) = y → f x = g y) (fh : f ≤ h) (gh : g ≤ h) :
    f.sup g H ≤ h :=
  have Hf : f ≤ f.sup g H ⊓ h := le_inf (f.left_le_sup g H) fh
  have Hg : g ≤ f.sup g H ⊓ h := le_inf (f.right_le_sup g H) gh
  le_of_eqLocus_ge <| sup_le Hf.1 Hg.1

/-- Hypothesis for `LinearPMap.sup` holds, if `f.domain` is disjoint with `g.domain`. -/
theorem sup_h_of_disjoint (f g : E →ₗ.[R] F) (h : Disjoint f.domain g.domain) (x : f.domain)
    (y : g.domain) (hxy : (x : E) = y) : f x = g y := by
  rw [disjoint_def] at h
  have hy : y = 0 := Subtype.ext (h y (hxy ▸ x.2) y.2)
  have hx : x = 0 := Subtype.ext (hxy.trans <| congr_arg _ hy)
  simp [*]

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

@[simp]
theorem smul_domain (a : M) (f : E →ₗ.[R] F) : (a • f).domain = f.domain :=
  rfl

theorem smul_apply (a : M) (f : E →ₗ.[R] F) (x : (a • f).domain) : (a • f) x = a • f x :=
  rfl

@[simp]
theorem coe_smul (a : M) (f : E →ₗ.[R] F) : ⇑(a • f) = a • ⇑f :=
  rfl

instance instSMulCommClass [SMulCommClass M N F] : SMulCommClass M N (E →ₗ.[R] F) :=
  ⟨fun a b f => ext' <| smul_comm a b f.toFun⟩

instance instIsScalarTower [SMul M N] [IsScalarTower M N F] : IsScalarTower M N (E →ₗ.[R] F) :=
  ⟨fun a b f => ext' <| smul_assoc a b f.toFun⟩

instance instMulAction : MulAction M (E →ₗ.[R] F) where
  one_smul := fun ⟨_s, f⟩ => ext' <| one_smul M f
  mul_smul a b f := ext' <| mul_smul a b f.toFun

end SMul

instance instNeg : Neg (E →ₗ.[R] F) :=
  ⟨fun f => ⟨f.domain, -f.toFun⟩⟩

@[simp]
theorem neg_domain (f : E →ₗ.[R] F) : (-f).domain = f.domain := rfl

@[simp]
theorem neg_apply (f : E →ₗ.[R] F) (x) : (-f) x = -f x :=
  rfl

instance instInvolutiveNeg : InvolutiveNeg (E →ₗ.[R] F) :=
  ⟨fun f => by
    ext x y hxy
    · rfl
    · simp only [neg_apply, neg_neg]⟩

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
    · simp only [add_apply, add_assoc]⟩

instance instAddZeroClass : AddZeroClass (E →ₗ.[R] F) where
  zero_add := fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]
  add_zero := fun f => by
    ext x y hxy
    · simp [add_domain]
    · simp [add_apply]

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
    · simp only [add_apply, add_comm]⟩

end Add

section VAdd

instance instVAdd : VAdd (E →ₗ[R] F) (E →ₗ.[R] F) :=
  ⟨fun f g =>
    { domain := g.domain
      toFun := f.comp g.domain.subtype + g.toFun }⟩

@[simp]
theorem vadd_domain (f : E →ₗ[R] F) (g : E →ₗ.[R] F) : (f +ᵥ g).domain = g.domain :=
  rfl

theorem vadd_apply (f : E →ₗ[R] F) (g : E →ₗ.[R] F) (x : (f +ᵥ g).domain) :
    (f +ᵥ g) x = f x + g x :=
  rfl

@[simp]
theorem coe_vadd (f : E →ₗ[R] F) (g : E →ₗ.[R] F) : ⇑(f +ᵥ g) = ⇑(f.comp g.domain.subtype) + ⇑g :=
  rfl

instance instAddAction : AddAction (E →ₗ[R] F) (E →ₗ.[R] F) where
  vadd := (· +ᵥ ·)
  zero_vadd := fun ⟨_s, _f⟩ => ext' <| zero_add _
  add_vadd := fun _f₁ _f₂ ⟨_s, _g⟩ => ext' <| LinearMap.ext fun _x => add_assoc _ _ _

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
    ext x _ h
    · rfl
    simp [sub_apply, add_apply, neg_apply, ← sub_eq_add_neg]
  neg_neg := neg_neg
  neg_add_rev f g := by
    ext x _ h
    · simp [add_domain, neg_domain, And.comm]
    simp [add_apply, neg_apply, ← sub_eq_add_neg]
  neg_eq_of_add f g h' := by
    ext x hf hg
    · have : (0 : E →ₗ.[R] F).domain = ⊤ := zero_domain
      simp only [← h', add_domain, inf_eq_top_iff] at this
      rw [neg_domain, this.1, this.2]
    simp only [neg_domain, neg_apply, neg_eq_iff_add_eq_zero]
    rw [ext_iff] at h'
    rcases h' with ⟨hdom, h'⟩
    rw [zero_domain] at hdom
    simp only [hdom, zero_domain, mem_top, zero_apply, forall_true_left] at h'
    apply h'
  zsmul := zsmulRec

end Sub

section

variable {K : Type*} [DivisionRing K] [Module K E] [Module K F]

/-- Extend a `LinearPMap` to `f.domain ⊔ K ∙ x`. -/
noncomputable def supSpanSingleton (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    E →ₗ.[K] F :=
  f.sup (mkSpanSingleton x y fun h₀ => hx <| h₀.symm ▸ f.domain.zero_mem) <|
    sup_h_of_disjoint _ _ <| by simpa [disjoint_span_singleton] using fun h ↦ False.elim <| hx h

@[simp]
theorem domain_supSpanSingleton (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) :
    (f.supSpanSingleton x y hx).domain = f.domain ⊔ K ∙ x :=
  rfl

@[simp]
theorem supSpanSingleton_apply_mk (f : E →ₗ.[K] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E)
    (hx' : x' ∈ f.domain) (c : K) :
    f.supSpanSingleton x y hx
        ⟨x' + c • x, mem_sup.2 ⟨x', hx', _, mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩⟩ =
      f ⟨x', hx'⟩ + c • y := by
  unfold supSpanSingleton
  rw [sup_apply _ ⟨x', hx'⟩ ⟨c • x, _⟩, mkSpanSingleton'_apply]
  · rfl
  · exact mem_span_singleton.2 ⟨c, rfl⟩

@[simp]
theorem supSpanSingleton_apply_smul_self (f : E →ₗ.[K] F) {x : E} (y : F) (hx : x ∉ f.domain)
    (c : K) :
    f.supSpanSingleton x y hx ⟨c • x, mem_sup_right <| mem_span_singleton.2 ⟨c, rfl⟩⟩ = c • y := by
  simpa [(mk_eq_zero _ _).mpr rfl] using supSpanSingleton_apply_mk f x y hx 0 (zero_mem _) c

@[simp]
theorem supSpanSingleton_apply_self (f : E →ₗ.[K] F) {x : E} (y : F) (hx : x ∉ f.domain) :
    f.supSpanSingleton x y hx ⟨x, mem_sup_right <| mem_span_singleton_self _⟩ = y := by
  simpa using supSpanSingleton_apply_smul_self f y hx 1

theorem supSpanSingleton_apply_of_mem (f : E →ₗ.[K] F) {x : E} (y : F) (hx : x ∉ f.domain)
    (x' : (f.supSpanSingleton x y hx).domain) (hx' : (x' : E) ∈ f.domain) :
    f.supSpanSingleton x y hx x' = f ⟨x', hx'⟩ := by
  simpa using supSpanSingleton_apply_mk f x y hx x' hx' 0

theorem supSpanSingleton_apply_mk_of_mem (f : E →ₗ.[K] F) {x : E} (y : F) (hx : x ∉ f.domain)
    {x' : E} (hx' : (x' : E) ∈ f.domain) :
    f.supSpanSingleton x y hx ⟨x', mem_sup_left hx'⟩ = f ⟨x', hx'⟩ :=
  supSpanSingleton_apply_of_mem f y hx _ hx'

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
    rwa [Set.exists_mem_image, ← bex_def, SetCoe.exists'] at this
  set f : ↥(sSup (domain '' c)) → F := fun x => (P x).val.val ⟨x, (P x).property⟩
  have f_eq : ∀ (p : c) (x : ↥(sSup (domain '' c))) (y : p.1.1) (_hxy : (x : E) = y),
      f x = p.1 y := by
    intro p x y hxy
    rcases hc (P x).1.1 (P x).1.2 p.1 p.2 with ⟨q, _hqc, ⟨hxq1, hxq2⟩, ⟨hpq1, hpq2⟩⟩
    exact (hxq2 (y := ⟨y, hpq1 y.2⟩) hxy).trans (hpq2 rfl).symm
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

theorem domain_sSup {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) :
    (LinearPMap.sSup c hc).domain = sSup (LinearPMap.domain '' c) := rfl

theorem mem_domain_sSup_iff {c : Set (E →ₗ.[R] F)} (hnonempty : c.Nonempty)
    (hc : DirectedOn (· ≤ ·) c) {x : E} :
    x ∈ (LinearPMap.sSup c hc).domain ↔ ∃ f ∈ c, x ∈ f.domain := by
  rw [domain_sSup, Submodule.mem_sSup_of_directed (hnonempty.image _)
    (DirectedOn.mono_comp LinearPMap.domain_mono.monotone hc)]
  simp

protected theorem le_sSup {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {f : E →ₗ.[R] F}
    (hf : f ∈ c) : f ≤ LinearPMap.sSup c hc :=
  Classical.choose_spec (sSup_aux c hc) hf

protected theorem sSup_le {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {g : E →ₗ.[R] F}
    (hg : ∀ f ∈ c, f ≤ g) : LinearPMap.sSup c hc ≤ g :=
  le_of_eqLocus_ge <|
    sSup_le fun _ ⟨f, hf, Eq⟩ =>
      Eq ▸
        have : f ≤ LinearPMap.sSup c hc ⊓ g := le_inf (LinearPMap.le_sSup _ hf) (hg f hf)
        this.1

protected theorem sSup_apply {c : Set (E →ₗ.[R] F)} (hc : DirectedOn (· ≤ ·) c) {l : E →ₗ.[R] F}
    (hl : l ∈ c) (x : l.domain) :
    (LinearPMap.sSup c hc) ⟨x, (LinearPMap.le_sSup hc hl).1 x.2⟩ = l x := by
  symm
  apply (Classical.choose_spec (sSup_aux c hc) hl).2
  rfl

end LinearPMap

namespace LinearMap

/-- Restrict a linear map to a submodule, reinterpreting the result as a `LinearPMap`. -/
def toPMap (f : E →ₗ[R] F) (p : Submodule R E) : E →ₗ.[R] F :=
  ⟨p, f.comp p.subtype⟩

@[simp]
theorem toPMap_apply (f : E →ₗ[R] F) (p : Submodule R E) (x : p) : f.toPMap p x = f x :=
  rfl

@[simp]
theorem toPMap_domain (f : E →ₗ[R] F) (p : Submodule R E) : (f.toPMap p).domain = p :=
  rfl

/-- Compose a linear map with a `LinearPMap` -/
def compPMap (g : F →ₗ[R] G) (f : E →ₗ.[R] F) : E →ₗ.[R] G where
  domain := f.domain
  toFun := g.comp f.toFun

@[simp]
theorem compPMap_apply (g : F →ₗ[R] G) (f : E →ₗ.[R] F) (x) : g.compPMap f x = g (f x) :=
  rfl

end LinearMap

namespace LinearPMap

/-- Restrict codomain of a `LinearPMap` -/
def codRestrict (f : E →ₗ.[R] F) (p : Submodule R F) (H : ∀ x, f x ∈ p) : E →ₗ.[R] p where
  domain := f.domain
  toFun := f.toFun.codRestrict p H

/-- Compose two `LinearPMap`s -/
def comp (g : F →ₗ.[R] G) (f : E →ₗ.[R] F) (H : ∀ x : f.domain, f x ∈ g.domain) : E →ₗ.[R] G :=
  g.toFun.compPMap <| f.codRestrict _ H

/-- `f.coprod g` is the partially defined linear map defined on `f.domain × g.domain`,
and sending `p` to `f p.1 + g p.2`. -/
def coprod (f : E →ₗ.[R] G) (g : F →ₗ.[R] G) : E × F →ₗ.[R] G where
  domain := f.domain.prod g.domain
  toFun :=
    (show f.domain.prod g.domain →ₗ[R] G from
      (f.comp (LinearPMap.fst f.domain g.domain) fun x => x.2.1).toFun) +
    (show f.domain.prod g.domain →ₗ[R] G from
      (g.comp (LinearPMap.snd f.domain g.domain) fun x => x.2.2).toFun)

@[simp]
theorem coprod_apply (f : E →ₗ.[R] G) (g : F →ₗ.[R] G) (x) :
    f.coprod g x = f ⟨(x : E × F).1, x.2.1⟩ + g ⟨(x : E × F).2, x.2.2⟩ :=
  rfl

/-- Restrict a partially defined linear map to a submodule of `E` contained in `f.domain`. -/
def domRestrict (f : E →ₗ.[R] F) (S : Submodule R E) : E →ₗ.[R] F :=
  ⟨S ⊓ f.domain, f.toFun.comp (Submodule.inclusion (by simp))⟩

@[simp]
theorem domRestrict_domain (f : E →ₗ.[R] F) {S : Submodule R E} :
    (f.domRestrict S).domain = S ⊓ f.domain :=
  rfl

theorem domRestrict_apply {f : E →ₗ.[R] F} {S : Submodule R E} ⦃x : ↥(S ⊓ f.domain)⦄ ⦃y : f.domain⦄
    (h : (x : E) = y) : f.domRestrict S x = f y := by
  have : Submodule.inclusion (by simp) x = y := by
    ext
    simp [h]
  rw [← this]
  exact LinearPMap.mk_apply _ _ _

theorem domRestrict_le {f : E →ₗ.[R] F} {S : Submodule R E} : f.domRestrict S ≤ f :=
  ⟨by simp, fun _ _ hxy => domRestrict_apply hxy⟩

/-! ### Graph -/


section Graph

/-- The graph of a `LinearPMap` viewed as a submodule on `E × F`. -/
def graph (f : E →ₗ.[R] F) : Submodule R (E × F) :=
  f.toFun.graph.map (f.domain.subtype.prodMap (LinearMap.id : F →ₗ[R] F))

theorem mem_graph_iff' (f : E →ₗ.[R] F) {x : E × F} :
    x ∈ f.graph ↔ ∃ y : f.domain, (↑y, f y) = x := by simp [graph]

@[simp]
theorem mem_graph_iff (f : E →ₗ.[R] F) {x : E × F} :
    x ∈ f.graph ↔ ∃ y : f.domain, (↑y : E) = x.1 ∧ f y = x.2 := by
  cases x
  simp_rw [mem_graph_iff', Prod.mk_inj]

/-- The tuple `(x, f x)` is contained in the graph of `f`. -/
theorem mem_graph (f : E →ₗ.[R] F) (x : domain f) : ((x : E), f x) ∈ f.graph := by simp

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
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.smul_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.smul_apply, Prod.mk_inj, Prod.exists, exists_exists_and_eq_and]
    use x_fst, y, hy
  rw [Submodule.mem_map] at h
  rcases h with ⟨x', hx', h⟩
  cases x'
  simp only [LinearMap.prodMap_apply, LinearMap.id_coe, id, LinearMap.smul_apply,
    Prod.mk_inj] at h
  rw [mem_graph_iff] at hx' ⊢
  rcases hx' with ⟨y, hy, hx'⟩
  use y
  rw [← h.1, ← h.2]
  simp [hy, hx']

/-- The graph of `-f` as a pushforward. -/
theorem neg_graph (f : E →ₗ.[R] F) :
    (-f).graph =
    f.graph.map ((LinearMap.id : E →ₗ[R] E).prodMap (-(LinearMap.id : F →ₗ[R] F))) := by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro h
  · rw [mem_graph_iff] at h
    rcases h with ⟨y, hy, h⟩
    rw [LinearPMap.neg_apply] at h
    rw [Submodule.mem_map]
    simp only [mem_graph_iff, LinearMap.prodMap_apply, LinearMap.id_coe, id,
      LinearMap.neg_apply, Prod.mk_inj, Prod.exists, exists_exists_and_eq_and]
    use x_fst, y, hy
  rw [Submodule.mem_map] at h
  rcases h with ⟨x', hx', h⟩
  cases x'
  simp only [LinearMap.prodMap_apply, LinearMap.id_coe, id, LinearMap.neg_apply,
    Prod.mk_inj] at h
  rw [mem_graph_iff] at hx' ⊢
  rcases hx' with ⟨y, hy, hx'⟩
  use y
  rw [← h.1, ← h.2]
  simp [hy, hx']

theorem mem_graph_snd_inj (f : E →ₗ.[R] F) {x y : E} {x' y' : F} (hx : (x, x') ∈ f.graph)
    (hy : (y, y') ∈ f.graph) (hxy : x = y) : x' = y' := by
  grind [mem_graph_iff]

theorem mem_graph_snd_inj' (f : E →ₗ.[R] F) {x y : E × F} (hx : x ∈ f.graph) (hy : y ∈ f.graph)
    (hxy : x.1 = y.1) : x.2 = y.2 := by
  cases x
  cases y
  exact f.mem_graph_snd_inj hx hy hxy

/-- The property that `f 0 = 0` in terms of the graph. -/
theorem graph_fst_eq_zero_snd (f : E →ₗ.[R] F) {x : E} {x' : F} (h : (x, x') ∈ f.graph)
    (hx : x = 0) : x' = 0 :=
  f.mem_graph_snd_inj h f.graph.zero_mem hx

theorem mem_domain_iff {f : E →ₗ.[R] F} {x : E} : x ∈ f.domain ↔ ∃ y : F, (x, y) ∈ f.graph := by
  constructor <;> intro h
  · use f ⟨x, h⟩
    exact f.mem_graph ⟨x, h⟩
  grind [mem_graph_iff]

theorem mem_domain_of_mem_graph {f : E →ₗ.[R] F} {x : E} {y : F} (h : (x, y) ∈ f.graph) :
    x ∈ f.domain := by
  rw [mem_domain_iff]
  exact ⟨y, h⟩

theorem image_iff {f : E →ₗ.[R] F} {x : E} {y : F} (hx : x ∈ f.domain) :
    y = f ⟨x, hx⟩ ↔ (x, y) ∈ f.graph := by
  grind [mem_graph_iff]

theorem mem_range_iff {f : E →ₗ.[R] F} {y : F} : y ∈ Set.range f ↔ ∃ x : E, (x, y) ∈ f.graph := by
  constructor <;> intro h
  · rw [Set.mem_range] at h
    rcases h with ⟨⟨x, hx⟩, h⟩
    use x
    rw [← h]
    exact f.mem_graph ⟨x, hx⟩
  grind [mem_graph_iff]

theorem mem_domain_iff_of_eq_graph {f g : E →ₗ.[R] F} (h : f.graph = g.graph) {x : E} :
    x ∈ f.domain ↔ x ∈ g.domain := by simp_rw [mem_domain_iff, h]

theorem le_of_le_graph {f g : E →ₗ.[R] F} (h : f.graph ≤ g.graph) : f ≤ g := by
  constructor
  · intro x hx
    rw [mem_domain_iff] at hx ⊢
    obtain ⟨y, hx⟩ := hx
    use y
    exact h hx
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  rw [image_iff]
  refine h ?_
  simp only at hxy
  rw [hxy] at hx
  rw [← image_iff hx]
  simp [hxy]

theorem le_graph_of_le {f g : E →ₗ.[R] F} (h : f ≤ g) : f.graph ≤ g.graph := by
  intro x hx
  rw [mem_graph_iff] at hx ⊢
  obtain ⟨y, hx⟩ := hx
  use ⟨y, h.1 y.2⟩
  simp only [hx, true_and]
  convert hx.2 using 1
  refine (h.2 ?_).symm
  simp only [hx.1]

theorem le_graph_iff {f g : E →ₗ.[R] F} : f.graph ≤ g.graph ↔ f ≤ g :=
  ⟨le_of_le_graph, le_graph_of_le⟩

theorem eq_of_eq_graph {f g : E →ₗ.[R] F} (h : f.graph = g.graph) : f = g := by
  apply dExt
  · ext
    exact mem_domain_iff_of_eq_graph h
  · apply (le_of_le_graph h.le).2

end Graph

end LinearPMap

namespace Submodule

section SubmoduleToLinearPMap

theorem existsUnique_from_graph {g : Submodule R (E × F)}
    (hg : ∀ {x : E × F} (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : ∃! b : F, (a, b) ∈ g := by
  refine existsUnique_of_exists_of_unique ?_ ?_
  · convert ha
    simp
  intro y₁ y₂ hy₁ hy₂
  have hy : ((0 : E), y₁ - y₂) ∈ g := by
    convert g.sub_mem hy₁ hy₂
    exact (sub_self _).symm
  exact sub_eq_zero.mp (hg hy (by simp))

/-- Auxiliary definition to unfold the existential quantifier. -/
noncomputable def valFromGraph {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : F :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose

theorem valFromGraph_mem {g : Submodule R (E × F)}
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) {a : E}
    (ha : a ∈ g.map (LinearMap.fst R E F)) : (a, valFromGraph hg ha) ∈ g :=
  (ExistsUnique.exists (existsUnique_from_graph @hg ha)).choose_spec

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

@[simp]
theorem toLinearPMap_graph_eq (g : Submodule R (E × F))
    (hg : ∀ (x : E × F) (_hx : x ∈ g) (_hx' : x.fst = 0), x.snd = 0) :
    g.toLinearPMap.graph = g := by
  ext ⟨x_fst, x_snd⟩
  constructor <;> intro hx
  · rw [LinearPMap.mem_graph_iff] at hx
    rcases hx with ⟨y, hx1, hx2⟩
    convert g.mem_graph_toLinearPMap hg y using 1
    exact Prod.ext hx1.symm hx2.symm
  rw [LinearPMap.mem_graph_iff]
  have hx_fst : x_fst ∈ g.map (LinearMap.fst R E F) := by
    simp only [mem_map, LinearMap.fst_apply, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨x_snd, hx⟩
  refine ⟨⟨x_fst, hx_fst⟩, Subtype.coe_mk x_fst hx_fst, ?_⟩
  rw [toLinearPMap_apply_aux hg]
  exact (existsUnique_from_graph @hg hx_fst).unique (valFromGraph_mem hg hx_fst) hx

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
include hf

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
  grind [mem_graph_iff]

end inverse

end LinearPMap
