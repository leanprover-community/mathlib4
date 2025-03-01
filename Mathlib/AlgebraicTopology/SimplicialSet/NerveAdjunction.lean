/-
Copyright (c) 2024 Mario Carneiro and Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!

# The adjunction between the nerve and the homotopy category functor.

We define an adjunction `nerveAdjunction : hoFunctor ⊣ nerveFunctor` between the functor that
takes a simplicial set to its homotopy category and the functor that takes a category to its nerve.

Up to natural isomorphism, this is constructed as the composite of two other adjunctions,
namely `nerve₂Adj : hoFunctor₂ ⊣ nerveFunctor₂` between analogously-defined functors involving
the category of 2-truncated simplicial sets and `coskAdj 2 : truncation 2 ⊣ Truncated.cosk 2`. The
aforementioned natural isomorphism

`cosk₂Iso : nerveFunctor ≅ nerveFunctor₂ ⋙ Truncated.cosk 2`

exists because nerves of categories are 2-coskeletal.

We also prove that `nerveFunctor` is fully faithful, demonstrating that `nerveAdjunction` is
reflective. Since the category of simplicial sets is cocomplete, we conclude in
`Mathlib.CategoryTheory.Category.Cat.Colimit` that the category of categories has colimits.

-/

namespace CategoryTheory

open Category Functor Limits Opposite SimplexCategory Simplicial SSet Nerve Truncated
universe v u v' u'

section

set_option quotPrecheck false
local macro:max (priority := high) "⦋" n:term "⦌₂" : term =>
  `((⟨SimplexCategory.mk $n, by decide⟩ : SimplexCategory.Truncated 2))

local macro:1000 (priority := high) X:term " _⦋" n:term "⦌₂" : term =>
    `(($X : SSet.Truncated 2).obj (Opposite.op ⟨SimplexCategory.mk $n, by decide⟩))

/-- The components of the counit of `nerve₂Adj`. -/
@[simps!]
def nerve₂Adj.counit.app (C : Type u) [SmallCategory C] :
    (nerveFunctor₂.obj (Cat.of C)).HomotopyCategory ⥤ C := by
  fapply Quotient.lift
  · exact
      (whiskerRight (OneTruncation₂.ofNerve₂.natIso).hom _ ≫ ReflQuiv.adj.{u}.counit).app (Cat.of C)
  · intro x y f g rel
    obtain ⟨φ⟩ := rel
    simpa [ReflQuiv.adj, Quot.liftOn, Cat.FreeRefl.quotientFunctor, Quotient.functor,
        Quiv.adj, OneTruncation₂.nerveHomEquiv] using
      φ.map_comp (X := 0) (Y := 1) (Z := 2) (homOfLE (by decide)) (homOfLE (by decide))

@[simp]
theorem nerve₂Adj.counit.app_eq (C : Type u) [SmallCategory C] :
    SSet.Truncated.HomotopyCategory.quotientFunctor (nerveFunctor₂.obj (Cat.of C)) ⋙
      nerve₂Adj.counit.app.{u} C =
    (whiskerRight OneTruncation₂.ofNerve₂.natIso.hom _ ≫
      ReflQuiv.adj.{u}.counit).app (Cat.of C) := rfl

/-- The naturality of `nerve₂Adj.counit.app`. -/
theorem nerve₂Adj.counit.naturality {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) :
    (nerveFunctor₂ ⋙ hoFunctor₂).map F ⋙ nerve₂Adj.counit.app D =
      nerve₂Adj.counit.app C ⋙ F := by
  apply HomotopyCategory.lift_unique'
  change ((oneTruncation₂ ⋙ Cat.freeRefl).map (nerveFunctor₂.map _)) ⋙
    HomotopyCategory.quotientFunctor (nerveFunctor₂.obj (Cat.of D)) ⋙ app D = _
  rw [nerve₂Adj.counit.app_eq D]
  rw [← Functor.assoc _ _ F, nerve₂Adj.counit.app_eq C]
  exact (whiskerRight OneTruncation₂.ofNerve₂.natIso.{u}.hom Cat.freeRefl ≫
    ReflQuiv.adj.counit).naturality _

/-- The counit of `nerve₂Adj.` -/
@[simps]
def nerve₂Adj.counit : nerveFunctor₂ ⋙ hoFunctor₂.{u} ⟶ 𝟭 Cat where
  app _ := nerve₂Adj.counit.app _
  naturality _ _ _ := nerve₂Adj.counit.naturality _

local notation (priority := high) "[" n "]" => SimplexCategory.mk n

variable {C : Type u} [SmallCategory C] {X : SSet.Truncated.{u} 2}
    (F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C)

/-- Because nerves are 2-coskeletal, the components of a map of 2-truncated simplicial sets valued
in a nerve can be recovered from the underlying ReflPrefunctor. -/
def toNerve₂.mk.app (n : SimplexCategory.Truncated 2) :
    X.obj (op n) ⟶ (nerveFunctor₂.obj (Cat.of C)).obj (op n) := by
  obtain ⟨n, hn⟩ := n
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => exact fun x => .mk₀ (F.obj x)
  | 1 => exact fun f => .mk₁ (F.map ⟨f, rfl, rfl⟩)
  | 2 => exact fun φ => .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ))

@[simp] theorem toNerve₂.mk.app_zero (x : X _⦋0⦌₂) : mk.app F ⦋0⦌₂ x = .mk₀ (F.obj x) := rfl

@[simp] theorem toNerve₂.mk.app_one (f : X _⦋1⦌₂) :
    mk.app F ⦋1⦌₂ f = .mk₁ (F.map ⟨f, rfl, rfl⟩) := rfl

@[simp] theorem toNerve₂.mk.app_two (φ : X _⦋2⦌₂) :
    mk.app F ⦋2⦌₂ φ = .mk₂ (F.map (ev01₂ φ)) (F.map (ev12₂ φ)) := rfl

/-- This is similar to one of the famous Segal maps, except valued in a product rather than a
pullback. -/
noncomputable def nerve₂.seagull (C : Type u) [Category C] :
    (nerveFunctor₂.obj (Cat.of C)).obj (op ⦋2⦌₂) ⟶
    (nerveFunctor₂.obj (Cat.of C)).obj (op ⦋1⦌₂) ⨯ (nerveFunctor₂.obj (Cat.of C)).obj (op ⦋1⦌₂) :=
  prod.lift
    ((nerveFunctor₂.obj (Cat.of C)).map (.op δ2₂)) ((nerveFunctor₂.obj (Cat.of C)).map (.op δ0₂))

instance (C : Type u) [Category C] : Mono (nerve₂.seagull C) where
  right_cancellation {X} (f g : X → ComposableArrows C 2) eq := by
    ext x
    simp [nerve₂.seagull] at eq
    have eq1 := congr($eq ≫ prod.fst)
    have eq2 := congr($eq ≫ prod.snd)
    simp only [limit.lift_π, BinaryFan.mk_fst, BinaryFan.mk_snd] at eq1 eq2
    replace eq1 := congr_fun eq1 x
    replace eq2 := congr_fun eq2 x
    simp only [types_comp_apply] at eq1 eq2
    generalize f x = fx at *
    generalize g x = gx at *
    fapply ComposableArrows.ext₂
    · exact congrArg (·.obj 0) <| eq1
    · exact congrArg (·.obj 1) <| eq1
    · exact congrArg (·.obj 1) <| eq2
    · exact (conj_eqToHom_iff_heq' _ _ _ _).2 (congr_arg_heq (·.hom) <| eq1)
    · exact (conj_eqToHom_iff_heq' _ _ _ _).2 (congr_arg_heq (·.hom) <| eq2)

/-- Naturality of the components defined by `toNerve₂.mk.app` as a morphism property of
maps in `SimplexCategory.Truncated 2`. -/
abbrev toNerve₂.mk.naturalityProperty : MorphismProperty (SimplexCategory.Truncated 2) :=
  (MorphismProperty.naturalityProperty (fun n => toNerve₂.mk.app F n.unop)).unop

lemma ReflPrefunctor.congr_mk₁_map
    {Y : Type u'} [ReflQuiver.{v'} Y] {C : Type u} [Category.{v} C]
    (F : ReflPrefunctor Y (ReflQuiv.of C))
    {x₁ y₁ x₂ y₂ : Y} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂)
    (hx : x₁ = x₂) (hy : y₁ = y₂) (hfg : Quiver.homOfEq f hx hy = g) :
    ComposableArrows.mk₁ (C := C) (F.map f) = ComposableArrows.mk₁ (C := C) (F.map g) := by
  subst hx hy hfg; rfl

lemma toNerve₂.mk_naturality_σ00 : toNerve₂.mk.naturalityProperty F (σ₂ (n := 0) 0) := by
  ext x
  refine Eq.trans ?_ (nerve.σ₀_mk₀_eq (C := C) (F.obj x)).symm
  have := ReflPrefunctor.map_id F x
  dsimp at this ⊢
  rw [← this, ← OneTruncation₂.id_edge x]
  fapply ReflPrefunctor.congr_mk₁_map
  · simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  · simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  · aesop

lemma toNerve₂.mk_naturality_δ0i (i : Fin 2) : toNerve₂.mk.naturalityProperty F (δ₂ i) := by
  ext x
  apply ComposableArrows.ext₀
  fin_cases i <;> rfl

section
variable
  (hyp : ∀ φ, F.map (ev02₂ φ) = CategoryStruct.comp (obj := C) (F.map (ev01₂ φ)) (F.map (ev12₂ φ)))
include hyp

lemma toNerve₂.mk_naturality_δ1i (i : Fin 3) : toNerve₂.mk.naturalityProperty F (δ₂ i) := by
  ext x
  simp only [types_comp_apply, mk.app_two, ComposableArrows.mk₂]
  rw [toNerve₂.mk.app_one]
  unfold nerveFunctor₂ truncation SimplicialObject.truncation
  simp only [comp_obj, nerveFunctor_obj, Cat.of_α, whiskeringLeft_obj_obj, id_eq, op_obj,
    nerve_obj, oneTruncation₂_obj, ReflQuiv.of_val, Nat.reduceAdd, mk.app_two,
    Functor.comp_map, op_map, Quiver.Hom.unop_op]
  unfold δ₂ inclusion
  simp only [fullSubcategoryInclusion.map]
  fin_cases i
  · simp only [Fin.zero_eta]
    show _ = (nerve C).δ 0 _
    rw [nerve.δ₀_mk₂_eq]
    fapply ReflPrefunctor.congr_mk₁_map
    · unfold ev1₂ ι1₂ δ₂
      simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
      have := δ_comp_δ (n := 0) (i := 0) (j := 1) (by decide)
      dsimp at this
      exact congrFun (congrArg X.map (congrArg Quiver.Hom.op this.symm)) x
    · unfold ev2₂ ι2₂ δ₂
      simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
      have := δ_comp_δ (n := 0) (i := 0) (j := 0) (by decide)
      dsimp at this
      exact congrFun (congrArg X.map (congrArg Quiver.Hom.op this.symm)) x
    · aesop
  · simp only [Fin.mk_one]
    show _ = (nerve C).δ 1 _
    rw [nerve.δ₁_mk₂_eq]
    rw [← hyp]
    fapply ReflPrefunctor.congr_mk₁_map
    · unfold ev0₂ ι0₂ δ₂
      simp [← FunctorToTypes.map_comp_apply, ← op_comp]
    · unfold ev2₂ ι2₂ δ₂
      simp [← FunctorToTypes.map_comp_apply, ← op_comp]
    · aesop
  · simp only [Fin.reduceFinMk]
    show _ = (nerve C).δ 2 _
    rw [nerve.δ₂_mk₂_eq]
    fapply ReflPrefunctor.congr_mk₁_map
    · unfold ev0₂ ι0₂ δ₂
      simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
      have := δ_comp_δ (n := 0) (i := 1) (j := 1) (by decide)
      dsimp at this
      exact congrFun (congrArg X.map (congrArg Quiver.Hom.op this)) x
    · unfold ev1₂ ι1₂ δ₂
      simp [← FunctorToTypes.map_comp_apply, ← op_comp]
    · aesop

lemma toNerve₂.mk_naturality_σ1i (i : Fin 2) : toNerve₂.mk.naturalityProperty F (σ₂ i) := by
  apply (cancel_mono (nerve₂.seagull _)).1
  simp only [nerve₂.seagull, prod.comp_lift, assoc]
  congr 1 <;> rw [← map_comp, ← op_comp]
  · unfold δ2₂
    rw [← toNerve₂.mk_naturality_δ1i F hyp, ← assoc, ← map_comp, ← op_comp]
    change toNerve₂.mk.naturalityProperty F (δ₂ 2 ≫ σ₂ i)
    fin_cases i
    · dsimp only [Fin.zero_eta]
      rw [δ₂_two_comp_σ₂_zero]
      exact (toNerve₂.mk.naturalityProperty F).comp_mem _ _
        (toNerve₂.mk_naturality_σ00 F) (toNerve₂.mk_naturality_δ0i F _)
    · dsimp only [Fin.mk_one]
      rw [δ₂_two_comp_σ₂_one]
      exact (toNerve₂.mk.naturalityProperty F).id_mem _
  · unfold δ0₂
    rw [← toNerve₂.mk_naturality_δ1i F hyp, ← assoc, ← map_comp, ← op_comp]
    change toNerve₂.mk.naturalityProperty F (δ₂ 0 ≫ σ₂ i)
    fin_cases i <;> dsimp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    · rw [δ₂_zero_comp_σ₂_zero]
      exact (toNerve₂.mk.naturalityProperty F).id_mem _
    · rw [δ₂_zero_comp_σ₂_one]
      exact (toNerve₂.mk.naturalityProperty F).comp_mem _ _
        (toNerve₂.mk_naturality_σ00 F) (toNerve₂.mk_naturality_δ0i F _)

/-- A proof that the components defined by `toNerve₂.mk.app` are natural. -/
theorem toNerve₂.mk_naturality : toNerve₂.mk.naturalityProperty F = ⊤ :=
  Truncated.morphismProperty_eq_top (toNerve₂.mk.naturalityProperty F)
    (fun
      | 0, _, _ => toNerve₂.mk_naturality_δ0i F _
      | 1, _, _ => toNerve₂.mk_naturality_δ1i F hyp _)
    (fun
      | 0, _, 0 => toNerve₂.mk_naturality_σ00 F
      | 1, _, _ => toNerve₂.mk_naturality_σ1i F hyp _)

/-- The morphism `X ⟶ nerveFunctor₂.obj (Cat.of C)` of 2-truncated simplicial sets that is
constructed from a refl prefunctor `F : SSet.oneTruncation₂.obj X ⟶ ReflQuiv.of C` assuming
`∀ (φ : : X _⦋2⦌₂), F.map (ev02₂ φ) = F.map (ev01₂ φ) ≫ F.map (ev12₂ φ)`. -/
@[simps!]
def toNerve₂.mk : X ⟶ nerveFunctor₂.obj (Cat.of C) where
  app n := toNerve₂.mk.app F n.unop
  naturality _ _ f := MorphismProperty.of_eq_top (toNerve₂.mk_naturality F hyp) f.unop

end

section

variable (F : SSet.oneTruncation₂.obj X ⟶ SSet.oneTruncation₂.obj (nerveFunctor₂.obj (Cat.of C)))
variable (hyp : (φ : X _⦋2⦌₂) →
            (F ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev02₂ φ) =
              CategoryStruct.comp (obj := C)
              ((F ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev01₂ φ))
              ((F ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom).map (ev12₂ φ)))

/-- An alternate version of `toNerve₂.mk`, which constructs a map of 2-truncated simplicial sets
`X ⟶ nerveFunctor₂.obj (Cat.of C)` from the underlying refl prefunctor under a composition
hypothesis, where that prefunctor the central hypothesis is conjugated by the isomorphism
`nerve₂Adj.NatIso.app C`. -/
@[simps!] def toNerve₂.mk' : X ⟶ nerveFunctor₂.obj (Cat.of C) :=
  toNerve₂.mk (F ≫ (OneTruncation₂.ofNerve₂.natIso.app (Cat.of C)).hom) hyp

/-- A computation about `toNerve₂.mk'`. -/
theorem oneTruncation₂_toNerve₂Mk' : oneTruncation₂.map (toNerve₂.mk' F hyp) = F := by
  refine ReflPrefunctor.ext (fun _ ↦ ComposableArrows.ext₀ rfl)
    (fun X Y g ↦ eq_of_heq (heq_eqRec_iff_heq.2 <| heq_eqRec_iff_heq.2 ?_))
  simp [oneTruncation₂]
  refine Quiver.heq_of_homOfEq_ext ?_ ?_ (f' := F.map g) ?_
  · exact ComposableArrows.ext₀ rfl
  · exact ComposableArrows.ext₀ rfl
  · apply OneTruncation₂.Hom.ext
    simp only [oneTruncation₂_obj, ReflQuiv.of_val, OneTruncation₂.homOfEq_edge]
    fapply ComposableArrows.ext₁ <;> simp [ReflQuiv.comp_eq_comp]
    · rw [g.src_eq]; exact congr_arg (·.obj 0) (F.map g).src_eq.symm
    · rw [g.tgt_eq]; exact congr_arg (·.obj 1) (F.map g).tgt_eq.symm
    · refine (conj_eqToHom_iff_heq' _ _ _ _).2 ?_
      simp [OneTruncation₂.nerveHomEquiv]
      obtain ⟨g, rfl, rfl⟩ := g
      rfl

end

/-- An equality between maps into the 2-truncated nerve is detected by an equality beteween their
underlying refl prefunctors. -/
theorem toNerve₂.ext (F G : X ⟶ nerveFunctor₂.obj (Cat.of C))
    (hyp : SSet.oneTruncation₂.map F = SSet.oneTruncation₂.map G) : F = G := by
  have eq₀ x : F.app (op ⦋0⦌₂) x = G.app (op ⦋0⦌₂) x := congr(($hyp).obj x)
  have eq₁ x : F.app (op ⦋1⦌₂) x = G.app (op ⦋1⦌₂) x := congr((($hyp).map ⟨x, rfl, rfl⟩).1)
  ext ⟨⟨n, hn⟩⟩ x
  induction' n using SimplexCategory.rec with n
  match n with
  | 0 => apply eq₀
  | 1 => apply eq₁
  | 2 =>
    apply Functor.hext (fun i : Fin 3 => ?_) (fun (i j : Fin 3) k => ?_)
    · let pt : ⦋0⦌₂ ⟶ ⦋2⦌₂ := SimplexCategory.const _ _ i
      refine congr(($(congr_fun (F.naturality pt.op) x)).obj 0).symm.trans ?_
      refine .trans ?_ congr(($(congr_fun (G.naturality pt.op) x)).obj 0)
      exact congr($(eq₀ _).obj 0)
    · let ar : ⦋1⦌₂ ⟶ ⦋2⦌₂ := mkOfLe _ _ k.le
      have h1 := congr_arg_heq (fun x => x.map' 0 1) (congr_fun (F.naturality (op ar)) x)
      have h2 := congr_arg_heq (fun x => x.map' 0 1) (congr_fun (G.naturality (op ar)) x)
      exact h1.symm.trans <| .trans (congr_arg_heq (fun x => x.map' 0 1) (eq₁ _)) h2

/-- The components of the 2-truncated nerve adjunction unit. -/
def nerve₂Adj.unit.app (X : SSet.Truncated.{u} 2) :
    X ⟶ nerveFunctor₂.obj (hoFunctor₂.obj X) := by
  fapply toNerve₂.mk' (C := hoFunctor₂.obj X)
  · exact (ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
      (SSet.Truncated.HomotopyCategory.quotientFunctor X).toReflPrefunctor ⋙rq
      (OneTruncation₂.ofNerve₂.natIso).inv.app (hoFunctor₂.obj X))
  · exact fun φ ↦ Quotient.sound _ (HoRel₂.mk φ)

theorem nerve₂Adj.unit.map_app_eq (X : SSet.Truncated.{u} 2) :
    SSet.oneTruncation₂.map (nerve₂Adj.unit.app X) =
    ReflQuiv.adj.{u}.unit.app (SSet.oneTruncation₂.obj X) ⋙rq
    (SSet.Truncated.HomotopyCategory.quotientFunctor X).toReflPrefunctor ⋙rq
    (OneTruncation₂.ofNerve₂.natIso).inv.app (hoFunctor₂.obj X) := by
  apply oneTruncation₂_toNerve₂Mk'

@[reassoc]
lemma nerve₂Adj.unit.naturality {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) :
    f ≫ unit.app Y = unit.app X ≫ nerveFunctor₂.map (hoFunctor₂.map f) :=
  toNerve₂.ext _ _ (by
    have := (OneTruncation₂.ofNerve₂.natIso).inv.naturality (hoFunctor₂.map f)
    dsimp at this ⊢
    rw [Functor.map_comp, Functor.map_comp, nerve₂Adj.unit.map_app_eq,
      nerve₂Adj.unit.map_app_eq, ← ReflQuiv.comp_eq_comp (Y := ReflQuiv.of _),
      ← ReflQuiv.comp_eq_comp (Y := ReflQuiv.of _), assoc, ← this]
    rfl)

/-- The 2-truncated nerve adjunction unit. -/
@[simps]
def nerve₂Adj.unit : 𝟭 (SSet.Truncated.{u} 2) ⟶ hoFunctor₂ ⋙ nerveFunctor₂ where
  app := nerve₂Adj.unit.app
  naturality _ _ _ := unit.naturality _


/-- The adjunction between the 2-truncated nerve functor and the 2-truncated homotopy category
functor. -/
nonrec def nerve₂Adj : hoFunctor₂.{u} ⊣ nerveFunctor₂ :=
  Adjunction.mkOfUnitCounit {
    unit := nerve₂Adj.unit
    counit := nerve₂Adj.counit
    left_triangle := by
      ext X
      apply HomotopyCategory.lift_unique'
      dsimp
      rw [Cat.comp_eq_comp, ← Functor.assoc]
      dsimp only [hoFunctor₂]
      rw [← hoFunctor₂_naturality (nerve₂Adj.unit.app X)]
      dsimp
      rw [nerve₂Adj.unit.map_app_eq X, Functor.assoc, id_comp]
      show _ ⋙ (HomotopyCategory.quotientFunctor _ ⋙ nerve₂Adj.counit.app (hoFunctor₂.obj X)) = _
      rw [nerve₂Adj.counit.app_eq]
      dsimp
      rw [← Cat.comp_eq_comp, ← assoc, ← Cat.freeRefl.map_comp, ReflQuiv.comp_eq_comp,
        ReflPrefunctor.comp_assoc]
      dsimp
      rw [← ReflQuiv.comp_eq_comp, Iso.inv_hom_id_app, ReflQuiv.id_eq_id]
      dsimp
      rw [ReflPrefunctor.comp_id (V := hoFunctor₂.obj X), ← ReflQuiv.comp_eq_comp (Z := .of _),
        Cat.freeRefl.map_comp, assoc]
      have := ReflQuiv.adj.counit.naturality
        (X := Cat.freeRefl.obj (ReflQuiv.of (OneTruncation₂ X)))
        (Y := hoFunctor₂.obj X) (SSet.Truncated.HomotopyCategory.quotientFunctor X)
      dsimp at this
      rw [this]
      apply Adjunction.left_triangle_components_assoc
    right_triangle := by
      refine NatTrans.ext (funext fun C ↦ ?_)
      apply toNerve₂.ext
      dsimp
      simp only [id_comp, map_comp, oneTruncation₂_obj, map_id]
      rw [nerve₂Adj.unit.map_app_eq, ReflPrefunctor.comp_assoc]
      rw [← ReflQuiv.comp_eq_comp,
        ← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _),
        assoc, assoc, ← Functor.comp_map, ← OneTruncation₂.ofNerve₂.natIso.inv.naturality]
      conv => lhs; rhs; rw [← assoc]
      show _ ≫ (ReflQuiv.forget.map _ ≫ ReflQuiv.forget.map _) ≫ _ = _
      rw [← ReflQuiv.forget.map_comp]
      dsimp
      conv => lhs; rhs; lhs; rw [Cat.comp_eq_comp]
      have : HomotopyCategory.quotientFunctor (nerveFunctor₂.obj C) ⋙ _ = _ :=
        nerve₂Adj.counit.app_eq C
      rw [this]
      dsimp
      rw [← assoc, Cat.comp_eq_comp, toReflPrefunctor.map_comp]
      rw [← ReflQuiv.comp_eq_comp (X := ReflQuiv.of _) (Y := ReflQuiv.of _) (Z := ReflQuiv.of _)]
      have := ReflQuiv.adj.unit.naturality (OneTruncation₂.ofNerve₂.natIso.hom.app C)
      dsimp at this ⊢
      rw [← assoc, ← this]
      have := ReflQuiv.adj.right_triangle_components C
      dsimp [ReflQuiv.forget] at this
      simp [reassoc_of% this]
  }

instance nerveFunctor₂.faithful : nerveFunctor₂.{u, u}.Faithful := by
  exact Functor.Faithful.of_comp_iso
    (G := oneTruncation₂) (H := ReflQuiv.forget) OneTruncation₂.ofNerve₂.natIso

instance nerveFunctor₂.full : nerveFunctor₂.{u, u}.Full where
  map_surjective := by
    intro X Y F
    let uF := SSet.oneTruncation₂.map F
    let uF' : X ⥤rq Y :=
      OneTruncation₂.ofNerve₂.natIso.inv.app X ≫ uF ≫ OneTruncation₂.ofNerve₂.natIso.hom.app Y
    have {a b c : X} (h : a ⟶ b) (k : b ⟶ c) :
        uF'.map (h ≫ k) = uF'.map h ≫ uF'.map k := by
      let hk := ComposableArrows.mk₂ h k
      let Fh : ComposableArrows Y 1 := F.app (op ⦋1⦌₂) (.mk₁ h)
      let Fk : ComposableArrows Y 1 := F.app (op ⦋1⦌₂) (.mk₁ k)
      let Fhk' : ComposableArrows Y 1 := F.app (op ⦋1⦌₂) (.mk₁ (h ≫ k))
      let Fhk : ComposableArrows Y 2 := F.app (op ⦋2⦌₂) hk
      have lem0 := congr_arg_heq (·.map' 0 1) (congr_fun (F.naturality δ0₂.op) hk)
      have lem1 := congr_arg_heq (·.map' 0 1) (congr_fun (F.naturality δ1₂.op) hk)
      have lem2 := congr_arg_heq (·.map' 0 1) (congr_fun (F.naturality δ2₂.op) hk)
      have eq0 : (nerveFunctor₂.obj X).map δ0₂.op hk = .mk₁ k := by
        apply ComposableArrows.ext₁ rfl rfl
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]
      have eq2 : (nerveFunctor₂.obj X).map δ2₂.op hk = .mk₁ h := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]; rfl
      have eq1 : (nerveFunctor₂.obj X).map δ1₂.op hk = .mk₁ (h ≫ k) := by
        apply ComposableArrows.ext₁ (by rfl) (by rfl)
        simp [nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂]; rfl
      dsimp at lem0 lem1 lem2
      rw [eq0] at lem0
      rw [eq1] at lem1
      rw [eq2] at lem2
      replace lem0 : HEq (uF'.map k) (Fhk.map' 1 2) := by
        refine HEq.trans (b := Fk.map' 0 1) ?_ lem0
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF]
      replace lem2 : HEq (uF'.map h) (Fhk.map' 0 1) := by
        refine HEq.trans (b := Fh.map' 0 1) ?_ lem2
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, ComposableArrows.hom, Fh]
      replace lem1 : HEq (uF'.map (h ≫ k)) (Fhk.map' 0 2) := by
        refine HEq.trans (b := Fhk'.map' 0 1) ?_ lem1
        simp only [Nat.reduceAdd, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int, Int.reduceSub,
          Int.reduceAdd, Nat.cast_ofNat, Fin.zero_eta, Fin.isValue, Fin.mk_one,
          ComposableArrows.map', homOfLE_leOfHom, Fk, uF, Fh, uF']
        dsimp
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, ComposableArrows.hom, Fhk']
      rw [Fhk.map'_comp 0 1 2] at lem1
      refine eq_of_heq (lem1.trans (heq_comp ?_ ?_ ?_ lem2.symm lem0.symm)) <;>
        simp [uF', nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂,
          ReflQuiv.comp_eq_comp, OneTruncation₂.nerveHomEquiv, Fk, uF, Fhk] <;>
        [let ι := ι0₂; let ι := ι1₂; let ι := ι2₂] <;>
      · replace := congr_arg (·.obj 0) (congr_fun (F.naturality ι.op) hk)
        dsimp [oneTruncation₂, ComposableArrows.left, SimplicialObject.truncation,
          nerveFunctor₂, SSet.truncation, forget₂, HasForget₂.forget₂] at this ⊢
        convert this.symm
        apply ComposableArrows.ext₀; rfl
    let fF : X ⥤ Y := ReflPrefunctor.toFunctor uF' this
    have eq : fF.toReflPrefunctor = uF' := rfl
    refine ⟨fF, toNerve₂.ext (nerveFunctor₂.{u,u}.map fF) F ?_⟩
    · have nat := OneTruncation₂.ofNerve₂.natIso.hom.naturality fF
      simp at nat
      rw [eq] at nat
      simp [uF', uF] at nat
      exact (Iso.cancel_iso_hom_right (oneTruncation₂.map (nerveFunctor₂.map fF))
        (oneTruncation₂.map F) (OneTruncation₂.ofNerve₂.natIso.app Y)).mp nat

/-- The 2-truncated nerve functor is both full and faithful and thus is fully faithful. -/
noncomputable def nerveFunctor₂.fullyfaithful : nerveFunctor₂.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor₂

instance nerve₂Adj.reflective : Reflective nerveFunctor₂.{u, u} :=
  Reflective.mk hoFunctor₂ nerve₂Adj

end

/-- The adjunction between the nerve functor and the homotopy category functor is, up to
isomorphism, the composite of the adjunctions `SSet.coskAdj 2` and `nerve₂Adj`. -/
noncomputable def nerveAdjunction : hoFunctor ⊣ nerveFunctor :=
  Adjunction.ofNatIsoRight ((SSet.coskAdj 2).comp nerve₂Adj) Nerve.cosk₂Iso.symm

/-- Repleteness exists for full and faithful functors but not fully faithful functors, which is
why we do this inefficiently. -/
instance nerveFunctor.faithful : nerveFunctor.{u, u}.Faithful :=
  have : (Nerve.nerveFunctor₂ ⋙ SSet.Truncated.cosk 2).Faithful :=
    Faithful.comp nerveFunctor₂ (SSet.Truncated.cosk 2)
  Functor.Faithful.of_iso Nerve.cosk₂Iso.symm

instance nerveFunctor.full : nerveFunctor.{u, u}.Full :=
  have : (Nerve.nerveFunctor₂ ⋙ SSet.Truncated.cosk 2).Full :=
    Full.comp nerveFunctor₂ (SSet.Truncated.cosk 2)
  Functor.Full.of_iso Nerve.cosk₂Iso.symm

/-- The nerve functor is both full and faithful and thus is fully faithful. -/
noncomputable def nerveFunctor.fullyfaithful : nerveFunctor.FullyFaithful :=
  FullyFaithful.ofFullyFaithful nerveFunctor

instance nerveAdjunction.isIso_counit : IsIso nerveAdjunction.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- The counit map of `nerveAdjunction` is an isomorphism since the nerve functor is fully
faithful. -/
noncomputable def nerveFunctorCompHoFunctorIso : nerveFunctor.{u, u} ⋙ hoFunctor ≅ 𝟭 Cat :=
  asIso (nerveAdjunction.counit)

noncomputable instance : Reflective nerveFunctor where
  L := hoFunctor
  adj := nerveAdjunction

end CategoryTheory
