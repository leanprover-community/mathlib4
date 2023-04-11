/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz

! This file was ported from Lean 3 source module category_theory.sites.sheafification
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.FullyFaithful
import Mathbin.CategoryTheory.Sites.Plus
import Mathbin.CategoryTheory.Limits.ConcreteCategory
import Mathbin.CategoryTheory.ConcreteCategory.Elementwise

/-!

# Sheafification

We construct the sheafification of a presheaf over a site `C` with values in `D` whenever
`D` is a concrete category for which the forgetful functor preserves the appropriate (co)limits
and reflects isomorphisms.

We generally follow the approach of https://stacks.math.columbia.edu/tag/00W1

-/


namespace CategoryTheory

open CategoryTheory.Limits Opposite

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable {D : Type w} [Category.{max v u} D]

section

variable [ConcreteCategory.{max v u} D]

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

/-- A concrete version of the multiequalizer, to be used below. -/
@[nolint has_nonempty_instance]
def Meq {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) :=
  { x : ∀ I : S.arrow, P.obj (op I.y) //
    ∀ I : S.Relation, P.map I.g₁.op (x I.fst) = P.map I.g₂.op (x I.snd) }
#align category_theory.meq CategoryTheory.Meq

end

namespace Meq

variable [ConcreteCategory.{max v u} D]

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

instance {X} (P : Cᵒᵖ ⥤ D) (S : J.cover X) :
    CoeFun (Meq P S) fun x => ∀ I : S.arrow, P.obj (op I.y) :=
  ⟨fun x => x.1⟩

@[ext]
theorem ext {X} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x y : Meq P S) (h : ∀ I : S.arrow, x I = y I) :
    x = y :=
  Subtype.ext <| funext <| h
#align category_theory.meq.ext CategoryTheory.Meq.ext

theorem condition {X} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : Meq P S) (I : S.Relation) :
    P.map I.g₁.op (x ((S.index P).fstTo I)) = P.map I.g₂.op (x ((S.index P).sndTo I)) :=
  x.2 _
#align category_theory.meq.condition CategoryTheory.Meq.condition

/-- Refine a term of `meq P T` with respect to a refinement `S ⟶ T` of covers. -/
def refine {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (x : Meq P T) (e : S ⟶ T) : Meq P S :=
  ⟨fun I => x ⟨I.y, I.f, (leOfHom e) _ I.hf⟩, fun I =>
    x.condition
      ⟨I.y₁, I.y₂, I.z, I.g₁, I.g₂, I.f₁, I.f₂, (leOfHom e) _ I.h₁, (leOfHom e) _ I.h₂, I.w⟩⟩
#align category_theory.meq.refine CategoryTheory.Meq.refine

@[simp]
theorem refine_apply {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (x : Meq P T) (e : S ⟶ T)
    (I : S.arrow) : x.refine e I = x ⟨I.y, I.f, (leOfHom e) _ I.hf⟩ :=
  rfl
#align category_theory.meq.refine_apply CategoryTheory.Meq.refine_apply

/-- Pull back a term of `meq P S` with respect to a morphism `f : Y ⟶ X` in `C`. -/
def pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : Meq P S) (f : Y ⟶ X) :
    Meq P ((J.pullback f).obj S) :=
  ⟨fun I => x ⟨_, I.f ≫ f, I.hf⟩, fun I =>
    x.condition
      ⟨I.y₁, I.y₂, I.z, I.g₁, I.g₂, I.f₁ ≫ f, I.f₂ ≫ f, I.h₁, I.h₂, by simp [reassoc_of I.w]⟩⟩
#align category_theory.meq.pullback CategoryTheory.Meq.pullback

@[simp]
theorem pullback_apply {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : Meq P S) (f : Y ⟶ X)
    (I : ((J.pullback f).obj S).arrow) : x.pullback f I = x ⟨_, I.f ≫ f, I.hf⟩ :=
  rfl
#align category_theory.meq.pullback_apply CategoryTheory.Meq.pullback_apply

@[simp]
theorem pullback_refine {Y X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (h : S ⟶ T) (f : Y ⟶ X)
    (x : Meq P T) : (x.pullback f).refine ((J.pullback f).map h) = (refine x h).pullback _ :=
  rfl
#align category_theory.meq.pullback_refine CategoryTheory.Meq.pullback_refine

/-- Make a term of `meq P S`. -/
def mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) : Meq P S :=
  ⟨fun I => P.map I.f.op x, fun I => by
    dsimp
    simp only [← comp_apply, ← P.map_comp, ← op_comp, I.w]⟩
#align category_theory.meq.mk CategoryTheory.Meq.mk

theorem mk_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) (I : S.arrow) :
    mk S x I = P.map I.f.op x :=
  rfl
#align category_theory.meq.mk_apply CategoryTheory.Meq.mk_apply

variable [PreservesLimits (forget D)]

/-- The equivalence between the type associated to `multiequalizer (S.index P)` and `meq P S`. -/
noncomputable def equiv {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) [HasMultiequalizer (S.index P)] :
    (multiequalizer (S.index P) : D) ≃ Meq P S :=
  Limits.Concrete.multiequalizerEquiv _
#align category_theory.meq.equiv CategoryTheory.Meq.equiv

@[simp]
theorem equiv_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} [HasMultiequalizer (S.index P)]
    (x : multiequalizer (S.index P)) (I : S.arrow) :
    equiv P S x I = Multiequalizer.ι (S.index P) I x :=
  rfl
#align category_theory.meq.equiv_apply CategoryTheory.Meq.equiv_apply

@[simp]
theorem equiv_symm_eq_apply {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} [HasMultiequalizer (S.index P)]
    (x : Meq P S) (I : S.arrow) : Multiequalizer.ι (S.index P) I ((Meq.equiv P S).symm x) = x I :=
  by
  let z := (meq.equiv P S).symm x
  rw [← equiv_apply]
  simp
#align category_theory.meq.equiv_symm_eq_apply CategoryTheory.Meq.equiv_symm_eq_apply

end Meq

namespace GrothendieckTopology

namespace Plus

variable [ConcreteCategory.{max v u} D]

attribute [local instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variable [PreservesLimits (forget D)]

variable [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]

noncomputable section

/-- Make a term of `(J.plus_obj P).obj (op X)` from `x : meq P S`. -/
def mk {X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : Meq P S) : (J.plusObj P).obj (op X) :=
  colimit.ι (J.diagram P X) (op S) ((Meq.equiv P S).symm x)
#align category_theory.grothendieck_topology.plus.mk CategoryTheory.GrothendieckTopology.Plus.mk

theorem res_mk_eq_mk_pullback {Y X : C} {P : Cᵒᵖ ⥤ D} {S : J.cover X} (x : Meq P S) (f : Y ⟶ X) :
    (J.plusObj P).map f.op (mk x) = mk (x.pullback f) :=
  by
  dsimp [mk, plus_obj]
  simp only [← comp_apply, colimit.ι_pre, ι_colim_map_assoc]
  simp_rw [comp_apply]
  congr 1
  apply_fun meq.equiv P _
  erw [Equiv.apply_symm_apply]
  ext i
  simp only [diagram_pullback_app, meq.pullback_apply, meq.equiv_apply, ← comp_apply]
  erw [multiequalizer.lift_ι, meq.equiv_symm_eq_apply]
  cases i; rfl
#align category_theory.grothendieck_topology.plus.res_mk_eq_mk_pullback CategoryTheory.GrothendieckTopology.Plus.res_mk_eq_mk_pullback

theorem toPlus_mk {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : P.obj (op X)) :
    (J.toPlus P).app _ x = mk (Meq.mk S x) :=
  by
  dsimp [mk, to_plus]
  let e : S ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
  rw [← colimit.w _ e.op]
  delta cover.to_multiequalizer
  simp only [comp_apply]
  congr 1
  dsimp [diagram]
  apply concrete.multiequalizer_ext
  intro i
  simpa only [← comp_apply, category.assoc, multiequalizer.lift_ι, category.comp_id,
    meq.equiv_symm_eq_apply]
#align category_theory.grothendieck_topology.plus.to_plus_mk CategoryTheory.GrothendieckTopology.Plus.toPlus_mk

theorem toPlus_apply {X : C} {P : Cᵒᵖ ⥤ D} (S : J.cover X) (x : Meq P S) (I : S.arrow) :
    (J.toPlus P).app _ (x I) = (J.plusObj P).map I.f.op (mk x) :=
  by
  dsimp only [to_plus, plus_obj]
  delta cover.to_multiequalizer
  dsimp [mk]
  simp only [← comp_apply, colimit.ι_pre, ι_colim_map_assoc]
  simp only [comp_apply]
  dsimp only [functor.op]
  let e : (J.pullback I.f).obj (unop (op S)) ⟶ ⊤ := hom_of_le (OrderTop.le_top _)
  rw [← colimit.w _ e.op]
  simp only [comp_apply]
  congr 1
  apply concrete.multiequalizer_ext
  intro i
  dsimp [diagram]
  simp only [← comp_apply, category.assoc, multiequalizer.lift_ι, category.comp_id,
    meq.equiv_symm_eq_apply]
  let RR : S.relation :=
    ⟨_, _, _, i.f, 𝟙 _, I.f, i.f ≫ I.f, I.hf, sieve.downward_closed _ I.hf _, by simp⟩
  cases I
  erw [x.condition RR]
  simpa [RR]
#align category_theory.grothendieck_topology.plus.to_plus_apply CategoryTheory.GrothendieckTopology.Plus.toPlus_apply

theorem toPlus_eq_mk {X : C} {P : Cᵒᵖ ⥤ D} (x : P.obj (op X)) :
    (J.toPlus P).app _ x = mk (Meq.mk ⊤ x) :=
  by
  dsimp [mk, to_plus]
  delta cover.to_multiequalizer
  simp only [comp_apply]
  congr 1
  apply_fun meq.equiv P ⊤
  ext i
  simpa
#align category_theory.grothendieck_topology.plus.to_plus_eq_mk CategoryTheory.GrothendieckTopology.Plus.toPlus_eq_mk

variable [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)]

theorem exists_rep {X : C} {P : Cᵒᵖ ⥤ D} (x : (J.plusObj P).obj (op X)) :
    ∃ (S : J.cover X)(y : Meq P S), x = mk y :=
  by
  obtain ⟨S, y, h⟩ := concrete.colimit_exists_rep (J.diagram P X) x
  use S.unop, meq.equiv _ _ y
  rw [← h]
  dsimp [mk]
  simp
#align category_theory.grothendieck_topology.plus.exists_rep CategoryTheory.GrothendieckTopology.Plus.exists_rep

theorem eq_mk_iff_exists {X : C} {P : Cᵒᵖ ⥤ D} {S T : J.cover X} (x : Meq P S) (y : Meq P T) :
    mk x = mk y ↔ ∃ (W : J.cover X)(h1 : W ⟶ S)(h2 : W ⟶ T), x.refine h1 = y.refine h2 :=
  by
  constructor
  · intro h
    obtain ⟨W, h1, h2, hh⟩ := concrete.colimit_exists_of_rep_eq _ _ _ h
    use W.unop, h1.unop, h2.unop
    ext I
    apply_fun multiequalizer.ι (W.unop.index P) I  at hh
    convert hh
    all_goals
      dsimp [diagram]
      simp only [← comp_apply, multiequalizer.lift_ι, category.comp_id, meq.equiv_symm_eq_apply]
      cases I; rfl
  · rintro ⟨S, h1, h2, e⟩
    apply concrete.colimit_rep_eq_of_exists
    use op S, h1.op, h2.op
    apply concrete.multiequalizer_ext
    intro i
    apply_fun fun ee => ee i  at e
    convert e
    all_goals
      dsimp [diagram]
      simp only [← comp_apply, multiequalizer.lift_ι, meq.equiv_symm_eq_apply]
      cases i; rfl
#align category_theory.grothendieck_topology.plus.eq_mk_iff_exists CategoryTheory.GrothendieckTopology.Plus.eq_mk_iff_exists

/-- `P⁺` is always separated. -/
theorem sep {X : C} (P : Cᵒᵖ ⥤ D) (S : J.cover X) (x y : (J.plusObj P).obj (op X))
    (h : ∀ I : S.arrow, (J.plusObj P).map I.f.op x = (J.plusObj P).map I.f.op y) : x = y :=
  by
  -- First, we choose representatives for x and y.
  obtain ⟨Sx, x, rfl⟩ := exists_rep x
  obtain ⟨Sy, y, rfl⟩ := exists_rep y
  simp only [res_mk_eq_mk_pullback] at h
  -- Next, using our assumption,
  -- choose covers over which the pullbacks of these representatives become equal.
  choose W h1 h2 hh using fun I : S.arrow => (eq_mk_iff_exists _ _).mp (h I)
  -- To prove equality, it suffices to prove that there exists a cover over which
  -- the representatives become equal.
  rw [eq_mk_iff_exists]
  -- Construct the cover over which the representatives become equal by combining the various
  -- covers chosen above.
  let B : J.cover X := S.bind W
  use B
  -- Prove that this cover refines the two covers over which our representatives are defined
  -- and use these proofs.
  let ex : B ⟶ Sx :=
    hom_of_le
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply le_of_hom (h1 ⟨_, _, he2⟩)
        exact he1)
  let ey : B ⟶ Sy :=
    hom_of_le
      (by
        rintro Y f ⟨Z, e1, e2, he2, he1, hee⟩
        rw [← hee]
        apply le_of_hom (h2 ⟨_, _, he2⟩)
        exact he1)
  use ex, ey
  -- Now prove that indeed the representatives become equal over `B`.
  -- This will follow by using the fact that our representatives become
  -- equal over the chosen covers.
  ext1 I
  let IS : S.arrow := I.from_middle
  specialize hh IS
  let IW : (W IS).arrow := I.to_middle
  apply_fun fun e => e IW  at hh
  convert hh
  · let Rx : Sx.relation :=
      ⟨I.Y, I.Y, I.Y, 𝟙 _, 𝟙 _, I.f, I.to_middle_hom ≫ I.from_middle_hom, _, _, by
        simp [I.middle_spec]⟩
    have := x.condition Rx
    simpa using this
  · let Ry : Sy.relation :=
      ⟨I.Y, I.Y, I.Y, 𝟙 _, 𝟙 _, I.f, I.to_middle_hom ≫ I.from_middle_hom, _, _, by
        simp [I.middle_spec]⟩
    have := y.condition Ry
    simpa using this
#align category_theory.grothendieck_topology.plus.sep CategoryTheory.GrothendieckTopology.Plus.sep

theorem inj_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
        (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) : Function.Injective ((J.toPlus P).app (op X)) :=
  by
  intro x y h
  simp only [to_plus_eq_mk] at h
  rw [eq_mk_iff_exists] at h
  obtain ⟨W, h1, h2, hh⟩ := h
  apply hsep X W
  intro I
  apply_fun fun e => e I  at hh
  exact hh
#align category_theory.grothendieck_topology.plus.inj_of_sep CategoryTheory.GrothendieckTopology.Plus.inj_of_sep

/-- An auxiliary definition to be used in the proof of `exists_of_sep` below.
  Given a compatible family of local sections for `P⁺`, and representatives of said sections,
  construct a compatible family of local sections of `P` over the combination of the covers
  associated to the representatives.
  The separatedness condition is used to prove compatibility among these local sections of `P`. -/
def meqOfSep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
        (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) (S : J.cover X) (s : Meq (J.plusObj P) S) (T : ∀ I : S.arrow, J.cover I.y)
    (t : ∀ I : S.arrow, Meq P (T I)) (ht : ∀ I : S.arrow, s I = mk (t I)) : Meq P (S.bind T)
    where
  val I := t I.fromMiddle I.toMiddle
  property := by
    intro II
    apply inj_of_sep P hsep
    rw [← comp_apply, ← comp_apply, (J.to_plus P).naturality, (J.to_plus P).naturality, comp_apply,
      comp_apply]
    erw [to_plus_apply (T II.fst.from_middle) (t II.fst.from_middle) II.fst.to_middle,
      to_plus_apply (T II.snd.from_middle) (t II.snd.from_middle) II.snd.to_middle, ← ht, ← ht, ←
      comp_apply, ← comp_apply, ← (J.plus_obj P).map_comp, ← (J.plus_obj P).map_comp]
    rw [← op_comp, ← op_comp]
    let IR : S.relation :=
      ⟨_, _, _, II.g₁ ≫ II.fst.to_middle_hom, II.g₂ ≫ II.snd.to_middle_hom, II.fst.from_middle_hom,
        II.snd.from_middle_hom, II.fst.from_middle_condition, II.snd.from_middle_condition, _⟩
    swap;
    · simp only [category.assoc, II.fst.middle_spec, II.snd.middle_spec]
      apply II.w
    exact s.condition IR
#align category_theory.grothendieck_topology.plus.meq_of_sep CategoryTheory.GrothendieckTopology.Plus.meqOfSep

theorem exists_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
        (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y)
    (X : C) (S : J.cover X) (s : Meq (J.plusObj P) S) :
    ∃ t : (J.plusObj P).obj (op X), Meq.mk S t = s :=
  by
  have inj : ∀ X : C, Function.Injective ((J.to_plus P).app (op X)) := inj_of_sep _ hsep
  -- Choose representatives for the given local sections.
  choose T t ht using fun I => exists_rep (s I)
  -- Construct a large cover over which we will define a representative that will
  -- provide the gluing of the given local sections.
  let B : J.cover X := S.bind T
  choose Z e1 e2 he2 he1 hee using fun I : B.arrow => I.hf
  -- Construct a compatible system of local sections over this large cover, using the chosen
  -- representatives of our local sections.
  -- The compatilibity here follows from the separatedness assumption.
  let w : meq P B := meq_of_sep P hsep X S s T t ht
  -- The associated gluing will be the candidate section.
  use mk w
  ext I
  erw [ht, res_mk_eq_mk_pullback]
  -- Use the separatedness of `P⁺` to prove that this is indeed a gluing of our
  -- original local sections.
  apply sep P (T I)
  intro II
  simp only [res_mk_eq_mk_pullback, eq_mk_iff_exists]
  -- It suffices to prove equality for representatives over a
  -- convenient sufficiently large cover...
  use (J.pullback II.f).obj (T I)
  let e0 : (J.pullback II.f).obj (T I) ⟶ (J.pullback II.f).obj ((J.pullback I.f).obj B) :=
    hom_of_le
      (by
        intro Y f hf
        apply sieve.le_pullback_bind _ _ _ I.hf
        · cases I
          exact hf)
  use e0, 𝟙 _
  ext IV
  dsimp only [meq.refine_apply, meq.pullback_apply, w]
  let IA : B.arrow := ⟨_, (IV.f ≫ II.f) ≫ I.f, _⟩
  swap
  · refine' ⟨I.Y, _, _, I.hf, _, rfl⟩
    apply sieve.downward_closed
    convert II.hf
    cases I
    rfl
  let IB : S.arrow := IA.from_middle
  let IC : (T IB).arrow := IA.to_middle
  let ID : (T I).arrow := ⟨IV.Y, IV.f ≫ II.f, sieve.downward_closed (T I) II.hf IV.f⟩
  change t IB IC = t I ID
  apply inj IV.Y
  erw [to_plus_apply (T I) (t I) ID, to_plus_apply (T IB) (t IB) IC, ← ht, ← ht]
  -- Conclude by constructing the relation showing equality...
  let IR : S.relation := ⟨_, _, IV.Y, IC.f, ID.f, IB.f, I.f, _, I.hf, IA.middle_spec⟩
  convert s.condition IR
  cases I; rfl
#align category_theory.grothendieck_topology.plus.exists_of_sep CategoryTheory.GrothendieckTopology.Plus.exists_of_sep

variable [ReflectsIsomorphisms (forget D)]

/-- If `P` is separated, then `P⁺` is a sheaf. -/
theorem isSheaf_of_sep (P : Cᵒᵖ ⥤ D)
    (hsep :
      ∀ (X : C) (S : J.cover X) (x y : P.obj (op X)),
        (∀ I : S.arrow, P.map I.f.op x = P.map I.f.op y) → x = y) :
    Presheaf.IsSheaf J (J.plusObj P) :=
  by
  rw [presheaf.is_sheaf_iff_multiequalizer]
  intro X S
  apply is_iso_of_reflects_iso _ (forget D)
  rw [is_iso_iff_bijective]
  constructor
  · intro x y h
    apply sep P S _ _
    intro I
    apply_fun meq.equiv _ _  at h
    apply_fun fun e => e I  at h
    convert h
    · erw [meq.equiv_apply, ← comp_apply, multiequalizer.lift_ι]
    · erw [meq.equiv_apply, ← comp_apply, multiequalizer.lift_ι]
  · rintro (x : (multiequalizer (S.index _) : D))
    obtain ⟨t, ht⟩ := exists_of_sep P hsep X S (meq.equiv _ _ x)
    use t
    apply_fun meq.equiv _ _
    swap
    · infer_instance
    rw [← ht]
    ext i
    dsimp
    rw [← comp_apply, multiequalizer.lift_ι]
    rfl
#align category_theory.grothendieck_topology.plus.is_sheaf_of_sep CategoryTheory.GrothendieckTopology.Plus.isSheaf_of_sep

variable (J)

/-- `P⁺⁺` is always a sheaf. -/
theorem isSheaf_plus_plus (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.plusObj (J.plusObj P)) :=
  by
  apply is_sheaf_of_sep
  intro X S x y
  apply sep
#align category_theory.grothendieck_topology.plus.is_sheaf_plus_plus CategoryTheory.GrothendieckTopology.Plus.isSheaf_plus_plus

end Plus

variable (J)

variable [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]

/-- The sheafification of a presheaf `P`.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
def sheafify (P : Cᵒᵖ ⥤ D) : Cᵒᵖ ⥤ D :=
  J.plusObj (J.plusObj P)
#align category_theory.grothendieck_topology.sheafify CategoryTheory.GrothendieckTopology.sheafify

/-- The canonical map from `P` to its sheafification. -/
def toSheafify (P : Cᵒᵖ ⥤ D) : P ⟶ J.sheafify P :=
  J.toPlus P ≫ J.plusMap (J.toPlus P)
#align category_theory.grothendieck_topology.to_sheafify CategoryTheory.GrothendieckTopology.toSheafify

/-- The canonical map on sheafifications induced by a morphism. -/
def sheafifyMap {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) : J.sheafify P ⟶ J.sheafify Q :=
  J.plusMap <| J.plusMap η
#align category_theory.grothendieck_topology.sheafify_map CategoryTheory.GrothendieckTopology.sheafifyMap

@[simp]
theorem sheafifyMap_id (P : Cᵒᵖ ⥤ D) : J.sheafifyMap (𝟙 P) = 𝟙 (J.sheafify P) :=
  by
  dsimp [sheafify_map, sheafify]
  simp
#align category_theory.grothendieck_topology.sheafify_map_id CategoryTheory.GrothendieckTopology.sheafifyMap_id

@[simp]
theorem sheafifyMap_comp {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    J.sheafifyMap (η ≫ γ) = J.sheafifyMap η ≫ J.sheafifyMap γ :=
  by
  dsimp [sheafify_map, sheafify]
  simp
#align category_theory.grothendieck_topology.sheafify_map_comp CategoryTheory.GrothendieckTopology.sheafifyMap_comp

@[simp, reassoc.1]
theorem toSheafify_naturality {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toSheafify _ = J.toSheafify _ ≫ J.sheafifyMap η :=
  by
  dsimp [sheafify_map, sheafify, to_sheafify]
  simp
#align category_theory.grothendieck_topology.to_sheafify_naturality CategoryTheory.GrothendieckTopology.toSheafify_naturality

variable (D)

/-- The sheafification of a presheaf `P`, as a functor.
*NOTE:* Additional hypotheses are needed to obtain a proof that this is a sheaf! -/
def sheafification : (Cᵒᵖ ⥤ D) ⥤ Cᵒᵖ ⥤ D :=
  J.plusFunctor D ⋙ J.plusFunctor D
#align category_theory.grothendieck_topology.sheafification CategoryTheory.GrothendieckTopology.sheafification

@[simp]
theorem sheafification_obj (P : Cᵒᵖ ⥤ D) : (J.sheafification D).obj P = J.sheafify P :=
  rfl
#align category_theory.grothendieck_topology.sheafification_obj CategoryTheory.GrothendieckTopology.sheafification_obj

@[simp]
theorem sheafification_map {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    (J.sheafification D).map η = J.sheafifyMap η :=
  rfl
#align category_theory.grothendieck_topology.sheafification_map CategoryTheory.GrothendieckTopology.sheafification_map

/-- The canonical map from `P` to its sheafification, as a natural transformation.
*Note:* We only show this is a sheaf under additional hypotheses on `D`. -/
def toSheafification : 𝟭 _ ⟶ sheafification J D :=
  J.toPlusNatTrans D ≫ whiskerRight (J.toPlusNatTrans D) (J.plusFunctor D)
#align category_theory.grothendieck_topology.to_sheafification CategoryTheory.GrothendieckTopology.toSheafification

@[simp]
theorem toSheafification_app (P : Cᵒᵖ ⥤ D) : (J.toSheafification D).app P = J.toSheafify P :=
  rfl
#align category_theory.grothendieck_topology.to_sheafification_app CategoryTheory.GrothendieckTopology.toSheafification_app

variable {D}

theorem isIso_toSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : IsIso (J.toSheafify P) :=
  by
  dsimp [to_sheafify]
  haveI : is_iso (J.to_plus P) := by apply is_iso_to_plus_of_is_sheaf J P hP
  haveI : is_iso ((J.plus_functor D).map (J.to_plus P)) := by apply functor.map_is_iso
  exact @is_iso.comp_is_iso _ _ _ _ _ (J.to_plus P) ((J.plus_functor D).map (J.to_plus P)) _ _
#align category_theory.grothendieck_topology.is_iso_to_sheafify CategoryTheory.GrothendieckTopology.isIso_toSheafify

/-- If `P` is a sheaf, then `P` is isomorphic to `J.sheafify P`. -/
def isoSheafify {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) : P ≅ J.sheafify P :=
  letI := is_iso_to_sheafify J hP
  as_iso (J.to_sheafify P)
#align category_theory.grothendieck_topology.iso_sheafify CategoryTheory.GrothendieckTopology.isoSheafify

@[simp]
theorem isoSheafify_hom {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).Hom = J.toSheafify P :=
  rfl
#align category_theory.grothendieck_topology.iso_sheafify_hom CategoryTheory.GrothendieckTopology.isoSheafify_hom

/-- Given a sheaf `Q` and a morphism `P ⟶ Q`, construct a morphism from
`J.sheafifcation P` to `Q`. -/
def sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.sheafify P ⟶ Q :=
  J.plusLift (J.plusLift η hQ) hQ
#align category_theory.grothendieck_topology.sheafify_lift CategoryTheory.GrothendieckTopology.sheafifyLift

@[simp, reassoc.1]
theorem toSheafify_sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) :
    J.toSheafify P ≫ sheafifyLift J η hQ = η :=
  by
  dsimp only [sheafify_lift, to_sheafify]
  simp
#align category_theory.grothendieck_topology.to_sheafify_sheafify_lift CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift

theorem sheafifyLift_unique {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (γ : J.sheafify P ⟶ Q) : J.toSheafify P ≫ γ = η → γ = sheafifyLift J η hQ :=
  by
  intro h
  apply plus_lift_unique
  apply plus_lift_unique
  rw [← category.assoc, ← plus_map_to_plus]
  exact h
#align category_theory.grothendieck_topology.sheafify_lift_unique CategoryTheory.GrothendieckTopology.sheafifyLift_unique

@[simp]
theorem isoSheafify_inv {P : Cᵒᵖ ⥤ D} (hP : Presheaf.IsSheaf J P) :
    (J.isoSheafify hP).inv = J.sheafifyLift (𝟙 _) hP :=
  by
  apply J.sheafify_lift_unique
  simp [iso.comp_inv_eq]
#align category_theory.grothendieck_topology.iso_sheafify_inv CategoryTheory.GrothendieckTopology.isoSheafify_inv

theorem sheafify_hom_ext {P Q : Cᵒᵖ ⥤ D} (η γ : J.sheafify P ⟶ Q) (hQ : Presheaf.IsSheaf J Q)
    (h : J.toSheafify P ≫ η = J.toSheafify P ≫ γ) : η = γ :=
  by
  apply J.plus_hom_ext _ _ hQ
  apply J.plus_hom_ext _ _ hQ
  rw [← category.assoc, ← category.assoc, ← plus_map_to_plus]
  exact h
#align category_theory.grothendieck_topology.sheafify_hom_ext CategoryTheory.GrothendieckTopology.sheafify_hom_ext

@[simp, reassoc.1]
theorem sheafifyMap_sheafifyLift {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    J.sheafifyMap η ≫ J.sheafifyLift γ hR = J.sheafifyLift (η ≫ γ) hR :=
  by
  apply J.sheafify_lift_unique
  rw [← category.assoc, ← J.to_sheafify_naturality, category.assoc, to_sheafify_sheafify_lift]
#align category_theory.grothendieck_topology.sheafify_map_sheafify_lift CategoryTheory.GrothendieckTopology.sheafifyMap_sheafifyLift

end GrothendieckTopology

variable (J)

variable [ConcreteCategory.{max v u} D] [PreservesLimits (forget D)]
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.cover X)ᵒᵖ D]
  [∀ X : C, PreservesColimitsOfShape (J.cover X)ᵒᵖ (forget D)] [ReflectsIsomorphisms (forget D)]

theorem GrothendieckTopology.sheafify_isSheaf (P : Cᵒᵖ ⥤ D) : Presheaf.IsSheaf J (J.sheafify P) :=
  GrothendieckTopology.Plus.isSheaf_plus_plus _ _
#align category_theory.grothendieck_topology.sheafify_is_sheaf CategoryTheory.GrothendieckTopology.sheafify_isSheaf

variable (D)

/-- The sheafification functor, as a functor taking values in `Sheaf`. -/
@[simps]
def presheafToSheaf : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D
    where
  obj P := ⟨J.sheafify P, J.sheafify_isSheaf P⟩
  map P Q η := ⟨J.sheafifyMap η⟩
  map_id' P := Sheaf.Hom.ext _ _ <| J.sheafifyMap_id _
  map_comp' P Q R f g := Sheaf.Hom.ext _ _ <| J.sheafifyMap_comp _ _
#align category_theory.presheaf_to_Sheaf CategoryTheory.presheafToSheaf

instance presheafToSheaf_preservesZeroMorphisms [Preadditive D] :
    (presheafToSheaf J D).PreservesZeroMorphisms
    where map_zero' F G := by
    ext
    erw [colimit.ι_map, comp_zero, J.plus_map_zero, J.diagram_nat_trans_zero, zero_comp]
#align category_theory.presheaf_to_Sheaf_preserves_zero_morphisms CategoryTheory.presheafToSheaf_preservesZeroMorphisms

/-- The sheafification functor is left adjoint to the forgetful functor. -/
@[simps unit_app counit_app_val]
def sheafificationAdjunction : presheafToSheaf J D ⊣ sheafToPresheaf J D :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun e => J.toSheafify P ≫ e.val
          invFun := fun e => ⟨J.sheafifyLift e Q.2⟩
          left_inv := fun e => Sheaf.Hom.ext _ _ <| (J.sheafifyLift_unique _ _ _ rfl).symm
          right_inv := fun e => J.toSheafify_sheafifyLift _ _ }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ; ext1; dsimp; symm
        apply J.sheafify_map_sheafify_lift
      homEquiv_naturality_right := fun P Q R η γ =>
        by
        dsimp
        rw [category.assoc] }
#align category_theory.sheafification_adjunction CategoryTheory.sheafificationAdjunction

instance sheafToPresheafIsRightAdjoint : IsRightAdjoint (sheafToPresheaf J D) :=
  ⟨_, sheafificationAdjunction J D⟩
#align category_theory.Sheaf_to_presheaf_is_right_adjoint CategoryTheory.sheafToPresheafIsRightAdjoint

instance presheaf_mono_of_mono {F G : Sheaf J D} (f : F ⟶ G) [Mono f] : Mono f.1 :=
  (sheafToPresheaf J D).map_mono _
#align category_theory.presheaf_mono_of_mono CategoryTheory.presheaf_mono_of_mono

theorem Sheaf.Hom.mono_iff_presheaf_mono {F G : Sheaf J D} (f : F ⟶ G) : Mono f ↔ Mono f.1 :=
  ⟨fun m => by
    skip
    infer_instance, fun m => by
    skip
    exact Sheaf.hom.mono_of_presheaf_mono J D f⟩
#align category_theory.Sheaf.hom.mono_iff_presheaf_mono CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono

variable {J D}

/-- A sheaf `P` is isomorphic to its own sheafification. -/
@[simps]
def sheafificationIso (P : Sheaf J D) : P ≅ (presheafToSheaf J D).obj P.val
    where
  Hom := ⟨(J.isoSheafify P.2).Hom⟩
  inv := ⟨(J.isoSheafify P.2).inv⟩
  hom_inv_id' := by
    ext1
    apply (J.iso_sheafify P.2).hom_inv_id
  inv_hom_id' := by
    ext1
    apply (J.iso_sheafify P.2).inv_hom_id
#align category_theory.sheafification_iso CategoryTheory.sheafificationIso

instance isIso_sheafificationAdjunction_counit (P : Sheaf J D) :
    IsIso ((sheafificationAdjunction J D).counit.app P) :=
  isIso_of_fully_faithful (sheafToPresheaf J D) _
#align category_theory.is_iso_sheafification_adjunction_counit CategoryTheory.isIso_sheafificationAdjunction_counit

instance sheafification_reflective : IsIso (sheafificationAdjunction J D).counit :=
  NatIso.isIso_of_isIso_app _
#align category_theory.sheafification_reflective CategoryTheory.sheafification_reflective

end CategoryTheory

