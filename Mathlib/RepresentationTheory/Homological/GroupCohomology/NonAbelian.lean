/-
Copyright (c) 2025 Jiedong Jiang, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Jingting Wang
-/
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Non-abelian group cohomology

Let `G` be a group acting on another (not necessarily abelian) group `A`, in this file we define
`H⁰(G, A)` and `H¹(G, A)`, and prove some basic properties about it.

## Main Results

## Reference

-/

universe u

open CategoryTheory

namespace groupCohomology

namespace NonAbelian

attribute [local simp] Equiv.apply_ofInjective_symm

variable (G : Type u) [Monoid G]

def H0 (A : Type*) [AddGroup A] [DistribMulAction G A] : AddSubgroup A where
  carrier := setOf fun v => ∀ g : G, g • v = v
  add_mem' := by simp +contextual
  zero_mem' := by simp
  neg_mem' := by simp +contextual

namespace H0

variable {G} {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
  [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
  (f : A →+[G] B) (g : B →+[G] C)

variable (G) in
@[simp] lemma mem_iff (a : A) : a ∈ H0 G A ↔ ∀ g : G, g • a = a := by rfl

def map : H0 G A →+ H0 G B :=
  f.toAddMonoidHom.restrict (H0 G A) |>.codRestrict (H0 G B) <|
    (fun ⟨a, ha⟩ ↦ fun g ↦ (by simpa using congr(f $(ha g))))

@[simp]
lemma map_eq (a : H0 G A) : ((H0.map f) a).val = f a.val := by simp [H0.map]

variable (G A) in
lemma map_id : H0.map (.id _) = .id (H0 G A) := AddMonoidHom.ext fun x ↦ Subtype.ext (by simp)

lemma map_comp : H0.map (g.comp f) = (H0.map g).comp (H0.map f) := rfl

theorem map_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (H0.map f) := fun _ _ h ↦ Subtype.ext (hf (congrArg Subtype.val h))

theorem map_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Function.Exact (H0.map f) (H0.map g) :=
  fun y ↦ ⟨fun h ↦ ⟨⟨(Equiv.ofInjective f hf).symm ⟨y, (hfg _).mp congr(Subtype.val $h)⟩,
    fun g ↦ hf (by simpa [map_smul] using y.2 g)⟩, Subtype.ext (Equiv.apply_ofInjective_symm _ _)⟩,
      fun ⟨x, hx⟩ ↦ Subtype.ext ((hfg _).mpr ⟨x.1, congr(Subtype.val $hx)⟩)⟩

end H0

def Z1 (A : Type*) [AddGroup A] [DistribMulAction G A] :=
  { f : G → A // ∀ g h : G, f (g * h) = f g + g • f h}

namespace Z1

variable {G} {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
  [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
  (f : A →+[G] B) (g : B →+[G] C)

instance zero : Zero (Z1 G A) := ⟨⟨0, fun g h => by simp⟩⟩
instance inhabited : Inhabited (Z1 G A) := ⟨0⟩

instance coeFun : CoeFun (Z1 G A) (fun _ ↦ G → A) := ⟨fun f ↦ f.val⟩

variable (G A) in
@[simp] lemma zero_apply (g : G) : (0 : Z1 G A) g = 0 := rfl

variable (G A) in
@[simp] lemma zero_coe : (0 : Z1 G A) = (0 : G → A) := rfl

def cohomologous (f g : G → A) : Prop :=
  ∃ a : A, ∀ h : G, g h = - a + f h + (h • a)

lemma cohomologous.refl (f : G → A) : Z1.cohomologous f f := ⟨0, fun h ↦ by simp⟩

lemma cohomologous.symm {f g : G → A} (h : Z1.cohomologous f g) : Z1.cohomologous g f := by
  obtain ⟨a, ha⟩ := h
  exact ⟨-a, fun h ↦ by simp [← add_assoc, ha h]⟩

lemma cohomologous.trans {f g h : G → A} (hfg : Z1.cohomologous f g) (hgh : Z1.cohomologous g h) :
    Z1.cohomologous f h := by
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hgh
  exact ⟨a + b, fun h ↦ by simp [← add_assoc, ha h, hb h]⟩

variable (G A) in @[simps]
instance setoid : Setoid (Z1 G A) where
  r x y := cohomologous x y
  iseqv := {
    refl f := cohomologous.refl f,
    symm h := h.symm,
    trans h h' := h.trans h'
  }

@[simp]
theorem equiv_iff_cohomologous (f : Z1 G A) (g : Z1 G A) : f ≈ g ↔ Z1.cohomologous f g := Iff.rfl

theorem mem_of_cohomologous (f : G → A) (f' : Z1 G A) (hfg : Z1.cohomologous f f') :
    ∀ g h : G, f (g * h) = f g + g • f h := by
  obtain ⟨a, ha⟩ := hfg.symm
  simp [ha, f'.2, add_assoc, mul_smul]

def map : Z1 G A → Z1 G B := fun z ↦ ⟨f ∘ z, fun g h => by simp [z.prop, map_smul]⟩

@[simp] lemma map_zero : Z1.map f 0 = 0 := Subtype.ext <| funext fun _ ↦ (by simp [Z1.map])

@[simp] lemma map_zero_apply (x : Z1 G A) : Z1.map (0 : A →+[G] B) x = 0 := by
  apply Subtype.ext
  simp [Z1.map]

@[simp] lemma map_apply (z : Z1 G A) (x : G) : (Z1.map f z) x = f (z x) := rfl

lemma map_cohomologous (z1 z2 : Z1 G A) (h : z1 ≈ z2) : Z1.map f z1 ≈ Z1.map f z2 := by
  obtain ⟨a, ha⟩ := h
  simp only [equiv_iff_cohomologous, cohomologous, map_apply]
  exact ⟨f a, fun h ↦ by simp [ha, map_smul]⟩

end Z1

def H1 (A : Type*) [AddGroup A] [DistribMulAction G A] := Quotient (Z1.setoid G A)

namespace H1

variable {G} {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
  [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
  (f : A →+[G] B) (g : B →+[G] C)

instance : Zero (H1 G A) := ⟨⟦0⟧⟩
instance : Inhabited (H1 G A) := ⟨0⟩

variable (G A) in
lemma zero_def : (0 : H1 G A) = ⟦0⟧ := rfl

def map : H1 G A → H1 G B :=
  Quotient.map (Z1.map f) (Z1.map_cohomologous f)

variable (G A) in
theorem map_id : H1.map (.id _) = @id (H1 G A) := funext fun a ↦ by
  induction a using Quotient.inductionOn with | h a =>
  refine Quotient.eq.mpr ⟨0, fun _ ↦ by simp⟩

@[simp]
theorem map_eq (x : Z1 G A) : H1.map f ⟦x⟧ = ⟦Z1.map f x⟧ := by simp [H1.map]

@[simp]
theorem map_zero : H1.map f 0 = 0 := by
  simp only [H1.map, zero_def, Quotient.map_mk]
  exact congrArg _ <| Subtype.ext (funext fun x ↦ f.map_zero)

@[simp]
theorem zero_map_apply (x : H1 G A) : H1.map (0 : A →+[G] B) x = 0 := by
  induction x using Quotient.inductionOn with | h a =>
  simp only [map, Quotient.map_mk, zero_def]
  rfl

theorem map_comp : H1.map (g.comp f) = (H1.map g).comp (H1.map f) :=
  funext fun a ↦ by induction a using Quotient.inductionOn with | _ => rfl

theorem map_comp_apply (x : H1 G A) : H1.map (g.comp f) x = (H1.map g) ((H1.map f) x) :=
  congr($(H1.map_comp f g) x)

theorem map_exact (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) : Function.Exact (H1.map f) (H1.map g) := by
  refine fun y ↦ ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ ?_⟩
  · induction y using Quotient.inductionOn with | h b =>
    obtain ⟨x, hx⟩ := Quotient.eq_iff_equiv.mp h
    obtain ⟨x, rfl⟩ := hg x
    simp only [Z1.zero_apply, ← map_neg, Z1.map_apply, ← map_add, ← map_smul] at hx
    choose a ha using fun (h : G) ↦ (hfg _).mp (hx h).symm
    refine ⟨Quotient.mk _ (⟨a, fun g h ↦ hf ?_⟩ : Z1 G A), Quotient.eq.mpr ?_⟩
    · simp only [map_add, map_smul]
      exact b.mem_of_cohomologous (f ∘ a) (.symm ⟨x, ha⟩) g h
    · exact .symm ⟨x, by simpa using ha⟩
  · rw [← map_comp_apply, ((g.comp f).ext (g := 0) hfg.apply_apply_eq_zero), zero_map_apply]

end H1

section connectHom₀₁

variable {G : Type u} [Group G] {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    {f : A →+[G] B} {g : B →+[G] C} (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g)

@[simps]
noncomputable def δ₀₁_aux (b : B) (c : H0 G C) (hb : g b = c) : Z1 G A := ⟨fun s ↦
  (Equiv.ofInjective f hf).symm ⟨-b + s • b, ((hfg _).mp (by simp [hb, c.prop s]))⟩,
    fun g h ↦ hf (by simp [mul_smul, ← add_assoc])⟩

theorem δ₀₁_aux_well_defined_1 (b b' : B) (c : H0 G C) (hb : g b = c) (hb' : g b' = c) :
    Z1.cohomologous (δ₀₁_aux hf hfg b c hb) (δ₀₁_aux hf hfg b' c hb') :=
  ⟨(Equiv.ofInjective f hf).symm ⟨- b + b', (hfg _).mp (by rw [map_add, map_neg, hb, hb',
    neg_add_cancel])⟩, fun h ↦ hf (by simp [δ₀₁_aux, ← add_assoc])⟩

noncomputable def δ₀₁ : H0 G C → H1 G A := fun x ↦
    ⟦δ₀₁_aux hf hfg (hg x).choose x (hg x).choose_spec⟧

theorem δ₀₁_eq_of_map (b : B) (c : H0 G C) (hb : g b = c) :
    δ₀₁ hf hg hfg c = ⟦δ₀₁_aux hf hfg b c hb⟧ :=
  Quotient.eq_iff_equiv.mpr (δ₀₁_aux_well_defined_1 ..)

theorem δ₀₁_zero : δ₀₁ hf hg hfg 0 = 0 :=
  (δ₀₁_eq_of_map hf hg hfg 0 0 (map_zero _)).trans (congrArg _ <| Subtype.ext <|
    funext fun x ↦ hf <| by simp [δ₀₁_aux])

theorem exact_H0_map_δ₀₁ : Function.Exact (H0.map g) (δ₀₁ hf hg hfg) := by
  refine fun y ↦ ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ (δ₀₁_eq_of_map (hb := congr(Subtype.val $hx)) ..).trans
    <| congrArg _ <| Subtype.ext <| funext <| fun s ↦ hf (by simp [δ₀₁_aux, x.2 s])⟩
  obtain ⟨b, hb⟩ := hg y
  obtain ⟨x, hx⟩ := Quotient.eq_iff_equiv.mp ((δ₀₁_eq_of_map (hb := hb) ..).symm.trans h)
  refine ⟨⟨b + f x, fun h ↦ (neg_add_eq_zero.mp ?_).symm⟩,
    Subtype.ext (by simpa [H0.map, hfg.apply_apply_eq_zero])⟩
  simpa [δ₀₁_aux, ← add_assoc] using congr(f $(hx h)).symm

theorem exact_δ₀₁_H1_map : Function.Exact (δ₀₁ hf hg hfg) (H1.map f) := by
  refine fun y ↦ ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ Quotient.eq_iff_equiv.mpr
    ⟨- (hg x).choose, fun h ↦ by simp⟩⟩
  induction y using Quotient.inductionOn
  simp only [H1.map, Quotient.map_mk] at h
  obtain ⟨x, hx⟩ := Quotient.eq_iff_equiv.mp h
  refine ⟨⟨g (-x), fun h ↦ (add_neg_eq_zero.mp ?_).symm⟩, (δ₀₁_eq_of_map hf hg hfg _ _ rfl).trans
    <| congrArg _ <| Subtype.ext <| funext fun h ↦ hf ?_⟩
  · simpa [hfg.apply_apply_eq_zero] using congr(g $(hx h)).symm
  · simp only [map_neg, δ₀₁_aux_coe, neg_neg, smul_neg, Equiv.apply_ofInjective_symm]
    refine eq_sub_iff_add_eq.mp (neg_add_eq_zero.mp ?_)
    simpa [add_assoc] using (hx h).symm

end connectHom₀₁

section connectHom₁₂

variable {G : Type u} [Group G] {k : Type u} [CommRing k] {A : Rep k G}
  {B C : Type*} [AddGroup B] [AddGroup C] [DistribMulAction G B] [DistribMulAction G C]
  {f : A →+[G] B} {g : B →+[G] C} (hf : Function.Injective f) (hg : Function.Surjective g)
  (hfg : Function.Exact f g) (hA : f.toAddMonoidHom.range ≤ AddSubgroup.center B)

noncomputable def δ₁₂_aux (b : G → B) (c : Z1 G C) (hbc : ∀ (x : G), c x = g (b x)) :
    groupCohomology.cocycles₂ A := by
  refine ⟨fun st ↦ (Equiv.ofInjective f hf).symm
    ⟨(b st.1) + st.1 • (b st.2) - b (st.1 * st.2), (hfg _).mp (by simp [← hbc, c.prop])⟩, ?_⟩
  refine funext fun ⟨x, y, z⟩ ↦ hf ?_
  dsimp only [d₂₃, ModuleCat.hom_ofHom, AddHom.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Rep.smul_eq_ρ_apply, sub_add_eq_add_sub]
  change _ = f 0
  have : (x • b y + x • y • b z + -(x • b (y * z))) ∈ AddSubgroup.center B :=
    (hA ((hfg _).mp (by simp [← hbc, c.prop, ← add_assoc]) : _ ∈ f.range))
  have := AddSubgroup.mem_center_iff.mp this (b x)
  simp [sub_eq_add_neg, mul_smul, ← add_assoc, this.symm, mul_assoc]

theorem δ₁₂_aux_well_defined_1 (b b' : G → B) (c : Z1 G C) (hbc : ∀ (x : G), c x = g (b x))
    (hbc' : ∀ (x : G), c x = g (b' x)) :
    ((δ₁₂_aux hf hfg hA b c hbc) - (δ₁₂_aux hf hfg hA b' c hbc') : (ModuleCat.of k (G × G → A))) ∈
    (LinearMap.range (ModuleCat.Hom.hom (d₁₂ A)) : Set (ModuleCat.of k (G × G → A))) := by
  obtain a := fun h ↦ (hfg _).mp (show g (b h - b' h) = 0 by simp [← hbc h, ← hbc' h])
  choose a ha using a
  refine ⟨a, funext fun ⟨h, h'⟩ ↦ hf (sub_eq_zero.mp ?_)⟩
  simp only [d₁₂_hom_apply, sub_eq_add_neg, map_add, δ₁₂_aux, cocycles₂.coe_mk, Pi.sub_apply,
    Equiv.apply_ofInjective_symm, neg_add_rev, ← map_neg, neg_neg, ← add_assoc]
  have h1 : f (h • a h') + f (-a (h * h')) + f (a h) + b' h + h • b' h' + -b' (h * h') =
    f (h • a h') + f (a h) + b' h + h • b' h' + -b' (h * h') + f (-a (h * h')) := by
    conv_lhs =>
      simp only [add_assoc]
      rw [← AddSubgroup.mem_center_iff.mp (hA (⟨-a (h * h'), rfl⟩ : f _ ∈ f.range))]
    simp only [add_assoc]
  have h2 : f (h • a h') + f (a h) + b' h = f (a h) + b' h + f (h • a h') := by
    conv_rhs => rw [AddSubgroup.mem_center_iff.mp (hA (⟨h • a h', rfl⟩ : f _ ∈ f.range))]
    rw [add_assoc]
  rw [← Rep.smul_eq_ρ_apply, h1, h2]
  simp [ha, sub_eq_add_neg, neg_add_rev, add_assoc]

include hg in
theorem δ₁₂_aux_well_defined_2 (b b' : G → B) (c c' : Z1 G C) (hbc : ∀ (x : G), c x = g (b x))
    (hbc' : ∀ (x : G), c' x = g (b' x)) (hcc' : Z1.cohomologous c c') :
    ((δ₁₂_aux hf hfg hA b c hbc) - (δ₁₂_aux hf hfg hA b' c' hbc') : (ModuleCat.of k (G × G → A))) ∈
    (LinearMap.range (ModuleCat.Hom.hom (d₁₂ A)) : Set (ModuleCat.of k (G × G → A))) := by
  obtain ⟨t, ht⟩ := hcc'
  obtain ⟨t', rfl⟩ := hg t
  let b'' : G → B := fun h ↦ (-t' + b h + h • t')
  have hbc'' : ∀ (x : G), c' x = g (b'' x) := by simpa [b'', ← hbc]
  rw [← sub_add_sub_cancel _ (δ₁₂_aux hf hfg hA b'' c' hbc'').1 _]
  refine Submodule.add_mem _ ⟨fun _ ↦ 0, funext fun ⟨h, h'⟩ ↦ hf ?_⟩ (δ₁₂_aux_well_defined_1 ..)
  have : b h + h • b h' + -b (h * h') + -t' = -t' + (b h + h • b h' + -b (h * h')) :=
    (AddSubgroup.mem_center_iff.mp (hA ((hfg _).mp (by simp [← hbc, c.prop, add_assoc]))) _).symm
  simp [δ₁₂_aux, b'', sub_eq_add_neg, neg_add_rev, ← add_assoc, mul_smul, this]

noncomputable def δ₁₂ : H1 G C → groupCohomology.H2 A := by
  refine (H2Iso A).symm.hom ∘ Quotient.lift (Submodule.Quotient.mk ∘
    (fun c ↦ ((δ₁₂_aux hf hfg hA (fun x ↦ (hg (c x)).choose) c
      (fun x ↦ (hg (c x)).choose_spec.symm)))))
        (fun c c' (hcc' : Z1.cohomologous c c') ↦ ?_)
  obtain ⟨a, ha⟩ := δ₁₂_aux_well_defined_2 hf hg hfg hA (fun x ↦ (hg (c x)).choose)
    (fun x ↦ (hg (c' x)).choose) c c' (fun x ↦ (hg (c x)).choose_spec.symm)
      (fun x ↦ (hg (c' x)).choose_spec.symm) hcc'
  exact (Submodule.Quotient.eq _).mpr (Exists.intro a (Subtype.ext ha))

theorem exact_H1_map_δ₁₂ : Function.Exact (H1.map g) (δ₁₂ hf hg hfg hA) := sorry

end connectHom₁₂

section compatibility

variable {G : Type u} [Group G] {k : Type u} [CommRing k] (A : Rep k G)

open CategoryTheory

/-- `H0 G A` and `A.ρ.invariants` are defEq. -/
noncomputable def H0Iso : groupCohomology.H0 A ≃+ H0 G A :=
  (groupCohomology.H0Iso A).toLinearEquiv.toAddEquiv

theorem H0Iso_map {A B : Rep k G} (f : A ⟶ B) :
    (H0Iso B).toAddMonoidHom.comp (groupCohomology.map (.id G) f 0).hom =
      (H0.map f).comp (H0Iso A).toAddMonoidHom := by
  ext x
  conv_lhs =>
    change (ConcreteCategory.hom (map (MonoidHom.id G) f 0 ≫ (groupCohomology.H0Iso B).hom)) x
  rw [congr($(groupCohomology.map_id_comp_H0Iso_hom f) x)]
  rfl

@[simps?!]
def Z1EquivCocycle₁ : Z1 G A ≃ (groupCohomology.cocycles₁ A) where
  toFun := fun f ↦ ⟨f.val, by
    refine funext fun ⟨g, h⟩ ↦ Eq.trans ?_ (sub_eq_zero.mpr (f.2 g h).symm)
    simp [← Rep.smul_eq_ρ_apply]
    abel⟩
  invFun := fun f ↦ ⟨f.val, fun g h ↦ by
    refine sub_eq_zero.mp (Eq.trans ?_ (congrFun (LinearMap.mem_ker.mp f.2) ⟨g, h⟩)) |> .symm
    simp [← Rep.smul_eq_ρ_apply]
    abel⟩
  left_inv f := Subtype.ext rfl
  right_inv f := Subtype.ext rfl

noncomputable def H1Iso_aux (A : Rep k G) :
    H1 G A ≃ (shortComplexH1 A).moduleCatLeftHomologyData.H :=
  Quotient.congr (Z1EquivCocycle₁ A) (fun a b ↦ by
    simp only [Z1.setoid_r, Submodule.quotientRel_def, LinearMap.mem_range, Subtype.ext_iff,
      LinearMap.codRestrict_apply, AddSubgroupClass.coe_sub]
    refine ⟨fun ⟨g, hg⟩ ↦ ⟨-g, ?_⟩, fun ⟨g, hg⟩ ↦ ⟨-g, ?_⟩⟩
    · sorry
    · sorry
    )

open ConcreteCategory MorphismProperty in
-- cocycle first, CategoryTheory.ConcreteCategory.surjective_eq_epimorphisms
noncomputable nonrec def H1Iso (A : Rep k G) : groupCohomology.H1 A ≃ H1 G A :=
  ((H1Iso A).toLinearEquiv.toEquiv).trans (H1Iso_aux A).symm

theorem H1Iso_zero : H1Iso A 0 = 0 := by
  sorry

theorem H1Iso_map {A B : Rep k G} (f : A ⟶ B) :
    H1Iso B ∘ (groupCohomology.map (.id G) f 1) = (H1.map f) ∘ H1Iso A := sorry

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

lemma _root_.CategoryTheory.ShortComplex.ShortExact.f_injective (hX : X.ShortExact) :
    Function.Injective (X.f : X.X₁ →+[G] X.X₂) := sorry

lemma _root_.CategoryTheory.ShortComplex.ShortExact.g_surjective (hX : X.ShortExact) :
    Function.Surjective (X.g : X.X₂ →+[G] X.X₃) := sorry

lemma _root_.CategoryTheory.ShortComplex.ShortExact.f_g_exact (hX : X.ShortExact) :
    Function.Exact (X.f : X.X₁ →+[G] X.X₂) (X.g : X.X₂ →+[G] X.X₃) := sorry

theorem δ₀₁_H0Iso_eq_H1Iso_δ :
    (δ₀₁ hX.f_injective hX.g_surjective hX.f_g_exact) ∘ (H0Iso X.X₃) =
    (H1Iso X.X₁) ∘ (groupCohomology.δ hX 0 1 rfl) := sorry

theorem δ₁₂_H1Iso_eq_δ :
    (δ₁₂ hX.f_injective hX.g_surjective hX.f_g_exact (by simp [AddCommGroup.center_eq_top])) ∘
      (H1Iso X.X₃) = (groupCohomology.δ hX 1 2 rfl) := sorry

end compatibility

end NonAbelian

end groupCohomology
