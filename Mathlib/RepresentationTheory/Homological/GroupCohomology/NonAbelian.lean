/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Jingting Wang
-/
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Category.Pointed.Exact
import Mathlib.CategoryTheory.Category.Pointed.Forgetful
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

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

section basic

abbrev NonAbelianRep (G : Type u) [Monoid G] := Action AddGrp.{u} G

variable (G : Type u) [Monoid G]

instance : CoeSort (NonAbelianRep G) (Type u) := ⟨fun V ↦ V.V⟩

instance (A : NonAbelianRep G) : DistribMulAction G A  where
  smul_zero _ :=  map_zero _
  smul_add _ := map_add _

instance (A B : NonAbelianRep G) : Coe (A ⟶ B) (A →+[G] B) where
  coe f := {
    __ := f.hom.hom'
    map_smul' m x := congr($(f.comm m) x)
  }

end basic

section H0

variable (G : Type u) [Monoid G]

def H0 (A : Type*) [AddGroup A] [DistribMulAction G A] : AddSubgroup A where
  carrier := setOf fun v => ∀ g : G, g • v = v
  add_mem' := by simp +contextual
  zero_mem' := by simp
  neg_mem' := by simp +contextual

variable {G}

def H0.map {A B : Type*} [AddGroup A] [AddGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+[G] B) : H0 G A →+ H0 G B where
  toFun v := ⟨f v.val, fun g ↦ by rw [← map_smul, v.prop]⟩
  map_add' v w := Subtype.ext (by simp)
  map_zero' := by simp

variable (G) in
theorem H0.map_id (A : Type*) [AddGroup A] [DistribMulAction G A] :
    H0.map (.id _) = .id (H0 G A) := AddMonoidHom.ext fun x ↦ by simp [H0.map, H0]

theorem H0.map_comp {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (f : A →+[G] B) (g : B →+[G] C) : H0.map (g.comp f) = (H0.map g).comp (H0.map f) := rfl

theorem H0.map_injective_of_injective {A B : Type*} [AddGroup A] [AddGroup B] [DistribMulAction G A]
    [DistribMulAction G B] (f : A →+[G] B) (hf : Function.Injective f) :
    Function.Injective (H0.map f) := fun _ _ h ↦ Subtype.ext (hf (congr_arg Subtype.val h))

end H0

section H1

variable (G : Type u) [Monoid G] (A : Type*) [AddGroup A] [DistribMulAction G A]

def Z1 := { f : G → A // ∀ g h : G, f (g * h) = f g + g • f h}

namespace Z1

instance zero : Zero (Z1 G A) := ⟨⟨0, fun g h => by simp⟩⟩
instance inhabited : Inhabited (Z1 G A) := ⟨0⟩

instance coeFun : CoeFun (Z1 G A) (fun _ ↦ G → A) := ⟨fun f ↦ f.val⟩

@[simp]
lemma zero_apply (g : G) : (0 : Z1 G A) g = 0 := rfl

variable {G} {A} in
def cohomologous (f g : Z1 G A) : Prop :=
  ∃ a : A, ∀ h : G, g h = - a + f h + (h • a)

instance setoid : Setoid (Z1 G A) where
  r := cohomologous
  iseqv := {
    refl := fun f ↦ ⟨0, fun h ↦ by simp⟩,
    symm := fun ⟨a, ha⟩ ↦ ⟨-a, fun h ↦ by simp [← add_assoc, ha h]⟩,
    trans := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, fun h ↦ by simp [← add_assoc, ha h, hb h]⟩
  }

end Z1

def H1 := Quotient (Z1.setoid G A)

instance : Zero (H1 G A) := ⟨⟦0⟧⟩
instance : Inhabited (H1 G A) := ⟨0⟩

lemma zero_def : (0 : H1 G A) = ⟦0⟧ := rfl

variable {G}

def H1.map {A B : Type*} [AddGroup A] [AddGroup B] [DistribMulAction G A]
    [DistribMulAction G B] (f : A →+[G] B) : H1 G A → H1 G B :=
  Quotient.map (fun z : Z1 G A => ⟨f ∘ z, fun g h => by simp [z.prop, map_smul]⟩)
    (fun z1 z2 ⟨a, ha⟩ => ⟨f a, fun h => by simp [ha, map_smul]⟩)

variable (G) in
theorem H1.map_id (A : Type*) [AddGroup A] [DistribMulAction G A] :
    H1.map (.id _) = @id (H1 G A) := funext fun a ↦ by
  induction a using Quotient.ind
  refine Quotient.eq.mpr ⟨0, fun _ ↦ by simp⟩

theorem H1.map_zero {A B : Type*} [AddGroup A] [AddGroup B] [DistribMulAction G A]
    [DistribMulAction G B] (f : A →+[G] B) : H1.map f 0 = 0 := by
  simp only [H1.map, zero_def, Quotient.map_mk]
  exact congrArg _ <| Subtype.ext (funext fun x ↦ f.map_zero)

theorem H1.map_comp {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    (f : A →+[G] B) (g : B →+[G] C) : H1.map (g.comp f) = (H1.map g).comp (H1.map f) := funext
  fun a ↦ by induction a using Quotient.ind with | _ => rfl

end H1

section connectHom₀₁

variable {G : Type u} [Group G] {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    {f : A →+[G] B} {g : B →+[G] C} (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g)

attribute [local simp] Equiv.apply_ofInjective_symm

@[simps]
noncomputable def δ₀₁_aux (b : B) (c : H0 G C) (hb : g b = c) : Z1 G A := ⟨fun s ↦
  (Equiv.ofInjective f hf).symm ⟨-b + s • b, ((hfg _).mp (by simp [hb, c.prop s]))⟩,
    fun g h ↦ hf (by simp [mul_smul, ← add_assoc])⟩

theorem δ₀₁_aux_well_defined_1 (b b' : B) (c : H0 G C) (hb : g b = c) (hb' : g b' = c) :
    Z1.cohomologous (δ₀₁_aux hf hfg b c hb) (δ₀₁_aux hf hfg b' c hb') :=
  ⟨(Equiv.ofInjective f hf).symm ⟨- b + b', (hfg _).mp (by rw [map_add, map_neg, hb, hb',
    neg_add_cancel])⟩, fun h ↦ hf (by simp [δ₀₁_aux, ← add_assoc])⟩

noncomputable def δ₀₁ : H0 G C → H1 G A := fun x ↦
    ⟦δ₀₁_aux hf hfg (Classical.choose (hg x)) x (Classical.choose_spec (hg x))⟧

theorem δ₀₁_eq_of_map (b : B) (c : H0 G C) (hb : g b = c) :
    δ₀₁ hf hg hfg c = ⟦δ₀₁_aux hf hfg b c hb⟧ :=
  Quotient.eq_iff_equiv.mpr (δ₀₁_aux_well_defined_1 ..)

theorem δ₀₁_zero : δ₀₁ hf hg hfg 0 = 0 :=
  (δ₀₁_eq_of_map hf hg hfg 0 0 (map_zero _)).trans (congrArg _ <| Subtype.ext <|
    funext fun x ↦ hf <| by simp [δ₀₁_aux])

include hf hfg in
theorem exact₁ : Function.Exact (H0.map f) (H0.map g) :=
  fun y ↦ ⟨fun h ↦ ⟨⟨(Equiv.ofInjective f hf).symm ⟨y, (hfg _).mp congr(Subtype.val $h)⟩,
    fun g ↦ hf (by simpa [map_smul] using y.2 g)⟩, Subtype.ext (Equiv.apply_ofInjective_symm _ _)⟩,
      fun ⟨x, hx⟩ ↦ Subtype.ext ((hfg _).mpr ⟨x.1, congr(Subtype.val $hx)⟩)⟩

theorem exact₂ : Function.Exact (H0.map g) (δ₀₁ hf hg hfg) := by
  refine fun y ↦ ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ (δ₀₁_eq_of_map (hb := congr(Subtype.val $hx)) ..).trans
    <| congrArg _ <| Subtype.ext <| funext <| fun s ↦ hf (by simp [δ₀₁_aux, x.2 s])⟩
  obtain ⟨b, hb⟩ := hg y
  obtain ⟨x, hx⟩ := Quotient.eq_iff_equiv.mp ((δ₀₁_eq_of_map (hb := hb) ..).symm.trans h)
  refine ⟨⟨b + f x, fun h ↦ (neg_add_eq_zero.mp ?_).symm⟩,
    Subtype.ext (by simpa [H0.map, hfg.apply_apply_eq_zero])⟩
  simpa [δ₀₁_aux, ← add_assoc] using congr(f $(hx h)).symm

theorem exact₃ : Function.Exact (δ₀₁ hf hg hfg) (H1.map f) := by
  refine fun y ↦ ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ Quotient.eq_iff_equiv.mpr
    ⟨- (Classical.choose (hg x)), fun h ↦ by simp⟩⟩
  induction y using Quotient.ind
  simp only [H1.map, Quotient.map_mk, zero_def] at h
  obtain ⟨x, hx⟩ := Quotient.eq_iff_equiv.mp h
  -- let z : f.range := sorry
  -- refine ⟨⟨g x, ?_⟩, Quotient.eq_iff_equiv.mpr ⟨(Equiv.ofInjective f hf).symm z , fun h ↦ hf ?_⟩⟩
  -- · sorry
  -- · simp [δ₀₁_aux]
  sorry

include hfg in
theorem exact₄ : Function.Exact (H1.map f) (H1.map g) := by
  refine fun y ↦ ⟨?_, fun ⟨x, hx⟩ ↦ hx ▸ ?_⟩
  · induction y using Quotient.ind
    sorry
  · induction x using Quotient.ind
    simp [H1.map, zero_def, ← Function.comp_assoc, hfg.comp_eq_zero]
    congr

end connectHom₀₁


section compatibility

variable {G : Type u} [Group G] {k : Type u} [CommRing k] (A : Rep k G)

-- Why can't this be found automatically?
instance : MulAction G A := Action.instMulAction A

-- should be moved
instance : DistribMulAction G A where
  smul_zero _ := map_zero _
  smul_add _ := map_add _

open CategoryTheory

noncomputable def H0Iso : groupCohomology.H0 A ≃+ H0 G A where
  toFun := (groupCohomology.H0Iso A).hom
  invFun := (groupCohomology.H0Iso A).inv
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

-- should be moved
def H0Iso_zero : H0Iso A 0 = 0 := sorry

variable {B : Rep k G} (f : A ⟶ B)
variable {A}

def Action.Hom.toDistribMulActionHom (f : A ⟶ B) : A →+[G] B where
  toFun := f
  map_smul' g x := congr($(f.comm g) x)
  map_zero' := map_zero f.hom.hom
  map_add' := map_add f.hom.hom

instance : Coe (A ⟶ B) (A →+[G] B) := ⟨Action.Hom.toDistribMulActionHom⟩

-- naturality of H0Iso
theorem H0Iso_map {A B : Rep k G} (f : A ⟶ B) :
    H0Iso B ∘ (groupCohomology.map (.id G) f 0) = (H0.map f) ∘ H0Iso A := sorry

def CocycleToZ1 (f : groupCohomology.cocycles₁ A) : Z1 G A := ⟨f.val, fun x y => Eq.symm (by
  rw [← sub_eq_zero, add_sub_right_comm, sub_add_comm]
  exact ((mem_cocycles₁_def f).mp f.2 x y))⟩

open ConcreteCategory MorphismProperty in
-- cocycle first, CategoryTheory.ConcreteCategory.surjective_eq_epimorphisms
noncomputable def H1Iso (A : Rep k G) : groupCohomology.H1 A ≃ H1 G A where
  toFun := Quotient.mk _ ∘ CocycleToZ1 ∘ Function.surjInv (f := (groupCohomology.H1π A).hom) (by
    rw [← MorphismProperty.surjective, ConcreteCategory.surjective_eq_epimorphisms,
        MorphismProperty.epimorphisms]
    infer_instance)
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

theorem H1Iso_zero : H1Iso A 0 = 0 := sorry

-- naturality of H1Iso
theorem H1Iso_map {A B : Rep k G} (f : A ⟶ B) :
    H1Iso B ∘ (groupCohomology.map (.id G) f 1) = (H1.map f) ∘ H1Iso A := sorry

end compatibility

section connectHom₁₂

variable {G : Type u} [Group G] {k : Type u} [CommRing k] {A : Rep k G}
  {B C : Type*} [AddGroup B] [AddGroup C] [DistribMulAction G B] [DistribMulAction G C]
  {f : A →+[G] B} {g : B →+[G] C} (hf : Function.Injective f) (hg : Function.Surjective g)
  (hfg : Function.Exact f g) (hA : f.toAddMonoidHom.range ≤ AddSubgroup.center B)

attribute [local simp] Equiv.apply_ofInjective_symm

noncomputable def δ₁₂_aux (b : G → B) (c : Z1 G C) (hbc : ∀ (x : G), c x = g (b x)) :
    LinearMap.ker (ModuleCat.Hom.hom (d₂₃ A)) := by
  refine ⟨fun st ↦ (Equiv.ofInjective f hf).symm
    ⟨(b st.1) + st.1 • (b st.2) - b (st.1 * st.2), (hfg _).mp (by simp [← hbc, c.prop])⟩, ?_⟩
  refine funext fun ⟨x, y, z⟩ ↦ hf ?_
  dsimp only [d₂₃, ModuleCat.hom_ofHom, AddHom.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
  conv in ((A.ρ _) _) => change x • _
  rw [sub_add_eq_add_sub]
  change _ = f 0
  have : x • b y + x • y • b z + -(x • b (y * z)) + (b x) =
    (b x) + (x • b y + x • y • b z + -(x • b (y * z))) := by
      refine (AddSubgroup.mem_center_iff.mp (hA ((hfg _).mp ?_ : _ ∈ f.range)) (b x)).symm
      simp [← hbc, c.prop, ← add_assoc]
  simp [sub_eq_add_neg, mul_smul, ← add_assoc, this, mul_assoc]

theorem δ₁₂_aux_well_defined_1 (b b' : G → B) (c : Z1 G C) (hbc : ∀ (x : G), c x = g (b x))
    (hbc' : ∀ (x : G), c x = g (b' x)) :
    ((δ₁₂_aux hf hfg hA b c hbc) - (δ₁₂_aux hf hfg hA b' c hbc') : (ModuleCat.of k (G × G → A))) ∈
    (LinearMap.range (ModuleCat.Hom.hom (d₁₂ A)) : Set (ModuleCat.of k (G × G → A))) := by
  obtain a : ∀ (h : G), ∃ (a : A), f a = b h - b' h := fun h ↦ (hfg _).mp
    (by simp [← hbc h, ← hbc' h])
  choose a ha using a
  refine ⟨a, funext fun ⟨h, h'⟩ ↦ hf (sub_eq_zero.mp ?_)⟩
  simp only [d₁₂_hom_apply, sub_eq_add_neg, map_add, δ₁₂_aux, cocycles₂.val_eq_coe,
    cocycles₂.coe_mk, Pi.sub_apply, Equiv.apply_ofInjective_symm, neg_add_rev, ← map_neg, neg_neg,
    ← add_assoc]
  conv in ((A.ρ _) _) => change h • _
  have h1 : f (h • a h') + f (-a (h * h')) + f (a h) + b' h + h • b' h' + -b' (h * h') =
    f (h • a h') + f (a h) + b' h + h • b' h' + -b' (h * h') + f (-a (h * h')) := by
    conv_lhs =>
      simp only [add_assoc]
      rw [← AddSubgroup.mem_center_iff.mp (hA (⟨-a (h * h'), rfl⟩ : f _ ∈ f.range))]
    simp only [add_assoc]
  have h2 : f (h • a h') + f (a h) + b' h = f (a h) + b' h + f (h • a h') := by
    conv_rhs => rw [AddSubgroup.mem_center_iff.mp (hA (⟨h • a h', rfl⟩ : f _ ∈ f.range))]
    rw [add_assoc]
  rw [h1, h2]
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

noncomputable def δ₁₂ : H1 G C → groupCohomology A 2 := by
  refine (H2Iso A).symm.hom ∘ Quotient.lift (Submodule.Quotient.mk ∘
    (fun c ↦ ((δ₁₂_aux hf hfg hA (fun x ↦ Classical.choose (hg (c x))) c
      (fun x ↦ (Classical.choose_spec (hg (c x))).symm)))))
        (fun c c' (hcc' : Z1.cohomologous c c') ↦ ?_)
  obtain ⟨a, ha⟩ := δ₁₂_aux_well_defined_2 hf hg hfg hA (fun x ↦ Classical.choose (hg (c x)))
    (fun x ↦ Classical.choose (hg (c' x))) c c' (fun x ↦ (Classical.choose_spec (hg (c x))).symm)
      (fun x ↦ (Classical.choose_spec (hg (c' x))).symm) hcc'
  exact (Submodule.Quotient.eq _).mpr (Exists.intro a (Subtype.ext ha))

theorem exact₅ : Function.Exact (H1.map g) (δ₁₂ hf hg hfg hA) := sorry

end connectHom₁₂

end NonAbelian

end groupCohomology
