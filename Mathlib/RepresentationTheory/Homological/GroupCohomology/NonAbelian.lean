/-
Copyright (c) 2025 Jiedong Jiang, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Jingting Wang
-/
module

public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Non-abelian group cohomology

Let `G` be a group acting on another (not necessarily abelian) group `A`, in this file we define
`H⁰(G, A)$` and `H¹(G, A)`, and prove some basic properties about it.

## Main definitions

- `groupCohomology.NonAbelian.H0 G A`: The subgroup of `A` consisting of elements invariant under
  `G`-action.
- `groupCohomology.NonAbelian.Z1 G A`: The set of functions `f : G → A` such that
  `∀ g h : G, f (g * h) = f g + g • f h`.
- `groupCohomology.NonAbelian.Z1.cohomologous`: An equivalence relationship on `G → A` such that
  `f g : G → A` are cohomologous if and only if `∃ a : A, ∀ h : G, f h = - a + g h + (h • a)`.
- `groupCohomology.NonAbelian.H1 G A`: The quotient of `Z1 G A` by the relation `Z1.cohomologous`.
- `groupCohomology.NonAbelian.δ₀ hf hfg`: For a short exact sequence `0 → A →f B →g C → 0`
  preserving `G`-action, we define `δ₀` as the connection morphism from `H0 G C` to `H1 G A`.
- `groupCohomology.NonAbelian.δ₁ hf hg hfg hA`: For a short exact sequence `0 → A →f B →g C → 0`
  preserving `G`-action, if `A` is commutative (here we assume `A` has type `Rep k G`), and the
  image of `A` under `f` is contained in the center of `B`, then we construct `δ₁` as the connection
  morphism from `H1 G C` to `groupCohomology.H 2 A`.

## Main results

For a short exact sequence `0 → A →f B →g C → 0` preserving `G`-action, we construct the long exact
sequence and prove its exactness:

- `H0.map_injective`: Injectivity of `H0 G A → H0 G B`.
- `H0.map_exact`: Exactness of `H0 G A → H0 G B → H0 G C`.
- `exact_H0_map_δ₀`: Exactness of `H0 G B → H0 G C → H1 G A`.
- `exact_δ₀_H1_map`: Exactness of `H0 G C → H1 G A → H1 G B`.
- `H1.map_exact`: Exactness of `H1 G A → H1 G B → H1 G C`.
- `exact_H1_map_δ₁`: If the image of `A` under `f` is contained in the center of `B`, then
  `H1 G B → H1 G C → groupCohomology.H 2 A` is also exact.

-/

@[expose] public section

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
lemma mem_iff (a : A) : a ∈ H0 G A ↔ ∀ g : G, g • a = a := by rfl

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
    Function.Exact (H0.map f) (H0.map g) := by
  refine fun b ↦ ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := (hfg b).mp congr(Subtype.val $h)
    refine ⟨⟨a, (mem_iff G a).mpr fun g ↦ hf ?_⟩, Subtype.ext ha⟩
    simpa [ha] using b.2 g
  · rintro ⟨x, rfl⟩
    exact Subtype.ext (by simpa using hfg (f x))

end H0

def Z1 (A : Type*) [AddGroup A] [DistribMulAction G A] :=
  { f : G → A | ∀ g h : G, f (g * h) = f g + g • f h}

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
  ∃ a : A, ∀ h : G, f h = - a + g h + (h • a)

lemma cohomologous.refl (f : G → A) : Z1.cohomologous f f := ⟨0, fun h ↦ by simp⟩

lemma cohomologous.symm {f g : G → A} (h : Z1.cohomologous f g) : Z1.cohomologous g f := by
  obtain ⟨a, ha⟩ := h
  exact ⟨-a, fun h ↦ by simp [← add_assoc, ha h]⟩

lemma cohomologous.trans {f g h : G → A} (hfg : Z1.cohomologous f g) (hgh : Z1.cohomologous g h) :
    Z1.cohomologous f h := by
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hgh
  exact ⟨b + a, fun h ↦ by simp [← add_assoc, ha h, hb h]⟩

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
  intro g h
  obtain ⟨a, ha⟩ := hfg
  simp [ha, f'.2 g h, add_assoc, mul_smul]

def map : Z1 G A → Z1 G B := fun z ↦ ⟨f ∘ z, fun g h => by simp [z.prop g h, map_smul]⟩

@[simp] lemma map_zero : Z1.map f 0 = 0 := Subtype.ext <| funext fun _ ↦ (by simp [Z1.map])

@[simp] lemma map_zero_apply (x : Z1 G A) : Z1.map (0 : A →+[G] B) x = 0 := Subtype.ext
  (by simp [Z1.map])

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

variable (G A) in
def mk (a : Z1 G A) : H1 G A := ⟦a⟧

lemma mk_eq_iff (a b : Z1 G A) : mk G A a = mk G A b ↔ Z1.cohomologous a b := Quotient.eq_iff_equiv

variable (G A) in
lemma mk_surjective : Function.Surjective (mk G A) := Quotient.mk_surjective

instance : Zero (H1 G A) := ⟨mk G A 0⟩
instance : Inhabited (H1 G A) := ⟨0⟩

variable (G A) in
lemma zero_def : (0 : H1 G A) = mk G A 0 := rfl

def map : H1 G A → H1 G B := Quotient.map (Z1.map f) (Z1.map_cohomologous f)

variable (G A) in
theorem map_id : H1.map (.id _) = @id (H1 G A) := funext fun a ↦ by
  induction a using Quotient.inductionOn with | h a =>
  refine Quotient.eq.mpr ⟨0, fun _ ↦ by simp⟩

@[simp]
theorem map_mk (x : Z1 G A) : H1.map f (mk G A x) = mk G B (Z1.map f x) := by simp [map, mk]

@[simp]
theorem map_zero : H1.map f 0 = 0 := by
  simp only [zero_def, map_mk]
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
  · obtain ⟨b, rfl⟩ := mk_surjective G B y
    obtain ⟨x, hx⟩ := Quotient.eq_iff_equiv.mp h
    obtain ⟨x, rfl⟩ := hg x
    have hx (h : G) : 0 = g (x + b h - h • x) := by
      simpa using congr((g x) + $(hx h) - (h • g x)).symm
    choose a ha using fun (h : G) ↦ (hfg _).mp (hx h).symm
    refine ⟨mk G A (⟨a, fun g h ↦ hf ?_⟩ : Z1 G A), (mk_eq_iff _ _).mpr ?_⟩
    · simp only [map_add, map_smul]
      exact Z1.mem_of_cohomologous (f ∘ a) b ⟨-x, by simp [ha, sub_eq_add_neg]⟩ g h
    · exact ⟨-x, by simpa [sub_eq_add_neg] using ha⟩
  · rw [← map_comp_apply, ((g.comp f).ext (g := 0) hfg.apply_apply_eq_zero), zero_map_apply]

end H1

section connectHom₀

variable {G : Type u} [Group G] {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    {f : A →+[G] B} {g : B →+[G] C} (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g)

include hf in
lemma mem_z1_of_comp_eq (b : B) (x : G → A) (hx : ∀ g : G, f (x g) = - b + g • b) :
    x ∈ Z1 G A := fun g h ↦ hf <| by simp [hx, add_assoc, mul_smul]

abbrev z1MkOfCompEq (b : B) (x : G → A) (hx : ∀ g : G, f (x g) = - b + g • b) : Z1 G A :=
  ⟨x, mem_z1_of_comp_eq hf b x hx⟩

noncomputable def δ₀_aux : g ⁻¹' (H0 G C) → Z1 G A := fun b ↦ ⟨
    fun s ↦ (Equiv.ofInjective _ hf).symm ⟨-b + s • b, (hfg _).mp <| by simp [b.2 s]⟩,
    mem_z1_of_comp_eq hf b.1 _ (fun g ↦ by simp)
  ⟩

lemma δ₀_aux_zero : δ₀_aux hf hfg ⟨0, by simp⟩ = 0 := by
  refine Subtype.ext (funext fun x ↦ hf ?_)
  simp [δ₀_aux]

@[simp]
lemma apply_δ₀_aux (b : g ⁻¹' (H0 G C)) : ∀ g : G, f ((δ₀_aux hf hfg b) g) = - b + g • b := by
  simp [δ₀_aux]

noncomputable def δ₀ : H0 G C → H1 G A :=
  Function.extend (Set.restrictPreimage (H0 G C) g) ((H1.mk G A) ∘ (δ₀_aux hf hfg)) 0

lemma mk_comp_δ₀_aux_factorsThrough :
    Function.FactorsThrough ((H1.mk G A) ∘ (δ₀_aux hf hfg)) (Set.restrictPreimage (H0 G C) g) := by
  intro ⟨b1, hb1⟩ ⟨b2, hb2⟩ heq
  obtain ⟨x, hx⟩ : ∃ x : A, f x = -b2 + b1 := (hfg _).mp (by simpa [neg_add_eq_zero] using heq.symm)
  exact (H1.mk_eq_iff _ _).mpr ⟨x, fun h ↦ hf (by simp [δ₀_aux, hx, add_assoc])⟩

lemma δ₀_apply_eq_mk_δ₀_aux (c : H0 G C) (b : B) (hb : g b = c) :
    δ₀ hf hfg c = H1.mk G A (δ₀_aux hf hfg ⟨b, (hb ▸ c.2 : g b ∈ (H0 G C))⟩) := by
  convert mk_comp_δ₀_aux_factorsThrough hf hfg |>.extend_apply ..
  exact Subtype.ext (by simpa using hb.symm)

lemma δ₀_apply (c : H0 G C) (b : B) (hb : g b = c) (x : G → A)
    (hx : ∀ g : G, f (x g) = - b + g • b) : δ₀ hf hfg c = H1.mk G A (z1MkOfCompEq hf b x hx) :=
  (δ₀_apply_eq_mk_δ₀_aux hf hfg c b hb).trans <| congrArg _ <| Subtype.ext <|
  funext fun s ↦ hf (by simp [δ₀_aux, hx])

lemma δ₀_apply' (c : H0 G C) (b : B) (hb : g b = c) (x : Z1 G A)
    (hx : ∀ g : G, f (x g) = - b + g • b) : δ₀ hf hfg c = H1.mk G A x := δ₀_apply hf hfg c b hb x hx

include hg in
theorem exact_H0_map_δ₀ : Function.Exact (H0.map g) (δ₀ hf hfg) := by
  refine fun y ↦ ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨b, hb⟩ := Set.restrictPreimage_surjective _ hg y
    obtain ⟨x, hx⟩ : Z1.cohomologous (δ₀_aux hf hfg b) 0 := by
      refine (H1.mk_eq_iff (G := G) (A := A) _ 0).mp ?_
      rw [← δ₀_apply_eq_mk_δ₀_aux _ _ y b.1 (congr(Subtype.val $hb)), h, H1.zero_def]
    replace hx := by simpa [δ₀_aux] using fun h : G ↦ congr(f $(hx h))
    refine ⟨⟨b - f x, fun h ↦ ?_⟩, Subtype.ext <| by simp [← hb, (hfg _)]⟩
    simpa [sub_eq_add_neg, add_assoc] using congr(b + ($(hx h) - h • (f x)))
  · rw [δ₀_apply_eq_mk_δ₀_aux hf hfg y x.1 congr(Subtype.val $hx), H1.zero_def]
    exact congrArg _ <| Subtype.ext <| funext fun s ↦ hf
      (by simpa [δ₀_aux, neg_add_eq_zero] using (x.2 s).symm)

include hg in
theorem exact_δ₀_H1_map : Function.Exact (δ₀ hf hfg) (H1.map f) := by
  refine fun y ↦ ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := H1.mk_surjective _ _ y
    obtain ⟨x, hx⟩ := (H1.mk_eq_iff ..).mp <| h.trans (H1.zero_def ..)
    have : g x ∈ H0 G C := fun s ↦ by
      have := by simpa [hfg.apply_apply_eq_zero] using congr(g $(hx s))
      exact (neg_add_eq_zero.mp this.symm).symm
    rw [← δ₀_apply' hf hfg ⟨g x, this⟩ x (by simp) y (by simpa using hx)]
    exact Set.mem_range_self _
  · obtain ⟨b, hb⟩ := hg x
    simp only [← hx, δ₀_apply_eq_mk_δ₀_aux hf hfg x b hb, H1.map_mk, H1.zero_def, H1.mk_eq_iff,
      Z1.zero_coe]
    exact ⟨b, by simp [δ₀_aux]⟩

end connectHom₀

section connectHom₁

variable {G : Type u} [Group G] {k : Type u} [CommRing k] {A : Rep k G}
  {B C : Type*} [AddGroup B] [AddGroup C] [DistribMulAction G B] [DistribMulAction G C]
  {f : A →+[G] B} {g : B →+[G] C} (hf : Function.Injective f) (hg : Function.Surjective g)
  (hfg : Function.Exact f g) (hA : f.toAddMonoidHom.range ≤ AddSubgroup.center B)

include hf hfg hA in
lemma mem_cocycles₂_of_comp_eq (b : G → B) (hb : g ∘ b ∈ Z1 G C) (x : G × G → A)
    (hx : ∀ g h : G, f (x ⟨g, h⟩) = b g + g • b h - b (g * h)) : x ∈ cocycles₂ A := by
  refine funext fun ⟨x, y, z⟩ ↦ hf ?_
  dsimp only [d₂₃, ModuleCat.hom_ofHom, AddHom.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Rep.smul_eq_ρ_apply, sub_add_eq_add_sub]
  change _ = f 0
  have : g (b (y * z)) = g (b y) + y • g (b z) := hb y z
  have : (x • b y + x • y • b z + -(x • b (y * z))) ∈ AddSubgroup.center B :=
    (hA ((hfg _).mp (by simp [this, add_assoc]) : _ ∈ f.range))
  have := AddSubgroup.mem_center_iff.mp this (b x)
  simp [sub_eq_add_neg, hx, mul_smul, ← add_assoc, this.symm, mul_assoc]

abbrev cocycles₂MkOfCompEq (b : G → B) (hb : g ∘ b ∈ Z1 G C) (x : G × G → A)
    (hx : ∀ g h : G, f (x ⟨g, h⟩) = b g + g • b h - b (g * h)) : cocycles₂ A := ⟨x,
  mem_cocycles₂_of_comp_eq hf hfg hA b hb x hx⟩

noncomputable def δ₁_aux : (g ∘ ·) ⁻¹' (Z1 G C) → cocycles₂ A := fun b ↦ ⟨
  fun st ↦ (Equiv.ofInjective f hf).symm ⟨(b.1 st.1) + st.1 • (b.1 st.2) - b.1 (st.1 * st.2),
    (hfg _).mp (by simpa [← sub_eq_zero] using (b.2 st.1 st.2).symm)⟩,
  mem_cocycles₂_of_comp_eq hf hfg hA b.1 b.2 _ (by simp)
⟩

lemma Z1_mem_preimage_Z1 (b : Z1 G B) : g ∘ b ∈ Z1 G C :=
  fun h h' ↦ by simpa using congr(g $(b.2 h h'))

lemma δ₁_aux_zero : δ₁_aux hf hfg hA ⟨0, by simp [Z1]⟩ = 0 := by
  refine cocycles₂_ext fun g h ↦ hf ?_
  simp only [δ₁_aux, Pi.zero_apply, smul_zero, add_zero, sub_self, cocycles₂.coe_mk,
    Equiv.apply_ofInjective_symm]
  exact f.map_zero.symm

@[simp]
lemma apply_δ₁_aux (b : (g ∘ ·) ⁻¹' (Z1 G C)) :
    ∀ g h : G, f ((δ₁_aux hf hfg hA b) ⟨g, h⟩) = b.1 g + g • b.1 h - b.1 (g * h) := by
  simp [δ₁_aux]

lemma apply_δ₁_aux' (b : (g ∘ ·) ⁻¹' (Z1 G C)) :
    f ∘ (δ₁_aux hf hfg hA b) = fun g ↦ b.1 g.1 + g.1 • b.1 g.2 - b.1 (g.1 * g.2) := by
  ext ⟨g, h⟩
  simp

noncomputable def δ₁ : H1 G C → H2 A :=
  (Function.extend ((H1.mk G C) ∘ (Set.restrictPreimage (Z1 G C) (g ∘ ·)))
    (H2π A ∘ (δ₁_aux hf hfg hA)) 0)

include hg in
lemma mk_comp_δ₁_aux_factorsThrough :
    Function.FactorsThrough (H2π A ∘ (δ₁_aux hf hfg hA))
    ((H1.mk G C) ∘ (Set.restrictPreimage (Z1 G C) (g ∘ ·))):= by
  intro ⟨b1, hb1⟩ ⟨b2, hb2⟩ heq
  obtain ⟨x, heq⟩ := by
    simpa only [Function.comp_apply, Set.restrictPreimage_mk, H1.mk_eq_iff] using heq
  obtain ⟨x, rfl⟩ := hg x
  replace heq : ∀ (h : G), g (b1 h - h • x - b2 h + x) = 0 := fun h ↦ by
    simpa using congr($(heq h) - h • g x - (g (b2 h)) + g x)
  choose a ha using fun h ↦ (hfg _).mp (heq h)
  replace ha (h : G) : b1 h = (f (a h)) - x + (b2 h) + h • x := by
    simpa using congr($(ha h) - x + b2 h + h • x).symm
  simp only [Function.comp_apply, δ₁_aux, H2π_eq_iff (A := A), coboundaries₂, d₁₂,
    ← Rep.smul_eq_ρ_apply, ModuleCat.hom_ofHom, cocycles₂.coe_mk, LinearMap.mem_range,
    LinearMap.coe_mk, AddHom.coe_mk, ← hf.comp_left.eq_iff, map_comp_sub]
  refine ⟨a, funext fun ⟨h1, h2⟩ ↦ ?_⟩
  have : b2 h1 + h1 • b2 h2 - b2 (h1 * h2) ∈ AddSubgroup.center B := by
    refine hA ((hfg _).mp ?_)
    simpa [sub_eq_zero] using (hb2 h1 h2).symm
  have : -x + b2 h1 + h1 • b2 h2 + -b2 (h1 * h2) = b2 h1 + h1 • b2 h2 + -b2 (h1 * h2) + -x := by
    simpa [sub_eq_add_neg, ← add_assoc] using AddSubgroup.mem_center_iff.mp this (-x)
  have f_comm (a : A) (b' : B) : f a + b' = b' + f a :=
    AddSubgroup.mem_center_iff.mp (hA ⟨a, rfl⟩) _ |>.symm
  simp only [sub_eq_add_neg, Function.comp_apply, map_add, ← f_comm (a h1), ← add_assoc, ha,
    smul_add, ← map_smul, smul_neg, mul_smul, neg_add_rev, neg_neg, ← map_neg, add_neg_cancel_right,
    Pi.sub_apply, Equiv.apply_ofInjective_symm]
  simp only [← add_assoc, ← f_comm (h1 • a h2)]
  simp only [← add_assoc, ← f_comm (-a (h1 * h2))]
  simp only [add_assoc, add_right_inj, left_eq_add]
  simp [← add_assoc, this]

include hg in
lemma δ₁_mk_eq_H2π_δ₁_aux (c : Z1 G C) (b : G → B) (hb : g ∘ b = c) :
    δ₁ hf hfg hA (H1.mk G C c) = H2π A (δ₁_aux hf hfg hA ⟨b, ((hb ▸ c.2) : g ∘ b ∈ _)⟩) := by
  convert mk_comp_δ₁_aux_factorsThrough hf hg hfg hA |>.extend_apply ..
  exact congrArg _ <| Subtype.ext hb.symm

include hg in
lemma δ₁_apply (c : Z1 G C) (b : G → B) (hb : g ∘ b = c) (x : G × G → A)
    (hx : ∀ g h : G, f (x ⟨g, h⟩) = b g + g • b h - b (g * h)) :
    δ₁ hf hfg hA (H1.mk G C c) = H2π A (cocycles₂MkOfCompEq hf hfg hA b (hb ▸ c.2) x hx) :=
  (δ₁_mk_eq_H2π_δ₁_aux hf hg hfg hA c b hb).trans <| congrArg _ <| Subtype.ext <|
  funext fun ⟨g, h⟩ ↦ hf (by simp [δ₁_aux, hx])

include hg in
lemma δ₁_apply' (c : Z1 G C) (b : G → B) (hb : g ∘ b = c) (x : cocycles₂ A)
    (hx : ∀ g h : G, f (x ⟨g, h⟩) = b g + g • b h - b (g * h)) :
    δ₁ hf hfg hA (H1.mk G C c) = H2π A x := δ₁_apply hf hg hfg hA c b hb x hx

include hg in
theorem exact_H1_map_δ₁ : Function.Exact (H1.map g) (δ₁ hf hfg hA) := by
  refine fun c ↦ ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨c, rfl⟩ := H1.mk_surjective G C c
    obtain ⟨b, hb⟩ := hg.comp_left c
    rw [δ₁_mk_eq_H2π_δ₁_aux hf hg hfg hA c b hb] at h
    obtain ⟨a, ha⟩ := (H2π_eq_zero_iff _).mp h
    replace ha := fun (g : G × G) ↦ congr((f ∘ $ha) g)
    simp only [Function.comp_apply, d₁₂_hom_apply, ← Rep.smul_eq_ρ_apply, map_add, map_sub,
      map_smul, Prod.forall, apply_δ₁_aux] at ha
    refine ⟨H1.mk G B ⟨fun g ↦ b g - f (a g), fun g h ↦ sub_eq_zero.mp ?_⟩, ?_⟩
    · convert (sub_eq_zero.mpr (ha g h)) using 1
      have f_comm (a : A) (b' : B) : f a + b' = b' + f a :=
        AddSubgroup.mem_center_iff.mp (hA ⟨a, rfl⟩) _ |>.symm
      simp only [sub_eq_add_neg, smul_add, neg_add_rev, neg_neg, ← add_assoc, ← smul_neg, ← map_neg,
      ← map_smul, ← map_add f, add_left_inj]
      simp only [f_comm _ (b (g * h)), add_assoc, add_right_inj, ← map_add f]
      simp only [f_comm _ (g • -b h), ← add_assoc _ (g • -b h) _, add_assoc, add_right_inj,
        ← map_add f]
      exact congrArg _ (by abel)
    · simp only [H1.map_mk]
      refine congrArg _ <| Subtype.ext <| funext fun h ↦ ?_
      simpa [hfg.apply_apply_eq_zero] using congr($hb h)
  · rintro ⟨b, rfl⟩
    obtain ⟨b, rfl⟩ := H1.mk_surjective G B b
    rw [H1.map_mk, δ₁_mk_eq_H2π_δ₁_aux hf hg hfg hA (Z1.map g b) b (funext fun x ↦ rfl)]
    have : δ₁_aux hf hfg hA ⟨b, Z1_mem_preimage_Z1 b⟩ = 0 := by
      refine Subtype.ext <| funext fun h ↦ hf ?_
      simp only [cocycles₂.val_eq_coe, apply_δ₁_aux hf hfg hA ⟨b, Z1_mem_preimage_Z1 b⟩ h.1 h.2,
        b.2 h.1 h.2, sub_self]
      exact f.map_zero.symm
    simp [this]

end connectHom₁

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

/-- Bijection between `Z1 G A` and `cocycles₁ A`. -/
@[simps!] def Z1EquivCocycles₁ : Z1 G A ≃ cocycles₁ A where
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

noncomputable def H1Iso_aux :
    H1 G A ≃ (shortComplexH1 A).moduleCatLeftHomologyData.H :=
  Quotient.congr (Z1EquivCocycles₁ A) (fun a b ↦ by
    simp only [Z1.setoid_r, shortComplexH1, LinearMap.codRestrict, QuotientAddGroup.leftRel_apply,
      Submodule.mem_toAddSubgroup, LinearMap.mem_range, LinearMap.coe_mk, AddHom.coe_mk,
      Subtype.ext_iff, cocycles₁.val_eq_coe, funext_iff, d₀₁_hom_apply]
    refine ⟨fun ⟨g, hg⟩ ↦ ⟨-g, fun h ↦ ?_⟩, fun ⟨g, hg⟩ ↦ ⟨-g, fun h ↦ ?_⟩⟩
    · change h • (-g) - -g = -a h + b h
      exact sub_eq_zero.mp (Eq.trans (by simp; abel) (sub_eq_zero.mpr (hg h)))
    · have : h • g - g = -a h + b h := hg h
      refine sub_eq_zero.mp (Eq.trans (by simp; abel) (sub_eq_zero.mpr this))
    )

noncomputable nonrec def H1Iso : groupCohomology.H1 A ≃ H1 G A :=
  ((H1Iso A).toLinearEquiv.toEquiv).trans (H1Iso_aux A).symm

lemma H1Iso_mk_eq_H1π_Z1EquivCocycles₁ :
    (H1Iso A).symm ∘ (H1.mk G A) = (H1π A) ∘ (Z1EquivCocycles₁ A) := rfl

lemma H1Iso_H1π_eq_mk_Z1EquivCocycles₁_symm :
    (H1Iso A) ∘ (H1π A) = (H1.mk G A) ∘ (Z1EquivCocycles₁ A).symm := by
  simpa [← Function.comp_assoc] using
    congr((H1Iso A) ∘ $(H1Iso_mk_eq_H1π_Z1EquivCocycles₁ A) ∘ (Z1EquivCocycles₁ A).symm).symm

lemma H1Iso_H1π_eq_mk_Z1EquivCocycles₁_symm_apply (x : cocycles₁ A) :
    (H1Iso A) ((H1π A) x) = (H1.mk G A) ((Z1EquivCocycles₁ A).symm x) :=
  congr($(H1Iso_H1π_eq_mk_Z1EquivCocycles₁_symm A) x)

theorem H1Iso_zero : H1Iso A 0 = 0 := by
  simp [H1Iso]
  rfl

theorem H1Iso_map {A B : Rep k G} (f : A ⟶ B) :
    H1Iso B ∘ (groupCohomology.map (.id G) f 1) = (H1.map f) ∘ H1Iso A := by
  refine funext fun x ↦ H1_induction_on x fun x ↦ ?_
  simp [H1Iso_H1π_eq_mk_Z1EquivCocycles₁_symm_apply B,
    H1Iso_H1π_eq_mk_Z1EquivCocycles₁_symm_apply A]
  rfl

lemma Rep.exact_iff_exact (X : ShortComplex (Rep k G)) :
    X.Exact ↔ Function.Exact (X.f : X.X₁ →+[G] X.X₂) (X.g : X.X₂ →+[G] X.X₃) := by
  convert (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (X.map (forget₂ (Rep k G) (ModuleCat k))))
  exact (ShortComplex.exact_map_iff_of_faithful X (forget₂ (Rep k G) (ModuleCat k))).symm

variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)

theorem δ₀_H0Iso_eq_H1Iso_δ :
    (δ₀ ((Rep.mono_iff_injective _).mp hX.mono_f) ((Rep.exact_iff_exact _).mp hX.exact)) ∘
    (H0Iso X.X₃) = (H1Iso X.X₁) ∘ (groupCohomology.δ hX 0 1 rfl) := by
  have hf := (Rep.mono_iff_injective _).mp hX.mono_f
  have hg := (Rep.epi_iff_surjective _).mp hX.epi_g
  have hfg := (Rep.exact_iff_exact _).mp hX.exact
  refine funext fun x ↦ H0_induction_on _ x fun c ↦ ?_
  simp only [H0Iso, Function.comp_apply]
  conv =>
    enter [1, 3]
    change (groupCohomology.H0Iso X.X₃).hom _
    simp only [Iso.inv_hom_id_apply]
  obtain ⟨b, hb⟩ := hg c
  have hb' : b ∈ X.g.hom ⁻¹' (H0 G X.X₃) := by simp [hb]
  rw [groupCohomology.δ₀_apply hX c b hb (δ₀_aux hf hfg ⟨b, hb'⟩) ?_]
  · rw [H1Iso_H1π_eq_mk_Z1EquivCocycles₁_symm_apply]
    exact δ₀_apply' hf hfg c b hb _ fun g ↦ by simp
  · ext g
    simp [← Rep.toDistribMulActionHom_eq_hom, apply_δ₀_aux hf hfg ⟨b, hb'⟩, ← Rep.smul_eq_ρ_apply,
      add_comm, sub_eq_add_neg]

theorem δ₁_H1Iso_eq_δ :
    (δ₁ ((Rep.mono_iff_injective _).mp hX.mono_f) ((Rep.exact_iff_exact _).mp hX.1)
    (by simp [AddCommGroup.center_eq_top])) ∘ (H1Iso X.X₃) = groupCohomology.δ hX 1 2 rfl := by
  have hf := (Rep.mono_iff_injective _).mp hX.mono_f
  have hg := (Rep.epi_iff_surjective _).mp hX.epi_g
  have hfg := (Rep.exact_iff_exact _).mp hX.exact
  have hA : (X.f : X.X₁ →+[G] X.X₂).toAddMonoidHom.range ≤ AddSubgroup.center X.X₂ := by
    simp [AddCommGroup.center_eq_top]
  refine funext fun x ↦ H1_induction_on x fun c ↦ ?_
  simp only [Function.comp_apply, H1Iso_H1π_eq_mk_Z1EquivCocycles₁_symm_apply X.X₃]
  obtain ⟨b, hb⟩ := hg.comp_left c
  have hb' : b ∈ (X.g ∘ ·) ⁻¹' (Z1 G X.X₃) := by
    simp only [Set.mem_preimage, show X.g ∘ b = c from hb]
    have := (mem_cocycles₁_iff c).mp c.2
    exact fun g h ↦ by simpa [add_comm] using this g h
  rw [groupCohomology.δ₁_apply hX c b hb (δ₁_aux hf hfg hA ⟨b, hb'⟩)]
  · refine δ₁_apply hf hg hfg hA ((Z1EquivCocycles₁ X.X₃).symm c) b ?_ _ fun g h ↦ by simp
    simpa [← Rep.toDistribMulActionHom_eq_hom]
  · ext ⟨g, h⟩
    simp [← Rep.toDistribMulActionHom_eq_hom, apply_δ₁_aux, ← Rep.smul_eq_ρ_apply,
      add_comm, add_sub_assoc]

end compatibility

end NonAbelian

end groupCohomology
