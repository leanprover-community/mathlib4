import Mathlib.CategoryTheory.Grothendieck
import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
universe v u
variable (n : ℕ)

lemma Fin.comp_contractNth {G H : Type*} [MulOneClass G] [MulOneClass H] (f : G →* H)
    (j : Fin (n + 1)) (g : Fin (n + 1) → G) :
    f ∘ Fin.contractNth j (· * ·) g = Fin.contractNth j (· * ·) (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h|h|h)
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_eq, h, f.map_mul]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_gt, h]

namespace groupCohomology
section Functoriality

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  (A : Rep k G) (B : Rep k H) (f : G →* H) (φ : B →ₗ[k] A) (n : ℕ)

def CompatiblePair : Prop := ∀ (g : G) (x : B.V), φ (B.ρ (f g) x) = A.ρ g (φ x)

open Representation CategoryTheory

def ummm : Rep k G where
  V := ModuleCat.of k (G → A)
  ρ := _

def resFunctor' (k : Type u) [CommRing k] : GroupCatᵒᵖ ⥤ Cat where
  obj := fun G ↦ Cat.of (Rep k G.unop)
  map := fun f ↦ Action.res (ModuleCat k) f.unop

def resFunctor2 (k : Type u) [CommRing k] : GroupCatᵒᵖ ⥤ Cat where
  obj := fun G ↦ Cat.of (Rep k G.unop)ᵒᵖ
  map := fun f ↦ (Action.res (ModuleCat k) f.unop).op

abbrev CompatiblePairs (k : Type u) [CommRing k] :=
  Grothendieck (resFunctor' k)

abbrev CompatiblePairs2 (k : Type u) [CommRing k] :=
  Grothendieck (resFunctor2 k)

lemma compatiblePairs_comm_apply2 {A B : CompatiblePairs2 k}
  (f : B ⟶ A) (g : A.base.unop) (x : A.fiber.unop.V) :
  f.fiber.unop.hom (A.fiber.unop.ρ g x) = B.fiber.unop.ρ (f.base.unop g) (f.fiber.unop.hom x) :=
  Rep.hom_comm_apply f.fiber.unop _ _

lemma compatiblePairs_comm_apply {A B : CompatiblePairs k}
    (f : A ⟶ B) (g : B.base.unop) (x : A.fiber.V) :
    f.fiber.hom (A.fiber.ρ (f.base.unop g) x) = B.fiber.ρ g (f.fiber.hom x) :=
  Rep.hom_comm_apply f.fiber _ _

@[simps] noncomputable def invariantsFunctor : Rep k G ⥤ ModuleCat k where
  obj := fun A => ModuleCat.of k (Representation.invariants A.ρ)
  map := fun {A B} f => ModuleCat.ofHom (LinearMap.codRestrict _
    (f.hom ∘ₗ (Representation.invariants A.ρ).subtype)
    (fun ⟨c, hc⟩ g => by
      show B.ρ g (f.hom c) = f.hom c
      erw [← Rep.hom_comm_apply f g c] -- why erw???
      rw [hc]
      rfl))

variable (S : Subgroup G)

abbrev resFunctor : Rep k H ⥤ Rep k G := Action.res _ (MonCat.ofHom f)

lemma resFunctor_obj_ρ (A : Rep k H) :
    ((resFunctor f).obj A).ρ = A.ρ.comp f := rfl

lemma resFunctor_map_hom {A B : Rep k H} (φ : A ⟶ B) :
    ((resFunctor f).map φ).hom = φ.hom := rfl

@[simps] noncomputable def infObjAux [h1 : S.Normal] :
    Representation k G (invariants (A.ρ.comp S.subtype)) where
  toFun := fun g => LinearMap.codRestrict _ ((A.ρ g).comp (Submodule.subtype _))
    (fun x h => by
      dsimp
      rw [← one_mul (h : G), ← mul_inv_self g, mul_assoc, A.ρ.map_mul,
        ← LinearMap.mul_apply, mul_assoc, ← A.ρ.map_mul]
      exact LinearMap.congr_arg (x.2 (⟨g⁻¹ * h * g, by
        nth_rw 2 [← inv_inv g]
        exact Subgroup.Normal.conj_mem h1 (h : S) h.2 g⁻¹⟩)))
  map_one' := by
    ext
    show A.ρ 1 _ = _
    simp only [map_one, Submodule.coeSubtype, LinearMap.one_apply]
  map_mul' := fun x y => by
    ext
    show A.ρ (x * y) _ = _
    simp only [A.ρ.map_mul]
    rfl

-- general version of this needs to be in the library..
-- what general version?
noncomputable def infObj [S.Normal] : Rep k (G ⧸ S) :=
Rep.of (V := invariants (A.ρ.comp S.subtype)) $
  (QuotientGroup.con S).lift (infObjAux A S)
  (fun x y h => LinearMap.ext (fun w => Subtype.ext $ by
    rcases h with ⟨z, rfl⟩
    show A.ρ (y * MulOpposite.unop z) w = A.ρ y w
    rw [A.ρ.map_mul]
    exact LinearMap.congr_arg (w.2 (⟨MulOpposite.unop z, z.2⟩))))

-- "hard to rewrite because of the type of x I guess."
lemma infObj_apply [S.Normal] (g : G) (x : invariants (A.ρ.comp S.subtype)) :
  ((infObj A S).ρ (g : G ⧸ S) x).1 = A.ρ g x :=
rfl

noncomputable def infMap [S.Normal] {A B : Rep k G} (φ : A ⟶ B) :
    infObj A S ⟶ infObj B S where
  hom := invariantsFunctor.map ((resFunctor S.subtype).map φ)
  comm := fun g => QuotientGroup.induction_on' g (fun g => LinearMap.ext
    fun x => Subtype.ext (Rep.hom_comm_apply φ g x.1))

@[simps] noncomputable def infFunctor [S.Normal] : Rep k G ⥤ Rep k (G ⧸ S) :=
{ obj := fun A => infObj A S
  map := fun f => infMap S f }

lemma infFunctor_obj_compatiblePair (S : Subgroup G) [S.Normal] :
  CompatiblePair A ((infFunctor S).obj A) (QuotientGroup.mk' S)
    (invariants (A.ρ.comp S.subtype)).subtype :=
fun _ _ => rfl

lemma resFunctor_obj_compatiblePair (S : Subgroup G) :
  CompatiblePair ((resFunctor S.subtype).obj A) A S.subtype LinearMap.id :=
fun _ _ => rfl

lemma hom_compatiblePair {k : Type u} [CommRing k] {G : Type u} [Group G]
    {A B : Rep k G} (f : A ⟶ B) :
    CompatiblePair B A (MonoidHom.id G) f.hom :=
fun _ => LinearMap.ext_iff.1 (f.comm _)

noncomputable def pairCochainMap (A B : CompatiblePairs k)
  (F : B ⟶ A) :
  inhomogeneousCochains B.fiber ⟶ inhomogeneousCochains A.fiber where
  f :=  fun i => F.fiber.hom.compLeft (Fin i → A.base.unop) ∘ₗ LinearMap.funLeft k B.fiber.V
      (fun x : Fin i → A.base.unop => (F.base.unop ∘ x))
  comm' := fun i j (hij : _ = _) => by
    subst hij
    ext x
    funext g
    simp only [inhomogeneousCochains.d_def]
    show inhomogeneousCochains.d i A.fiber (fun g : Fin i → A.base.unop ↦ F.fiber.hom (x (F.base.unop ∘ g))) g
      = F.fiber.hom (inhomogeneousCochains.d i B.fiber x (F.base.unop ∘ g))
    simp only [inhomogeneousCochains.d_apply, Fin.comp_contractNth,
      Function.comp_apply, map_add]
    erw [map_add, compatiblePairs_comm_apply F (g 0) (x fun i_1 ↦ F.base.unop (g (Fin.succ i_1)))]
    erw [map_sum]
    convert (add_left_inj _).2 _
    erw [map_smul]
    rfl
-- lol.

#exit

lemma pairCochainMap_f_apply {hp : CompatiblePair A B f φ}
    (x : (Fin n → H) → B) (g : Fin n → G) :
  (pairCochainMap A B f φ hp).f n x g = φ (x (f ∘ g)) :=
rfl

noncomputable abbrev pairCocyclesMap (hp : CompatiblePair A B f φ) (n : ℕ) :
  (inhomogeneousCochains B).cycles n ⟶ (inhomogeneousCochains A).cycles n :=
HomologicalComplex.cyclesMap (pairCochainMap A B f φ hp) n

noncomputable abbrev pairCohomologyMap (hp : CompatiblePair A B f φ) (n : ℕ) :
  groupCohomology B n ⟶ groupCohomology A n :=
HomologicalComplex.homologyMap (pairCochainMap A B f φ hp) n

/-
-- ⟶ or →ₗ[k]? ⟶ makes sense w defn, don't have to rw an of_hom
def pairH0Map (hp : CompatiblePair A B f φ) :
  H0 B ⟶ H0 A :=
(H_0_iso B).inv ≫ pair_cohomology_map A B f φ hp 0 ≫ (H_0_iso A).hom

lemma pair_H_0_map_comp_subtype (hp : compatible A B f φ) :
  (A.ρ.invariants.subtype).comp (pair_H_0_map A B f φ hp) =
  φ.comp B.ρ.invariants.subtype :=
begin
  show (_ ≫ _) ≫ ModuleCat.of_hom A.ρ.invariants.subtype
    = ModuleCat.of_hom B.ρ.invariants.subtype ≫ ModuleCat.of_hom φ,
  rw [category.assoc, iso.inv_comp_eq, ←cancel_epi (homology.π _ _ _)],
  simp only [category.assoc, π_comp_H_0_iso_hom_comp_subtype_assoc, pair_cohomology_map,
    homology_functor_map, homology.π_map_assoc, π_comp_H_0_iso_hom_comp_subtype],
  delta homological_complex.cycles,
  rw limits.kernel_subobject_map_arrow_assoc,
  ext,
  show φ ((((inhomogeneous_cochains B).cycles 0).arrow x) (f ∘ default))
    = φ ((((inhomogeneous_cochains B).cycles 0).arrow x) default),
  rw unique.eq_default (f ∘ default),
  { delta homology.π,
    apply_instance }
end

-- would need some ModuleCat.of's for this to be a ⟶
def pair_one_cocycles_map (hp : compatible A B f φ) :
  one_cocycles B →ₗ[k] one_cocycles A :=
(one_cocycles_iso B).inv ≫ (cycles_functor _ _ 1).map (pair_chain_map A B f φ hp)
  ≫ (one_cocycles_iso A).hom

lemma pair_one_cocycles_map_apply (hp : compatible A B f φ) (x : one_cocycles B) (g : G) :
  (pair_one_cocycles_map A B f φ hp x : G → A) g
    = φ ((x : H → B) (f g)) :=
begin
  show ((one_cocycles_iso A).hom ≫ ModuleCat.of_hom (one_cocycles A).subtype)
    (((one_cocycles_iso B).inv ≫ _) x) g = _,
  simpa only [one_cocycles_iso_hom_comp_subtype, ←LinearMap.comp_apply, ←ModuleCat.comp_def,
    category.assoc, cycles_functor_map, cycles_map_arrow_assoc,
    one_cocycles_iso_inv_comp_arrow_assoc],
end

def pair_H_1_map (hp : compatible A B f φ) :
  H_1 B ⟶ H_1 A :=
(H_1_iso B).inv ≫ pair_cohomology_map A B f φ hp 1 ≫ (H_1_iso A).hom

lemma mkq_comp_pair_H_1_map (hp : compatible A B f φ) :
  ModuleCat.of_hom (one_coboundaries B).mkq ≫ pair_H_1_map A B f φ hp
  = (one_coboundaries A).mkq.comp (pair_one_cocycles_map A B f φ hp) :=
begin
  simpa only [pair_H_1_map, mkq_comp_H_1_iso_inv_assoc, pair_cohomology_map, homology_functor_map,
    homology.π_map_assoc, π_comp_H_1_iso_hom, ←ModuleCat.comp_def, category.assoc,
    pair_one_cocycles_map],
end

def pair_two_cocycles_map (hp : compatible A B f φ) :
  two_cocycles B →ₗ[k] two_cocycles A :=
(two_cocycles_iso B).inv ≫ (cycles_functor _ _ 2).map (pair_chain_map A B f φ hp)
  ≫ (two_cocycles_iso A).hom

lemma pair_two_cocycles_map_apply (hp : compatible A B f φ) (x : one_cocycles B) (g : G) :
  (pair_one_cocycles_map A B f φ hp x : G → A) g
    = φ ((x : H → B) (f g)) :=
begin
  show ((one_cocycles_iso A).hom ≫ ModuleCat.of_hom (one_cocycles A).subtype)
    (((one_cocycles_iso B).inv ≫ _) x) g = _,
  simpa only [one_cocycles_iso_hom_comp_subtype, ←LinearMap.comp_apply, ←ModuleCat.comp_def,
    category.assoc, cycles_functor_map, cycles_map_arrow_assoc,
    one_cocycles_iso_inv_comp_arrow_assoc],
end

def pair_H_2_map (hp : compatible A B f φ) :
  H_2 B ⟶ H_2 A :=
(H_2_iso B).inv ≫ pair_cohomology_map A B f φ hp 2 ≫ (H_2_iso A).hom

lemma mkq_comp_pair_H_2_map (hp : compatible A B f φ) :
  ModuleCat.of_hom (two_coboundaries B).mkq ≫ pair_H_2_map A B f φ hp
  = (two_coboundaries A).mkq.comp (pair_two_cocycles_map A B f φ hp) :=
begin
  simpa only [pair_H_2_map, mkq_comp_H_2_iso_inv_assoc, pair_cohomology_map, homology_functor_map,
    homology.π_map_assoc, π_comp_H_2_iso_hom, ←ModuleCat.comp_def, category.assoc,
    pair_two_cocycles_map],
end
-/

noncomputable def groupCohomologyMap' {A B : Rep k G} (φ : A →ₗ[k] B)
  (hp : CompatiblePair B A (MonoidHom.id G) φ) (n : ℕ) :
  groupCohomology A n ⟶ groupCohomology B n :=
(pairCohomologyMap B A (MonoidHom.id G) φ hp n)

noncomputable def groupCohomologyMap {A B : Rep k G} (φ : A ⟶ B) (n : ℕ) :
  groupCohomology A n ⟶ groupCohomology B n :=
(pairCohomologyMap _ _ (MonoidHom.id G) φ.hom (hom_compatiblePair φ) n)

noncomputable def res (S : Subgroup G) (n : ℕ) :
  groupCohomology A n ⟶ groupCohomology ((resFunctor S.subtype).obj A) n :=
pairCohomologyMap _ _ S.subtype LinearMap.id (resFunctor_obj_compatiblePair A S) n

/-def Res_one_cocycles : one_cocycles A →ₗ[k] one_cocycles (Res_rep A S) :=
pair_one_cocycles_map _ _ S.subtype LinearMap.id (subgroup_pair A S)

def Res_one (S : subgroup G) : H_1 A ⟶ H_1 (Res_rep A S) :=
pair_H_1_map _ _ S.subtype LinearMap.id (subgroup_pair A S)-/

noncomputable def Inf (S : Subgroup G) [S.Normal] (n : ℕ) :
  groupCohomology ((infFunctor S).obj A) n ⟶ groupCohomology A n :=
pairCohomologyMap _ _ (QuotientGroup.mk' S) (invariants (A.ρ.comp S.subtype)).subtype
  (infFunctor_obj_compatiblePair A S) n

/-def Inf_one_cocycles (S : subgroup G) [h1 : S.normal] :
  one_cocycles (Inf_rep A S) →ₗ[k] one_cocycles A :=
pair_one_cocycles_map A (Inf_rep A S) (quotient_group.mk' S)
  (invariants (A.ρ.comp S.subtype)).subtype (quotient_pair A S)

def Inf_one (S : subgroup G) [h1 : S.normal] :
  H_1 (Inf_rep A S) ⟶ H_1 A :=
pair_H_1_map _ _ (quotient_group.mk' S) (invariants (A.ρ.comp S.subtype)).subtype
  (quotient_pair A S)

variables {A S}

lemma Res_one_cocycles_apply (x : one_cocycles A) (g : S) :
  (Res_one_cocycles A S x : S → Res_rep A S) g = (x : G → A) g :=
begin
  rw [Res_one_cocycles, pair_one_cocycles_map_apply],
  refl,
end

lemma Inf_one_cocycles_apply [h1 : S.normal] (x : one_cocycles (Inf_rep A S)) (g : G) :
  ((Inf_one_cocycles A S x) : G → A) g = (x : G ⧸ S → Inf_rep A S) g :=
begin
  rw [Inf_one_cocycles, pair_one_cocycles_map_apply],
  refl,
end

variables (A S)

lemma Inf_one_comp_mkq [h1 : S.normal] :
  (Inf_one A S).comp (one_coboundaries (Inf_rep A S)).mkq
    = (one_coboundaries A).mkq.comp (Inf_one_cocycles A S) :=
mkq_comp_pair_H_1_map A (Inf_rep A S) (quotient_group.mk' S)
  (invariants (A.ρ.comp S.subtype)).subtype (quotient_pair A S)

lemma Res_one_comp_mkq :
  (Res_one A S).comp (one_coboundaries A).mkq
    = (one_coboundaries (Res_rep A S)).mkq.comp (Res_one_cocycles A S) :=
mkq_comp_pair_H_1_map (Res_rep A S) A S.subtype LinearMap.id (subgroup_pair A S)

lemma Inf_one_apply [h1 : S.normal] (x : one_cocycles (Inf_rep A S)) :
  Inf_one A S (quotient.mk' x) = quotient.mk' (Inf_one_cocycles A S x) :=
LinearMap.ext_iff.1 (by apply Inf_one_comp_mkq A S) x

lemma Res_one_apply (x : one_cocycles A) :
  Res_one A S (quotient.mk' x) = quotient.mk' (Res_one_cocycles A S x) :=
LinearMap.ext_iff.1 (by apply Res_one_comp_mkq A S) x

lemma Inf_ker_eq_bot (S : subgroup G) [h1 : S.normal] :
  (Inf_one A S).ker = ⊥ :=
begin
  rw eq_bot_iff,
  intros x,
  refine x.induction_on' _,
  intros y hy,
  erw [LinearMap.mem_ker, Inf_one_apply] at hy,
  refine (submodule.quotient.mk_eq_zero _).2 _,
  obtain ⟨m, hm⟩ := (submodule.quotient.mk_eq_zero _).1 hy,
  refine ⟨⟨m, _⟩, _⟩,
  { intros g,
    dsimp,
    have := function.funext_iff.1 (subtype.ext_iff.1 hm) g,
    simp only [LinearMap.cod_restrict_apply, d_zero_apply] at this,
    rw [←sub_eq_zero, this, Inf_one_cocycles_apply,
      (quotient_group.eq_one_iff (g : G)).2 g.2, one_cocycles_map_one, submodule.coe_zero] },
  { ext z,
    refine quotient_group.induction_on' z (fun w, _),
    rw ←Inf_one_cocycles_apply y w,
    exact function.funext_iff.1 (subtype.ext_iff.1 hm) w }
end

lemma Inf_one_range_le_Res_one_ker (S : subgroup G) [h1 : S.normal] :
  (Inf_one A S).range ≤ (Res_one A S).ker :=
begin
  intros x hx,
  obtain ⟨y, rfl⟩ := hx,
  refine quotient.induction_on' y (fun z, _),
  rw [LinearMap.mem_ker, Inf_one_apply, Res_one_apply,
    submodule.quotient.mk'_eq_mk, submodule.quotient.mk_eq_zero],
  use 0,
  ext,
  simp only [Res_one_cocycles_apply, Inf_one_cocycles_apply, map_zero,
    submodule.coe_zero, pi.zero_apply, (quotient_group.eq_one_iff (x : G)).2 x.2,
    one_cocycles_map_one, submodule.coe_zero],
end

lemma seriously (S : subgroup G) [h1 : S.normal] (h : S) (g : G) :
  g⁻¹ * h * g ∈ S :=
by {convert subgroup.normal.conj_mem h1 h h.2 g⁻¹, rw inv_inv }

lemma helper (S : subgroup G) [h1 : S.normal]  (y : one_cocycles A) (m : A)
  (Hy : ∀ h : S, (y : G → A) h = A.ρ h m - m) (g : G) (h : S) :
  A.ρ h ((y : G → A) g - A.ρ g m + m) = (y : G → A) g - A.ρ g m + m :=
begin
  have := (mem_one_cocycles_iff' (y : G → A)).1 y.2 (g, (g⁻¹ * h * g)),
  simp only [prod.fst] at this,
  rw [mul_assoc, mul_inv_cancel_left, (mem_one_cocycles_iff' (y : G → A)).1 y.2 (h, g), Hy,
    ←mul_assoc, (show (y : G → A) (g⁻¹ * h * g) = A.ρ (g⁻¹ * h * g) m - m, from Hy (⟨g⁻¹ * h * g,
    seriously _ _ _⟩)), map_sub, ←LinearMap.mul_apply, ←map_mul, ←mul_assoc, mul_inv_cancel_left,
    sub_add_comm, ←sub_eq_sub_iff_add_eq_add] at this,
  rw [map_add, map_sub, ←LinearMap.mul_apply, ←map_mul, this,
    sub_add_eq_add_sub, add_sub_assoc, sub_sub_self],
end

lemma Inf_one_range_eq_Res_one_ker (S : subgroup G) [h1 : S.normal] :
  (Inf_one A S).range = (Res_one A S).ker :=
le_antisymm (Inf_one_range_le_Res_one_ker A S) $ fun x,
begin
  refine quotient.induction_on' x _,
  intros y hy,
  rw [LinearMap.mem_ker, Res_one_apply] at hy,
  obtain ⟨m, hm⟩ := (submodule.quotient.mk_eq_zero _).1 hy,
  refine ⟨quotient.mk' ⟨fun (g : G ⧸ S), quotient.lift_on' g (fun x : G, (⟨(y : G → A) x - A.ρ x m + m,
    fun g, helper A S y m (fun h, _) x g⟩
    : invariants (A.ρ.comp S.subtype))) (fun a b hab, _), _⟩, _⟩,
  { simp only [subtype.ext_iff, function.funext_iff, Res_one_cocycles_apply] at hm,
    exact (hm h).symm },
  { ext,
    dsimp only [subtype.coe_mk],
    congr' 1,
    have := function.funext_iff.1 (subtype.ext_iff.1 hm) (⟨a⁻¹ * b,
      quotient_group.eq.1 (quotient.eq'.2 hab)⟩),
    simp only [Res_one_cocycles_apply, LinearMap.cod_restrict_apply, d_zero_apply,
        subgroup.coe_mk, Res_rep_apply, (mem_one_cocycles_iff' (y : G → A)).1 y.2 (a⁻¹, b)] at this,
    replace this := congr_arg (A.ρ a) this,
    simp only [map_sub, ←LinearMap.mul_apply, ←map_mul, map_add, mul_inv_cancel_left,
      mul_inv_self, map_one, LinearMap.one_apply, one_cocycles_map_inv, ←sub_eq_add_neg,
      sub_eq_sub_iff_add_eq_add] at this,
    rw [sub_eq_sub_iff_add_eq_add, add_comm, this] },
  { refine (mem_one_cocycles_iff' _).2 _,
    rintros ⟨g, h⟩,
    refine quotient.induction_on₂' g h (fun w z, _),
    show quotient.lift_on' (quotient.mk' (_ * _)) _ _ = _,
    ext,
    simp only [quotient.lift_on'_mk', subtype.coe_mk, submodule.coe_add],
    simp only [show quotient.mk' w = (w : G ⧸ S), from rfl, Inf_rep_apply, subtype.coe_mk, map_sub,
      map_add, ←LinearMap.mul_apply, ←map_mul, ←add_assoc, add_left_inj],
    simp only [add_assoc, add_sub_cancel'_right, sub_add_eq_add_sub, sub_left_inj,
        (mem_one_cocycles_iff' (y : G → A)).1 y.2 (w, z)] },
  { rw Inf_one_apply,
    refine (submodule.quotient.eq _).2 ⟨-m, subtype.ext (funext $ fun g, _)⟩,
    simp only [LinearMap.cod_restrict_apply, submodule.coe_sub, pi.sub_apply,
      Inf_one_cocycles_apply],
    simp only [d_zero_apply, subtype.coe_mk, quotient_group.quotient_lift_on_coe],
    rw [map_neg, neg_sub_neg, eq_sub_iff_add_eq', ←add_sub_assoc, sub_add_eq_add_sub] }
end-/

end Functoriality
end groupCohomology
