import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

universe v u
noncomputable section

@[simp]
lemma QuotientGroup.mk'_comp_subtype {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (mk' N).comp N.subtype = 1 := by ext; simp

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
noncomputable def ofQuotientGroup [IsTrivial (ρ.comp S.subtype)] :
    Representation k (G ⧸ S) V :=
  (QuotientGroup.con S).lift ρ <| by
    rintro x y ⟨⟨z, hz⟩, rfl⟩
    ext w
    have : ρ y (ρ z.unop _) = _ :=
      congr((ρ y) ($(IsTrivial.out (ρ := ρ.comp S.subtype) (⟨z.unop, hz⟩)) w))
    simpa [← LinearMap.mul_apply, ← map_mul] using this

@[simp]
lemma ofQuotientGroup_coe_apply [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V) :
    ofQuotientGroup ρ S (g : G ⧸ S) x = ρ g x :=
  rfl

section QuotientGroup

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
@[simps]
noncomputable def toInvariantsOfNormal :
    Representation k G (invariants (ρ.comp S.subtype)) where
  toFun g := ((ρ g).comp (Submodule.subtype _)).codRestrict _ (fun ⟨x, hx⟩ ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩)))
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

instance : IsTrivial ((toInvariantsOfNormal ρ S).comp S.subtype) where
  out g := LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext <| by
    simpa using (hx g)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
noncomputable abbrev quotientGroupToInvariants :
    Representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
  ofQuotientGroup (toInvariantsOfNormal ρ S) S

end QuotientGroup

end Representation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

open CategoryTheory
namespace Rep

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
noncomputable abbrev ofQuotientGroup [Representation.IsTrivial (A.ρ.comp S.subtype)] :
    Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotientGroup S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
abbrev quotientGroupToInvariants (S : Subgroup G) [S.Normal] :=
  Rep.of (A.ρ.quotientGroupToInvariants S)

end Rep
namespace groupCohomology
open Rep ShortComplex

theorem congr {H : Type u} [Monoid H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : (Action.res _ f₁).obj A ⟶ B} {T : Type*}
    (F : (f : G →* H) → (φ : (Action.res _ f).obj A ⟶ B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

@[simp]
theorem mapOneCocycles_one {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : (Action.res _ 1).obj A ⟶ B) :
    mapOneCocycles 1 φ = 0 := by
  rw [mapOneCocycles, ← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i,
    ShortComplex.cyclesMap'_i]
  refine ModuleCat.hom_ext (LinearMap.ext fun _ ↦ funext fun _ => ?_)
  show _ = 0
  simp [mapShortComplexH1, shortComplexH1]

@[simp]
theorem H1Map_one {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : (Action.res _ 1).obj A ⟶ B) :
    H1Map 1 φ = 0 := by
  simp [← cancel_epi (H1π _)]

@[simps X₁ X₂ X₃ f g]
def H1InfRes₁ (A : Rep k G) (H : Subgroup G) [H.Normal] :
     ShortComplex (ModuleCat k) where
  X₁ := H1 (A.quotientGroupToInvariants H)
  X₂ := H1 A
  X₃ := H1 ((Action.res _ H.subtype).obj A)
  f := H1Map (QuotientGroup.mk' H) ⟨ModuleCat.ofHom (Submodule.subtype _), fun _ => rfl⟩
  g := H1Map H.subtype (𝟙 _)
  zero := by rw [← H1Map_comp, Category.comp_id,
    congr (QuotientGroup.mk'_comp_subtype H) H1Map, H1Map_one]

@[simp]
lemma _root_.QuotientGroup.coe_subtype {G : Type*} [Group G] {S : Subgroup G} [S.Normal]
    (x : S) : (x : G ⧸ S) = 1 := by simp

instance : Mono (H1InfRes₁ A S).f := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  induction' x using Quotient.inductionOn' with x
  simp_all only [H1InfRes₁_X₂, H1InfRes₁_X₁, H1InfRes₁_f, Submodule.Quotient.mk''_eq_mk,
    H1π_comp_H1Map_apply (QuotientGroup.mk' S), Submodule.Quotient.mk_eq_zero]
  rcases hx with ⟨y, hy⟩
  refine ⟨⟨y, fun s => ?_⟩, Subtype.ext <| funext fun g => Quotient.inductionOn' g
    fun g => Subtype.ext <| congr_fun (Subtype.ext_iff.1 hy) g⟩
  replace hy := congr_fun (Subtype.ext_iff.1 hy) s.1
  simp_all [sub_eq_zero, shortComplexH1, moduleCatToCycles]

instance : (H1InfRes₁ A S).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x
  refine Quotient.inductionOn' x fun x hx => ?_
  simp_all only [H1InfRes₁_X₂, H1InfRes₁_X₃, H1InfRes₁_g, Submodule.Quotient.mk''_eq_mk,
    LinearMap.mem_ker, H1π_comp_H1Map_apply S.subtype, Submodule.Quotient.mk_eq_zero,
    H1InfRes₁_X₁, H1InfRes₁_f]
  rcases hx with ⟨y, hy⟩
  have h1 := (mem_oneCocycles_iff x.1).1 x.2
  have h2 : ∀ s ∈ S, x.1 s = (A.ρ s y - · : A → A) y :=
    fun s hs  => (groupCohomology.oneCocycles_ext_iff.1 hy ⟨s, hs⟩).symm
  refine ⟨H1π _ ⟨fun g => Quotient.liftOn' g
    (fun g => ⟨(x.1 g - A.ρ g y + · : A → A) y, ?_⟩) ?_, ?_⟩, ?_⟩
  · intro s
    simp_all only [MonoidHom.coe_comp, Subgroup.coeSubtype, Function.comp_apply, map_add, map_sub]
    rw [eq_add_of_sub_eq (h2 s s.2).symm, eq_sub_of_add_eq (h1 s g).symm,
      eq_sub_of_add_eq' (h1 g (g⁻¹ * s * g)).symm,
      h2 (g⁻¹ * s * g) (Subgroup.Normal.conj_mem' ‹_› _ s.2 _)]
    simp only [mul_assoc, mul_inv_cancel_left, map_mul, LinearMap.mul_apply, map_sub,
      Representation.ρ_self_inv_apply]
    abel
  · intro g h hgh
    have := congr(A.ρ g $(h2 (g⁻¹ * h) <| QuotientGroup.leftRel_apply.1 hgh))
    rw [h1] at this
    simp_all [← sub_eq_add_neg, sub_eq_sub_iff_sub_eq_sub]
  · rw [mem_oneCocycles_iff]
    intro g h
    induction' g using QuotientGroup.induction_on with g
    induction' h using QuotientGroup.induction_on with h
    apply Subtype.ext
    simp [-oneCocycles.val_eq_coe, coe_of, ← QuotientGroup.mk_mul, h1 g h, sub_add_eq_add_sub,
      add_assoc]
  · symm
    simp only [ModuleCat.hom_ofHom, oneCocycles.val_eq_coe, Submodule.mkQ_apply,
      H1π_comp_H1Map_apply, Submodule.Quotient.eq, LinearMap.mem_range]
    use y
    simp_rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', sub_add]
    rfl -- I can't seem to close this without abusing defeq rn

end groupCohomology
