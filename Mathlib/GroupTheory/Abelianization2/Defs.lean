import Mathlib.GroupTheory.Congruence.Defs

inductive Abelianization2.Rel (M : Type*) [Mul M] : M → M → Prop where
  | of a b : Abelianization2.Rel M (a * b) (b * a)


def Abelianization2 (M : Type*) [Mul M] : Type _ :=
  (conGen (Abelianization2.Rel M)).Quotient

namespace Abelianization2
variable {M : Type*} [Mul M]
instance : Mul (Abelianization2 M) :=
  inferInstanceAs (Mul (conGen (Abelianization2.Rel M)).Quotient)

protected lemma mul_comm : ∀ (a b : Abelianization2 M),
    a * b = b * a := by
  delta Abelianization2
  intro a b
  induction a, b using Con.induction_on₂ with
  | H a b =>
    change ((a * b : M) : (conGen (Abelianization2.Rel M)).Quotient) = (b * a : M)
    rw [Con.eq]
    exact (ConGen.Rel.of (a * b) (b * a) (Rel.of a b))

protected lemma commute {a b : Abelianization2 M} : Commute a b := a.mul_comm b

instance [Unique M] : Unique (Abelianization2 M) := Quotient.instUniqueQuotient _
instance [Inhabited M] : Inhabited (Abelianization2 M) := ⟨.mk _ default⟩


def mk [Semigroup M] : M → Abelianization2 M := Quotient.mk _

end Abelianization2

-- /-- The abelianization of G is the quotient of G by its commutator subgroup. -/
-- def Abelianization : Type u :=
--   G ⧸ commutator G

namespace Abelianization

-- attribute [local instance] QuotientGroup.leftRel

variable {G}

-- adapt later
-- variable (G) in
-- @[simp]
-- theorem ker_of : of.ker = commutator G :=
--   QuotientGroup.ker_mk' (commutator G)

section lift

-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthermore we defined the canonical projection `of : G → Gᵃᵇ`
-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
-- variable {A : Type v} [CommGroup A] (f : G →* A)

-- theorem commutator_subset_ker : commutator G ≤ f.ker := by
--   rw [commutator_eq_closure, Subgroup.closure_le]
--   rintro x ⟨p, q, rfl⟩
--   simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]

-- /-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map
--   from the abelianization of a `G` to `A` that factors through `f`. -/
-- def lift : (G →* A) ≃ (Abelianization G →* A) where
--   toFun f := QuotientGroup.lift _ f fun _ h => MonoidHom.mem_ker.2 <| commutator_subset_ker _ h
--   invFun F := F.comp of
--   left_inv _ := MonoidHom.ext fun _ => rfl
--   right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

-- @[simp]
-- theorem lift.of (x : G) : lift f (of x) = f x :=
--   rfl

-- theorem lift.unique (φ : Abelianization G →* A)
--     -- hφ : φ agrees with f on the image of G in Gᵃᵇ
--     (hφ : ∀ x : G, φ (Abelianization.of x) = f x)
--     {x : Abelianization G} : φ x = lift f x :=
--   QuotientGroup.induction_on x hφ

-- @[simp]
-- theorem lift_of : lift of = MonoidHom.id (Abelianization G) :=
--   lift.apply_symm_apply <| MonoidHom.id _

end lift

variable {A : Type*} [Monoid A]

-- /-- See note [partially-applied ext lemmas]. -/
-- @[ext]
-- theorem hom_ext (φ ψ : Abelianization G →* A) (h : φ.comp of = ψ.comp of) : φ = ψ :=
--   MonoidHom.ext fun x => QuotientGroup.induction_on x <| DFunLike.congr_fun h

section Map

-- variable {H : Type v} [Group H] (f : G →* H)

-- /-- The map operation of the `Abelianization` functor -/
-- def map : Abelianization G →* Abelianization H :=
--   lift (of.comp f)

-- /-- Use `map` as the preferred simp normal form. -/
-- @[simp] theorem lift_of_comp :
--     Abelianization.lift (Abelianization.of.comp f) = Abelianization.map f := rfl

-- @[simp]
-- theorem map_of (x : G) : map f (of x) = of (f x) :=
--   rfl

-- @[simp]
-- theorem map_id : map (MonoidHom.id G) = MonoidHom.id (Abelianization G) :=
--   hom_ext _ _ rfl

-- @[simp]
-- theorem map_comp {I : Type w} [Group I] (g : H →* I) : (map g).comp (map f) = map (g.comp f) :=
--   hom_ext _ _ rfl

-- @[simp]
-- theorem map_map_apply {I : Type w} [Group I] {g : H →* I} {x : Abelianization G} :
--     map g (map f x) = map (g.comp f) x :=
--   DFunLike.congr_fun (map_comp _ _) x

end Map

end Abelianization

section AbelianizationCongr

-- Porting note: `[Group G]` should not be necessary here
variable {G} {H : Type*} [Group H]

-- /-- Equivalent groups have equivalent abelianizations -/
-- def MulEquiv.abelianizationCongr (e : G ≃* H) : Abelianization G ≃* Abelianization H where
--   toFun := Abelianization.map e.toMonoidHom
--   invFun := Abelianization.map e.symm.toMonoidHom
--   left_inv := by
--     rintro ⟨a⟩
--     simp
--   right_inv := by
--     rintro ⟨a⟩
--     simp
--   map_mul' := MonoidHom.map_mul _

-- @[simp]
-- theorem abelianizationCongr_of (e : G ≃* H) (x : G) :
--     e.abelianizationCongr (Abelianization.of x) = Abelianization.of (e x) :=
--   rfl

-- @[simp]
-- theorem abelianizationCongr_refl :
--     (MulEquiv.refl G).abelianizationCongr = MulEquiv.refl (Abelianization G) :=
--   MulEquiv.toMonoidHom_injective Abelianization.lift_of

-- @[simp]
-- theorem abelianizationCongr_symm (e : G ≃* H) :
--     e.abelianizationCongr.symm = e.symm.abelianizationCongr :=
--   rfl

-- @[simp]
-- theorem abelianizationCongr_trans {I : Type v} [Group I] (e : G ≃* H) (e₂ : H ≃* I) :
--     e.abelianizationCongr.trans e₂.abelianizationCongr = (e.trans e₂).abelianizationCongr :=
--   MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ rfl)

end AbelianizationCongr

-- /-- An Abelian group is equivalent to its own abelianization. -/
-- @[simps]
-- def Abelianization.equivOfComm {H : Type*} [CommGroup H] : H ≃* Abelianization H :=
--   { Abelianization.of with
--     toFun := Abelianization.of
--     invFun := Abelianization.lift (MonoidHom.id H)
--     left_inv := fun _ => rfl
--     right_inv := by
--       rintro ⟨a⟩
--       rfl }
