import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.CategoryTheory.Limits.VanKampen

open CategoryTheory Limits

variable {C : Type*} [Category C]

-- /--
-- If a coproduct interacts well enough with pullbacks, then a family whose domains are the terms of
-- the coproduct is effective epimorphic whenever `Sigma.desc` induces an effective epimorphism from
-- the coproduct itself.
-- -/
-- noncomputable
-- def effectiveEpiFamilyStructOfEffectiveEpiDesc' {B : C} {α : Type*} (X : α → C)
--     (π : (a : α) → (X a ⟶ B)) (c : Cofan X)  (hc : IsUniversalColimit c) [EffectiveEpi (hc.isColimit.desc (Cofan.mk B π))]
--     [∀ {Z : C} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)]
--     [∀ {Z : C} (g : Z ⟶ ∐ X), HasCoproduct (fun a ↦ pullback g (Sigma.ι X a))]
--     [∀ {Z : C} (g : Z ⟶ ∐ X),
--       Epi (Sigma.desc (fun a ↦ pullback.fst (f := g) (g := (Sigma.ι X a))))] :
--     EffectiveEpiFamilyStruct X π where
--   desc e h := EffectiveEpi.desc (Sigma.desc π) (Sigma.desc e) fun _ _ hg ↦
--     effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg
--   fac e h a := by
--     rw [(by simp : π a = Sigma.ι X a ≫ Sigma.desc π), (by simp : e a = Sigma.ι X a ≫ Sigma.desc e),
--       Category.assoc, EffectiveEpi.fac (Sigma.desc π) (Sigma.desc e) (fun g₁ g₂ hg ↦
--       effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg)]
--   uniq _ _ _ hm := by
--     apply EffectiveEpi.uniq (Sigma.desc π)
--     ext
--     simpa using hm _
