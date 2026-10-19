/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitGroupRepresentation

/-! # Restricting actual modulus units modulo parameter scalars -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y Y' S : Scheme.{u}} {q : Y ⟶ S} {q' : Y' ⟶ S}
  (j : Y' ⟶ Y) (w : j ≫ q = q')

/-- The actual morphism of moduli after changing to a parameter scheme. -/
def unitRestrictionPullback (T : Over S) :
    ((Over.pullback q').obj T).left ⟶ ((Over.pullback q).obj T).left :=
  pullback.lift (pullback.fst T.hom q') (pullback.snd T.hom q' ≫ j) (by
    rw [Category.assoc, w, pullback.condition])

@[reassoc] theorem unitRestrictionPullback_fst (T : Over S) :
    unitRestrictionPullback j w T ≫ modulusProjection q T = modulusProjection q' T :=
  pullback.lift_fst _ _ _

@[reassoc] theorem unitRestrictionPullback_snd (T : Over S) :
    unitRestrictionPullback j w T ≫ pullback.snd T.hom q = pullback.snd T.hom q' ≫ j :=
  pullback.lift_snd _ _ _

/-- The modulus inclusion commutes with every change of parameters. -/
theorem unitRestrictionPullback_naturality {T T' : Over S} (f : T' ⟶ T) :
    ((Over.pullback q').map f).left ≫ unitRestrictionPullback j w T =
      unitRestrictionPullback j w T' ≫ ((Over.pullback q).map f).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, unitRestrictionPullback, Over.pullback_map_left,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, unitRestrictionPullback, Over.pullback_map_left,
      pullback.lift_snd, pullback.lift_snd_assoc]

/-- Restriction is the homomorphism on units of the actual fibre products. -/
def modulusUnitsRestriction (T : Over S) : ModulusUnits q T →* ModulusUnits q' T :=
  Units.map (unitRestrictionPullback j w T).appTop.hom.toMonoidHom

/-- Parameter scalar units restrict to the same parameter scalar units. -/
theorem modulusUnitsRestriction_scalar (T : Over S) (a : Γ(T.left, ⊤)ˣ) :
    modulusUnitsRestriction j w T
        (Units.map (modulusProjection q T).appTop.hom.toMonoidHom a) =
      Units.map (modulusProjection q' T).appTop.hom.toMonoidHom a := by
  apply Units.ext
  have h := congrArg Scheme.Hom.appTop (unitRestrictionPullback_fst j w T)
  rw [Scheme.Hom.comp_appTop] at h
  exact congrArg (fun k : Γ(T.left, ⊤) ⟶ Γ(((Over.pullback q').obj T).left, ⊤) =>
    k (a : Γ(T.left, ⊤))) h

/-- The scalar subgroup maps into the target scalar subgroup. -/
theorem modulusUnitsRestriction_scalars (T : Over S) :
    modulusScalars q T ≤ (modulusScalars q' T).comap (modulusUnitsRestriction j w T) := by
  rintro a ⟨s, rfl⟩
  exact ⟨s, (modulusUnitsRestriction_scalar j w T s).symm⟩

/-- The induced homomorphism on actual unit classes modulo scalars. -/
def modulusUnitQuotientRestriction (T : Over S) :
    ModulusUnits q T ⧸ modulusScalars q T →* ModulusUnits q' T ⧸ modulusScalars q' T :=
  QuotientGroup.map _ _ (modulusUnitsRestriction j w T) (modulusUnitsRestriction_scalars j w T)

/-- Unit restriction is natural on arbitrary parameter schemes. -/
theorem modulusUnitsRestriction_naturality {T T' : Over S} (f : T' ⟶ T)
    (a : ModulusUnits q T) :
    modulusUnitsRestriction j w T' (modulusUnitMap q f a) =
      modulusUnitMap q' f (modulusUnitsRestriction j w T a) := by
  apply Units.ext
  have h := congrArg Scheme.Hom.appTop (unitRestrictionPullback_naturality j w f)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact congrArg (fun k : Γ(((Over.pullback q).obj T).left, ⊤) ⟶
      Γ(((Over.pullback q').obj T').left, ⊤) =>
    k (a : Γ(((Over.pullback q).obj T).left, ⊤))) h.symm

/-- The natural map of intrinsic unit-quotient group presheaves. -/
def modulusUnitRestrictionPresheaf : modulusUnitQuotientPresheaf q ⟶
    modulusUnitQuotientPresheaf q' where
  app T := CommGrpCat.ofHom (modulusUnitQuotientRestriction j w T.unop)
  naturality {T T'} f := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    refine QuotientGroup.induction_on x fun a => ?_
    change QuotientGroup.mk (modulusUnitsRestriction j w T'.unop
        (modulusUnitMap q f.unop a)) =
      QuotientGroup.mk (modulusUnitMap q' f.unop
        (modulusUnitsRestriction j w T.unop a))
    rw [modulusUnitsRestriction_naturality]

/-- The same actual restriction in the group-sheaf value universe. -/
def liftedModulusUnitRestrictionPresheaf : liftedModulusUnitQuotientGroupPresheaf q ⟶
    liftedModulusUnitQuotientGroupPresheaf q' :=
  Functor.whiskerRight (modulusUnitRestrictionPresheaf j w) CommGrpCat.uliftFunctor.{u + 1, u}

/-- The canonical restriction of intrinsic modulus-unit quotient group sheaves. -/
def modulusUnitRestrictionSheaf : modulusUnitQuotientGroupSheaf q ⟶
    modulusUnitQuotientGroupSheaf q' :=
  (presheafToSheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1}).map
    (liftedModulusUnitRestrictionPresheaf j w)

/-- Restriction along the identity acts identically on the actual fibre product. -/
theorem unitRestrictionPullback_id (T : Over S) :
    unitRestrictionPullback (𝟙 Y) (Category.id_comp q) T = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [unitRestrictionPullback, pullback.lift_fst, Category.id_comp]
  · simp only [unitRestrictionPullback, pullback.lift_snd, Category.comp_id, Category.id_comp]

/-- Successive modulus restrictions give the composite actual fibre-product map. -/
theorem unitRestrictionPullback_comp {Y'' : Scheme.{u}} {q'' : Y'' ⟶ S}
    (k : Y'' ⟶ Y') (w' : k ≫ q' = q'') (T : Over S) :
    unitRestrictionPullback k w' T ≫ unitRestrictionPullback j w T =
      unitRestrictionPullback (k ≫ j) (by rw [Category.assoc, w, w']) T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, unitRestrictionPullback, pullback.lift_fst]
  · simp only [Category.assoc, unitRestrictionPullback, pullback.lift_snd,
      pullback.lift_snd_assoc]

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
