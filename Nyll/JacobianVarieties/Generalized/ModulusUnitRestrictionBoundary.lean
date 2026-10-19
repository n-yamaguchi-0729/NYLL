/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitRestriction
import Nyll.JacobianVarieties.Generalized.ModulusUnitBoundary
import Nyll.JacobianVarieties.Generalized.ModulusRestrictionMapSheaf
import Nyll.JacobianVarieties.Generalized.ModulusRestrictionUnits

/-! # Modulus restriction commutes with the actual unit boundary -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  (j : D' ⟶ D) (w : i' = j ≫ i)

/-- Pullback symmetry identifies the actual two conventions for unit restriction. -/
theorem modulusBoundaryUnitsEquiv_restriction (T : Over (Spec (CommRingCat.of R)))
    (a : ModulusUnits (i ≫ c) T) :
    modulusBoundaryUnitsEquiv c i' T
        (modulusUnitsRestriction j (by rw [← Category.assoc, ← w]) T a) =
      Units.map (modulusRestrictionPullback c j w T.hom).appTop.hom.toMonoidHom
        (modulusBoundaryUnitsEquiv c i T a) := by
  apply scalarUnits_square
  change (pullbackSymmetry (i' ≫ c) T.hom).hom ≫
      unitRestrictionPullback j (by rw [← Category.assoc, ← w]) T =
    modulusRestrictionPullback c j w T.hom ≫ (pullbackSymmetry (i ≫ c) T.hom).hom
  apply pullback.hom_ext
  · simp only [Category.assoc, unitRestrictionPullback, modulusRestrictionPullback,
      pullback.lift_fst, pullbackSymmetry_hom_comp_fst,
      pullback.lift_snd]
  · simp only [Category.assoc, unitRestrictionPullback, modulusRestrictionPullback,
      pullback.lift_snd, pullbackSymmetry_hom_comp_snd,
      pullbackSymmetry_hom_comp_snd_assoc, pullback.lift_fst]

/-- Restriction of scalar rigidifications is the boundary of restricted unit classes. -/
theorem modulusUnitQuotientBoundary_restriction (T : Over (Spec (CommRingCat.of R)))
    (x : ModulusUnits (i ≫ c) T ⧸ modulusScalars (i ≫ c) T) :
    modulusUnitQuotientBoundary c i' T
        (modulusUnitQuotientRestriction j (by rw [← Category.assoc, ← w]) T x) =
      modulusRestrictionZeroClasses c j w T (modulusUnitQuotientBoundary c i T x) := by
  refine QuotientGroup.induction_on x fun a => ?_
  apply Subtype.ext
  change RigidifiedLineBundle.scalarClass (modulusBaseChange c i' T.hom)
      (modulusBoundaryUnitsEquiv c i' T
        (modulusUnitsRestriction j (by rw [← Category.assoc, ← w]) T a)) =
    RigidifiedLineBundle.classesPullback (𝟙 _) (modulusRestrictionPullback c j w T.hom)
      (modulusRestrictionPullback_square c j w T.hom)
      (RigidifiedLineBundle.scalarClass (modulusBaseChange c i T.hom)
        (modulusBoundaryUnitsEquiv c i T a))
  rw [RigidifiedLineBundle.scalarClass_pullback, modulusBoundaryUnitsEquiv_restriction]

/-- The canonical restriction square commutes before sheafification. -/
theorem modulusUnitBoundaryPresheaf_restriction :
    liftedModulusUnitRestrictionPresheaf j (by rw [← Category.assoc, ← w]) ≫
        modulusUnitBoundaryPresheaf c i' =
      modulusUnitBoundaryPresheaf c i ≫ modulusRestrictionZeroPresheaf c j w := by
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  exact modulusUnitQuotientBoundary_restriction c j w T.unop x.down

/-- The actual unit-boundary square commutes in the fppf category of group sheaves. -/
theorem modulusUnitBoundarySheaf_restriction :
    modulusUnitRestrictionSheaf j (by rw [← Category.assoc, ← w]) ≫
        modulusUnitBoundarySheaf c i' =
      modulusUnitBoundarySheaf c i ≫ modulusRestrictionZeroSheaf c j w := by
  let H := presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}
  exact (H.map_comp (liftedModulusUnitRestrictionPresheaf j
      (by rw [← Category.assoc, ← w])) (modulusUnitBoundaryPresheaf c i')).symm.trans
    ((congrArg (fun v => H.map v) (modulusUnitBoundaryPresheaf_restriction c j w)).trans
      (H.map_comp (modulusUnitBoundaryPresheaf c i) (modulusRestrictionZeroPresheaf c j w)))

variable [IsClosedImmersion j] [IsFinite (i ≫ c)]

/-- On a field-valued test, restriction lifts actual intrinsic modulus units. -/
theorem modulusUnitsRestriction_field_surjective {L : Type u} [Field L]
    (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)) :
    Function.Surjective
      (modulusUnitsRestriction (q := i ≫ c) (q' := i' ≫ c)
        j (by rw [← Category.assoc, ← w]) (Over.mk t)) := by
  intro a
  obtain ⟨b, hb⟩ := modulusRestrictionUnits_surjective c j w t
    (modulusBoundaryUnitsEquiv c i' (Over.mk t) a)
  refine ⟨(modulusBoundaryUnitsEquiv c i (Over.mk t)).symm b, ?_⟩
  apply (modulusBoundaryUnitsEquiv c i' (Over.mk t)).injective
  rw [modulusBoundaryUnitsEquiv_restriction c j w, MulEquiv.apply_symm_apply]
  exact hb

/-- The actual scalar-unit quotient restriction is also onto on every field-valued test. -/
theorem modulusUnitQuotientRestriction_field_surjective {L : Type u} [Field L]
    (t : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)) :
    Function.Surjective
      (modulusUnitQuotientRestriction (q := i ≫ c) (q' := i' ≫ c)
        j (by rw [← Category.assoc, ← w]) (Over.mk t)) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, hb⟩ := modulusUnitsRestriction_field_surjective c j w t a
  refine ⟨QuotientGroup.mk b, ?_⟩
  exact congrArg (fun a : ModulusUnits (i' ≫ c) (Over.mk t) =>
    (QuotientGroup.mk a : ModulusUnits (i' ≫ c) (Over.mk t) ⧸
      modulusScalars (i' ≫ c) (Over.mk t))) hb

end AlgebraicGeometry.GeneralizedJacobian
