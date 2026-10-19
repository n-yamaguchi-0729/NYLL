/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusAbelOneMap
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionScheme

/-! # The intrinsic Abel scheme square for the actual scalar-extended divisor -/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in
/-- The inverse whole-divisor isomorphism preserves its inclusion into the curve. -/
theorem divisorScalarExtensionModulusIso_inv_square :
    modulusBaseChange c (modulusCurveMap D) (specMap K L) =
      (divisorScalarExtensionModulusIso D L).inv ≫
        modulusCurveMap (D.changeBaseOfIdentity (specMap K L)) := by
  rw [divisorScalarExtensionModulusIso_square, Iso.inv_hom_id_assoc]

/-- A point of the actual extended complement gives its original point over the original base. -/
def divisorScalarExtensionPoint {T : Over (Spec (CommRingCat.of L))}
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    (Over.map (specMap K L)).obj T ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
  modulusScalarExtensionPoint c (modulusCurveMap D) L
    (P ≫ modulusComplementRestriction (baseChange K c L)
      (divisorScalarExtensionModulusIso D L).inv
      (divisorScalarExtensionModulusIso_inv_square c D L))

/-- The raw degree-one comparison preserves the actual Abel family for the extended divisor. -/
theorem modulusAbelOnePresheafMap_divisorScalarExtension
    {T : Over (Spec (CommRingCat.of L))}
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    (modulusPicardOne_divisorScalarExtensionIso D L).hom.app (op T)
        ((modulusAbelOnePresheafMap (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).app (op T) (ULift.up P)) =
      (modulusAbelOnePresheafMap c (modulusCurveMap D)).app
        (op ((Over.map (specMap K L)).obj T)) (ULift.up (divisorScalarExtensionPoint c D L P)) := by
  apply Subtype.ext
  change scalarExtensionClassesEquiv c (modulusCurveMap D) L T.hom
      (modulusRestrictionClasses (baseChange K c L)
        (divisorScalarExtensionModulusIso D L).inv
        (divisorScalarExtensionModulusIso_inv_square c D L) T.hom
          (modulusAbelPointClass (baseChange K c L)
            (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) (T := T) P)) = _
  rw [modulusRestrictionClasses_abelPoint]
  exact scalarExtensionClassesEquiv_abelPoint c (modulusCurveMap D) L _

/-- Sheafification retains the exact Abel compatibility for the full extended divisor. -/
theorem modulusAbelOneSheafMap_divisorScalarExtension
    {T : Over (Spec (CommRingCat.of L))}
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)
        ((modulusAbelOneSheafMap (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).app (op T) (ULift.up P)) =
      (modulusAbelOneSheafMap c (modulusCurveMap D)).app
        (op ((Over.map (specMap K L)).obj T)) (ULift.up (divisorScalarExtensionPoint c D L P)) := by
  let z := (modulusAbelOnePresheafMap (baseChange K c L)
    (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).app (op T) (ULift.up P)
  have h := congrArg (fun α => α.app (op T) z)
    (toSheafify_modulusPicardOne_divisorScalarExtension D L)
  change (modulusPicardOneSheaf_divisorScalarExtensionIso D L).hom.hom.app (op T)
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
        (modulusPicardOnePresheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))))).app (op T) z) =
    (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardOnePresheaf c (modulusCurveMap D))).app
        (op ((Over.map (specMap K L)).obj T))
          ((modulusPicardOne_divisorScalarExtensionIso D L).hom.app (op T) z) at h
  exact h.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardOnePresheaf c (modulusCurveMap D))).app
        (op ((Over.map (specMap K L)).obj T)))
    (modulusAbelOnePresheafMap_divisorScalarExtension c D L P))

/-- The actual Abel morphism commutes with the canonical scalar-extension scheme isomorphism. -/
theorem abelOneMap_scalarExtension {T : Over (Spec (CommRingCat.of L))}
    (P : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    (Over.mapPullbackAdj (specMap K L)).homEquiv T (picardOne c D)
        (divisorScalarExtensionPoint c D L P ≫ abelOneMap c D) ≫
      (picardOneScalarExtensionIso c D L).hom =
        P ≫ abelOneMap (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) := by
  let f := (Over.mapPullbackAdj (specMap K L)).homEquiv T (picardOne c D)
    (divisorScalarExtensionPoint c D L P ≫ abelOneMap c D)
  have hf : (picardOneScalarExtensionRepresentable c D L).homEquiv f =
      (modulusAbelOneSheafMap c (modulusCurveMap D)).app
        (op ((Over.map (specMap K L)).obj T)) (ULift.up (divisorScalarExtensionPoint c D L P)) := by
    change (picardOneRepresentable c D).homEquiv
      (((Over.mapPullbackAdj (specMap K L)).homEquiv T (picardOne c D)).symm
        (((Over.mapPullbackAdj (specMap K L)).homEquiv T (picardOne c D)) _)) = _
    rw [Equiv.symm_apply_apply]
    exact abelOneMap_classifies c D _
  let e := ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
    (Type (u + 1))).mapIso (modulusPicardOneSheaf_divisorScalarExtensionIso D L)).app (op T)
  apply (picardOneRepresentable (baseChange K c L)
    (D.changeBaseOfIdentity (specMap K L))).homEquiv.injective
  refine (picardOneScalarExtensionIso_homEquiv c D L f).trans ?_
  rw [hf, ← modulusAbelOneSheafMap_divisorScalarExtension c D L P]
  exact (Iso.hom_inv_id_apply e _).trans
    (abelOneMap_classifies (baseChange K c L)
      (D.changeBaseOfIdentity (specMap K L)) P).symm

end AlgebraicGeometry.GeneralizedJacobian
