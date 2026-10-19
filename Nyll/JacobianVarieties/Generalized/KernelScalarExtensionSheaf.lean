/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ExactSequence
import Nyll.JacobianVarieties.Generalized.ModulusForgetfulScalarExtension
import Mathlib.CategoryTheory.Sites.Limits

/-! # The canonical scalar-extension diagram of actual kernel group sheaves -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SmoothProperCurve SchemeTheory.Affine

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The actual identity homomorphisms are compatible with scalar extension. -/
theorem modulusForgetfulIdentitySheaf_divisorScalarExtension :
    (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom ≫
        (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
          (modulusForgetfulIdentitySheaf c (modulusCurveMap D)) =
      modulusForgetfulIdentitySheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) ≫
        (ordinaryZeroGroupSheafScalarExtensionIso c L).hom := by
  apply Sheaf.hom_ext
  ext T x
  change ((modulusForgetfulIdentitySheaf c (modulusCurveMap D)).hom.app
      (op ((Over.map (specMap K L)).obj T.unop))).hom
        (((modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom.hom.app T).hom x) =
    (((ordinaryZeroGroupSheafScalarExtensionIso c L).hom.hom.app T).hom
      (((modulusForgetfulIdentitySheaf (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).hom.app T).hom x))
  exact (modulusForgetfulIdentitySheaf_apply c (modulusCurveMap D)
    (op ((Over.map (specMap K L)).obj T.unop)) _).trans
      ((((ordinaryZeroGroupSheafScalarExtensionIso c L).hom.hom.app T).hom.map_one).symm.trans
        (congrArg ((ordinaryZeroGroupSheafScalarExtensionIso c L).hom.hom.app T).hom
          (modulusForgetfulIdentitySheaf_apply (baseChange K c L)
            (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) T x).symm))

/-- The actual forgetting and identity diagrams are isomorphic after field extension. -/
def modulusKernelDiagramScalarExtensionIso :
    parallelPair
        (forgetModulusZeroGroupSheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))))
        (modulusForgetfulIdentitySheaf (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))) ≅
      parallelPair
        ((Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
          (forgetModulusZeroGroupSheaf c (modulusCurveMap D)))
        ((Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
          (modulusForgetfulIdentitySheaf c (modulusCurveMap D))) :=
  parallelPairIso _ _ _ _ (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L)
    (ordinaryZeroGroupSheafScalarExtensionIso c L)
    (forgetModulusZeroGroupSheaf_divisorScalarExtension D L).symm
    (modulusForgetfulIdentitySheaf_divisorScalarExtension D L).symm

/-- Restriction to the extended slice preserves equalizers, as can be checked on presheaves. -/
private instance scalarExtension_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)) := by
  let P := Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)
  let V := sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
    CommGrpCat.{u + 1}
  have : PreservesLimitsOfShape WalkingParallelPair (P ⋙ V) := by
    change PreservesLimitsOfShape WalkingParallelPair
      (sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) CommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft _ _ CommGrpCat.{u + 1}).obj (Over.map (specMap K L)).op)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves P V

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The norm-open kernel sheaves have the canonical scalar-extension comparison determined
by the proved actual forgetting square and the actual kernel universal properties. -/
def kernelUnitSheafScalarExtensionIso :
    ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf L
        (modulusAlgebra (D.changeBaseOfIdentity (specMap K L))) ≅
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).obj
        (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)) :=
  IsLimit.conePointsIsoOfNatIso
    (modulusNormBoundarySheafIsKernel (D.changeBaseOfIdentity (specMap K L)))
    (isLimitForkMapOfIsLimit
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L))
      (modulusNormBoundarySheaf_condition D) (modulusNormBoundarySheafIsKernel D))
    (modulusKernelDiagramScalarExtensionIso D L)

/-- The canonical kernel comparison commutes with the actual scalar boundary. -/
@[reassoc] theorem kernelUnitSheafScalarExtensionIso_boundary :
    (kernelUnitSheafScalarExtensionIso D L).hom ≫
        (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
          (modulusNormBoundarySheaf D) =
      modulusNormBoundarySheaf (D.changeBaseOfIdentity (specMap K L)) ≫
        (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).hom :=
  IsLimit.conePointsIsoOfNatIso_hom_comp
    (modulusNormBoundarySheafIsKernel (D.changeBaseOfIdentity (specMap K L)))
    (isLimitForkMapOfIsLimit
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L))
      (modulusNormBoundarySheaf_condition D) (modulusNormBoundarySheafIsKernel D))
    (modulusKernelDiagramScalarExtensionIso D L) WalkingParallelPair.zero

/-- The inverse comparison also preserves the actual scalar boundary. -/
@[reassoc] theorem kernelUnitSheafScalarExtensionIso_inv_boundary :
    (kernelUnitSheafScalarExtensionIso D L).inv ≫
        modulusNormBoundarySheaf (D.changeBaseOfIdentity (specMap K L)) =
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L)).map
          (modulusNormBoundarySheaf D) ≫
        (modulusPicardZeroGroupSheaf_divisorScalarExtensionIso D L).inv :=
  IsLimit.conePointsIsoOfNatIso_inv_comp
    (modulusNormBoundarySheafIsKernel (D.changeBaseOfIdentity (specMap K L)))
    (isLimitForkMapOfIsLimit
      (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} (specMap K L))
      (modulusNormBoundarySheaf_condition D) (modulusNormBoundarySheafIsKernel D))
    (modulusKernelDiagramScalarExtensionIso D L) WalkingParallelPair.zero

end AlgebraicGeometry.GeneralizedJacobian
