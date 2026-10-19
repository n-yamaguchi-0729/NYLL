/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PointedConstruction
import Nyll.JacobianVarieties.Generalized.EmptyModulusZero
import Nyll.JacobianVarieties.Generalized.ModulusDegreeZero
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupIso

/-! # The degree-zero modulus recovers the ordinary Picard group scheme -/

noncomputable section

universe u

open CategoryTheory NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian.Pointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K))))

/-- The full degree-zero modulus is proved empty, so its actual group sheaf is ordinary Picard. -/
def zeroDegreeSheafIso :
    modulusPicardZeroGroupSheaf c (modulusCurveMap D) ≅
      ordinaryRelativePicardZeroGroupSheaf c := by
  let : IsEmpty D.I.subscheme := isEmpty_modulus_of_degree_zero D
  exact EmptyModulus.ordinaryPicardZeroGroupSheafIso c (modulusCurveMap D)

/-- The ordinary carrier represents the actual degree-zero modulus group sheaf. -/
def zeroDegreeGroupRepresentable :
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (Over.mk (ordinaryPicard c ε).toBase) :=
  (ordinaryZeroGroupSheafRepresentable (ordinaryRepresentation c ε)).ofIso
    (Functor.isoWhiskerRight
      ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        CommGrpCat.{u + 1}).mapIso (zeroDegreeSheafIso c D).symm)
      (forget CommGrpCat.{u + 1}))

/-- The degree-zero modulus has its represented tensor group on the ordinary Picard carrier. -/
def zeroDegreeGroupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  SchemeTheory.RepresentedGroups.groupObject
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    (zeroDegreeGroupRepresentable c ε D)

/-- Forgetting the empty modulus gives an actual group-scheme isomorphism. -/
def zeroDegreeOrdinaryIso :
    zeroDegreeGroupScheme c ε D ≅ ordinaryZeroCommGroupScheme (ordinaryRepresentation c ε) :=
  SchemeTheory.RepresentedGroups.iso _ _ (zeroDegreeGroupRepresentable c ε D)
    (ordinaryZeroGroupSheafRepresentable (ordinaryRepresentation c ε))
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      CommGrpCat.{u + 1}).mapIso (zeroDegreeSheafIso c D))

/-- In degree zero the genus dimension is retained, and the constructed group is proper. -/
theorem zeroDegreeGeometry :
    SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K c)
        (zeroDegreeGroupScheme c ε D).X.hom ∧
      IsProper (zeroDegreeGroupScheme c ε D).X.hom ∧
      GeometricallyConnected (zeroDegreeGroupScheme c ε D).X.hom := by
  let J := ordinaryPicard c ε
  have : Smooth J.toBase := (exists_representsRelSubPic_of_field K c ε).choose_spec.2.1
  have : IsProper J.toBase := (exists_representsRelSubPic_of_field K c ε).choose_spec.2.2.1
  have : GeometricallyConnected J.toBase :=
    (exists_representsRelSubPic_of_field K c ε).choose_spec.2.2.2
  change SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K c) J.toBase ∧
    IsProper J.toBase ∧ GeometricallyConnected J.toBase
  exact ⟨(ordinaryRepresentation c ε).smoothOfRelativeDimension_geometricGenus,
    inferInstance, inferInstance⟩

end AlgebraicGeometry.GeneralizedJacobian.Pointed
