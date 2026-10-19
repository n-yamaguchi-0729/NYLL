/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusEmptyRegularMap
import Nyll.JacobianVarieties.Generalized.GeometricModulusScalarExtension
import Nyll.JacobianVarieties.Generalized.PicardOneAbelEquivariantUniqueness
import Nyll.JacobianVarieties.Generalized.PicardOneEquivariantMap
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates

/-! # Regular torsor maps from the full modulus condition

Over an algebraically closed field, a regular map to a commutative group torsor
with any effective modulus factors uniquely through the intrinsic Picard-one torsor.
The group morphism is constructed from the actual coordinate map's modulus;
neither a group factor nor a torsor factor is assumed.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
  (Q : Over (Spec (CommRingCat.of K))) [ModObj H.X Q]
  [IsIso (ModObj.leftSMul H.X Q)]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ Q)

/-- The actual coordinate modulus constructs the unique pair of group and
equivariant torsor morphisms factoring the original regular curve map. -/
theorem existsUnique_picardOneMapFromModulus :
    let q₀ : SchemeHomOver
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) H.X.hom :=
      (commGroupPointEquiv H
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
        (q ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) (ε ≫ q))
    M.regularMapHasModulus D H q₀ →
      ∃! fg : (groupScheme M.toBase D ⟶ H) × (picardOne M.toBase D ⟶ Q),
        abelOneMap M.toBase D ≫ fg.2 = q ∧
          ∀ (T : Over (Spec (CommRingCat.of K)))
            (a : T ⟶ (groupScheme M.toBase D).X) (x : T ⟶ picardOne M.toBase D),
            (a • x) ≫ fg.2 = (a ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  intro q₀ hmod
  have hε : ε ≫ Over.homMk q₀.1 q₀.2 = 1 := by
    change ε ≫ (q ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) (ε ≫ q)) = 1
    rw [← Category.assoc]
    simpa only [toUnit_unit, Category.id_comp] using
      SchemeTheory.PointedTorsor.coordinate_basepoint (G := H.X) (ε ≫ q)
        (𝟙_ (Over (Spec (CommRingCat.of K))))
  obtain ⟨φ, hφ, _⟩ := M.existsUnique_groupHom_fullModulus D ε H q₀ hmod hε
  exact picardOneEquivariantMap_factors_uniquely M.toBase D ε q φ hφ


/-- Over an algebraically closed field, the intrinsic torsor modulus
constructs the unique equivariant Abel factor in every degree. A point of
the curve and its image in the target are supplied internally. -/
theorem existsUnique_picardOneMapFromGeometricModulus
    (hmod : geometricTorsorMapHasModulus M.toBase D H Q q) :
    ∃! fg : (groupScheme M.toBase D ⟶ H) × (picardOne M.toBase D ⟶ Q),
      abelOneMap M.toBase D ≫ fg.2 = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
            (a : T ⟶ (groupScheme M.toBase D).X) (x : T ⟶ picardOne M.toBase D),
          (a • x) ≫ fg.2 = (a ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  obtain ⟨ε₀⟩ := modulusComplement_point M.toBase D
  let q₀ : SchemeHomOver
      ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) H.X.hom :=
    (commGroupPointEquiv H
      ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
        (q ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) (ε₀ ≫ q))
  have hcoord : geometricRegularMapHasModulus M.toBase D H (Over.homMk q₀.1 q₀.2) :=
    (geometricTorsorMapHasModulus_iff_coordinate M.toBase D H Q q (ε₀ ≫ q)).mp hmod
  exact M.existsUnique_picardOneMapFromModulus D ε₀ H Q q
    ((M.geometricRegularMapHasModulus_iff D H q₀).mp hcoord)

end AlgebraicCurve.CurveModel
