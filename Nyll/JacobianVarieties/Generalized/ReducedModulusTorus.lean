/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ReducedModulusAlgebra
import Nyll.JacobianVarieties.Generalized.ModulusNormScalarExtension
import Nyll.SchemeTheory.Affine.WeilRestriction.SplitScalarQuotientTorus
import Nyll.SchemeTheory.CategoryTheory.RepresentedGroupPullbackIso
import Nyll.SchemeTheory.GroupSchemes.Torus

/-! # The actual norm-boundary group of a geometrically reduced modulus is a torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry.SmoothProperCurve SchemeTheory.Affine

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

/-- Over an algebraically closed field the actual reduced-modulus norm quotient
is the split torus of precisely the full divisor degree minus one. -/
def reducedModulusNormIso [IsAlgClosed K] [IsReduced D.I.subscheme] :
    modulusUnitQuotient D hd ≅ GroupSchemes.splitTorus K (d - 1) :=
  ScalarQuotientSchemePresheaf.splitScalarQuotientTorusIso
    (positiveReducedModulusAlgebraSplit D hd) (positiveModulusBasis D hd)

variable (c) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The scalar comparison preserves the actual pullback group operation. -/
def modulusNormActualScalarExtensionIso (L : Type u) [Field L] [Algebra K L] :
    (GroupSchemes.baseChange (specMap K L)).obj (modulusUnitQuotient D hd) ≅
      modulusUnitQuotient (D.changeBaseOfIdentity (specMap K L)) hd :=
  SchemeTheory.RepresentedGroups.groupObjectPullbackIso (specMap K L)
    (ScalarQuotientSchemePresheaf.scalarQuotientGroupSheaf K (modulusAlgebra D)).obj
    (modulusUnitQuotientRepresentable D hd) ≪≫ modulusNormGroupScalarExtensionIso c D hd L

/-- Geometric reducedness of the original actual divisor supplies a torus kernel
with constant geometric rank `degree - 1`. -/
instance modulusUnitQuotient_isTorus [GeometricallyReduced (modulusBaseMap D)] :
    IsTorus (modulusUnitQuotient D hd) := by
  refine ⟨d - 1, fun Ω _ _ f => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  let : Algebra K Ω := φ.hom.toAlgebra
  have : IsReduced (D.changeBaseOfIdentity (specMap K Ω)).I.subscheme :=
    modulus_changeBase_isReduced D (specMap K Ω)
  change Nonempty ((GroupSchemes.baseChange (specMap K Ω)).obj (modulusUnitQuotient D hd) ≅
    GroupSchemes.splitTorus Ω (d - 1))
  exact ⟨modulusNormActualScalarExtensionIso c D hd Ω ≪≫
    reducedModulusNormIso (D.changeBaseOfIdentity (specMap K Ω)) hd⟩

/-- The group carried by the literal identity fibre is a torus through its actual norm iso. -/
instance kernelGroupScheme_isTorus [GeometricallyReduced (modulusBaseMap D)] :
    IsTorus (kernelGroupScheme c D hd) :=
  IsTorus.of_iso (kernelGroupIso c D hd).symm

end AlgebraicGeometry.GeneralizedJacobian
