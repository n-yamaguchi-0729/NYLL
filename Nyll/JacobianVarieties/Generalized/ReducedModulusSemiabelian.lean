/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ReducedModulusTorus
import Nyll.JacobianVarieties.Generalized.ModulusNormKernel
import Nyll.JacobianVarieties.Generalized.AbelianSchemeExamples
import Nyll.JacobianVarieties.Generalized.GroupProjectionGeometry
import Nyll.JacobianVarieties.Generalized.GroupProjectionSurjective
import Nyll.SchemeTheory.GroupSchemes.SemiabelianExamples

/-! # Actual semiabelian structure for a geometrically reduced modulus -/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [GeometricallyReduced (modulusBaseMap D)]

/-- The actual norm boundary and ordinary-Jacobian projection form the semiabelian
extension for a positive geometrically reduced modulus. -/
def reducedModulusSemiabelianExtension (hd : 0 < d) :
    SemiabelianExtension (groupScheme c D) where
  torus := modulusUnitQuotient D hd
  quotient := ordinaryGroupScheme c
  inclusion := modulusNormBoundary c D hd
  projection := groupProjection c D
  condition := modulusNormBoundary_condition c D hd
  isKernel := modulusNormBoundaryIsKernel c D hd
  projection_smooth := groupProjection_smooth c D
  projection_surjective := groupProjection_surjective c D

/-- The constructed generalized Jacobian is semiabelian for every geometrically reduced
modulus, including the empty modulus. -/
instance groupScheme_isSemiabelian_of_geometricallyReduced : IsSemiabelian (groupScheme c D) := by
  cases d with
  | zero => infer_instance
  | succ n =>
      exact (reducedModulusSemiabelianExtension c D (Nat.zero_lt_succ n)).isSemiabelian

end AlgebraicGeometry.GeneralizedJacobian
