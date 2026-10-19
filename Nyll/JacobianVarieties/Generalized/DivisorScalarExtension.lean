/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.ChangeBaseSubscheme
import Nyll.JacobianVarieties.Generalized.ModulusFramePicard
import Nyll.JacobianVarieties.Generalized.ModulusScalarExtension

/-! # The full modulus of the actual scalar-extended relative divisor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The whole scalar-extended divisor, including all multiplicities, is the modulus pullback. -/
def divisorScalarExtensionModulusIso :
    (D.changeBaseOfIdentity (specMap K L)).I.subscheme ≅
      pullback (modulusCurveMap D ≫ c) (specMap K L) :=
  D.changeBaseOfIdentitySubschemeIso (specMap K L) ≪≫
    modulusFamilyDomainIso D (specMap K L)

/-- The isomorphism preserves the actual inclusions into the extended curve. -/
theorem divisorScalarExtensionModulusIso_square :
    modulusCurveMap (D.changeBaseOfIdentity (specMap K L)) =
      (divisorScalarExtensionModulusIso D L).hom ≫
        modulusBaseChange c (modulusCurveMap D) (specMap K L) := by
  change modulusCurveMap (D.changeBaseOfIdentity (specMap K L)) =
    ((D.changeBaseOfIdentitySubschemeIso (specMap K L)).hom ≫
      (modulusFamilyDomainIso D (specMap K L)).hom) ≫ _
  rw [Category.assoc, ← modulusFamilyDomainIso_square, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, modulusFamilyInclusion_fst,
      RelEffCartierDiv.changeBaseOfIdentitySubschemeIso_hom_fst_assoc]
    exact (RelEffCartierDiv.changeBaseOfIdentityMap_curve (specMap K L) D).symm
  · simp only [Category.assoc, modulusFamilyInclusion_snd,
      RelEffCartierDiv.changeBaseOfIdentitySubschemeIso_hom_snd]
    exact modulusCurveMap_toBase (D.changeBaseOfIdentity (specMap K L))

end AlgebraicGeometry.GeneralizedJacobian
