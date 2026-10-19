/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarClasses
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionSheaf

/-! # Raw scalar extension for the actual extended relative divisor -/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- Raw classes for the actual extended divisor correspond to the original classes
over the composite parameter, including their full specified rigidifications. -/
def divisorScalarExtensionClassesEquiv {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of L)) :
    RigidifiedLineBundle.Classes
      (modulusBaseChange (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) t) ≃*
      RigidifiedLineBundle.Classes (modulusBaseChange c (modulusCurveMap D)
        (t ≫ specMap K L)) :=
  (modulusIsoClassesEquiv (baseChange K c L) (divisorScalarExtensionModulusIso D L)
    (divisorScalarExtensionModulusIso_square D L) t).symm.trans
      (scalarExtensionClassesEquiv c (modulusCurveMap D) L t)

/-- The actual transported divisor avoids the actual full extended relative divisor. -/
theorem divisorScalarExtensionSupported {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of L)) {n : ℕ}
    (E : RelEffCartierDiv c n (t ≫ specMap K L))
    (hE : E.SupportedIn (modulusComplement (modulusCurveMap D))) :
    ((RelEffCartierDiv.changeBaseEquiv c (specMap K L) t n).symm E).SupportedIn
      (modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))) :=
  (divisor_changeBaseEquiv_supported c (modulusCurveMap D) L t E hE).mono
    (modulusComplement_le_of_restriction (divisorScalarExtensionModulusIso D L).hom
      (divisorScalarExtensionModulusIso_square D L))

variable [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- The actual family class comparison preserves its normalized divisor section. -/
theorem divisorScalarExtensionClassesEquiv_divisorFamily {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of L)) {n : ℕ}
    (E : RelEffCartierDiv c n (t ≫ specMap K L))
    (hE : E.SupportedIn (modulusComplement (modulusCurveMap D))) :
    divisorScalarExtensionClassesEquiv c D L t
      (modulusDivisorFamilyClass (baseChange K c L)
        (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))
        ((RelEffCartierDiv.changeBaseEquiv c (specMap K L) t n).symm E)
        (divisorScalarExtensionSupported c D L t E hE)) =
      modulusDivisorFamilyClass c (modulusCurveMap D) E hE := by
  let hraw := divisor_changeBaseEquiv_supported c (modulusCurveMap D) L t E hE
  have h := modulusIsoClassesEquiv_divisorFamily (baseChange K c L)
    (divisorScalarExtensionModulusIso D L) (divisorScalarExtensionModulusIso_square D L)
    ((RelEffCartierDiv.changeBaseEquiv c (specMap K L) t n).symm E) hraw
  rw [divisorScalarExtensionClassesEquiv, MulEquiv.trans_apply]
  exact (congrArg (scalarExtensionClassesEquiv c (modulusCurveMap D) L t)
    ((modulusIsoClassesEquiv (baseChange K c L) (divisorScalarExtensionModulusIso D L)
      (divisorScalarExtensionModulusIso_square D L) t).symm_apply_eq.mpr h.symm)).trans
    (scalarExtensionClassesEquiv_divisorFamily c (modulusCurveMap D) L t E hE)

end AlgebraicGeometry.GeneralizedJacobian
