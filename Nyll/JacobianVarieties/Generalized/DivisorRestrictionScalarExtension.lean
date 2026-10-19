/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusRestrictionScalarExtension
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionClasses

/-! # The same actual divisor comparison preserves restriction of rigidifications -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d d' : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (D' : RelEffCartierDiv c d' (𝟙 (Spec (CommRingCat.of K))))
  (j : D'.I.subscheme ⟶ D.I.subscheme)
  (w : modulusCurveMap D' = j ≫ modulusCurveMap D)
  (L : Type u) [Field L] [Algebra K L]

/-- The scalar extension of the given full-modulus morphism on the actual relative divisors. -/
def divisorRestrictionScalarMap :
    (D'.changeBaseOfIdentity (specMap K L)).I.subscheme ⟶
      (D.changeBaseOfIdentity (specMap K L)).I.subscheme :=
  (divisorScalarExtensionModulusIso D' L).hom ≫
    modulusRestrictionScalarMap c j w L ≫ (divisorScalarExtensionModulusIso D L).inv

/-- The map is over the actual scalar-extended curve. -/
theorem divisorRestrictionScalarMap_square :
    modulusCurveMap (D'.changeBaseOfIdentity (specMap K L)) =
      divisorRestrictionScalarMap D D' j w L ≫
        modulusCurveMap (D.changeBaseOfIdentity (specMap K L)) := by
  rw [divisorScalarExtensionModulusIso_square D' L,
    divisorScalarExtensionModulusIso_square D L]
  simp only [divisorRestrictionScalarMap, Category.assoc, Iso.inv_hom_id_assoc,
    ← modulusRestrictionScalarMap_square]

/-- The same full-divisor class equivalence used by group, torsor and kernel comparison
commutes with restriction of the chosen rigidification. -/
theorem divisorScalarExtensionClassesEquiv_restriction {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of L))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange (baseChange K c L)
      (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) t)) :
    divisorScalarExtensionClassesEquiv c D' L t
      (modulusRestrictionClasses (baseChange K c L) (divisorRestrictionScalarMap D D' j w L)
        (divisorRestrictionScalarMap_square D D' j w L) t x) =
      modulusRestrictionClasses c j w (t ≫ specMap K L)
        (divisorScalarExtensionClassesEquiv c D L t x) := by
  let c' := baseChange K c L
  let a := divisorScalarExtensionModulusIso D L
  let b := divisorScalarExtensionModulusIso D' L
  let j' := modulusRestrictionScalarMap c j w L
  let j'' := divisorRestrictionScalarMap D D' j w L
  have wa : modulusBaseChange c (modulusCurveMap D) (specMap K L) =
      a.inv ≫ modulusCurveMap (D.changeBaseOfIdentity (specMap K L)) := by
    rw [divisorScalarExtensionModulusIso_square D L, a.inv_hom_id_assoc]
  have wb : modulusBaseChange c (modulusCurveMap D') (specMap K L) =
      b.inv ≫ modulusCurveMap (D'.changeBaseOfIdentity (specMap K L)) := by
    rw [divisorScalarExtensionModulusIso_square D' L, b.inv_hom_id_assoc]
  have hcomp : b.inv ≫ j'' = j' ≫ a.inv := by
    change b.inv ≫ (b.hom ≫ j' ≫ a.inv) = _
    exact b.inv_hom_id_assoc _
  have hres :
      (modulusIsoClassesEquiv c' b (divisorScalarExtensionModulusIso_square D' L) t).symm
        (modulusRestrictionClasses c' j'' (divisorRestrictionScalarMap_square D D' j w L)
          t x) =
      modulusRestrictionClasses c' j' (modulusRestrictionScalarMap_square c j w L) t
        ((modulusIsoClassesEquiv c' a (divisorScalarExtensionModulusIso_square D L) t).symm
          x) := by
    change modulusRestrictionClasses c' b.inv wb t
      (modulusRestrictionClasses c' j'' _ t x) =
        modulusRestrictionClasses c' j' _ t (modulusRestrictionClasses c' a.inv wa t x)
    rw [modulusRestrictionClasses_comp, modulusRestrictionClasses_comp]
    simp only [hcomp]
  change scalarExtensionClassesEquiv c (modulusCurveMap D') L t _ =
    modulusRestrictionClasses c j w (t ≫ specMap K L)
      (scalarExtensionClassesEquiv c (modulusCurveMap D) L t _)
  exact (congrArg (scalarExtensionClassesEquiv c (modulusCurveMap D') L t) hres).trans
    (scalarExtensionClassesEquiv_restriction c j w L t _)

end AlgebraicGeometry.GeneralizedJacobian
