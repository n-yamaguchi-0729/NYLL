/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorScalarExtensionClasses
import Nyll.JacobianVarieties.Generalized.RigidifiedScalarNaturality

/-! # The actual scalar formula for the boundary under extension of the ground field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard.BaseChange

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- The actual scalar-extension equivalence restricts the actual modulus unit by pullback. -/
theorem scalarExtensionClassesEquiv_scalar {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R'))
    (a : Γ(pullback (modulusBaseChange c i (specMap R R') ≫ baseChange R c R') t, ⊤)ˣ) :
    scalarExtensionClassesEquiv c i R' t
        (RigidifiedLineBundle.scalarClass
          (modulusBaseChange (baseChange R c R') (modulusBaseChange c i (specMap R R')) t) a) =
      RigidifiedLineBundle.scalarClass (modulusBaseChange c i (t ≫ specMap R R'))
        (Units.map (modulusScalarExtensionIso c i R' t).inv.appTop.hom.toMonoidHom a) :=
  RigidifiedLineBundle.scalarClass_pullback (κ c R' t).inv
    (modulusScalarExtensionIso c i R' t).inv
    (RigidifiedLineBundle.inverse_square (κ c R' t) (modulusScalarExtensionIso c i R' t)
      (modulusScalarExtension_square c i R' t)) a

variable {D' : Scheme.{u}} {i' : D' ⟶ C} (e : D' ≅ D) (w : i' = e.hom ≫ i)

/-- Inverse transport along an actual whole-modulus isomorphism preserves the scalar formula. -/
theorem modulusIsoClassesEquiv_symm_scalar {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a : Γ(pullback (i' ≫ c) t, ⊤)ˣ) :
    (modulusIsoClassesEquiv c e w t).symm
        (RigidifiedLineBundle.scalarClass (modulusBaseChange c i' t) a) =
      RigidifiedLineBundle.scalarClass (modulusBaseChange c i t)
        (Units.map (modulusIsoPullback c e w t).inv.appTop.hom.toMonoidHom a) :=
  RigidifiedLineBundle.scalarClass_pullback (𝟙 _)
    (modulusIsoPullback c e w t).inv
    (RigidifiedLineBundle.inverse_square (Iso.refl _) (modulusIsoPullback c e w t)
      (modulusIsoPullback_square c e w t)) a

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The canonical comparison of the entire actual modulus on a parameter scheme. -/
def divisorScalarExtensionFamilyIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of L)) :
    pullback (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)) ≫ baseChange K c L) t ≅
      pullback (modulusCurveMap D ≫ c) (t ≫ specMap K L) :=
  modulusIsoPullback (baseChange K c L) (divisorScalarExtensionModulusIso D L)
    (divisorScalarExtensionModulusIso_square D L) t ≪≫
      modulusScalarExtensionIso c (modulusCurveMap D) L t

/-- The actual divisor comparison pulls scalar rigidifications by its actual whole-modulus map. -/
theorem divisorScalarExtensionClassesEquiv_scalar {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of L))
    (a : Γ(pullback (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)) ≫
      baseChange K c L) t, ⊤)ˣ) :
    divisorScalarExtensionClassesEquiv c D L t
        (RigidifiedLineBundle.scalarClass (modulusBaseChange (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) t) a) =
      RigidifiedLineBundle.scalarClass
        (modulusBaseChange c (modulusCurveMap D) (t ≫ specMap K L))
        (Units.map (divisorScalarExtensionFamilyIso D L t).inv.appTop.hom.toMonoidHom a) := by
  change scalarExtensionClassesEquiv c (modulusCurveMap D) L t
    ((modulusIsoClassesEquiv (baseChange K c L) (divisorScalarExtensionModulusIso D L)
      (divisorScalarExtensionModulusIso_square D L) t).symm
        (RigidifiedLineBundle.scalarClass (modulusBaseChange (baseChange K c L)
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) t) a)) = _
  rw [modulusIsoClassesEquiv_symm_scalar, scalarExtensionClassesEquiv_scalar]
  apply congrArg (RigidifiedLineBundle.scalarClass
    (modulusBaseChange c (modulusCurveMap D) (t ≫ specMap K L)))
  apply Units.ext
  change _ = (Scheme.Hom.appTop
    ((modulusScalarExtensionIso c (modulusCurveMap D) L t).inv ≫
      (modulusIsoPullback (baseChange K c L) (divisorScalarExtensionModulusIso D L)
        (divisorScalarExtensionModulusIso_square D L) t).inv)).hom a.val
  rw [Scheme.Hom.comp_appTop]
  rfl

end AlgebraicGeometry.GeneralizedJacobian
