/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFamilyIdeal
import Nyll.JacobianVarieties.Generalized.RigidifiedSquareEquivalence
import Nyll.JacobianVarieties.Generalized.RigidifiedIdealPullbackComparison

/-! # Recovering the original full-modulus class from the canonical ideal family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))

/-- The actual ideal-family identification preserves the rigidified tensor group. -/
def modulusFamilyIdealClassesEquiv :
    RigidifiedLineBundle.Classes (modulusBaseChange c (modulusCurveMap D) t) ≃*
      RigidifiedLineBundle.Classes (modulusFamilyDivisor D t).I.subschemeι :=
  RigidifiedLineBundle.classesPullbackMulEquiv (Iso.refl _) (modulusFamilyIdealIso D t)
    (modulusFamilyIdealIso_square D t)

/-- Avoidance of the canonical ideal family is avoidance of the original full modulus. -/
theorem modulusFamilyAvoidance (I : (pullback c t).IdealSheafData)
    (ha : ∀ y : (modulusFamilyDivisor D t).I.subscheme,
      (modulusFamilyDivisor D t).I.subschemeι.base y ∉ I.support) :
    ∀ y : (pullback (modulusCurveMap D ≫ c) t : Scheme.{u}),
      (modulusBaseChange c (modulusCurveMap D) t).base y ∉ I.support := by
  have hw : modulusBaseChange c (modulusCurveMap D) t =
      (modulusFamilyIdealIso D t).inv ≫ (modulusFamilyDivisor D t).I.subschemeι :=
    (Category.comp_id _).symm.trans (RigidifiedLineBundle.inverse_square (Iso.refl _)
      (modulusFamilyIdealIso D t) (modulusFamilyIdealIso_square D t))
  intro y
  rw [hw, Scheme.Hom.comp_apply]
  exact ha _

/-- The comparison carries the specified canonical frame to the specified canonical frame. -/
theorem modulusFamilyIdealClassesEquiv_ofInvertibleIdeal
    (I : (pullback c t).IdealSheafData) (hI : I.IsInvertible)
    (ha : ∀ y : (modulusFamilyDivisor D t).I.subscheme,
      (modulusFamilyDivisor D t).I.subschemeι.base y ∉ I.support) :
    modulusFamilyIdealClassesEquiv D t
        (RigidifiedLineBundle.classOf (RigidifiedLineBundle.ofInvertibleIdeal
          (modulusBaseChange c (modulusCurveMap D) t) I hI (modulusFamilyAvoidance D t I ha))) =
      RigidifiedLineBundle.classOf (RigidifiedLineBundle.ofInvertibleIdeal
        (modulusFamilyDivisor D t).I.subschemeι I hI ha) := by
  apply (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
  exact ⟨RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq
    (𝟙 _) (modulusFamilyIdealIso D t).hom (modulusFamilyIdealIso_square D t)
    I hI (modulusFamilyAvoidance D t I ha) I hI ha (Scheme.IdealSheafData.comap_id I)⟩

/-- The compatible isomorphism over the canonical ideal family gives the original one. -/
theorem modulusFamilyIdeal_tensorIso
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) t))
    (I J : (pullback c t).IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (ha : ∀ y : (modulusFamilyDivisor D t).I.subscheme,
      (modulusFamilyDivisor D t).I.subschemeι.base y ∉ I.support)
    (hb : ∀ y : (modulusFamilyDivisor D t).I.subscheme,
      (modulusFamilyDivisor D t).I.subschemeι.base y ∉ J.support)
    (he : Nonempty (RigidifiedLineBundle.Iso
      ((modulusFamilyIdealBundle D t M).tensor (RigidifiedLineBundle.ofInvertibleIdeal
        (modulusFamilyDivisor D t).I.subschemeι I hI ha))
      (RigidifiedLineBundle.ofInvertibleIdeal (modulusFamilyDivisor D t).I.subschemeι J hJ hb))) :
    Nonempty (RigidifiedLineBundle.Iso
      (M.tensor (RigidifiedLineBundle.ofInvertibleIdeal
        (modulusBaseChange c (modulusCurveMap D) t) I hI (modulusFamilyAvoidance D t I ha)))
      (RigidifiedLineBundle.ofInvertibleIdeal
        (modulusBaseChange c (modulusCurveMap D) t) J hJ (modulusFamilyAvoidance D t J hb))) := by
  apply (RigidifiedLineBundle.classOf_eq_iff _ _).mp
  apply (modulusFamilyIdealClassesEquiv D t).injective
  change modulusFamilyIdealClassesEquiv D t
      (RigidifiedLineBundle.classOf M * RigidifiedLineBundle.classOf
        (RigidifiedLineBundle.ofInvertibleIdeal
          (modulusBaseChange c (modulusCurveMap D) t) I hI (modulusFamilyAvoidance D t I ha))) =
    modulusFamilyIdealClassesEquiv D t (RigidifiedLineBundle.classOf
      (RigidifiedLineBundle.ofInvertibleIdeal
        (modulusBaseChange c (modulusCurveMap D) t) J hJ (modulusFamilyAvoidance D t J hb)))
  rw [map_mul, modulusFamilyIdealClassesEquiv_ofInvertibleIdeal D t I hI ha,
    modulusFamilyIdealClassesEquiv_ofInvertibleIdeal D t J hJ hb]
  exact (RigidifiedLineBundle.classOf_eq_iff _ _).mpr he

end AlgebraicGeometry.GeneralizedJacobian
