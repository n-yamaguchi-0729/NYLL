/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Topology.FppfAlgebraicallyClosedPoint
import Nyll.JacobianVarieties.Generalized.ModulusAbelMap

/-!
# Actual rigidified classes and generalized Jacobian points over a closed field

Fppf sheafification is bijective on an algebraically closed field-valued test.
Combined with the constructed representative, this identifies the naive group
of actual degree-zero modulus-rigidified line bundles with the rational points
of the generalized Jacobian. The comparison sends the actual canonical point
difference to the value of the constructed Abel morphism.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] [IsAlgClosed K] {C E : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : E ⟶ C)

/-- On the ground algebraically closed field, every fppf class is represented
by an actual rigidified line bundle, uniquely up to compatible isomorphism. -/
def modulusPicardZeroFieldEquiv :
    modulusPicardZeroSubgroup c i (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≃*
      (modulusPicardZeroGroupSheaf c i).obj.obj
        (op (Over.mk (𝟙 (Spec (CommRingCat.of K))))) := by
  let a := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (modulusPicardZeroGroupPresheaf c i)
  exact MulEquiv.ofBijective
    (a.app (op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))).hom
    (Scheme.fppf_locallyBijective_app_bijective
      (Functor.whiskerRight a (forget CommGrpCat.{u + 1}))
      (𝟙 (Spec (CommRingCat.of K))))

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual naive degree-zero modulus classes identify with the rational
points of the already constructed generalized Jacobian, as groups. -/
def rigidifiedZeroClassPointEquiv :
    modulusPicardZeroSubgroup c (modulusCurveMap D)
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≃*
        (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme c D).X) :=
  (modulusPicardZeroFieldEquiv c (modulusCurveMap D)).trans
    (pointEquiv c D (Over.mk (𝟙 (Spec (CommRingCat.of K))))).symm

/-- The comparison classifies the same sheafification of each actual bundle. -/
theorem rigidifiedZeroClassPointEquiv_classifies
    (x : modulusPicardZeroSubgroup c (modulusCurveMap D)
      (Over.mk (𝟙 (Spec (CommRingCat.of K))))) :
    (pointEquiv c D (Over.mk (𝟙 (Spec (CommRingCat.of K)))))
        (rigidifiedZeroClassPointEquiv c D x) =
      ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
        (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app
          (op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))) x := by
  change (pointEquiv c D (Over.mk (𝟙 (Spec (CommRingCat.of K)))))
      ((pointEquiv c D (Over.mk (𝟙 (Spec (CommRingCat.of K))))).symm _) = _
  exact (pointEquiv c D (Over.mk (𝟙 (Spec (CommRingCat.of K))))).apply_symm_apply _

/-- The actual point-minus-basepoint bundle corresponds to the value of the
actual Abel morphism, with its full modulus normalization. -/
theorem rigidifiedZeroClassPointEquiv_abel
    (ε x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    rigidifiedZeroClassPointEquiv c D
        (modulusAbelZeroClass c (modulusCurveMap D) ε x) =
      x ≫ modulusAbelMap c D ε := by
  apply (pointEquiv c D (Over.mk (𝟙 (Spec (CommRingCat.of K))))).injective
  rw [rigidifiedZeroClassPointEquiv_classifies]
  cases d with
  | zero => exact (modulusAbelMap_classifies c D ε x).symm
  | succ n => exact (modulusAbelMap_classifies c D ε x).symm

end AlgebraicGeometry.GeneralizedJacobian
