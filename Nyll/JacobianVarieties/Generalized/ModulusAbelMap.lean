/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelZeroClass
import Nyll.JacobianVarieties.Generalized.Construction

/-!
# The pointed Abel morphism into the constructed generalized Jacobian

The canonically rigidified point-minus-basepoint family has proved Picard-zero
classes. Their actual fppf sheaf sections are classified by the group scheme
constructed without a rational point, for every effective modulus degree.
The selected point of the open complement maps to the group identity.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))

/-- The fppf group-sheaf class of the actual point-minus-basepoint family. -/
def modulusAbelZeroSheafClass {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.obj (op T) :=
  ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app (op T)).hom
      (modulusAbelZeroClass c (modulusCurveMap D) ε x)

/-- The classifying family respects every pullback of a point. -/
theorem modulusAbelZeroSheafClass_naturality
    {T T' : Over (Spec (CommRingCat.of K))} (f : T' ⟶ T)
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.map f.op
        (modulusAbelZeroSheafClass c D ε x) =
      modulusAbelZeroSheafClass c D ε (f ≫ x) := by
  let F := modulusPicardZeroGroupPresheaf c (modulusCurveMap D)
  let η₀ := toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) F
  let q : F.obj (op T) := modulusAbelZeroClass c (modulusCurveMap D) ε x
  have h := ConcreteCategory.congr_hom (η₀.naturality f.op) q
  exact h.symm.trans (congrArg (fun y : F.obj (op T') => η₀.app (op T') y)
    (modulusAbelZeroClass_naturality c (modulusCurveMap D) ε f x))

/-- The actual scheme morphism classifying the canonically rigidified point difference. -/
def modulusAbelMap :
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ (groupScheme c D).X :=
  (groupRepresentable c D).homEquiv.symm
    (modulusAbelZeroSheafClass c D ε (𝟙 _))

/-- Every test point is sent to the actual point-minus-basepoint modulus class. -/
theorem modulusAbelMap_classifies {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    (groupRepresentable c D).homEquiv (x ≫ modulusAbelMap c D ε) =
      modulusAbelZeroSheafClass c D ε x := by
  rw [(groupRepresentable c D).homEquiv_comp]
  change (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.map x.op
      ((groupRepresentable c D).homEquiv
        ((groupRepresentable c D).homEquiv.symm _)) = _
  rw [Equiv.apply_symm_apply]
  simpa only [Category.comp_id] using
    modulusAbelZeroSheafClass_naturality c D ε x (𝟙 _)

/-- At the selected point the actual rigidified line bundle is the tensor unit. -/
theorem modulusAbelZeroSheafClass_basepoint :
    modulusAbelZeroSheafClass c D ε ε = 1 := by
  unfold modulusAbelZeroSheafClass
  rw [modulusAbelZeroClass_basepoint]
  exact ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
    (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app
      (op (Over.mk (𝟙 (Spec (CommRingCat.of K)))))).hom.map_one

/-- The pointed Abel morphism carries its basepoint to the group-scheme identity. -/
theorem modulusAbelMap_basepoint : ε ≫ modulusAbelMap c D ε = 1 := by
  apply (groupRepresentable c D).homEquiv.injective
  rw [modulusAbelMap_classifies, modulusAbelZeroSheafClass_basepoint]
  symm
  cases d with
  | zero =>
    exact (SchemeTheory.RepresentedGroups.pointEquiv _
      (Unpointed.zeroDegreeGroupRepresentable c D)
        (Over.mk (𝟙 (Spec (CommRingCat.of K))))).map_one
  | succ n =>
    exact (SchemeTheory.RepresentedGroups.pointEquiv _
      (Unpointed.groupRepresentable c D (Nat.zero_lt_succ n))
        (Over.mk (𝟙 (Spec (CommRingCat.of K))))).map_one

end AlgebraicGeometry.GeneralizedJacobian
