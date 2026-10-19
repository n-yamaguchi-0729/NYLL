/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelFamily
import Nyll.JacobianVarieties.Generalized.PicardTranslation
import Nyll.JacobianVarieties.Generalized.PointedConstruction

/-!
# The represented Picard component selected by a point outside the modulus

An actual point of the open complement supplies the degree-one diagonal class.
Tensor translation identifies its component with the already constructed
Picard-zero scheme. The representation here is constructed, not assumed.
The choice-free degree-one sheaf and its descent are separate.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian.Pointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- A point of the actual modulus complement, expressed without support assumptions. -/
abbrev ComplementPoint :=
  Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)

/-- The same selected open-curve point supplies the section for Picard-zero existence. -/
def complementPointSection (ε : ComplementPoint c D) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c :=
  ⟨ε.left ≫ (modulusComplement (modulusCurveMap D)).ι,
    (Category.assoc _ _ _).trans (Over.w ε)⟩

/-- The selected class is the actual canonically rigidified diagonal evaluated at the point. -/
def complementPointClass (ε : ComplementPoint c D) :
    RigidifiedLineBundle.Classes
      (modulusBaseChange c (modulusCurveMap D) (𝟙 (Spec (CommRingCat.of K)))) :=
  (modulusAbelPresheafMap c (modulusCurveMap D)).app
    (op (Over.mk (𝟙 (Spec (CommRingCat.of K))))) (ULift.up ε)

/-- The actual component algebraically equivalent to the selected degree-one family. -/
def pointComponentSheaf (ε : ComplementPoint c D) :
    Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) (Type (u + 1)) :=
  modulusPicardTranslateSheaf c (modulusCurveMap D) (complementPointClass c D ε)

/-- The previously constructed carrier represents this pointed Picard component. -/
def pointComponentRepresentable (ε : ComplementPoint c D) (hd : 0 < d) :
    (pointComponentSheaf c D ε).obj.RepresentableBy
      (groupScheme c (complementPointSection c D ε) D hd).X :=
  (picardZeroRepresentable c (complementPointSection c D ε) D hd).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (Type (u + 1))).mapIso
        (modulusPicardTranslationSheafIso c (modulusCurveMap D)
          (complementPointClass c D ε)))

end AlgebraicGeometry.GeneralizedJacobian.Pointed
