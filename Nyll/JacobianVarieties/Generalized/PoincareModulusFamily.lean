/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFrameSheaf
import Nyll.JacobianVarieties.Generalized.PoincareTotalFamily
import Nyll.SchemeTheory.WeilRestriction.RelativeTotalMap

/-!
# The total Poincaré frame family has actual modulus Picard classes

The relative frame classification gives a natural map over the original field.
Its universal value on the constructed frame scheme pulls back to the class of
every represented frame-family section. Picard-zero classification is separate.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open SchemeTheory.WeilRestriction AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {P : SubPicCondition c ε} {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P J)

/-- The total Poincaré frame family classifies actual modulus Picard sheaf sections. -/
def poincareFrameTotalToModulusPicard :
    poincareFrameTotalFamily D h ⟶ (modulusPicardSheaf c (modulusCurveMap D)).obj :=
  relativeTotalDesc.{u, u + 1} J.toBase
    (modulusFrameSheafToPicard D J.toBase h.poincare.isInvertible).hom

/-- The constructed frame scheme carries its actual universal modulus Picard sheaf class. -/
def poincareFrameQuotientModulusClass (hd : 0 < d) :
    (modulusPicardSheaf c (modulusCurveMap D)).obj.obj
      (op ((Over.map J.toBase).obj (poincareFrameQuotient D h hd))) :=
  (poincareFrameTotalToModulusPicard D h).app _
    ((poincareFrameTotalRepresentable D h hd).homEquiv (𝟙 _))

/-- The universal class pulls back to the actual class of every represented family section. -/
theorem poincareFrameTotalToModulusPicard_homEquiv (hd : 0 < d)
    {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (Over.map J.toBase).obj (poincareFrameQuotient D h hd)) :
    (poincareFrameTotalToModulusPicard D h).app (op T)
        ((poincareFrameTotalRepresentable D h hd).homEquiv f) =
      (modulusPicardSheaf c (modulusCurveMap D)).obj.map f.op
        (poincareFrameQuotientModulusClass D h hd) :=
  (poincareFrameTotalRepresentable D h hd).natTrans_homEquiv
    (poincareFrameTotalToModulusPicard D h) f

end AlgebraicGeometry.GeneralizedJacobian
