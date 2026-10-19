/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareModulusFamily
import Nyll.JacobianVarieties.Generalized.ModulusFramesZero

/-!
# The Poincaré frame scheme maps to the modulus Picard-zero sheaf

The zero condition is supplied by the actual ordinary Picard-zero representation.
This constructs the natural map and its universal sheaf class. Proving that this
map is an isomorphism, and hence obtaining generalized Jacobian representation,
remains separate.
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
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c] in
/-- The actual ordinary Poincaré family is algebraically trivial on geometric fibres. -/
theorem poincareUnderlying_fibrewiseZero :
    Unrigidified.FibrewiseZero
      (⟨h.poincare.L, h.poincare.isInvertible⟩ : Unrigidified.LineBundle c J.toBase) :=
  h.poincare_mem

/-- The actual total frame family maps naturally into the modulus Picard-zero sheaf. -/
def poincareFrameTotalToModulusPicardZero :
    poincareFrameTotalFamily D h ⟶ (modulusPicardZeroSheaf c (modulusCurveMap D)).obj :=
  relativeTotalDesc.{u, u + 1} J.toBase
    (modulusFrameSheafToPicardZero D J.toBase h.poincare.isInvertible
      (poincareUnderlying_fibrewiseZero h)).hom

/-- The candidate frame scheme carries its actual universal modulus Picard-zero sheaf class. -/
def poincareFrameQuotientModulusZeroClass (hd : 0 < d) :
    (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj
      (op ((Over.map J.toBase).obj (poincareFrameQuotient D h hd))) :=
  (poincareFrameTotalToModulusPicardZero D h).app _
    ((poincareFrameTotalRepresentable D h hd).homEquiv (𝟙 _))

/-- Pulling back that universal zero class gives the actual class of each frame-family section. -/
theorem poincareFrameTotalToModulusPicardZero_homEquiv (hd : 0 < d)
    {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (Over.map J.toBase).obj (poincareFrameQuotient D h hd)) :
    (poincareFrameTotalToModulusPicardZero D h).app (op T)
        ((poincareFrameTotalRepresentable D h hd).homEquiv f) =
      (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map f.op
        (poincareFrameQuotientModulusZeroClass D h hd) :=
  (poincareFrameTotalRepresentable D h hd).natTrans_homEquiv
    (poincareFrameTotalToModulusPicardZero D h) f

end AlgebraicGeometry.GeneralizedJacobian
