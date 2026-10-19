/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareModulusZero

/-!
# The total Poincaré frame presheaf before relative sheafification

Elements retain an actual parameter map and a scalar class of an actual frame.
They map to the represented frame family and to actual modulus Picard-zero
classes. Local classification of these maps is kept separate.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open SchemeTheory.WeilRestriction AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)

/-- The total actual scalar-frame presheaf before relative fppf sheafification. -/
def poincareRawFrameFamily : (Over (Spec (CommRingCat.of K)))ᵒᵖ ⥤ Type (u + 1) :=
  relativeTotalPresheaf J.toBase
    (liftedScalarFramePresheaf (pullback.snd (modulusBaseMap D) J.toBase)
      (poincareModulusBundle D h))

/-- The canonical relative sheafification map preserves the actual parameter of a frame. -/
def poincareRawToFrameFamily : poincareRawFrameFamily D h ⟶ poincareFrameTotalFamily D h :=
  relativeTotalMap.{u, u + 1} J.toBase
    (toScalarFrameSheaf (pullback.snd (modulusBaseMap D) J.toBase) (poincareModulusBundle D h))

/-- The ordinary class of a raw frame is classified by its actual parameter map. -/
def poincareRawFrameToPicard :
    poincareRawFrameFamily D h ⟶ relSubPicPresheaf c ε (algEquivZeroCut c ε) where
  app T := TypeCat.ofHom (fun x => h.representableBy.homEquiv x.1)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    exact h.representableBy.homEquiv_comp f.unop x.1

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- Raw frames give actual compatible-isomorphism classes in the modulus zero presheaf. -/
def poincareRawFrameToModulusZero :
    poincareRawFrameFamily D h ⟶ modulusPicardZeroPresheaf c (modulusCurveMap D) :=
  relativeTotalDesc.{u, u + 1} J.toBase
    (modulusFramesToPicardZero D J.toBase h.poincare.isInvertible
      (poincareUnderlying_fibrewiseZero h))

end AlgebraicGeometry.GeneralizedJacobian
