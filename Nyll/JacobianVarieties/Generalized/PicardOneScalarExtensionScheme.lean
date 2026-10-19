/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardOneDivisorScalarExtension
import Nyll.JacobianVarieties.Generalized.PicardOneUnpointedConstruction
import Nyll.SchemeTheory.WeilRestriction.Restriction

/-! # Scalar extension of the actual intrinsic Picard-one scheme -/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- The actual pullback scheme classifies the restricted original degree-one fppf sheaf. -/
def picardOneScalarExtensionRepresentable :
    ((Over.map (specMap K L)).op ⋙
      (modulusPicardOneSheaf c (modulusCurveMap D)).obj).RepresentableBy
        ((Over.pullback (specMap K L)).obj (picardOne c D)) :=
  SchemeTheory.WeilRestriction.representableByBaseChange (specMap K L)
    (picardOneRepresentable c D)

/-- Intrinsic Picard-one commutes with every extension by the actual relative divisor. -/
def picardOneScalarExtensionIso :
    (Over.pullback (specMap K L)).obj (picardOne c D) ≅
      picardOne (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)) :=
  ((picardOneScalarExtensionRepresentable c D L).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
      (Type (u + 1))).mapIso
        (modulusPicardOneSheaf_divisorScalarExtensionIso D L).symm)).uniqueUpToIso
    (picardOneRepresentable (baseChange K c L) (D.changeBaseOfIdentity (specMap K L)))

/-- The scheme isomorphism preserves the universal classification of every degree-one family. -/
theorem picardOneScalarExtensionIso_homEquiv {T : Over (Spec (CommRingCat.of L))}
    (f : T ⟶ (Over.pullback (specMap K L)).obj (picardOne c D)) :
    (picardOneRepresentable (baseChange K c L)
        (D.changeBaseOfIdentity (specMap K L))).homEquiv
          (f ≫ (picardOneScalarExtensionIso c D L).hom) =
      (modulusPicardOneSheaf_divisorScalarExtensionIso D L).inv.hom.app (op T)
        ((picardOneScalarExtensionRepresentable c D L).homEquiv f) := by
  let a := (picardOneScalarExtensionRepresentable c D L).ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of L)))
      (Type (u + 1))).mapIso
        (modulusPicardOneSheaf_divisorScalarExtensionIso D L).symm)
  let b := picardOneRepresentable (baseChange K c L)
    (D.changeBaseOfIdentity (specMap K L))
  change b.homEquiv (f ≫ b.homEquiv.symm (a.homEquiv (𝟙 _))) = a.homEquiv f
  rw [b.homEquiv_comp, Equiv.apply_symm_apply]
  exact (a.homEquiv_comp f (𝟙 _)).symm.trans
    (congrArg a.homEquiv (Category.comp_id f))

end AlgebraicGeometry.GeneralizedJacobian
