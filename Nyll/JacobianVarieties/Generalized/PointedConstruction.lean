/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareKernelScheme
import Nyll.JacobianVarieties.Generalized.PoincareProjectionSurjectivity
import Nyll.JacobianVarieties.Picard.GenusDimension
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Construction over a field with a chosen curve section and positive modulus

The ordinary Picard existence theorem supplies the Poincaré family used in
the concrete frame construction. No Picard representation is an input here.
The constructed commutative group represents the modulus Picard-zero sheaf
and has smooth relative dimension `genus + degree - 1`.
-/

noncomputable section

universe u

open CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian.Pointed

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- The ordinary Picard scheme supplied by the existing field-level existence theorem. -/
def ordinaryPicard : RelativePic0Designation K c :=
  (exists_representsRelSubPic_of_field K c ε).choose

/-- The actual Poincaré family supplied by that theorem, not an extra input. -/
def ordinaryRepresentation :
    RepresentsRelSubPic c ε (algEquivZeroCut c ε) (ordinaryPicard c ε) :=
  (exists_representsRelSubPic_of_field K c ε).choose_spec.1.some

variable {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)

/-- The concrete commutative group scheme for a positive modulus on the pointed curve. -/
def groupScheme : CommGrp (Over (Spec (CommRingCat.of K))) :=
  poincareModulusCommGroupScheme D (ordinaryRepresentation c ε) hd

/-- The constructed scheme represents the actual modulus Picard-zero group sheaf. -/
def groupRepresentable :
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (groupScheme c ε D hd).X :=
  poincareModulusPicardZeroGroupRepresentable D (ordinaryRepresentation c ε) hd

/-- The same carrier represents the original type-valued modulus Picard-zero sheaf. -/
def picardZeroRepresentable :
    (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.RepresentableBy
      (groupScheme c ε D hd).X :=
  poincareModulusPicardZeroRepresentable D (ordinaryRepresentation c ε) hd

/-- Smoothness, dimension, finite type, separation and geometric connectedness follow
from the actual affine smooth projection to the proper ordinary Picard scheme. -/
theorem geometry :
    SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K c + d - 1)
        (groupScheme c ε D hd).X.hom ∧
      LocallyOfFiniteType (groupScheme c ε D hd).X.hom ∧
      QuasiCompact (groupScheme c ε D hd).X.hom ∧
      IsSeparated (groupScheme c ε D hd).X.hom ∧
      GeometricallyConnected (groupScheme c ε D hd).X.hom := by
  let J := ordinaryPicard c ε
  let h := ordinaryRepresentation c ε
  let W := poincareFrameQuotient D h hd
  have : Smooth J.toBase := (exists_representsRelSubPic_of_field K c ε).choose_spec.2.1
  have : IsProper J.toBase := (exists_representsRelSubPic_of_field K c ε).choose_spec.2.2.1
  have : GeometricallyConnected J.toBase :=
    (exists_representsRelSubPic_of_field K c ε).choose_spec.2.2.2
  have : SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K c) J.toBase :=
    h.smoothOfRelativeDimension_geometricGenus
  have : SmoothOfRelativeDimension (d - 1) W.hom :=
    poincareFrameQuotient_smoothOfRelativeDimension D h hd
  have : Smooth W.hom := SmoothOfRelativeDimension.smooth (d - 1) W.hom
  have : IsAffineHom W.hom := poincareFrameQuotient_isAffineHom D h hd
  have : GeometricallyConnected W.hom := poincareFrameQuotient_geometricallyConnected D h hd
  have hdim : (d - 1) + SmoothProperCurve.geometricGenus K c =
      SmoothProperCurve.geometricGenus K c + d - 1 := by omega
  change SmoothOfRelativeDimension (SmoothProperCurve.geometricGenus K c + d - 1)
      (W.hom ≫ J.toBase) ∧ LocallyOfFiniteType (W.hom ≫ J.toBase) ∧
        QuasiCompact (W.hom ≫ J.toBase) ∧ IsSeparated (W.hom ≫ J.toBase) ∧
          GeometricallyConnected (W.hom ≫ J.toBase)
  refine ⟨?_, inferInstance, inferInstance, inferInstance, ?_⟩
  · rw [← hdim]
    infer_instance
  · exact GeometricallyConnected.comp W.hom J.toBase

end AlgebraicGeometry.GeneralizedJacobian.Pointed
