/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareGroupProjection

/-!
# Geometry of the actual modulus-forgetting group morphism

The proved equality with the frame projection supplies affineness, relative
smooth dimension and geometric connectedness of its fibres.
-/

noncomputable section

universe u

open CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J) (hd : 0 < d)

/-- The actual forgetful group morphism is affine. -/
theorem poincareModulusGroupProjection_isAffineHom :
    IsAffineHom (poincareModulusGroupProjection D h hd).hom.hom.hom.left := by
  rw [poincareModulusGroupProjection_eq]
  exact poincareFrameQuotient_isAffineHom D h hd

/-- Its smooth relative dimension is the full modulus degree minus one. -/
theorem poincareModulusGroupProjection_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (d - 1)
      (poincareModulusGroupProjection D h hd).hom.hom.hom.left := by
  rw [poincareModulusGroupProjection_eq]
  exact poincareFrameQuotient_smoothOfRelativeDimension D h hd

/-- The fibres of the actual forgetful group morphism are geometrically connected. -/
theorem poincareModulusGroupProjection_geometricallyConnected :
    GeometricallyConnected (poincareModulusGroupProjection D h hd).hom.hom.hom.left := by
  rw [poincareModulusGroupProjection_eq]
  exact poincareFrameQuotient_geometricallyConnected D h hd

/-- The projection is surjective on scheme points; no rational-point surjectivity is asserted. -/
theorem poincareModulusGroupProjection_surjective :
    Surjective (poincareModulusGroupProjection D h hd).hom.hom.hom.left := by
  have : GeometricallyConnected (poincareModulusGroupProjection D h hd).hom.hom.hom.left :=
    poincareModulusGroupProjection_geometricallyConnected D h hd
  infer_instance

end AlgebraicGeometry.GeneralizedJacobian
