/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.AffineKernel
import Nyll.JacobianVarieties.Generalized.FrameGeometry
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation

/-!
# The actual Poincaré frame quotient

Restrict the supplied ordinary Poincaré bundle to the whole finite modulus,
including its multiplicities. The intrinsic scalar-frame sheaf is represented
by a scheme glued from the norm-open local models. Its map to the ordinary
Picard carrier is affine, smooth of relative dimension `degree - 1`, and
geometrically connected.

Identification with the degree-zero modulus Picard sheaf, its group law,
and the basepoint-free generalized Jacobian remain separate theorems.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The full divisor subscheme mapped to the original curve. -/
abbrev modulusCurveMap : D.I.subscheme ⟶ C :=
  D.I.subschemeι ≫ pullback.fst c (𝟙 (Spec (CommRingCat.of K)))

/-- The actual finite structure map of the full modulus. -/
abbrev modulusBaseMap : D.I.subscheme ⟶ Spec (CommRingCat.of K) :=
  D.I.subschemeι ≫ pullback.snd c (𝟙 (Spec (CommRingCat.of K)))

@[reassoc] theorem modulusCurveMap_toBase : modulusCurveMap D ≫ c = modulusBaseMap D := by
  rw [modulusCurveMap, Category.assoc, pullback.condition, Category.comp_id]

/-- The actual inclusion of the base-changed full modulus in the family of curves. -/
def modulusFamilyInclusion {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pullback (modulusBaseMap D) t ⟶ pullback c t :=
  pullback.lift (pullback.fst (modulusBaseMap D) t ≫ modulusCurveMap D)
    (pullback.snd (modulusBaseMap D) t) (by
      rw [Category.assoc, modulusCurveMap_toBase]
      exact pullback.condition)

@[reassoc] theorem modulusFamilyInclusion_fst {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    modulusFamilyInclusion D t ≫ pullback.fst c t =
      pullback.fst (modulusBaseMap D) t ≫ modulusCurveMap D :=
  pullback.lift_fst _ _ _

@[reassoc] theorem modulusFamilyInclusion_snd {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    modulusFamilyInclusion D t ≫ pullback.snd c t = pullback.snd (modulusBaseMap D) t :=
  pullback.lift_snd _ _ _

variable {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {P : SubPicCondition c ε} {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε P J)

/-- Restriction of the same ordinary Poincaré bundle to the whole modulus. -/
def poincareModulusBundle : (pullback (modulusBaseMap D) J.toBase).Modules :=
  (Scheme.Modules.pullback (modulusFamilyInclusion D J.toBase)).obj h.poincare.L

theorem poincareModulusBundle_isInvertible :
    Scheme.Modules.IsInvertible (poincareModulusBundle D h) :=
  h.poincare.isInvertible.pullback (modulusFamilyInclusion D J.toBase)

variable (hd : 0 < d)

/-- The concrete scalar-frame quotient over the ordinary Picard carrier. -/
def poincareFrameQuotient : Over J.P := by
  let : IsFinite (modulusBaseMap D) := D.isFinite
  exact finiteScalarFrameRepresenter (modulusBaseMap D) (positiveModulusBasis D hd) J.toBase
    (poincareModulusBundle_isInvertible D h)

/-- This scheme represents the actual intrinsic Poincaré scalar-frame sheaf. -/
def poincareFrameQuotientRepresentable :
    (scalarFrameSheaf (pullback.snd (modulusBaseMap D) J.toBase)
      (poincareModulusBundle D h)).obj.RepresentableBy (poincareFrameQuotient D h hd) := by
  let : IsFinite (modulusBaseMap D) := D.isFinite
  exact finiteScalarFrameRepresentable (modulusBaseMap D) (positiveModulusBasis D hd) J.toBase
    (poincareModulusBundle_isInvertible D h)

/-- The quotient is affine relative to the ordinary Picard carrier. -/
theorem poincareFrameQuotient_isAffineHom : IsAffineHom (poincareFrameQuotient D h hd).hom := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  exact finiteScalarFrameRepresenter_isAffineHom
    (modulusBaseMap D) (positiveModulusBasis D hd) J.toBase
    (poincareModulusBundle_isInvertible D h)

/-- The full modulus degree controls the dimension of the frame fibres. -/
theorem poincareFrameQuotient_smoothOfRelativeDimension :
    SmoothOfRelativeDimension (d - 1) (poincareFrameQuotient D h hd).hom := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  exact finiteScalarFrameRepresenter_smoothOfRelativeDimension
    (modulusBaseMap D) (positiveModulusBasis D hd) J.toBase
    (poincareModulusBundle_isInvertible D h)

/-- Every geometric fibre of the same quotient is connected. -/
theorem poincareFrameQuotient_geometricallyConnected :
    GeometricallyConnected (poincareFrameQuotient D h hd).hom := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  exact finiteScalarFrameRepresenter_geometricallyConnected
    (modulusBaseMap D) (positiveModulusBasis D hd) J.toBase
    (poincareModulusBundle_isInvertible D h)

end AlgebraicGeometry.GeneralizedJacobian
