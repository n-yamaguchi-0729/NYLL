/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareRepresentability
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupSheaf
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The commutative group scheme on the constructed Poincaré frame quotient

The proved representation transports the actual modulus Picard-zero group
sheaf to the same glued scheme. In particular, this does not replace the
extension by a product with the ordinary Picard scheme.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
  {J : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J) (hd : 0 < d)

/-- The same frame quotient represents the underlying presheaf of the actual zero group sheaf. -/
def poincareModulusPicardZeroGroupRepresentable :
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy
        ((Over.map J.toBase).obj (poincareFrameQuotient D h hd)) :=
  (poincareModulusPicardZeroRepresentable D h hd).ofIso
    (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).symm

/-- Tensor product equips the concrete Poincaré frame scheme with a commutative group law. -/
def poincareModulusCommGroupScheme : CommGrp (Over (Spec (CommRingCat.of K))) := by
  let : CommGrpObj ((Over.map J.toBase).obj (poincareFrameQuotient D h hd)) :=
    CommGrpObj.ofRepresentableBy _ (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
      (poincareModulusPicardZeroGroupRepresentable D h hd)
  exact ⟨(Over.map J.toBase).obj (poincareFrameQuotient D h hd)⟩

/-- The group law is placed on the previously constructed scheme. -/
theorem poincareModulusCommGroupScheme_carrier :
    (poincareModulusCommGroupScheme D h hd).X =
      (Over.map J.toBase).obj (poincareFrameQuotient D h hd) := rfl

/-- The represented group class is the universal modulus zero class pulled back by the point. -/
theorem poincareModulusPicardZeroGroupRepresentable_homEquiv
    {T : Over (Spec (CommRingCat.of K))}
    (f : T ⟶ (Over.map J.toBase).obj (poincareFrameQuotient D h hd)) :
    (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).hom.app (op T)
      ((poincareModulusPicardZeroGroupRepresentable D h hd).homEquiv f) =
        (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.map f.op
          (poincareFrameQuotientModulusZeroClass D h hd) := by
  change (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).hom.app (op T)
      ((modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).inv.app (op T)
        ((poincareFrameTotalToModulusPicardZero D h).app (op T)
          ((poincareFrameTotalRepresentable D h hd).homEquiv f))) = _
  exact (Iso.inv_hom_id_apply
    ((modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D)).app (op T)) _).trans
      (poincareFrameTotalToModulusPicardZero_homEquiv D h hd f)

/-- Points of the constructed group scheme classify modulus zero group sections with their law. -/
def poincareModulusPointEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (poincareModulusCommGroupScheme D h hd).X) ≃*
      ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.obj (op T)) where
  toEquiv := (poincareModulusPicardZeroGroupRepresentable D h hd).homEquiv
  map_mul' f g := by
    let W := (poincareModulusCommGroupScheme D h hd).X
    let F := (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj
    let e : (F ⋙ forget CommGrpCat).RepresentableBy W :=
      poincareModulusPicardZeroGroupRepresentable D h hd
    change e.homEquiv (CartesianMonoidalCategory.lift f g ≫
      e.homEquiv.symm (e.homEquiv (CartesianMonoidalCategory.fst W W) *
        e.homEquiv (CartesianMonoidalCategory.snd W W))) = _
    rw [e.homEquiv_comp, Equiv.apply_symm_apply]
    change (F.map (CartesianMonoidalCategory.lift f g).op).hom (_ * _) = _
    rw [map_mul]
    change (F ⋙ forget CommGrpCat).map (CartesianMonoidalCategory.lift f g).op
        (e.homEquiv (CartesianMonoidalCategory.fst W W)) *
      (F ⋙ forget CommGrpCat).map (CartesianMonoidalCategory.lift f g).op
        (e.homEquiv (CartesianMonoidalCategory.snd W W)) = _
    rw [← e.homEquiv_comp, ← e.homEquiv_comp,
      CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
    rfl

end AlgebraicGeometry.GeneralizedJacobian
