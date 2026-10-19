/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Semiabelian
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Points in the fibres of a semiabelian extension

Once one lift is given, every other lift is obtained uniquely by multiplication
by a point of the torus kernel. The equivalence works for every parameter scheme
and commutes with changing the parameter scheme.
-/

noncomputable section

universe u

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.SemiabelianExtension

variable {K : Type u} [Field K]
  {G : CommGrp (Over (Spec (CommRingCat.of K)))} (E : SemiabelianExtension G)

/-- A chosen lift identifies its entire parameter-point fibre with the torus kernel. -/
def pointFiberEquiv (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ G.X) :
    (T ⟶ E.torus.X) ≃
      {y : T ⟶ G.X | y ≫ E.projection.hom.hom.hom = x ≫ E.projection.hom.hom.hom} :=
  Equiv.ofBijective
    (fun a => ⟨(a ≫ E.inclusion.hom.hom.hom) * x, by
      change ((a ≫ E.inclusion.hom.hom.hom) * x) ≫ E.projection.hom.hom.hom =
        x ≫ E.projection.hom.hom.hom
      rw [MonObj.mul_comp, Category.assoc, E.condition, MonObj.comp_one, one_mul]⟩)
    (by
      constructor
      · intro a b hab
        have : Mono E.inclusion.hom.hom.hom := E.inclusion_mono
        apply (cancel_mono E.inclusion.hom.hom.hom).mp
        exact mul_right_cancel (congrArg Subtype.val hab)
      · intro y
        have hk : (y.val * x⁻¹) ≫ E.projection.hom.hom.hom = 1 := by
          rw [MonObj.mul_comp, GrpObj.inv_comp, y.property, mul_inv_cancel]
        obtain ⟨a, ha⟩ := (Set.ext_iff.mp (E.point_exact T) (y.val * x⁻¹)).mpr hk
        refine ⟨a, Subtype.ext ?_⟩
        change (a ≫ E.inclusion.hom.hom.hom) * x = y.val
        change a ≫ E.inclusion.hom.hom.hom = y.val * x⁻¹ at ha
        rw [ha, inv_mul_cancel_right])

/-- The fibre identification uses the original inclusion and group operation. -/
theorem pointFiberEquiv_apply (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ G.X)
    (a : T ⟶ E.torus.X) :
    (E.pointFiberEquiv T x a).val = (a ≫ E.inclusion.hom.hom.hom) * x := rfl

/-- Changing the parameter scheme commutes with the torus translation of a chosen lift. -/
theorem pointFiberEquiv_naturality {T T' : Over (Spec (CommRingCat.of K))}
    (f : T' ⟶ T) (x : T ⟶ G.X) (a : T ⟶ E.torus.X) :
    f ≫ (E.pointFiberEquiv T x a).val =
      (E.pointFiberEquiv T' (f ≫ x) (f ≫ a)).val := by
  change f ≫ ((a ≫ E.inclusion.hom.hom.hom) * x) =
    ((f ≫ a) ≫ E.inclusion.hom.hom.hom) * (f ≫ x)
  rw [MonObj.comp_mul, Category.assoc]

end AlgebraicGeometry.SemiabelianExtension
