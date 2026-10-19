/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.UnpointedConstruction
import Nyll.JacobianVarieties.Generalized.UnpointedEmptyConstruction

/-!
# The generalized Jacobian for every effective modulus over an arbitrary field

The zero and positive degree constructions both represent the actual modulus
Picard-zero group sheaf. This single interface retains the appropriate proved
construction in each case, including its group law and geometric properties.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The generalized Jacobian group scheme of the whole effective modulus,
without choosing a rational point on the curve. -/
def groupScheme : {d : ℕ} →
    RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))) →
      CommGrp (Over (Spec (CommRingCat.of K)))
  | 0, D => Unpointed.zeroDegreeGroupScheme c D
  | n + 1, D => Unpointed.groupScheme c D (Nat.zero_lt_succ n)

variable {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The tensor-product group sheaf is represented by the constructed group scheme. -/
def groupRepresentable :
    ((modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj ⋙
      forget CommGrpCat.{u + 1}).RepresentableBy (groupScheme c D).X := by
  cases d with
  | zero => exact Unpointed.zeroDegreeGroupRepresentable c D
  | succ n => exact Unpointed.groupRepresentable c D (Nat.zero_lt_succ n)

/-- The same scheme represents the actual type-valued modulus Picard-zero sheaf. -/
def picardZeroRepresentable :
    (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.RepresentableBy
      (groupScheme c D).X :=
  (groupRepresentable c D).ofIso (modulusPicardZeroGroupSheafForgetIso c (modulusCurveMap D))

/-- The classifying equivalence preserves the actual tensor-product group operation. -/
def pointEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (groupScheme c D).X) ≃*
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.obj (op T) := by
  cases d with
  | zero =>
    exact SchemeTheory.RepresentedGroups.pointEquiv _
      (Unpointed.zeroDegreeGroupRepresentable c D) T
  | succ n =>
    exact SchemeTheory.RepresentedGroups.pointEquiv _
      (Unpointed.groupRepresentable c D (Nat.zero_lt_succ n)) T

/-- Smoothness, finite type, separation and geometric connectedness for the same
constructed group. The uniform dimension also treats degree zero correctly. -/
theorem geometry :
    SmoothOfRelativeDimension (geometricGenus K c + (d - 1)) (groupScheme c D).X.hom ∧
      LocallyOfFiniteType (groupScheme c D).X.hom ∧
      QuasiCompact (groupScheme c D).X.hom ∧
      IsSeparated (groupScheme c D).X.hom ∧
      GeometricallyConnected (groupScheme c D).X.hom := by
  cases d with
  | zero =>
    have h := Unpointed.zeroDegreeGeometry c D
    have : SmoothOfRelativeDimension (geometricGenus K c)
        (Unpointed.zeroDegreeGroupScheme c D).X.hom := h.1
    have : Smooth (Unpointed.zeroDegreeGroupScheme c D).X.hom :=
      SmoothOfRelativeDimension.smooth (geometricGenus K c) _
    have : IsProper (Unpointed.zeroDegreeGroupScheme c D).X.hom := h.2.1
    simpa only [groupScheme, Nat.zero_sub, Nat.add_zero] using
      (show SmoothOfRelativeDimension (geometricGenus K c)
          (Unpointed.zeroDegreeGroupScheme c D).X.hom ∧
        LocallyOfFiniteType (Unpointed.zeroDegreeGroupScheme c D).X.hom ∧
        QuasiCompact (Unpointed.zeroDegreeGroupScheme c D).X.hom ∧
        IsSeparated (Unpointed.zeroDegreeGroupScheme c D).X.hom ∧
        GeometricallyConnected (Unpointed.zeroDegreeGroupScheme c D).X.hom from
          ⟨h.1, inferInstance, inferInstance, inferInstance, h.2.2⟩)
  | succ n =>
    simpa only [groupScheme, Nat.succ_sub_one, Nat.add_succ] using
      Unpointed.geometry c D (Nat.zero_lt_succ n)

/-- A positive modulus has smooth relative dimension `g + deg D - 1`. -/
theorem dimension_of_pos (hd : 0 < d) :
    SmoothOfRelativeDimension (geometricGenus K c + d - 1) (groupScheme c D).X.hom := by
  have he : geometricGenus K c + (d - 1) = geometricGenus K c + d - 1 := by omega
  rw [← he]
  exact (geometry c D).1

/-- The zero modulus gives a proper group of genus dimension. -/
theorem zeroDegreeGeometry (D₀ : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K)))) :
    SmoothOfRelativeDimension (geometricGenus K c) (groupScheme c D₀).X.hom ∧
      IsProper (groupScheme c D₀).X.hom ∧
      GeometricallyConnected (groupScheme c D₀).X.hom :=
  Unpointed.zeroDegreeGeometry c D₀

end AlgebraicGeometry.GeneralizedJacobian
