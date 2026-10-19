/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelMap
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Changing the actual Abel basepoint gives the specified tensor translation -/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

section

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- Changing basepoint translates actual point differences by the original basepoint's class. -/
theorem modulusAbelZeroClass_changeBasepoint
    (ε ε' : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusAbelZeroClass c i ε' x =
      modulusAbelZeroClass c i ε x *
        modulusAbelZeroClass c i ε'
          ((Over.homMk T.hom (Category.comp_id T.hom) :
            T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ ε) := by
  let p : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk T.hom (Category.comp_id T.hom)
  let a := modulusAbelPointClass c i (T := T) x
  let b := modulusGroundClass c i
    (modulusAbelPointClass c i (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T
  let b' := modulusGroundClass c i
    (modulusAbelPointClass c i (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε') T
  have hb : b = modulusAbelPointClass c i (T := T) (p ≫ ε) :=
    modulusGroundClass_abel c i ε T
  apply Subtype.ext
  change a / b' = a / b * (modulusAbelPointClass c i (T := T) (p ≫ ε) / b')
  rw [← hb]
  exact (div_mul_div_cancel a b b').symm

end

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε ε' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))

/-- The same specified translation holds in the fppf tensor group sheaf. -/
theorem modulusAbelZeroSheafClass_changeBasepoint
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    modulusAbelZeroSheafClass c D ε' x =
      modulusAbelZeroSheafClass c D ε x *
        modulusAbelZeroSheafClass c D ε'
          ((Over.homMk T.hom (Category.comp_id T.hom) :
            T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ ε) := by
  let m : modulusPicardZeroSubgroup c (modulusCurveMap D) T →*
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.obj (op T) :=
    ((toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
      (modulusPicardZeroGroupPresheaf c (modulusCurveMap D))).app (op T)).hom
  exact (congrArg m (modulusAbelZeroClass_changeBasepoint c (modulusCurveMap D) ε ε' x)).trans
    (m.map_mul _ _)

/-- The actual Abel morphisms differ by translation by the original basepoint's actual image. -/
theorem modulusAbelMap_changeBasepoint
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    x ≫ modulusAbelMap c D ε' = (x ≫ modulusAbelMap c D ε) *
      (((Over.homMk T.hom (Category.comp_id T.hom) :
        T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ ε) ≫ modulusAbelMap c D ε') := by
  let p : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk T.hom (Category.comp_id T.hom)
  let a := x ≫ modulusAbelMap c D ε
  let b := (p ≫ ε) ≫ modulusAbelMap c D ε'
  have hmul : (groupRepresentable c D).homEquiv (a * b) =
      (groupRepresentable c D).homEquiv a * (groupRepresentable c D).homEquiv b := by
    cases d with
    | zero => exact (SchemeTheory.RepresentedGroups.pointEquiv _
        (Unpointed.zeroDegreeGroupRepresentable c D) T).map_mul a b
    | succ n => exact (SchemeTheory.RepresentedGroups.pointEquiv _
        (Unpointed.groupRepresentable c D (Nat.zero_lt_succ n)) T).map_mul a b
  apply (groupRepresentable c D).homEquiv.injective
  change (groupRepresentable c D).homEquiv (x ≫ modulusAbelMap c D ε') =
    (groupRepresentable c D).homEquiv (a * b)
  rw [hmul]
  exact (modulusAbelMap_classifies c D ε' x).trans
    ((modulusAbelZeroSheafClass_changeBasepoint c D ε ε' x).trans
      (congrArg₂ (fun y z => y * z)
        (modulusAbelMap_classifies c D ε x).symm
        (modulusAbelMap_classifies c D ε' (p ≫ ε)).symm))

/-- A translated Abel factorization at one basepoint gives the translated
factorization at every basepoint, using the same group morphism. -/
theorem modulusAbelMap_factor_changeBasepoint
    (H : CommGrp (Over (Spec (CommRingCat.of K))))
    (φ : groupScheme c D ⟶ H)
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    modulusAbelMap c D ε ≫ φ.hom.hom.hom = q / (b ≫ ε ≫ q) →
      modulusAbelMap c D ε' ≫ φ.hom.hom.hom = q / (b ≫ ε' ≫ q) := by
  intro b hfac
  have hb : ε' ≫ b = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Over.w ε'
  have hc : (b ≫ ε') ≫ (b ≫ ε ≫ q) = b ≫ ε ≫ q := by
    rw [Category.assoc, ← Category.assoc ε' b, hb, Category.id_comp]
  have hpre : (b ≫ ε') ≫ (q / (b ≫ ε ≫ q)) =
      (b ≫ ε' ≫ q) / (b ≫ ε ≫ q) := by
    rw [GrpObj.comp_div, hc, Category.assoc]
  have ht : modulusAbelMap c D ε ≫ φ.hom.hom.hom =
      (modulusAbelMap c D ε' ≫ φ.hom.hom.hom) *
        ((b ≫ ε') ≫ (modulusAbelMap c D ε ≫ φ.hom.hom.hom)) := by
    simpa only [Category.id_comp, MonObj.mul_comp, Category.assoc] using
      congrArg (fun t => t ≫ φ.hom.hom.hom)
        (modulusAbelMap_changeBasepoint c D ε' ε (𝟙 _))
  rw [hfac, hpre] at ht
  exact mul_right_cancel
    (ht.symm.trans (div_mul_div_cancel q (b ≫ ε' ≫ q) (b ≫ ε ≫ q)).symm)

end AlgebraicGeometry.GeneralizedJacobian
