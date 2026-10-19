/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOnePointedConstruction
import Nyll.JacobianVarieties.Generalized.PicardOneSheafTorsor

/-!
# The represented pointed Picard-one torsor identity

The pointed carrier is the constructed generalized Jacobian, with Picard-one
classification given by actual tensor translation. Its action/difference
identity is an isomorphism of schemes, not just a bijection on field points.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The pointed carrier's tensor action and difference give the scheme torsor isomorphism. -/
def picardOnePointedTorsorIso :
    (groupScheme c D).X ⊗ (groupScheme c D).X ≅
      (groupScheme c D).X ⊗ (groupScheme c D).X where
  hom := lift (fst _ _ * snd _ _) (snd _ _)
  inv := lift (fst _ _ / snd _ _) (snd _ _)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, GrpObj.comp_div, lift_snd,
        Category.id_comp, mul_div_cancel_right]
    · simp only [Category.assoc, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, MonObj.comp_mul, lift_snd,
        Category.id_comp, div_mul_cancel]
    · simp only [Category.assoc, lift_snd, Category.id_comp]

/-- The action component is actual multiplication on the constructed Jacobian carrier. -/
theorem picardOnePointedTorsorIso_action
    {T : Over (Spec (CommRingCat.of K))} (g p : T ⟶ (groupScheme c D).X) :
    lift g p ≫ (picardOnePointedTorsorIso c D).hom ≫ fst _ _ = g * p := by
  simp only [picardOnePointedTorsorIso, lift_fst,
    MonObj.comp_mul, lift_snd]

/-- The inverse component classifies the actual difference of the two represented classes. -/
theorem picardOnePointedTorsorIso_difference
    {T : Over (Spec (CommRingCat.of K))} (p q : T ⟶ (groupScheme c D).X) :
    lift p q ≫ (picardOnePointedTorsorIso c D).inv ≫ fst _ _ = p / q := by
  simp only [picardOnePointedTorsorIso, lift_fst,
    GrpObj.comp_div, lift_snd]

/-- The scheme action classifies tensor action on the actual Picard-one sheaf. -/
theorem picardOnePointed_mul_classifies
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {T : Over (Spec (CommRingCat.of K))} (g p : T ⟶ (groupScheme c D).X) :
    (picardOnePointedRepresentable c D ε).homEquiv (g * p) =
      modulusPicardOneSheafAction c (modulusCurveMap D) ε T
        ((groupRepresentable c D).homEquiv g)
        ((picardOnePointedRepresentable c D ε).homEquiv p) := by
  let φ : (T ⟶ (groupScheme c D).X) →
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.obj (op T) :=
    (groupRepresentable c D).homEquiv
  let E := modulusPicardOneSheafTranslationEquiv c (modulusCurveMap D) ε T
  have hmul : φ (g * p) = φ g * φ p := by
    cases d with
    | zero => exact (SchemeTheory.RepresentedGroups.pointEquiv _
        (Unpointed.zeroDegreeGroupRepresentable c D) T).map_mul g p
    | succ n => exact (SchemeTheory.RepresentedGroups.pointEquiv _
        (Unpointed.groupRepresentable c D (Nat.zero_lt_succ n)) T).map_mul g p
  change E (φ (g * p)) = E (φ g * E.symm (E (φ p)))
  rw [Equiv.symm_apply_apply, hmul]

/-- The inverse scheme component classifies difference of actual Picard-one sheaf classes. -/
theorem picardOnePointed_div_classifies
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    {T : Over (Spec (CommRingCat.of K))} (p q : T ⟶ (groupScheme c D).X) :
    (groupRepresentable c D).homEquiv (p / q) =
      modulusPicardOneSheafDifference c (modulusCurveMap D) ε T
        ((picardOnePointedRepresentable c D ε).homEquiv p)
        ((picardOnePointedRepresentable c D ε).homEquiv q) := by
  change (groupRepresentable c D).homEquiv (p / q) =
    (modulusPicardOneSheafTranslationEquiv c (modulusCurveMap D) ε T).symm
        (modulusPicardOneSheafTranslationEquiv c (modulusCurveMap D) ε T
          ((groupRepresentable c D).homEquiv p)) /
      (modulusPicardOneSheafTranslationEquiv c (modulusCurveMap D) ε T).symm
        (modulusPicardOneSheafTranslationEquiv c (modulusCurveMap D) ε T
          ((groupRepresentable c D).homEquiv q))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  cases d with
  | zero => exact (SchemeTheory.RepresentedGroups.pointEquiv _
      (Unpointed.zeroDegreeGroupRepresentable c D) T).map_div p q
  | succ n => exact (SchemeTheory.RepresentedGroups.pointEquiv _
      (Unpointed.groupRepresentable c D (Nat.zero_lt_succ n)) T).map_div p q

end AlgebraicGeometry.GeneralizedJacobian
