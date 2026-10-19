/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOneIntrinsicAction
import Nyll.JacobianVarieties.Generalized.PicardOneUnpointedConstruction
import Nyll.JacobianVarieties.Generalized.Construction
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-! # The canonical tensor action on the actual intrinsic Picard-one scheme -/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The Cartesian product representation uses the actual individual classifying maps. -/
def picardOneTensorProductRepresentable :
    (modulusPicardZeroSheaf c (modulusCurveMap D) ⊗
      modulusPicardOneSheaf c (modulusCurveMap D)).obj.RepresentableBy
        ((groupScheme c D).X ⊗ picardOne c D) :=
  Functor.Monoidal.RepresentableBy.tensorObj
    (picardZeroRepresentable c D) (picardOneRepresentable c D)

/-- The action morphism classifying actual rigidified tensor product. -/
def picardOneTensorAction : (groupScheme c D).X ⊗ picardOne c D ⟶ picardOne c D :=
  (picardOneRepresentable c D).homEquiv.symm
    ((modulusPicardOneTensorAction c (modulusCurveMap D)).hom.app
      (op ((groupScheme c D).X ⊗ picardOne c D))
        ((picardOneTensorProductRepresentable c D).homEquiv (𝟙 _)))

/-- Every pair of test points is sent to the actual intrinsic tensor action on its classes. -/
theorem picardOneTensorAction_classifies {T : Over (Spec (CommRingCat.of K))}
    (g : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D) :
    (picardOneRepresentable c D).homEquiv (lift g x ≫ picardOneTensorAction c D) =
      modulusPicardOneIntrinsicAction c (modulusCurveMap D) T
        ((groupRepresentable c D).homEquiv g) ((picardOneRepresentable c D).homEquiv x) := by
  let a := modulusPicardOneTensorAction c (modulusCurveMap D)
  let e := picardOneTensorProductRepresentable c D
  rw [(picardOneRepresentable c D).homEquiv_comp]
  change (modulusPicardOneSheaf c (modulusCurveMap D)).obj.map (lift g x).op
    ((picardOneRepresentable c D).homEquiv ((picardOneRepresentable c D).homEquiv.symm _)) = _
  rw [Equiv.apply_symm_apply]
  have h := a.hom.naturality_apply (lift g x).op (e.homEquiv (𝟙 _))
  have he : (modulusPicardZeroSheaf c (modulusCurveMap D) ⊗
      modulusPicardOneSheaf c (modulusCurveMap D)).obj.map (lift g x).op
        (e.homEquiv (𝟙 _)) = e.homEquiv (lift g x) :=
    (e.homEquiv_comp (lift g x) (𝟙 _)).symm.trans
      (congrArg e.homEquiv (Category.comp_id _))
  refine h.symm.trans ((congrArg (a.hom.app (op T)) he).trans ?_)
  change a.hom.app (op T)
    ((picardZeroRepresentable c D).homEquiv (lift g x ≫ fst _ _),
      (picardOneRepresentable c D).homEquiv (lift g x ≫ snd _ _)) = _
  rw [lift_fst, lift_snd]
  rfl

/-- The actual group identity acts as the identity on every test scheme. -/
theorem picardOneTensorAction_one {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ picardOne c D) :
    lift (1 : T ⟶ (groupScheme c D).X) x ≫ picardOneTensorAction c D = x := by
  apply (picardOneRepresentable c D).homEquiv.injective
  rw [picardOneTensorAction_classifies]
  have hone : (groupRepresentable c D).homEquiv (1 : T ⟶ (groupScheme c D).X) = 1 := by
    cases d with
    | zero => exact (SchemeTheory.RepresentedGroups.pointEquiv _
        (Unpointed.zeroDegreeGroupRepresentable c D) T).map_one
    | succ n => exact (SchemeTheory.RepresentedGroups.pointEquiv _
        (Unpointed.groupRepresentable c D (Nat.zero_lt_succ n)) T).map_one
  rw [hone]
  exact modulusPicardOneIntrinsicAction_one c (modulusCurveMap D) T _

/-- Tensor action is associative with the canonical multiplication of the actual group scheme. -/
theorem picardOneTensorAction_mul {T : Over (Spec (CommRingCat.of K))}
    (g h : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D) :
    lift (g * h) x ≫ picardOneTensorAction c D =
      lift g (lift h x ≫ picardOneTensorAction c D) ≫ picardOneTensorAction c D := by
  apply (picardOneRepresentable c D).homEquiv.injective
  rw [picardOneTensorAction_classifies, picardOneTensorAction_classifies,
    picardOneTensorAction_classifies]
  let φ : (T ⟶ (groupScheme c D).X) →
      (modulusPicardZeroGroupSheaf c (modulusCurveMap D)).obj.obj (op T) :=
    (groupRepresentable c D).homEquiv
  have hmul : φ (g * h) = φ g * φ h := by
    cases d with
    | zero => exact (SchemeTheory.RepresentedGroups.pointEquiv _
        (Unpointed.zeroDegreeGroupRepresentable c D) T).map_mul g h
    | succ n => exact (SchemeTheory.RepresentedGroups.pointEquiv _
        (Unpointed.groupRepresentable c D (Nat.zero_lt_succ n)) T).map_mul g h
  exact (congrArg (fun z => modulusPicardOneIntrinsicAction c (modulusCurveMap D) T z
    ((picardOneRepresentable c D).homEquiv x)) hmul).trans
      (modulusPicardOneIntrinsicAction_mul c (modulusCurveMap D) T (φ g) (φ h) _)

end AlgebraicGeometry.GeneralizedJacobian
