/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusComplementBaseChange

/-! # Actual open-curve points on a scalar-extended parameter scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- Project an actual point of the extended complement to the original complement. -/
def modulusScalarExtensionPoint {T : Over (Spec (CommRingCat.of R'))}
    (P : T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R')) :
    (Over.map (specMap R R')).obj T ⟶ Over.mk ((modulusComplement i).ι ≫ c) := by
  refine Over.homMk (P.left ≫ modulusComplementBaseChangeMap c i (specMap R R')) ?_
  change (P.left ≫ modulusComplementBaseChangeMap c i (specMap R R')) ≫
    ((modulusComplement i).ι ≫ c) = T.hom ≫ specMap R R'
  rw [Category.assoc, modulusComplementBaseChangeMap_ι_assoc, pullback.condition]
  have hP : P.left ≫
      ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
        pullback.snd c (specMap R R')) = T.hom := Over.w P
  simpa only [Category.assoc] using congrArg (· ≫ specMap R R') hP

/-- The canonical curve point lying above a point with an extended parameter map. -/
def modulusScalarExtensionCurvePoint {T : Over (Spec (CommRingCat.of R'))}
    (P : (Over.map (specMap R R')).obj T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    T.left ⟶ pullback c (specMap R R') :=
  pullback.lift (P.left ≫ (modulusComplement i).ι) T.hom
    ((Category.assoc _ _ _).trans (Over.w P))

/-- The canonical lifted curve point avoids the entire base-changed modulus. -/
theorem modulusScalarExtensionCurvePoint_range {T : Over (Spec (CommRingCat.of R'))}
    (P : (Over.map (specMap R R')).obj T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    Set.range (modulusScalarExtensionCurvePoint c i R' P) ⊆
      Set.range (modulusComplement (modulusBaseChange c i (specMap R R'))).ι := by
  rintro y ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι, modulusComplement_baseChange]
  change pullback.fst c (specMap R R') (modulusScalarExtensionCurvePoint c i R' P x) ∈
    modulusComplement i
  rw [← Scheme.Hom.comp_apply]
  change (pullback.lift (P.left ≫ (modulusComplement i).ι) T.hom _ ≫
    pullback.fst c (specMap R R')) x ∈ modulusComplement i
  rw [pullback.lift_fst]
  exact (P.left x).property

/-- Lift an actual original open-curve point to the scalar-extended open curve. -/
def modulusScalarExtensionPointLift {T : Over (Spec (CommRingCat.of R'))}
    (P : (Over.map (specMap R R')).obj T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R') := by
  refine Over.homMk
    (IsOpenImmersion.lift (modulusComplement (modulusBaseChange c i (specMap R R'))).ι
      (modulusScalarExtensionCurvePoint c i R' P)
      (modulusScalarExtensionCurvePoint_range c i R' P)) ?_
  change IsOpenImmersion.lift _ _ _ ≫
    ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      pullback.snd c (specMap R R')) = T.hom
  rw [IsOpenImmersion.lift_fac_assoc]
  exact pullback.lift_snd _ _ _

@[reassoc] theorem modulusScalarExtensionPointLift_ι
    {T : Over (Spec (CommRingCat.of R'))}
    (P : (Over.map (specMap R R')).obj T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    (modulusScalarExtensionPointLift c i R' P).left ≫
        (modulusComplement (modulusBaseChange c i (specMap R R'))).ι =
      modulusScalarExtensionCurvePoint c i R' P :=
  IsOpenImmersion.lift_fac _ _ _

/-- Projection of the actual lifted point recovers the original point. -/
theorem modulusScalarExtensionPoint_lift {T : Over (Spec (CommRingCat.of R'))}
    (P : (Over.map (specMap R R')).obj T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusScalarExtensionPoint c i R' (modulusScalarExtensionPointLift c i R' P) = P := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (modulusComplement i).ι).mp
  change ((modulusScalarExtensionPointLift c i R' P).left ≫
    modulusComplementBaseChangeMap c i (specMap R R')) ≫ (modulusComplement i).ι =
      P.left ≫ (modulusComplement i).ι
  rw [Category.assoc, modulusComplementBaseChangeMap_ι,
    modulusScalarExtensionPointLift_ι_assoc]
  exact pullback.lift_fst _ _ _

/-- Lifting the projection recovers the same scalar-extended point. -/
theorem modulusScalarExtensionPointLift_point {T : Over (Spec (CommRingCat.of R'))}
    (P : T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R')) :
    modulusScalarExtensionPointLift c i R' (modulusScalarExtensionPoint c i R' P) = P := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (modulusComplement (modulusBaseChange c i (specMap R R'))).ι).mp
  rw [modulusScalarExtensionPointLift_ι]
  apply pullback.hom_ext
  · change (pullback.lift _ _ _ ≫ pullback.fst c (specMap R R')) = _
    rw [pullback.lift_fst]
    change (P.left ≫ modulusComplementBaseChangeMap c i (specMap R R')) ≫
      (modulusComplement i).ι = _
    rw [Category.assoc, modulusComplementBaseChangeMap_ι, ← Category.assoc]
  · change (pullback.lift _ _ _ ≫ pullback.snd c (specMap R R')) = _
    rw [pullback.lift_snd, Category.assoc]
    exact (Over.w P).symm

/-- The points of the two actual complements agree on every extended test scheme. -/
def modulusScalarExtensionPointEquiv (T : Over (Spec (CommRingCat.of R'))) :
    (T ⟶ Over.mk ((modulusComplement (modulusBaseChange c i (specMap R R'))).ι ≫
      baseChange R c R')) ≃
        ((Over.map (specMap R R')).obj T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) where
  toFun := modulusScalarExtensionPoint c i R'
  invFun := modulusScalarExtensionPointLift c i R'
  left_inv := modulusScalarExtensionPointLift_point c i R'
  right_inv := modulusScalarExtensionPoint_lift c i R'

end AlgebraicGeometry.GeneralizedJacobian
