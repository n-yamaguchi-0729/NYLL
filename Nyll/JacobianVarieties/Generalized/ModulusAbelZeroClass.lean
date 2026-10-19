/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelDifference
import Nyll.JacobianVarieties.Generalized.PicardTranslation

/-! # Natural Picard-zero classes of the pointed modulus Abel family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- The canonically rigidified point class on any test scheme. -/
def modulusAbelPointClass {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) :=
  (modulusPicardGroupPresheaf c i).map x.op (modulusAbelClass c i)

omit [GeometricallyIntegral c] in
/-- Point classes are restrictions of one actual diagonal family. -/
theorem modulusAbelPointClass_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    (modulusPicardGroupPresheaf c i).map f.op (modulusAbelPointClass c i x) =
      modulusAbelPointClass c i (f ≫ x) := by
  let a : (modulusPicardGroupPresheaf c i).obj
      (op (Over.mk ((modulusComplement i).ι ≫ c))) := modulusAbelClass c i
  change (modulusPicardGroupPresheaf c i).map f.op
      ((modulusPicardGroupPresheaf c i).map x.op a) =
    (modulusPicardGroupPresheaf c i).map (f ≫ x).op a
  rw [← CommGrpCat.comp_apply, ← Functor.map_comp]
  rfl

omit [GeometricallyIntegral c] in
/-- Restricting the basepoint class gives the constant point family on every test. -/
theorem modulusGroundClass_abel
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    (T : Over (Spec (CommRingCat.of R))) :
    modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T =
      RigidifiedLineBundle.classOf (modulusAbelBundleAt c i
        (modulusConstantPoint c i ⟨ε.left, Over.w ε⟩ T.hom)) := by
  let p : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
    Over.homMk T.hom (Category.comp_id T.hom)
  exact modulusAbelPointClass_naturality c i p ε

/-- The actual point-minus-basepoint class, with its proved geometric-fibre zero condition. -/
def modulusAbelZeroClass
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusPicardZeroSubgroup c i T :=
  ⟨modulusAbelPointClass c i x /
      modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T, by
    rw [modulusGroundClass_abel]
    let M := modulusAbelBundleAt c i (⟨x.left, Over.w x⟩ :
      SchemeHomOver T.hom ((modulusComplement i).ι ≫ c))
    let N := modulusAbelBundleAt c i
      (modulusConstantPoint c i ⟨ε.left, Over.w ε⟩ T.hom)
    change RigidifiedLineBundle.classOf M / RigidifiedLineBundle.classOf N ∈ _
    rw [div_eq_mul_inv, ← RigidifiedLineBundle.classOf_dual]
    exact modulusAbelDifference_mem_zero c i ⟨ε.left, Over.w ε⟩ ⟨x.left, Over.w x⟩⟩

/-- The zero classes commute with every test-scheme restriction. -/
theorem modulusAbelZeroClass_naturality
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (x : T ⟶ Over.mk ((modulusComplement i).ι ≫ c)) :
    (modulusPicardZeroGroupPresheaf c i).map f.op (modulusAbelZeroClass c i ε x) =
      modulusAbelZeroClass c i ε (f ≫ x) := by
  apply Subtype.ext
  let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) →*
      RigidifiedLineBundle.Classes (modulusBaseChange c i T'.hom) :=
    ((modulusPicardGroupPresheaf c i).map f.op).hom
  have hx : m (modulusAbelPointClass c i x) = modulusAbelPointClass c i (f ≫ x) :=
    modulusAbelPointClass_naturality c i f x
  have hb : m (modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T) =
      modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T' :=
    modulusGroundClass_naturality c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) f
  change m (modulusAbelPointClass c i x /
      modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T) = _
  rw [m.map_div, hx, hb]
  rfl

/-- The selected basepoint has the unit class, with its chosen modulus frame. -/
theorem modulusAbelZeroClass_basepoint
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c)) :
    modulusAbelZeroClass c i ε ε = 1 := by
  apply Subtype.ext
  change modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε /
    modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε)
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) = 1
  have hp : (Over.homMk (𝟙 (Spec (CommRingCat.of R)))
      (Category.comp_id (𝟙 (Spec (CommRingCat.of R)))) :
        Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
          Over.mk (𝟙 (Spec (CommRingCat.of R)))) = 𝟙 _ :=
    Over.OverMorphism.ext rfl
  have hb : modulusGroundClass c i (modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε)
      (Over.mk (𝟙 (Spec (CommRingCat.of R)))) = modulusAbelPointClass c i
        (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε := by
    let b : (modulusPicardGroupPresheaf c i).obj
        (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :=
      modulusAbelPointClass c i (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε
    change (modulusPicardGroupPresheaf c i).map
      (Over.homMk (𝟙 (Spec (CommRingCat.of R)))
        (Category.comp_id (𝟙 (Spec (CommRingCat.of R))))).op b = b
    rw [hp, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hb]
  exact div_self' (modulusAbelPointClass c i
    (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε)

end AlgebraicGeometry.GeneralizedJacobian
