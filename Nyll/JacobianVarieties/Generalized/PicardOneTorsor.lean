/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardOne
import Nyll.JacobianVarieties.Generalized.ModulusTwoPointDifference

/-!
# Actual tensor action and difference on intrinsic Picard-one

Both operations and their identities are independent of a chosen point.
A point of the complement proves nonemptiness and therefore supplies an actual
torsor on each test scheme. The fieldwise closure proofs use the original
rigidified classes and the proved algebraic triviality of arbitrary point differences.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- Concrete degree-one classes with their original rigidifications. -/
abbrev ModulusPicardOneClasses (T : Over (Spec (CommRingCat.of R))) :=
  {x : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) //
    x ∈ (modulusPicardOneSubfunctor c i).obj (op T)}

/-- Tensor product by a zero class preserves the intrinsic degree-one condition. -/
def modulusPicardOneAction (T : Over (Spec (CommRingCat.of R)))
    (g : modulusPicardZeroSubgroup c i T) (x : ModulusPicardOneClasses c i T) :
    ModulusPicardOneClasses c i T :=
  ⟨g.1 * x.1, by
    intro k _ _ t s
    obtain ⟨P, hP⟩ := x.2 k t s
    refine ⟨P, ?_⟩
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      ((modulusPicardGroupPresheaf c i).map s.op).hom
    let bP : RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
      modulusAbelPointClass c i (T := Over.mk t) P
    change m (g.1 * x.1) / bP ∈ _
    rw [m.map_mul, mul_div_assoc]
    exact (modulusPicardZeroSubgroup c i (Over.mk t)).mul_mem
      ((modulusPicardZeroSubfunctor c i).map s.op g.2) hP⟩

/-- The actual difference of two intrinsic degree-one classes is a zero class. -/
def modulusPicardOneDifference (T : Over (Spec (CommRingCat.of R)))
    (x y : ModulusPicardOneClasses c i T) : modulusPicardZeroSubgroup c i T :=
  ⟨x.1 / y.1, by
    apply modulusPicardZero_of_fieldRestrictions c i T.hom
    intro k _ _ s
    let S := Over.mk (s ≫ T.hom)
    let f : S ⟶ T := Over.homMk s rfl
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i S.hom) :=
      ((modulusPicardGroupPresheaf c i).map f.op).hom
    obtain ⟨P, hP⟩ := x.2 k S.hom f
    obtain ⟨Q, hQ⟩ := y.2 k S.hom f
    let bP : RigidifiedLineBundle.Classes (modulusBaseChange c i S.hom) :=
      modulusAbelPointClass c i (T := S) P
    let bQ : RigidifiedLineBundle.Classes (modulusBaseChange c i S.hom) :=
      modulusAbelPointClass c i (T := S) Q
    have hPQ : bP / bQ ∈ modulusPicardZeroSubgroup c i S :=
      modulusAbelPointClass_div_mem_zero c i (T := S) P Q
    have hxQ := (modulusPicardZeroSubgroup c i S).mul_mem hP hPQ
    change m x.1 / bP * (bP / bQ) ∈ _ at hxQ
    rw [div_mul_div_cancel] at hxQ
    have h := (modulusPicardZeroSubgroup c i S).div_mem hxQ hQ
    change m x.1 / bQ / (m y.1 / bQ) ∈ _ at h
    rw [div_div_div_cancel_right] at h
    change m (x.1 / y.1) ∈ _
    rw [m.map_div]
    exact h⟩

omit [GeometricallyIntegral c] in
/-- The tensor unit fixes each intrinsic degree-one class. -/
theorem modulusPicardOneAction_one (T : Over (Spec (CommRingCat.of R)))
    (x : ModulusPicardOneClasses c i T) : modulusPicardOneAction c i T 1 x = x :=
  Subtype.ext (one_mul x.1)

omit [GeometricallyIntegral c] in
/-- The intrinsic action is associative for the actual tensor-product group. -/
theorem modulusPicardOneAction_mul (T : Over (Spec (CommRingCat.of R)))
    (g h : modulusPicardZeroSubgroup c i T) (x : ModulusPicardOneClasses c i T) :
    modulusPicardOneAction c i T (g * h) x =
      modulusPicardOneAction c i T g (modulusPicardOneAction c i T h x) :=
  Subtype.ext (mul_assoc g.1 h.1 x.1)

/-- Difference followed by tensor action recovers the first actual degree-one class. -/
theorem modulusPicardOneDifference_action (T : Over (Spec (CommRingCat.of R)))
    (x y : ModulusPicardOneClasses c i T) :
    modulusPicardOneAction c i T (modulusPicardOneDifference c i T x y) y = x :=
  Subtype.ext (div_mul_cancel x.1 y.1)

/-- Dividing a translated actual class by that class recovers the acting zero class. -/
theorem modulusPicardOneAction_difference (T : Over (Spec (CommRingCat.of R)))
    (g : modulusPicardZeroSubgroup c i T) (x : ModulusPicardOneClasses c i T) :
    modulusPicardOneDifference c i T (modulusPicardOneAction c i T g x) x = g :=
  Subtype.ext (mul_div_cancel_right g.1 x.1)

omit [GeometricallyIntegral c] in
/-- Tensor action commutes with every change of test scheme. -/
theorem modulusPicardOneAction_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (g : modulusPicardZeroSubgroup c i T) (x : ModulusPicardOneClasses c i T) :
    (modulusPicardOnePresheaf c i).map f.op (modulusPicardOneAction c i T g x) =
      modulusPicardOneAction c i T'
        ((modulusPicardZeroGroupPresheaf c i).map f.op g)
        ((modulusPicardOnePresheaf c i).map f.op x) := by
  apply Subtype.ext
  exact ((modulusPicardGroupPresheaf c i).map f.op).hom.map_mul g.1 x.1

/-- Actual differences also commute with every change of test scheme. -/
theorem modulusPicardOneDifference_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (x y : ModulusPicardOneClasses c i T) :
    (modulusPicardZeroGroupPresheaf c i).map f.op
        (modulusPicardOneDifference c i T x y) =
      modulusPicardOneDifference c i T'
        ((modulusPicardOnePresheaf c i).map f.op x)
        ((modulusPicardOnePresheaf c i).map f.op y) := by
  apply Subtype.ext
  exact ((modulusPicardGroupPresheaf c i).map f.op).hom.map_div x.1 y.1

/-- The translation coordinate realizes the intrinsic action as actual tensor product. -/
theorem modulusPicardOneTranslationEquiv_action
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    (T : Over (Spec (CommRingCat.of R)))
    (g : modulusPicardZeroSubgroup c i T) (x : ModulusPicardOneClasses c i T) :
    modulusPicardOneTranslationEquiv c i ε T
        (g * (modulusPicardOneTranslationEquiv c i ε T).symm x) =
      modulusPicardOneAction c i T g x := by
  apply Subtype.ext
  change (g.1 * (x.1 / modulusGroundClass c i
    (modulusAbelPointClass c i (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T)) *
      modulusGroundClass c i
        (modulusAbelPointClass c i (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T =
      g.1 * x.1
  rw [mul_assoc, div_mul_cancel]

/-- Dividing translation coordinates gives the intrinsic rigidified difference. -/
theorem modulusPicardOneTranslationEquiv_difference
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    (T : Over (Spec (CommRingCat.of R))) (x y : ModulusPicardOneClasses c i T) :
    (modulusPicardOneTranslationEquiv c i ε T).symm x /
        (modulusPicardOneTranslationEquiv c i ε T).symm y =
      modulusPicardOneDifference c i T x y := by
  apply Subtype.ext
  exact div_div_div_cancel_right x.1 y.1
    (modulusGroundClass c i
      (modulusAbelPointClass c i (T := Over.mk (𝟙 (Spec (CommRingCat.of R)))) ε) T)

/-- An actual complement point proves nonemptiness; action and difference remain intrinsic. -/
@[instance_reducible] def modulusPicardOneTorsor
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
      Over.mk ((modulusComplement i).ι ≫ c))
    (T : Over (Spec (CommRingCat.of R))) :
    Torsor (modulusPicardZeroSubgroup c i T) (ModulusPicardOneClasses c i T) where
  smul := modulusPicardOneAction c i T
  one_smul x := Subtype.ext (one_mul x.1)
  mul_smul g h x := Subtype.ext (mul_assoc g.1 h.1 x.1)
  sdiv := modulusPicardOneDifference c i T
  nonempty := ⟨modulusPicardOneTranslationEquiv c i ε T 1⟩
  sdiv_smul' := modulusPicardOneDifference_action c i T
  smul_sdiv' := modulusPicardOneAction_difference c i T

end AlgebraicGeometry.GeneralizedJacobian
