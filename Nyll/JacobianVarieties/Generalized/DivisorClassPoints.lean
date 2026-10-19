/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorZeroClassAbel
import Nyll.JacobianVarieties.Generalized.RigidifiedEulerZeroComparison
import Nyll.JacobianVarieties.Generalized.ModulusCurveIdeal
import Nyll.JacobianVarieties.Generalized.ModulusClosedFieldPoints
import Nyll.JacobianVarieties.Generalized.ModulusIdentityPointComparison

/-!
# Full-modulus degree-zero divisor classes are generalized Jacobian points

The comparison uses the actual Cartier ideal of the specified relative
modulus, its full valuation multiplicities, the proved principal kernel and
divisor representatives, and the constructed generalized Jacobian. All choices
of sections and a two-affine cover are supplied by the given curve geometry.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GeneralizedJacobian
open AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) [GeometricallyIntegral M.toBase]

private def comparisonCover : M.C.TwoAffineOpenCover := by
  have : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  have hx := nonempty_inter_closedPoints
    (Z := (Set.univ : Set M.C)) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let x := hx.choose
  have hxc : IsClosed ({x} : Set M.C) := hx.choose_spec.2
  let ε := pointOfClosedPoint M.toBase x hxc
  have hε : ε ≫ M.toBase = 𝟙 _ := pointOfClosedPoint_comp M.toBase x hxc
  exact (SmoothProperCurve.exists_twoAffineOpenCover_of_section K M.toBase ⟨ε, hε⟩).choose

variable {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))

/-- The full function-field modulus of the given actual relative Cartier divisor. -/
def functionFieldModulus : Modulus K F :=
  M.cartierModulus (modulusCurveIdeal D) (modulusCurveIdeal_isInvertible D)

/-- The genuine degree-zero divisor class group with the full specified modulus
is canonically identified with points of the constructed generalized Jacobian.
No representability, divisor representative, principal kernel, or comparison
is supplied as an assumption. -/
def divisorClassPointEquiv : (M.functionFieldModulus D).ClassGroupZero ≃+
    Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D).X) :=
  (M.rigidifiedZeroClassEquiv (modulusCurveIdeal D) (modulusCurveIdeal_isInvertible D)
    (comparisonCover M)).trans
      ((closedModulusEulerZeroEquiv M.toBase (modulusCurveMap D) (comparisonCover M)).trans
        (rigidifiedZeroClassPointEquiv M.toBase D).toAdditive)

/-- The constructed point is the point classifying the original full-modulus
rigidified bundle of the given degree-zero divisor. -/
theorem divisorClassPointEquiv_classifies
    (E : (M.functionFieldModulus D).divAwayZero) :
    (pointEquiv M.toBase D (Over.mk (𝟙 (Spec (CommRingCat.of K)))))
        (Additive.toMul (M.divisorClassPointEquiv D ((M.functionFieldModulus D).mkZero E))) =
      modulusPicardZeroFieldEquiv M.toBase (modulusCurveMap D)
        (Additive.toMul (closedModulusEulerZeroEquiv M.toBase (modulusCurveMap D)
          (comparisonCover M) (M.rigidifiedDivisorZeroHom (modulusCurveIdeal D)
            (modulusCurveIdeal_isInvertible D) (comparisonCover M) E))) := by
  change (pointEquiv M.toBase D (Over.mk (𝟙 (Spec (CommRingCat.of K)))))
    ((pointEquiv M.toBase D (Over.mk (𝟙 (Spec (CommRingCat.of K))))).symm _) = _
  exact (pointEquiv M.toBase D (Over.mk (𝟙 (Spec (CommRingCat.of K))))).apply_symm_apply _

/-- The actual place corresponding to a field point of the modulus complement. -/
def modulusPlace
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) : Place K F :=
  M.pointEquivPlace (modulusComplementSection M.toBase (modulusCurveMap D)
    ⟨x.left, Over.w x⟩)

omit [GeometricallyIntegral M.toBase] in
/-- A point of the actual open complement avoids the full function-field modulus. -/
theorem functionFieldModulus_modulusPlace_eq_zero
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) :
    M.functionFieldModulus D (M.modulusPlace D x) = 0 := by
  apply (M.cartierModulus_eq_zero_iff (modulusCurveIdeal D)
    (modulusCurveIdeal_isInvertible D) (M.modulusPlace D x)).mpr
  change (M.placeEquiv.symm (M.placeEquiv (pointEquivClosedPoint M.toBase
    (modulusComplementSection M.toBase (modulusCurveMap D) ⟨x.left, Over.w x⟩)))).1 ∉ _
  rw [M.placeEquiv.symm_apply_apply]
  exact (x.left (IsLocalRing.closedPoint K)).property

omit [GeometricallyIntegral M.toBase] in
private theorem pointBundle_class_comparison
    (x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) :
    closedModulusIdentityClassesEquiv M.toBase (modulusCurveMap D)
      (classOf (M.rigidifiedPointBundle (modulusCurveIdeal D)
        (modulusCurveIdeal_isInvertible D) (M.modulusPlace D x)
        (M.functionFieldModulus_modulusPlace_eq_zero D x))) =
      classOf (modulusAbelBundleAt M.toBase (modulusCurveMap D) ⟨x.left, Over.w x⟩) := by
  let p := modulusComplementSection M.toBase (modulusCurveMap D) ⟨x.left, Over.w x⟩
  have hp : pointOfClosedPoint M.toBase (M.placeEquiv.symm (M.modulusPlace D x)).1
      (M.placeEquiv.symm (M.modulusPlace D x)).2 =
        x.left ≫ (modulusComplement (modulusCurveMap D)).ι :=
    congrArg Subtype.val (M.pointEquivPlace.symm_apply_apply p)
  have ha : ∀ y : (modulusCurveIdeal D).subscheme,
      (modulusCurveIdeal D).subschemeι.base y ∉
        (x.left ≫ (modulusComplement (modulusCurveMap D)).ι).ker.support := by
    simpa only [hp] using M.pointIdeal_avoids_modulus (modulusCurveIdeal D)
      (modulusCurveIdeal_isInvertible D) (M.modulusPlace D x)
      (M.functionFieldModulus_modulusPlace_eq_zero D x)
  simpa only [rigidifiedPointBundle, hp] using
    closedModulusIdentityClassesEquiv_ofPoint M.toBase (modulusCurveMap D)
      ⟨x.left, Over.w x⟩ ha

omit [IsAlgClosed K] in
private theorem abelZeroClass_val_ground
    (ε x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) :
    (modulusAbelZeroClass M.toBase (modulusCurveMap D) ε x).1 =
      classOf (modulusAbelBundleAt M.toBase (modulusCurveMap D) ⟨x.left, Over.w x⟩) /
        classOf (modulusAbelBundleAt M.toBase (modulusCurveMap D) ⟨ε.left, Over.w ε⟩) := by
  dsimp only [modulusAbelZeroClass]
  rw [modulusGroundClass_abel]
  have hconst : modulusConstantPoint M.toBase (modulusCurveMap D)
      ⟨ε.left, Over.w ε⟩ (Over.mk (𝟙 (Spec (CommRingCat.of K)))).hom =
        ⟨ε.left, Over.w ε⟩ :=
    Subtype.ext (Category.id_comp ε.left)
  rw [hconst]
  rfl

private theorem zeroClass_abel_comparison (𝒱 : M.C.TwoAffineOpenCover)
    (ε x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) :
    Additive.toMul (closedModulusEulerZeroEquiv M.toBase (modulusCurveMap D) 𝒱
      (M.rigidifiedZeroClassEquiv (modulusCurveIdeal D) (modulusCurveIdeal_isInvertible D) 𝒱
        ((M.functionFieldModulus D).classAbel (M.modulusPlace D ε)
          (M.functionFieldModulus_modulusPlace_eq_zero D ε)
          (M.place_deg_eq_one (M.modulusPlace D ε)) (M.modulusPlace D x)))) =
      modulusAbelZeroClass M.toBase (modulusCurveMap D) ε x := by
  let I := modulusCurveIdeal D
  let hI := modulusCurveIdeal_isInvertible D
  let E := (M.functionFieldModulus D).classAbel (M.modulusPlace D ε)
    (M.functionFieldModulus_modulusPlace_eq_zero D ε)
    (M.place_deg_eq_one (M.modulusPlace D ε)) (M.modulusPlace D x)
  apply Subtype.ext
  change closedModulusIdentityClassesEquiv M.toBase (modulusCurveMap D)
    (Additive.toMul (M.rigidifiedZeroClassEquiv I hI 𝒱 E).1) = _
  rw [abelZeroClass_val_ground M D ε x]
  have he := M.rigidifiedZeroClassEquiv_classAbel I hI 𝒱
    (M.modulusPlace D ε) (M.modulusPlace D x)
    (M.functionFieldModulus_modulusPlace_eq_zero D ε)
    (M.functionFieldModulus_modulusPlace_eq_zero D x)
  change (M.rigidifiedZeroClassEquiv I hI 𝒱 E).1 = _ at he
  rw [he]
  change closedModulusIdentityClassesEquiv M.toBase (modulusCurveMap D)
    (classOf (M.rigidifiedPointBundle I hI (M.modulusPlace D x)
        (M.functionFieldModulus_modulusPlace_eq_zero D x)) /
      classOf (M.rigidifiedPointBundle I hI (M.modulusPlace D ε)
        (M.functionFieldModulus_modulusPlace_eq_zero D ε))) = _
  rw [map_div, pointBundle_class_comparison M D x, pointBundle_class_comparison M D ε]

/-- The genuine divisor comparison sends the full-modulus Abel class to the
value of the actual constructed Abel morphism. -/
theorem divisorClassPointEquiv_abel
    (ε x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)) :
    M.divisorClassPointEquiv D
      ((M.functionFieldModulus D).classAbel (M.modulusPlace D ε)
        (M.functionFieldModulus_modulusPlace_eq_zero D ε)
        (M.place_deg_eq_one (M.modulusPlace D ε)) (M.modulusPlace D x)) =
      Additive.ofMul (x ≫ modulusAbelMap M.toBase D ε) := by
  change Additive.ofMul (rigidifiedZeroClassPointEquiv M.toBase D
    (Additive.toMul (closedModulusEulerZeroEquiv M.toBase (modulusCurveMap D)
      (comparisonCover M) (M.rigidifiedZeroClassEquiv (modulusCurveIdeal D)
        (modulusCurveIdeal_isInvertible D) (comparisonCover M) _)))) = _
  rw [zeroClass_abel_comparison M D (comparisonCover M) ε x,
    rigidifiedZeroClassPointEquiv_abel]

end AlgebraicCurve.CurveModel
