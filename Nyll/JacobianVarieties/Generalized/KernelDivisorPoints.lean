/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorClassTransitionPoints
import Nyll.JacobianVarieties.Generalized.ModulusTransitionTorsor

/-! # Divisor classes and points of the actual ordinary-projection fibre

The scheme-theoretic identity fibre has precisely the expected parameter
points. On a geometric curve model, the full divisor-class comparison
identifies these actual fibre points with the kernel of forgetting the
modulus on divisor classes.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual identity-fibre scheme represents the pointwise kernel on
every parameter scheme, including nonreduced parameter schemes. -/
def kernelPointsEquiv (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ groupKernelScheme c D) ≃
      {p : T ⟶ (groupScheme c D).X //
        p ≫ (groupProjection c D).hom.hom.hom = 1} where
  toFun x := ⟨x ≫ groupKernelInclusion c D, by
    rw [Category.assoc, groupKernelInclusion_condition, MonObj.comp_one]⟩
  invFun p :=
    let h : p.1.left ≫ (groupProjection c D).hom.hom.hom.left =
        T.hom ≫ (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
          (ordinaryGroupScheme c).X).left := by
      let b : T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
        Over.homMk T.hom (Category.comp_id _)
      exact congrArg Over.Hom.left (p.2.trans (MonObj.comp_one b).symm)
    Over.homMk (pullback.lift p.1.left T.hom h) (pullback.lift_snd _ _ _)
  left_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w x).symm
  right_inv p := by
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

end AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

open AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual ordinary-Jacobian projection has exactly the divisor-class
forgetful kernel under the canonical full-modulus comparison. -/
theorem divisorClassPointEquiv_projection_kernel
    (z : (M.functionFieldModulus D).ClassGroupZero) :
    (M.divisorClassPointEquiv D z).toMul ≫
        (groupProjection M.toBase D).hom.hom.hom = 1 ↔
      (M.functionFieldModulus D).toPic0 z = 0 := by
  let D₀ := RelEffCartierDiv.empty M.toBase (𝟙 (Spec (CommRingCat.of K)))
  let hD₀ : D.I ≤ D₀.I := D₀.I_eq_top_of_degree_zero.symm ▸ le_top
  let τ := (GeneralizedJacobian.transition M.toBase D D₀ hD₀).hom.hom.hom
  let e : (groupScheme M.toBase D₀).X ≅ (ordinaryGroupScheme M.toBase).X :=
    (CommGrp.forget _).mapIso (emptyModulusGroupIso M.toBase D₀)
  have he : τ ≫ e.hom = (groupProjection M.toBase D).hom.hom.hom :=
    transitionAlong_groupProjection M.toBase D D₀
      (Scheme.IdealSheafData.inclusion hD₀) (modulusIdealInclusion_curve M.toBase D D₀ hD₀)
  have hker : (M.divisorClassPointEquiv D z).toMul ≫ τ = 1 ↔
      (M.functionFieldModulus D).toPic0 z = 0 :=
    M.divisorClassPointEquiv_emptyTransition_kernel D D₀ z
  rw [← hker]
  have h1 : (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D₀).X) ≫
      e.hom = 1 :=
    map_one (IsMonHom.monoidHom (groupProjection M.toBase D₀).hom.hom.hom _)
  constructor
  · intro hp
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, he, hp, h1]
  · intro hp
    rw [← he, ← Category.assoc, hp, h1]

/-- Divisor classes in the forgetful kernel correspond to points of the
actual scheme fibre, using its pullback lift rather than an assumed comparison. -/
def kernelDivisorPointEquiv :
    (M.functionFieldModulus D).toPic0.ker ≃
      (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ groupKernelScheme M.toBase D) :=
  (Equiv.subtypeEquiv
    ((M.divisorClassPointEquiv D).toEquiv.trans Additive.toMul)
    (fun z => (M.divisorClassPointEquiv_projection_kernel D z).symm)).trans
      (kernelPointsEquiv M.toBase D _).symm

/-- The fibre point lifts the original divisor-class point through the
actual kernel inclusion, so the comparison preserves its boundary value. -/
theorem kernelDivisorPointEquiv_inclusion
    (z : (M.functionFieldModulus D).toPic0.ker) :
    M.kernelDivisorPointEquiv D z ≫ groupKernelInclusion M.toBase D =
      (M.divisorClassPointEquiv D z.1).toMul := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

end AlgebraicCurve.CurveModel
