/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorClassPoints
import Nyll.JacobianVarieties.Generalized.ModulusClassUniversality
import Nyll.JacobianVarieties.Generalized.GeometricIntegrality
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ExtCompEq

/-!
# Uniqueness of actual morphisms out of the generalized Jacobian

The genuine full-modulus divisor comparison proves that actual Abel points
generate the group of field points. Reducedness then detects equality of
morphisms of the constructed group scheme.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))

omit [GeometricallyIntegral M.toBase] in
/-- Every place outside the full modulus comes from an actual point of its
open complement. -/
theorem exists_modulusPlace_eq (w : Place K F) (hw : M.functionFieldModulus D w = 0) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase),
      M.modulusPlace D x = w := by
  let U := modulusComplement (modulusCurveMap D)
  let z := M.placeEquiv.symm w
  have hzc : IsClosed ({z.1} : Set M.C) := z.2
  let p := pointOfClosedPoint M.toBase z.1 hzc
  have hp : p ≫ M.toBase = 𝟙 _ := pointOfClosedPoint_comp M.toBase z.1 hzc
  have hz : z.1 ∈ U :=
    (M.cartierModulus_eq_zero_iff (modulusCurveIdeal D)
      (modulusCurveIdeal_isInvertible D) w).mp hw
  have hr : Set.range p ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨a, rfl⟩
    change pointOfClosedPoint M.toBase z.1 hzc a ∈ U
    rw [pointOfClosedPoint_apply]
    exact hz
  let l := IsOpenImmersion.lift U.ι p hr
  have hl : l ≫ U.ι = p := IsOpenImmersion.lift_fac U.ι p hr
  let x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk (U.ι ≫ M.toBase) :=
    Over.homMk l ((Category.assoc l U.ι M.toBase).symm.trans
      ((congrArg (fun q => q ≫ M.toBase) hl).trans hp))
  refine ⟨x, ?_⟩
  change M.pointEquivPlace (modulusComplementSection M.toBase (modulusCurveMap D)
    ⟨x.left, Over.w x⟩) = w
  have he : modulusComplementSection M.toBase (modulusCurveMap D)
      ⟨x.left, Over.w x⟩ = M.pointEquivPlace.symm w := Subtype.ext hl
  rw [he, M.pointEquivPlace.apply_symm_apply]

/-- Actual Abel points determine a homomorphism on all field points of the
constructed generalized Jacobian. The generation statement is proved from
actual divisor classes, with no generation hypothesis. -/
theorem modulusAbel_points_addHom_ext
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
    {A : Type*} [AddCommGroup A]
    (φ ψ : Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (groupScheme M.toBase D).X) →+ A)
    (heq : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase),
      φ (Additive.ofMul (x ≫ modulusAbelMap M.toBase D ε)) =
        ψ (Additive.ofMul (x ≫ modulusAbelMap M.toBase D ε))) : φ = ψ := by
  have hc := (M.functionFieldModulus D).classAbel_addHom_ext (M.modulusPlace D ε)
    (M.functionFieldModulus_modulusPlace_eq_zero D ε)
    (M.place_deg_eq_one (M.modulusPlace D ε))
    (φ.comp (M.divisorClassPointEquiv D).toAddMonoidHom)
    (ψ.comp (M.divisorClassPointEquiv D).toAddMonoidHom) (fun w hw => by
      obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq D w hw
      change φ (M.divisorClassPointEquiv D _) = ψ (M.divisorClassPointEquiv D _)
      rw [M.divisorClassPointEquiv_abel D ε x]
      exact heq x)
  apply AddMonoidHom.ext
  intro y
  obtain ⟨z, rfl⟩ := (M.divisorClassPointEquiv D).surjective y
  exact DFunLike.congr_fun hc z

/-- Two actual group scheme morphisms agreeing on the pointed Abel morphism
are equal over an algebraically closed field. -/
theorem modulusAbel_groupHom_ext
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    [IsSeparated G.X.hom]
    (f g : groupScheme M.toBase D ⟶ G)
    (heq : modulusAbelMap M.toBase D ε ≫ f.hom.hom.hom =
      modulusAbelMap M.toBase D ε ≫ g.hom.hom.hom) : f = g := by
  have hpoint : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      (groupScheme M.toBase D).X, x ≫ f.hom.hom.hom = x ≫ g.hom.hom.hom := by
    have h := M.modulusAbel_points_addHom_ext D ε
      (IsMonHom.monoidHom f.hom.hom.hom (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive
      (IsMonHom.monoidHom g.hom.hom.hom (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive
      (fun x => by
        change Additive.ofMul ((x ≫ modulusAbelMap M.toBase D ε) ≫ f.hom.hom.hom) =
          Additive.ofMul ((x ≫ modulusAbelMap M.toBase D ε) ≫ g.hom.hom.hom)
        rw [Category.assoc, Category.assoc, heq])
    intro x
    exact congrArg Additive.toMul (DFunLike.congr_fun h (Additive.ofMul x))
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  have : LocallyOfFiniteType (groupScheme M.toBase D).X.hom :=
    (geometry M.toBase D).2.1
  apply ext_of_forall_comp_eq_of_isAlgClosed (groupScheme M.toBase D).X.hom G.X.hom
    (Over.w f.hom.hom.hom) (Over.w g.hom.hom.hom)
  intro x hx
  exact congrArg Over.Hom.left (hpoint (Over.homMk x hx))

end AlgebraicCurve.CurveModel
