/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.TorusRationalMapModulus
import Nyll.JacobianVarieties.Generalized.ProperRationalMapModulus
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalEvaluation
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField
import Nyll.SchemeTheory.GroupSchemes.AbelianScheme
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-! # Full moduli for product targets

An actual map to a product has a geometric full modulus exactly when its
two projections do. Pullback preserves the joint injectivity of the two
projections. In particular, a map to a torus times an abelian variety has
the modulus given by its original domain, over every ground field.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory
open AlgebraicGeometry.GeneralizedJacobian AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj BigOperators

namespace AlgebraicCurve.CurveModel

private theorem regularMapHasModulus_of_jointly_injective
    {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (G H J : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ G.X)
    (φ : G ⟶ H) (ψ : G ⟶ J)
    (hinj : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X,
      x ≫ φ.hom.hom.hom = y ≫ φ.hom.hom.hom →
      x ≫ ψ.hom.hom.hom = y ≫ ψ.hom.hom.hom → x = y)
    (hφ : M.regularMapHasModulus D H
      ((commGroupPointEquiv H _).symm (q ≫ φ.hom.hom.hom)))
    (hψ : M.regularMapHasModulus D J
      ((commGroupPointEquiv J _).symm (q ≫ ψ.hom.hom.hom))) :
    M.regularMapHasModulus D G ((commGroupPointEquiv G _).symm q) := by
  have hcurve : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : HasPrincipalDivisors K F := hcurve.toHasPrincipalDivisors
  let A := Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X)
  let a : Place K F → A :=
    M.regularMapValues (modulusComplement (modulusCurveMap D)) G ((commGroupPointEquiv G _).symm q)
  let f := (IsMonHom.monoidHom φ.hom.hom.hom
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive
  let g := (IsMonHom.monoidHom ψ.hom.hom.hom
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive
  let E := M.cartierModulus (modulusCurveIdeal D) (modulusCurveIdeal_isInvertible D)
  have hf : E.HasModulus (fun v => f (a v)) := by
    change E.HasModulus _ at hφ
    have he := funext (M.regularMapValues_comp (modulusComplement (modulusCurveMap D))
      G H ((commGroupPointEquiv G _).symm q) φ)
    rw [Equiv.apply_symm_apply] at he
    rw [he] at hφ
    exact hφ
  have hg : E.HasModulus (fun v => g (a v)) := by
    change E.HasModulus _ at hψ
    have he := funext (M.regularMapValues_comp (modulusComplement (modulusCurveMap D))
      G J ((commGroupPointEquiv G _).symm q) ψ)
    rw [Equiv.apply_symm_apply] at he
    rw [he] at hψ
    exact hψ
  intro r hr
  have hf0 : f (∑ᶠ v : Place K F, v.ord (r : F) • a v) = 0 := by
    rw [f.map_finsum (principalEvaluation_finiteSupport a r)]
    simpa only [map_zsmul] using hf r hr
  have hg0 : g (∑ᶠ v : Place K F, v.ord (r : F) • a v) = 0 := by
    rw [g.map_finsum (principalEvaluation_finiteSupport a r)]
    simpa only [map_zsmul] using hg r hr
  apply Additive.toMul.injective
  apply hinj
  · rw [show Additive.toMul (0 : A) = 1 from rfl, MonObj.one_comp]
    exact congrArg Additive.toMul hf0
  · rw [show Additive.toMul (0 : A) = 1 from rfl, MonObj.one_comp]
    exact congrArg Additive.toMul hg0

end AlgebraicCurve.CurveModel

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (G H : CommGrp (Over (Spec (CommRingCat.of K))))
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
    (GroupSchemes.product G H).X)

/-- A full geometric modulus for a product-valued map is equivalent to the
two coordinate conditions, without a rational basepoint or splitting assumption. -/
theorem geometricRegularMapHasModulus_product_iff :
    geometricRegularMapHasModulus c D (GroupSchemes.product G H) q ↔
      geometricRegularMapHasModulus c D G (q ≫ fst G.X H.X) ∧
      geometricRegularMapHasModulus c D H (q ≫ snd G.X H.X) := by
  have hf : IsMonHom (fst G.X H.X) := inferInstance
  have hs : IsMonHom (snd G.X H.X) := inferInstance
  let π₁ : GroupSchemes.product G H ⟶ G :=
    InducedCategory.homMk (Grp.homMk' { hom := fst G.X H.X, isMonHom_hom := hf })
  let π₂ : GroupSchemes.product G H ⟶ H :=
    InducedCategory.homMk (Grp.homMk' { hom := snd G.X H.X, isMonHom_hom := hs })
  constructor
  · intro h
    exact ⟨geometricRegularMapHasModulus_comp c D _ G q h π₁,
      geometricRegularMapHasModulus_comp c D _ H q h π₂⟩
  · rintro ⟨hG, hH⟩ L fieldL algebraL closedL cL DL algL ML qL
    let B := Over.pullback (specMap K L)
    let P := (GroupSchemes.baseChange (specMap K L)).obj (GroupSchemes.product G H)
    let G_L :=  (GroupSchemes.baseChange (specMap K L)).obj G
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let p₁ := (GroupSchemes.baseChange (specMap K L)).map π₁
    let p₂ := (GroupSchemes.baseChange (specMap K L)).map π₂
    apply ML.regularMapHasModulus_of_jointly_injective DL P G_L HL qL p₁ p₂
    · intro x y h₁ h₂
      change Over.mk (𝟙 (Spec (CommRingCat.of L))) ⟶ B.obj (G.X ⊗ H.X) at x y
      let e := Functor.Monoidal.μIso B G.X H.X
      apply (cancel_mono e.inv).mp
      apply CartesianMonoidalCategory.hom_ext
      · have he : e.inv ≫ fst (B.obj G.X) (B.obj H.X) = B.map (fst G.X H.X) := by
          rw [← Functor.Monoidal.μ_fst B G.X H.X]
          exact e.inv_hom_id_assoc _
        rw [Category.assoc, Category.assoc, he]
        exact h₁
      · have he : e.inv ≫ snd (B.obj G.X) (B.obj H.X) = B.map (snd G.X H.X) := by
          rw [← Functor.Monoidal.μ_snd B G.X H.X]
          exact e.inv_hom_id_assoc _
        rw [Category.assoc, Category.assoc, he]
        exact h₂
    · have he := modulusGroupMapScalarExtension_comp c D L (GroupSchemes.product G H) G q π₁
      exact (congrArg (fun r => ML.regularMapHasModulus DL G_L
        ((commGroupPointEquiv G_L ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm r))
          he).mp (hG L)
    · have he := modulusGroupMapScalarExtension_comp c D L (GroupSchemes.product G H) H q π₂
      exact (congrArg (fun r => ML.regularMapHasModulus DL HL
        ((commGroupPointEquiv HL ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm r))
          he).mp (hH L)

/-- Every map to a torus times an abelian variety has the geometric full
modulus of its original domain. The torus may be nonsplit and the ground
field imperfect; no stronger modulus is requested from the caller. -/
theorem geometricRegularMapHasModulus_torus_abelian_product
    [IsTorus G] [IsAbelianScheme H] :
    geometricRegularMapHasModulus c D (GroupSchemes.product G H) q :=
  (geometricRegularMapHasModulus_product_iff c D G H q).mpr
    ⟨geometricRegularMapHasModulus_of_isTorus c G D _,
      geometricRegularMapHasModulus_of_isAbelianScheme c H D _⟩

end AlgebraicGeometry.GeneralizedJacobian
