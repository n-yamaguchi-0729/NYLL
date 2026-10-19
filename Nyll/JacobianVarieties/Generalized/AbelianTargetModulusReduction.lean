/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ProperRationalMapModulus
import Nyll.JacobianVarieties.Generalized.GeometricModulusPointedUniversalProperty
import Nyll.JacobianVarieties.Generalized.ModulusAbelTransition
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessGeometric
import Nyll.JacobianVarieties.Generalized.ModulusTransitionFibers

/-! # Abelian targets do not detect the modulus

Every group homomorphism to an abelian variety descends uniquely through
every smaller modulus, including the empty modulus. Unlike the torus case,
the supports need not agree. The proof extends the actual Abel composite
over the whole curve and uses the constructed geometric universal property.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d e : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (E : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of K))))
  (hDE : D.I ≤ E.I)

/-- Maps to an abelian variety are unchanged by any reduction of the
modulus, even a change of support or passage to the empty modulus. -/
theorem transition_abelianHom_bijective
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme H] :
    Function.Bijective
      (fun ψ : groupScheme c E ⟶ H => transition c D E hDE ≫ ψ) := by
  let r := modulusComplementRestriction c (Scheme.IdealSheafData.inclusion hDE)
    (modulusIdealInclusion_curve c D E hDE)
  let εE := ε ≫ r
  let aD := modulusAbelMap c D ε
  let aE := modulusAbelMap c E εE
  have ha : aD ≫ (transition c D E hDE).hom.hom.hom = r ≫ aE :=
    modulusAbelMap_transitionAlong c D E (Scheme.IdealSheafData.inclusion hDE)
      (modulusIdealInclusion_curve c D E hDE) ε
  constructor
  · intro ψ χ h
    have : Surjective (transition c D E hDE).hom.hom.hom.left :=
      (transition_geometry c D E hDE).2.1
    have : SmoothOfRelativeDimension (geometricGenus K c + (e - 1))
        (groupScheme c E).X.hom := (geometry c E).1
    have : Smooth (groupScheme c E).X.hom :=
      SmoothOfRelativeDimension.smooth (geometricGenus K c + (e - 1)) _
    have : IsReduced (groupScheme c E).X.left :=
      isReduced_of_smooth_over_field (g := (groupScheme c E).X.hom) inferInstance
    apply CommGrp.hom_ext
    apply Over.OverMorphism.ext
    exact ext_of_isDominant_of_isSeparated H.X.hom
      ((Over.w ψ.hom.hom.hom).trans (Over.w χ.hom.hom.hom).symm)
      (transition c D E hDE).hom.hom.hom.left
      (congrArg (fun f : groupScheme c D ⟶ H => f.hom.hom.hom.left) h)
  · intro φ
    let UD := modulusComplement (modulusCurveMap D)
    let UE := modulusComplement (modulusCurveMap E)
    let qD := aD ≫ φ.hom.hom.hom
    obtain ⟨x⟩ := modulusComplement_nonempty c D
    obtain ⟨q, hq, _⟩ := existsUnique_extension_to_abelianScheme c H UD
      ⟨x.1, x.2⟩ qD
    let jD : Over.mk (UD.ι ≫ c) ⟶ Over.mk c := Over.homMk UD.ι rfl
    let jE : Over.mk (UE.ι ≫ c) ⟶ Over.mk c := Over.homMk UE.ι rfl
    let qE : Over.mk (UE.ι ≫ c) ⟶ H.X := jE ≫ q
    have hr : r ≫ qE = qD := by
      rw [← hq]
      change r ≫ (jE ≫ q) = jD ≫ q
      rw [← Category.assoc]
      congr 1
      apply Over.OverMorphism.ext
      exact Scheme.homOfLE_ι C
        (modulusComplement_le_of_restriction (Scheme.IdealSheafData.inclusion hDE)
          (modulusIdealInclusion_curve c D E hDE))
    have hε : εE ≫ qE = 1 := by
      change (ε ≫ r) ≫ qE = 1
      rw [Category.assoc, hr]
      change ε ≫ (aD ≫ φ.hom.hom.hom) = 1
      rw [← Category.assoc, modulusAbelMap_basepoint, MonObj.one_comp]
    have hm := geometricRegularMapHasModulus_of_isAbelianScheme c H E qE
    obtain ⟨ψ, hψ, _⟩ := existsUnique_groupHom_geometricModulus c E εE H qE hm hε
    refine ⟨ψ, ?_⟩
    apply modulusAbel_groupHom_ext c D ε H
    change aD ≫ (transition c D E hDE).hom.hom.hom ≫ ψ.hom.hom.hom = qD
    rw [← Category.assoc, ha, Category.assoc, hψ]
    exact hr

/-- Every abelian-valued group morphism kills the entire transition kernel
on every test scheme, with no equality-of-support assumption. -/
theorem abelianHom_kills_transition_kernel
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme H]
    (φ : groupScheme c D ⟶ H)
    {S : Over (Spec (CommRingCat.of K))} (x : S ⟶ (groupScheme c D).X)
    (hx : x ≫ (transition c D E hDE).hom.hom.hom = 1) :
    x ≫ φ.hom.hom.hom = 1 := by
  obtain ⟨ψ, hψ⟩ := (transition_abelianHom_bijective c D E hDE ε H).surjective φ
  rw [← hψ]
  change x ≫ (transition c D E hDE).hom.hom.hom ≫ ψ.hom.hom.hom = 1
  rw [← Category.assoc, hx, MonObj.one_comp]

end AlgebraicGeometry.GeneralizedJacobian
