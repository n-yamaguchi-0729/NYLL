/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.SchemeTheory.Morphisms.FiniteExtensionPoint

/-! # A complement point over a finite separable extension

Smoothness of the open complement supplies a finite separable intermediate
field in the specified algebraically closed extension. The actual
scalar-extension comparison lifts its point to the complement of the whole
extended modulus, including every multiplicity. No perfectness assumption
on the ground field is needed.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]

/-- A finite separable extension gives an actual rational point outside
the full scalar-extended modulus over an arbitrary ground field. -/
theorem modulusComplement_finiteSeparableExtension_point :
    ∃ E : IntermediateField K Ω, Module.Finite K E ∧ Algebra.IsSeparable K E ∧
      Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶
        Over.mk ((modulusComplement
          (modulusCurveMap (D.changeBaseOfIdentity (specMap K E)))).ι ≫
            baseChange K c E)) := by
  let U := modulusComplement (modulusCurveMap D)
  have : Nonempty U := modulusComplement_nonempty c D
  obtain ⟨E, hE, hsep, p, hp⟩ :=
    exists_point_finite_separable_intermediateField_of_smooth K Ω (U.ι ≫ c)
  let T := Over.mk (𝟙 (Spec (CommRingCat.of E)))
  let pOver : (Over.map (specMap K E)).obj T ⟶ Over.mk (U.ι ≫ c) :=
    Over.homMk p (by
      change p ≫ (U.ι ≫ c) = 𝟙 _ ≫ specMap K E
      rw [Category.id_comp]
      exact hp)
  exact ⟨E, hE, hsep, ⟨divisorScalarExtensionPointLift c D E pOver⟩⟩

/-- A map from the modulus complement supplies a point of its actual
scalar-extended target over a finite separable intermediate field. The
point lies in the image of the same extended curve map. In particular this
constructs a point of a target torsor without assuming one over the base field. -/
theorem exists_imagePoint_finiteSeparableExtension
    (Q : Over (Spec (CommRingCat.of K)))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    ∃ E : IntermediateField K Ω, Module.Finite K E ∧ Algebra.IsSeparable K E ∧
      ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶
          (Over.pullback (specMap K E)).obj Q,
        ∃ ε : Over.mk (𝟙 (Spec (CommRingCat.of E))) ⟶
            Over.mk ((modulusComplement
              (modulusCurveMap (D.changeBaseOfIdentity (specMap K E)))).ι ≫
                baseChange K c E),
          ε ≫ modulusMapScalarExtension c D E Q q = p := by
  obtain ⟨E, hE, hsep, ⟨ε⟩⟩ := modulusComplement_finiteSeparableExtension_point c D Ω
  exact ⟨E, hE, hsep, ε ≫ modulusMapScalarExtension c D E Q q, ε, rfl⟩

end AlgebraicGeometry.GeneralizedJacobian
