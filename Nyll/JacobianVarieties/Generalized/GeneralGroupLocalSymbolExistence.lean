/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeneralGroupRegularMapModulus
import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolConductor

/-! # Local symbols and the least conductor of an actual group map

The original map supplies a full modulus. The existing place-theoretic
construction then supplies its unique reciprocal local symbol and its
coefficientwise least conductor, without a modulus assumption from the caller.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} [IsIntegral C]
  (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (U : C.Opens) (hU : (U : Set C).Nonempty)
  (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (q : SchemeHomOver (U.ι ≫ c) G.X.hom)

include hU

/-- A regular group map constructs a modulus with exactly its original
boundary and the unique full reciprocal local symbol for its actual values. -/
theorem exists_group_regularMap_localSymbol :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := CurveModel.ofSmoothProperCurve c
    let _ : IsCurveOver K C.functionField :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        c (RingEquiv.refl _) (fun _ => rfl)
    ∃ D : Modulus K C.functionField,
      (∀ w, D w = 0 ↔ (M.placeEquiv.symm w).1 ∈ U) ∧
      ∃! σ, D.IsLocalSymbol (M.regularMapValues U G q) σ := by
  intro algC M curveC
  obtain ⟨D, hboundary, hmod⟩ := exists_group_regularMap_modulus c U hU G q
  exact ⟨D, hboundary,
    (Modulus.hasModulus_iff_existsUnique_localSymbol D (M.regularMapValues U G q)).mp hmod⟩

/-- The actual map has a unique coefficientwise least full conductor.
Its construction requires neither a candidate modulus nor a local symbol. -/
theorem existsUnique_group_regularMap_conductor :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := CurveModel.ofSmoothProperCurve c
    let _ : IsCurveOver K C.functionField :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        c (RingEquiv.refl _) (fun _ => rfl)
    ∃! D : Modulus K C.functionField,
      D.HasModulus (M.regularMapValues U G q) ∧
      ∀ E : Modulus K C.functionField,
        E.HasModulus (M.regularMapValues U G q) → D ≤ E := by
  intro algC M curveC
  obtain ⟨D, _, hmod⟩ := exists_group_regularMap_modulus c U hU G q
  exact Modulus.existsUnique_least_modulus ⟨D, hmod⟩

/-- Every full modulus of the actual map is exactly a modulus above its unique
conductor. This conductor vanishes at every place centred in the original
regular domain. -/
theorem existsUnique_group_regularMap_modulus_classification :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    let M := CurveModel.ofSmoothProperCurve c
    let _ : IsCurveOver K C.functionField :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        c (RingEquiv.refl _) (fun _ => rfl)
    ∃! D : Modulus K C.functionField,
      (∀ E : Modulus K C.functionField,
        E.HasModulus (M.regularMapValues U G q) ↔ D ≤ E) ∧
      (∀ w, (M.placeEquiv.symm w).1 ∈ U → D w = 0) := by
  intro algC M curveC
  obtain ⟨D₀, hboundary, hD₀⟩ := exists_group_regularMap_modulus c U hU G q
  obtain ⟨D, ⟨hD, hleast⟩, _⟩ := Modulus.existsUnique_least_modulus ⟨D₀, hD₀⟩
  refine ⟨D, ⟨?_, ?_⟩, ?_⟩
  · intro E
    exact ⟨hleast E, hD.mono⟩
  · intro w hw
    have hDD₀ : D ≤ D₀ := hleast D₀ hD₀
    exact Nat.eq_zero_of_le_zero ((hboundary w).mpr hw ▸ hDD₀ w)
  · intro E hE
    exact le_antisymm ((hE.1 D).mp hD)
      (hleast E ((hE.1 E).mpr le_rfl))

end AlgebraicGeometry.GeneralizedJacobian
