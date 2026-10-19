/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ProperTargetModulus
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.IsoCompEqOpenImmersion
import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.ValuationRingStalkSmoothOfRelativeDimensionOne
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty

/-! # Modulus existence for rational maps to abelian varieties

Properness extends an actual map from any nonempty curve open across every
missing point, using the valuation rings of the smooth curve. The extension
is unique and has empty modulus. Consequently every effective modulus whose
complement is the given domain satisfies the full geometric condition.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_exists_iso_comp_eq_of_isOpenImmersion_of_isProper.ProperCurveExtension

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme H]

omit [IsProper c] in
/-- A rational map from the smooth curve to an actual abelian variety
extends uniquely over all missing points, over the original field. -/
theorem existsUnique_extension_to_abelianScheme
    (U : C.Opens) (hU : (U : Set C).Nonempty)
    (q : Over.mk (U.ι ≫ c) ⟶ H.X) :
    ∃! r : Over.mk c ⟶ H.X,
      (Over.homMk U.ι rfl : Over.mk (U.ι ≫ c) ⟶ Over.mk c) ≫ r = q := by
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  have hdense : Dense (U : Set C) := U.isOpen.dense hU
  let f : C.PartialMap H.X.left := ⟨U, hdense, q.left⟩
  have hf : f.hom ≫ H.X.hom = f.domain.ι ≫ c := Over.w q
  let hv : ∀ x : C, ValuationRing (C.presheaf.stalk x) :=
    valuationRing_stalk_of_smoothOfRelativeDimension_one c
  let r₀ : C ⟶ H.X.left := extend c H.X.hom hv f hf
  have hr₀ : r₀ ≫ H.X.hom = c := extend_over c H.X.hom hv f hf
  let r : Over.mk c ⟶ H.X := Over.homMk r₀ hr₀
  have hr : (Over.homMk U.ι rfl : Over.mk (U.ι ≫ c) ⟶ Over.mk c) ≫ r = q := by
    apply Over.OverMorphism.ext
    exact ι_extend c H.X.hom hv f hf
  refine ⟨r, hr, ?_⟩
  intro r' hr'
  have : IsDominant U.ι := isDominant_ι U hU
  have : H.X.left.IsSeparated := isSeparated_of_isSeparated_over H.X.hom
  apply Over.OverMorphism.ext
  apply ext_of_isDominant U.ι
  exact (congrArg Over.Hom.left hr').trans (congrArg Over.Hom.left hr).symm

/-- An arbitrary rational map to an abelian variety has the full
geometric modulus on its actual modulus-complement domain. Extension
over the complete curve is proved internally, not an input hypothesis. -/
theorem geometricRegularMapHasModulus_of_isAbelianScheme
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X) :
    geometricRegularMapHasModulus c D H q := by
  let U := modulusComplement (modulusCurveMap D)
  obtain ⟨x⟩ := modulusComplement_nonempty c D
  obtain ⟨r, hr, _⟩ := existsUnique_extension_to_abelianScheme c H U ⟨x.1, x.2⟩ q
  have hm := geometricRegularMapHasModulus_restriction_of_isAbelianScheme c D H r
  rw [hr] at hm
  exact hm

end AlgebraicGeometry.GeneralizedJacobian
