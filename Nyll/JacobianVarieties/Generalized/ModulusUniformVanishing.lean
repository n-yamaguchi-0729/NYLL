/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.EventuallyNormalizedSection
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgebraicEquivalenceEulerCharSectionsOfTensorEq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealModuleTensorInvModuleIso

/-!
# A uniform modulus bound for every algebraically trivial line bundle

The Euler characteristic of an algebraically trivial bundle is unchanged
after tensoring a fixed bundle. The full Cartier modulus contributes its
scheme length, and the point-power twist contributes its exponent. Thus the
vanishing bound is independent of the particular Picard-zero class.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RelPicard
open AlgebraicCurves.Cohomology.Sheaves.Proofs
open Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq.Ws31ChiA

namespace AlgebraicGeometry.GeneralizedJacobian

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of k)) [IsProper c] (𝒱 : X.TwoAffineOpenCover)

/-- The ideal of the full finite Cartier modulus subtracts its actual scheme length. -/
theorem eulerChar_modulusIdeal (I : X.IdealSheafData) (hI : I.IsInvertible)
    {d : ℕ} (hZ : IsFinite (I.subschemeι ≫ c))
    (hdeg : ∀ t : Spec (CommRingCat.of k), (I.subschemeι ≫ c).finrank t = d) :
    (Module.finrank k (𝒱.sectionsOf c I.module).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf c I.module).H1 =
      (Module.finrank k (𝒱.sectionsOf c (𝟙_ X.Modules)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf c (𝟙_ X.Modules)).H1 - d := by
  obtain ⟨e⟩ := hI.nonempty_module_tensor_invModule_iso.1
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso c 𝒱 e
  have hχ := hI.eulerChar_sectionsOf_tensor_invModule_eq c hZ hdeg
    I.module hI.isInvertible_module 𝒱
  rw [e0.finrank_eq, e1.finrank_eq] at hχ
  omega

variable [SmoothOfRelativeDimension 1 c]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ c = 𝟙 _)
  (L : X.Modules) (hL : IsInvertible L) (h0 : IsAlgEquivZero c L)

include hε hL h0 in
/-- A point-power twist of any Picard-zero family has the prescribed degree. -/
theorem eulerChar_zero_pointTwist (n : ℕ) :
    (Module.finrank k (𝒱.sectionsOf c (L ⊗ (ε.ker ^ n).invModule)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf c (L ⊗ (ε.ker ^ n).invModule)).H1 =
      (Module.finrank k (𝒱.sectionsOf c (𝟙_ X.Modules)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf c (𝟙_ X.Modules)).H1 + n := by
  have hp := (Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow n
  obtain ⟨hf, hd, _⟩ := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
    ε hε n
  have hχ := hp.eulerChar_sectionsOf_tensor_invModule_eq c hf hd
    (𝟙_ X.Modules) (isInvertible_unit _) 𝒱
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso c 𝒱 (λ_ (ε.ker ^ n).invModule)
  rw [e0.finrank_eq, e1.finrank_eq] at hχ
  exact (IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq c 𝒱 L
    (ε.ker ^ n).invModule hL hp.isInvertible_invModule h0).trans hχ

include hε hL h0 in
/-- The usual large-degree modulus bound kills the actual restriction-kernel obstruction. -/
theorem subsingleton_H1_zero_pointTwist_modulus [IsAlgClosed k] [IsIntegral X]
    (I : X.IdealSheafData) (hI : I.IsInvertible) {d : ℕ}
    (hZ : IsFinite (I.subschemeι ≫ c))
    (hdeg : ∀ t : Spec (CommRingCat.of k), (I.subschemeι ≫ c).finrank t = d)
    (n : ℕ)
    (hn : 2 * Module.finrank k (𝒱.sectionsOf c (𝟙_ X.Modules)).H1 + d ≤ n + 1) :
    Subsingleton (𝒱.sectionsOf c ((L ⊗ (ε.ker ^ n).invModule) ⊗ I.module)).H1 := by
  have hp := (Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow n
  have hLI : IsInvertible (L ⊗ I.module) := hL.tensor hI.isInvertible_module
  obtain ⟨hf, hd, _⟩ := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
    ε hε n
  have hχp := hp.eulerChar_sectionsOf_tensor_invModule_eq c hf hd (L ⊗ I.module) hLI 𝒱
  have hχL := IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq c 𝒱 L I.module
    hL hI.isInvertible_module h0
  have hχI := eulerChar_modulusIdeal c 𝒱 I hI hZ hdeg
  let e : (L ⊗ (ε.ker ^ n).invModule) ⊗ I.module ≅
      (L ⊗ I.module) ⊗ (ε.ker ^ n).invModule :=
    α_ L (ε.ker ^ n).invModule I.module ≪≫
      whiskerLeftIso L (β_ (ε.ker ^ n).invModule I.module) ≪≫
      (α_ L I.module (ε.ker ^ n).invModule).symm
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso c 𝒱 e
  apply IsInvertible.subsingleton_H1_sectionsOf_of_le_eulerChar_sub k c
    ((L ⊗ (ε.ker ^ n).invModule) ⊗ I.module)
    ((hL.tensor hp.isInvertible_invModule).tensor hI.isInvertible_module) 𝒱
  change 2 * (Module.finrank k (𝒱.sectionsOf c (𝟙_ X.Modules)).H1 : ℤ) - 1 ≤
    ((Module.finrank k (𝒱.sectionsOf c ((L ⊗ (ε.ker ^ n).invModule) ⊗ I.module)).H0 : ℤ) -
      Module.finrank k (𝒱.sectionsOf c ((L ⊗ (ε.ker ^ n).invModule) ⊗ I.module)).H1) -
    ((Module.finrank k (𝒱.sectionsOf c (𝟙_ X.Modules)).H0 : ℤ) -
      Module.finrank k (𝒱.sectionsOf c (𝟙_ X.Modules)).H1)
  rw [e0.finrank_eq, e1.finrank_eq, hχp, hχL, hχI]
  omega

end AlgebraicGeometry.GeneralizedJacobian
