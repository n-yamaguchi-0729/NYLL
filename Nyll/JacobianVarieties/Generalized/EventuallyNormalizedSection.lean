/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.NormalizedSectionLift
import Nyll.AlgebraicCurves.Cohomology.Sheaves.EulerCharacteristic.InvertibleIdealEulerCharSectionsOfTensorInvModuleEq
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomFiniteFinrankSubschemeIotaKerPow

/-!
# Normalized sections after twisting by a point

For any actual modulus-rigidified line bundle, sufficiently high twists by a
rational point outside the modulus admit a section equal to one on the whole
modulus. The proof supplies the cohomology bound from the Euler characteristic
of the actual point-power ideal, with its multiplicity retained.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Cohomology.Sheaves.Proofs
open Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq.Ws31ChiA

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K))
  [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- The point-power twist supplies the degree bound for lifting a prescribed
frame; neither vanishing nor existence of the section is assumed. -/
theorem eventually_exists_normalizedSection
    (𝒱 : X.TwoAffineOpenCover) (I : X.IdealSheafData) (hI : I.IsInvertible)
    (ε : Spec (CommRingCat.of K) ⟶ X) (hε : ε ≫ c = 𝟙 _)
    (havoid : ∀ y : I.subscheme, I.subschemeι.base y ∉ ε.ker.support)
    (M : RigidifiedLineBundle I.subschemeι) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ ha : ∀ y : I.subscheme, I.subschemeι.base y ∉ (ε.ker ^ (n + 1)).support,
        ∃ s : 𝟙_ X.Modules ⟶ M.L ⊗ (ε.ker ^ (n + 1)).invModule,
          pullbackSection I.subschemeι s ≫
              (M.tensor (ofInvertibleIdeal I.subschemeι (ε.ker ^ (n + 1))
                ((Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow (n + 1))
                ha)).trivialization.hom =
            𝟙 (𝟙_ I.subscheme.Modules) := by
  let L := M.L ⊗ I.module
  have hL : IsInvertible L := M.isInvertible.tensor hI.isInvertible_module
  let χL : ℤ := (Module.finrank K (𝒱.sectionsOf c L).H0 : ℤ) -
    Module.finrank K (𝒱.sectionsOf c L).H1
  let χO : ℤ := (Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H0 : ℤ) -
    Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H1
  let g : ℤ := Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H1
  refine ⟨(2 * g - 1 + χO - χL).toNat, ?_⟩
  intro n hn
  have hp : ε.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε
  have ha : ∀ y : I.subscheme, I.subschemeι.base y ∉ (ε.ker ^ (n + 1)).support := by
    rw [Scheme.IdealSheafData.support_pow_succ]
    exact havoid
  let T := M.tensor (ofInvertibleIdeal I.subschemeι (ε.ker ^ (n + 1)) (hp.pow (n + 1)) ha)
  let e : (T.L ⊗ I.module) ≅ (L ⊗ (ε.ker ^ (n + 1)).invModule) :=
    α_ M.L (ε.ker ^ (n + 1)).invModule I.module ≪≫
      whiskerLeftIso M.L (β_ (ε.ker ^ (n + 1)).invModule I.module) ≪≫
      (α_ M.L I.module (ε.ker ^ (n + 1)).invModule).symm
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso c 𝒱 e
  have hd := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id ε hε (n + 1)
  have hχ := (hp.pow (n + 1)).eulerChar_sectionsOf_tensor_invModule_eq
    c hd.1 hd.2.1 L hL 𝒱
  have hb : 2 * (Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H1 : ℤ) - 1 ≤
      ((Module.finrank K (𝒱.sectionsOf c (T.L ⊗ I.module)).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf c (T.L ⊗ I.module)).H1) -
      ((Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H1) := by
    rw [e0.finrank_eq, e1.finrank_eq, hχ]
    change 2 * g - 1 ≤ χL + (n + 1 : ℕ) - χO
    omega
  obtain ⟨s, hs⟩ := exists_normalizedSection_of_eulerChar_bound c 𝒱 I hI T hb
  exact ⟨ha, s, hs⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
