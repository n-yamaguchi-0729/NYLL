/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.SurjectiveAppSup
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealEpiUnitAppTensorInvModulePowShortExact
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.LocallyFreeOneIffInvertible
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveLeSectionInvModuleDisjoint
import Nyll.AlgebraicCurves.Cohomology.Sheaves.Vanishing.ModulesInvertibleSubsingletonH1SectionsOf

/-!
# Lifting an actual modulus frame

The exact sequence for restriction to the entire Cartier modulus has kernel
`L ⊗ I`. Vanishing of its first cohomology gives a section with exactly the
prescribed restriction. The numerical criterion below supplies this vanishing
from Riemann--Roch, retaining all nilpotents of the modulus.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
open AlgebraicCurves.Geometry.Curves.Proofs
open Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
open Ws31IdealSES (exists_shortExact_unit)
open SmoothProperCurve_exists_forall_le_exists_section_invModule_disjoint_of_twoAffineOpenCover
open AlgebraicGeometry.SmoothProperCurve.LiftSectionAux (exists_pullbackSection_eq)

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

section GeneralBase

variable {K : Type u} [CommRing K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) (𝒱 : X.TwoAffineOpenCover)
  (I : X.IdealSheafData)

/-- Construct a section inducing the specified frame on the whole modulus.
The proof uses the actual restriction sequence, affine section lifting, and
the Cech coboundary witnessing vanishing of its obstruction. -/
theorem exists_normalizedSection_of_H1
    (hI : I.IsInvertible)
    (M : RigidifiedLineBundle I.subschemeι)
    [Subsingleton (𝒱.sectionsOf c (M.L ⊗ I.module)).H1] :
    ∃ s : 𝟙_ X.Modules ⟶ M.L,
      pullbackSection I.subschemeι s ≫ M.trivialization.hom = 𝟙 (𝟙_ I.subscheme.Modules) := by
  have hML : IsLocallyFreeOfRank 1 M.L :=
    (isLocallyFreeOfRank_one_iff_isInvertible M.L).mpr M.isInvertible
  obtain ⟨w, hS⟩ := exists_shortExact_unit I M.L hML
  let S := ShortComplex.mk ((M.L ◁ I.moduleι) ≫ (ρ_ M.L).hom)
    ((Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app M.L) w
  have hsurj : Function.Surjective (S.g.app ⊤) := by
    have hsup := surjective_app_sup_of_shortExact_of_locallyTrivial S hS
      (M.isInvertible.tensor hI.isInvertible_module).exists_trivialization
      𝒱.U0 𝒱.U1 𝒱.isAffineOpen_U0 𝒱.isAffineOpen_U1
    rw [𝒱.sup_eq_top] at hsup
    apply hsup
    intro δ
    let T := 𝒱.sectionsOf c (M.L ⊗ I.module)
    have hδ : (Submodule.Quotient.mk δ : T.H1) = 0 := Subsingleton.elim _ _
    obtain ⟨⟨a, b⟩, hab⟩ := (Submodule.Quotient.mk_eq_zero _).mp hδ
    refine ⟨-a, -b, ?_⟩
    change δ = T.r0 (-a) - T.r1 (-b)
    rw [map_neg, map_neg, neg_sub_neg]
    exact (TwoChartCech.Sections.cechDiff_apply T (a, b)).symm.trans hab |>.symm
  obtain ⟨s, hs⟩ := exists_pullbackSection_eq
    I.subschemeι M.L hsurj M.trivialization.inv
  refine ⟨s, ?_⟩
  exact (congrArg (fun t => t ≫ M.trivialization.hom) hs).trans
    M.trivialization.inv_hom_id

end GeneralBase

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) (𝒱 : X.TwoAffineOpenCover)
  (I : X.IdealSheafData)

/-- The classical degree bound proves the obstruction vanishes, and hence
produces the chosen normalized section rather than assuming a lift. -/
theorem exists_normalizedSection_of_eulerChar_bound [IsAlgClosed K]
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (hI : I.IsInvertible)
    (M : RigidifiedLineBundle I.subschemeι)
    (h : 2 * (Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H1 : ℤ) - 1 ≤
      ((Module.finrank K (𝒱.sectionsOf c (M.L ⊗ I.module)).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf c (M.L ⊗ I.module)).H1) -
      ((Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf c (𝟙_ X.Modules)).H1)) :
    ∃ s : 𝟙_ X.Modules ⟶ M.L,
      pullbackSection I.subschemeι s ≫ M.trivialization.hom = 𝟙 (𝟙_ I.subscheme.Modules) := by
  have : Subsingleton (𝒱.sectionsOf c (M.L ⊗ I.module)).H1 :=
    IsInvertible.subsingleton_H1_sectionsOf_of_le_eulerChar_sub K c
      (M.L ⊗ I.module) (M.isInvertible.tensor hI.isInvertible_module) 𝒱 h
  exact exists_normalizedSection_of_H1 c 𝒱 I hI M

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
