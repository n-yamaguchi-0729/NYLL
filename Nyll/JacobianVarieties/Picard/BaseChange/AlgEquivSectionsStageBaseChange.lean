/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Scheme
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Nyll.SchemeTheory.Modules.Functoriality.AffinePullbackSections
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.StageHom
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd
public import Nyll.AlgebraicCurves.Geometry.Schemes.Cohomology.TwoAffineCoverStageBaseChangeIsosStructureSheaf

public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Designation
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation
/-!
# Algebra equivalences for affine sections after a change of stage
-/

@[expose] public section

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.StageSectionsBaseChange

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.RelPicard.LFP

noncomputable section

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs
open Scheme_TwoAffineOpenCover_exists_stage_baseChangeIsos_structureSheaf
open AlgebraicGeometry.RelPicard.LFP.Stage AlgebraicGeometry.RelPicard.LFP.StageTransport

attribute [local simp] φ_hom_fst φ_hom_snd φ_inv_σ φ_inv_prA

/-- Sections on an affine stage base change are the scalar extension of the original sections. -/
theorem _root_.AlgebraicGeometry.RelPicard.exists_algEquiv_sections_stage_baseChange_of_isAffineOpen
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
      [IsScalarTower R A₀ A']
    (U : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Opens) (hU : IsAffineOpen U)
    (U' : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A')).Opens)
    (hU' : RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))
      ⁻¹ᵁ U = U') :
    let _ : Algebra A₀ Γ(Limits.pullback c
        (Scheme.TwoAffineOpenCover.specMap R A₀), U) :=
      Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) U
    let _ : Algebra A' Γ(Limits.pullback c
        (Scheme.TwoAffineOpenCover.specMap R A'), U') :=
      Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) U'
    ∃ e : (A' ⊗[A₀] Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀), U)) ≃ₐ[A']
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), U'),
      ∀ s, e ((1 : A') ⊗ₜ[A₀] s) =
        ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀
          A'))).appLE U U' hU'.ge).hom s := by
  intro iU iU'
  let iW : Algebra A' Γ(X' R c A₀ A', (fst' R c A₀ A') ⁻¹ᵁ U) :=
    Scheme.TwoAffineOpenCover.algebraOfHom (snd' R c A₀ A') ((fst' R c A₀ A') ⁻¹ᵁ U)
  obtain ⟨e, he⟩ :=
    AlgebraicGeometry.Scheme.exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
      (prA R c A₀) U hU A'
  obtain ⟨τ, hτ⟩ := exists_transportAlgEquiv (φ R c A₀ A').hom
    (W := (fst' R c A₀ A') ⁻¹ᵁ U) (W' := U')
    (φ_hom_preimage_eq R c A₀ A' U U' hU') (snd' R c A₀ A') (prA R c A') (φ_hom_snd R c A₀ A')
  refine ⟨e.trans τ, fun s => ?_⟩
  rw [AlgEquiv.trans_apply, he]
  exact (hτ _).trans (φ_appLE_fst_app R c A₀ A' U U' hU' _ s)
end

end JacobianVarieties.Picard.Proofs.StageSectionsBaseChange
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec
  GoodReductionJacobian.AvatarSchemeBridge.mk.injEq
  GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe
  NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe
  GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
