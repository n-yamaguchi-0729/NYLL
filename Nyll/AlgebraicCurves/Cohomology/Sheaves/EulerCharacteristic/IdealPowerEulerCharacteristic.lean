/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Sheaves.EulerCharacteristic.InverseIdealPowerEulerCharacteristic

/-!
# Scheme Ideal Sheaf Data Is Invertible euler Char sections Of pullback pow module tensor eq
sub mul
-/

section ProofImplementation

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs.EulerCharacteristicInversePower
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem eulerChar_sectionsOf_pullback_pow_module_tensor_eq_sub_mul
    {k : Type u} [Field k] {X Y : Scheme.{u}} (ι : Y ⟶ X) (y : Y ⟶ Spec (CommRingCat.of k))
      [IsProper y]
    {I : X.IdealSheafData} (hI : I.IsInvertible) (hIY : (I.comap ι).IsInvertible) {d : ℕ}
    (hZ : IsFinite ((I.comap ι).subschemeι ≫ y))
    (hdeg : ∀ t : Spec (CommRingCat.of k), ((I.comap ι).subschemeι ≫ y).finrank t = d)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (r : ℕ) (𝒲 : Y.TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((I ^ r).module ⊗ M))).H0 :
      ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj ((I ^ r).module ⊗
          M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback ι).obj M)).H1 - r * d := by
  rw [← AlgebraicGeometry.PullbackPowTwist.chi_def, ← AlgebraicGeometry.PullbackPowTwist.chi_def]
  exact AlgebraicGeometry.PullbackPowTwist.chi_pullback_module_pow_tensor y 𝒲 ι hI hIY hZ hdeg r M
    hM
end AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  isScalarTower
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instLinearOrder
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  module
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instFintype
  instFintypeIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  addCommGroup
open AlgebraicGeometry.Scheme.OrderedAffineCover in
attribute [-instance]
  instDecidableEqIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  moduleSections
open _root_.SheafOfModules in
attribute [-instance]
  isIso_ihomModelToIhom
open AlgebraicGeometry.Scheme.OrderedAffineCoverOf in
attribute [-instance]
  instDecidableEqIdx
  instFintype
  instLinearOrder
  instFintypeIdx
open AlgebraicGeometry.OModulePresheaf in
attribute [-instance]
  instSubsingletonObjZero
open AlgebraicGeometry.OModulePresheaf.Leray in
attribute [-instance]
  relAltC_scalarTower
  ker_relAltd_modΓ
  relAltC_modΓ
  biC_abGrp
  relAltH_modΓ
  ker_relAltd_smul
  relAltH_scalarTower
  relAltH_smul
  biC_module
attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed
  AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper
  AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper
  AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ
  AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π
  AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorPow_zero
  AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
attribute [-simp] AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app
  AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec
  AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq
  AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap
attribute [-simp] ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
