/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.AffineReflexiveExtension
public import Nyll.EtaleFundamentalGroups.Purity.BoundaryScalarHartogs
public import Nyll.SchemeTheory.Modules.Functoriality.BaseChangeIsomorphism
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineLocal
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# The finite canonical extension over a locally Noetherian base

Actual open base change identifies every affine restriction of the original
open-cover direct image with the corresponding affine extension algebra.
The affine depth-two finiteness theorem therefore gives finite type globally,
and the original relative spectrum is finite over the given base.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace
open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq
open Ws14Port.IsLocalRing.IsCohenMacaulayOfDim

open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection

namespace EtaleFundamentalGroups.FiniteBoundaryExtension

open AlgebraicGeometry Scheme.Modules

/-- The original direct image restricts to the actual pulled-back open
cover, through native open base change and the native unit comparison. -/
def directImageRestrictionIso {X Y V : Scheme.{u}} (U : X.Opens)
    (π : V ⟶ U.toScheme) (j : Y ⟶ X) [IsOpenImmersion j] :
    (((pushforward (π ≫ U.ι)).obj (𝟙_ V.Modules)).restrict j) ≅
      (pushforward (pullback.snd π (j ∣_ U) ≫ (j ⁻¹ᵁ U).ι)).obj
        (𝟙_ (pullback π (j ∣_ U)).Modules) := by
  let q := pullback.snd π (j ∣_ U)
  let a := pullback.fst π (j ∣_ U)
  have h : IsPullback a (q ≫ (j ⁻¹ᵁ U).ι) (π ≫ U.ι) j :=
    (IsPullback.of_hasPullback π (j ∣_ U)).paste_vert
      (isPullback_morphismRestrict j U)
  have : IsIso (baseChangeHom h.w (𝟙_ V.Modules)) :=
    isIso_baseChangeHom_of_isOpenImmersion h (𝟙_ V.Modules)
  exact (restrictFunctorIsoPullback j).app _ ≪≫
    asIso (baseChangeHom h.w (𝟙_ V.Modules)) ≪≫
      (pushforward (q ≫ (j ⁻¹ᵁ U).ι)).mapIso (pullbackTensorUnitObjIso a)

variable (X : Scheme.{u}) [IsLocallyNoetherian X]
  (U : X.Opens) {V : Scheme.{u}} (π : V ⟶ U.toScheme) [IsFinite π] [Etale π]

/-- The original composite direct-image algebra is quasicoherent over
the whole locally Noetherian base. -/
theorem isQuasicoherent_underlyingModule :
    (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent := by
  let N : U.toScheme.Modules := (pushforward π).obj (𝟙_ V.Modules)
  have : N.IsQuasicoherent := isQuasicoherent_of_finiteFreeLocus_eq_top N
    (finiteFreeLocus_pushforward_unit_eq_top π)
  have hP : ((pushforward U.ι).obj N).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_openImmersion U.ι N
  let e : Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)) ≅ (pushforward U.ι).obj N :=
    Scheme.DirectImageAlgebra.underlyingModuleIso (π ≫ U.ι) ≪≫
      ((pushforwardComp π U.ι).app (𝟙_ V.Modules)).symm
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm hP

variable (hdepth : ∀ x : X, x ∉ U →
  (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))

include hdepth in
/-- Depth two on the boundary gives finite type of the original
open-cover direct-image algebra, with no global affineness assumption. -/
theorem isFiniteType_underlyingModule :
    (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsFiniteType := by
  let P : X.Modules := (pushforward (π ≫ U.ι)).obj (𝟙_ V.Modules)
  have hP : P.IsFiniteType := by
    apply isFiniteType_of_affineSpecRestrictions P
    intro W hW
    let R : CommRingCat.{u} := Γ(X, W)
    have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    let j : Spec R ⟶ X := hW.fromSpec
    have : IsOpenImmersion j := hW.isOpenImmersion_fromSpec
    let T : (Spec R).Opens := j ⁻¹ᵁ U
    let q := pullback.snd π (j ∣_ U)
    have hT : ∀ p : Spec R, p ∉ T →
        (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
          ((Spec R).presheaf.stalk p) := by
      intro p hp
      exact (hdepth (j p) hp).trans
        (Module.depth_le_depth_of_ringEquiv
          (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv)
    have hB := AffineReflexiveExtension.isFiniteType_underlyingModule R T q hT
    let e : P.restrict j ≅ Scheme.RelativeSpec.underlyingModule
        (Scheme.DirectImageAlgebra.structureMap (q ≫ T.ι)) :=
      directImageRestrictionIso U π j ≪≫
        (Scheme.DirectImageAlgebra.underlyingModuleIso (q ≫ T.ι)).symm
    exact SheafOfModules.IsFiniteType.of_iso
      (C := (Spec R).Opens) (R := (Spec R).ringCatSheaf) e.symm hB
  exact SheafOfModules.IsFiniteType.of_iso (C := X.Opens) (R := X.ringCatSheaf)
    (Scheme.DirectImageAlgebra.underlyingModuleIso (π ≫ U.ι)).symm hP

include hdepth in
/-- The actual relative spectrum of the original open-cover algebra is
finite over the locally Noetherian base. -/
theorem isFinite_relativeSpec_toBase :
    let : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
        isQuasicoherent_underlyingModule X U π
    IsFinite (Scheme.RelativeSpec.toBase
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))) := by
  have : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
    isQuasicoherent_underlyingModule X U π
  have : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsFiniteType :=
    isFiniteType_underlyingModule X U π hdepth
  apply Scheme.RelativeSpec.isFinite_toBase
  intro W
  exact moduleFinite_sections_of_isFiniteType
    (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))) W.1 W.2


include hdepth in
/-- The original direct-image algebra is reflexive through its canonical
bidual evaluation on the whole locally Noetherian base. -/
theorem isIso_toBidual_underlyingModule :
    IsIso (ZeroSchemeCanonMC.toBidual (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)))) := by
  let N : U.toScheme.Modules := (pushforward π).obj (𝟙_ V.Modules)
  have : IsIso (ZeroSchemeCanonMC.toBidual ((pushforward U.ι).obj N)) :=
    isIso_toBidual_pushforward_of_locallyNoetherian_boundary_two_le_depth X U hdepth N
      (finiteFreeLocus_pushforward_unit_eq_top π)
  let e : Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)) ≅ (pushforward U.ι).obj N :=
    Scheme.DirectImageAlgebra.underlyingModuleIso (π ≫ U.ι) ≪≫
      ((pushforwardComp π U.ι).app (𝟙_ V.Modules)).symm
  exact isIso_toBidual_of_iso e.symm

end EtaleFundamentalGroups.FiniteBoundaryExtension
