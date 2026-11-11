/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.Local.BoundaryFiniteDirectImage
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreePushforward
public import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebra
public import Nyll.SchemeTheory.Modules.Functoriality.FiniteRelativeSpec
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality

/-!
# The actual reflexive finite extension algebra on an affine base

For a finite etale cover of an open in a Noetherian affine scheme, the
original direct-image structure algebra is quasicoherent and finite type,
and its canonical bidual evaluation is invertible when the boundary has
depth at least two. Its actual relative spectrum is consequently finite.
No normality, integrality, fixed rank, or supplied extension algebra is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection

namespace EtaleFundamentalGroups.AffineReflexiveExtension

open AlgebraicGeometry Scheme.Modules

variable (R : CommRingCat.{u}) [IsNoetherianRing R]
  (U : (Spec R).Opens) {V : Scheme.{u}} (π : V ⟶ U.toScheme)
  [IsFinite π] [Etale π]

/-- The actual composite direct-image algebra has the expected original
iterated direct-image module. -/
def underlyingModuleIso :
    Scheme.RelativeSpec.underlyingModule (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)) ≅
      (pushforward U.ι).obj ((pushforward π).obj (𝟙_ V.Modules)) :=
  Scheme.DirectImageAlgebra.underlyingModuleIso (π ≫ U.ι) ≪≫
    ((pushforwardComp π U.ι).app (𝟙_ V.Modules)).symm

/-- Quasicoherence of the original direct-image algebra of the open cover. -/
theorem isQuasicoherent_underlyingModule :
    (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent := by
  let N : U.toScheme.Modules := (pushforward π).obj (𝟙_ V.Modules)
  have hN : finiteFreeLocus N = ⊤ := finiteFreeLocus_pushforward_unit_eq_top π
  have : N.IsQuasicoherent := isQuasicoherent_of_finiteFreeLocus_eq_top N hN
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : QuasiCompact U.ι := inferInstance
  have hP : ((pushforward U.ι).obj N).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_openImmersion U.ι N
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (underlyingModuleIso R U π).symm hP

variable (hdepth : ∀ p : Spec R, p ∉ U →
  (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p) ((Spec R).presheaf.stalk p))

include hdepth

/-- The original open-cover direct-image algebra is finite type. -/
theorem isFiniteType_underlyingModule :
    (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsFiniteType := by
  have hP := isFiniteType_pushforward_of_boundary_two_le_depth R U hdepth
    ((pushforward π).obj (𝟙_ V.Modules)) (finiteFreeLocus_pushforward_unit_eq_top π)
  exact SheafOfModules.IsFiniteType.of_iso
    (C := (Spec R).Opens) (R := (Spec R).ringCatSheaf)
    (underlyingModuleIso R U π).symm hP

/-- Reflexivity concerns the canonical evaluation map of the original
algebra module, and holds without an integrality assumption. -/
theorem isIso_toBidual_underlyingModule :
    IsIso (ZeroSchemeCanonMC.toBidual (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)))) := by
  have : IsIso (ZeroSchemeCanonMC.toBidual
      ((pushforward U.ι).obj ((pushforward π).obj (𝟙_ V.Modules)))) :=
    isIso_toBidual_pushforward_of_boundary_two_le_depth R U hdepth
      ((pushforward π).obj (𝟙_ V.Modules)) (finiteFreeLocus_pushforward_unit_eq_top π)
  exact isIso_toBidual_of_iso (underlyingModuleIso R U π).symm

/-- The actual relative spectrum of the original direct-image algebra
is finite over the original affine base. -/
theorem isFinite_relativeSpec_toBase :
    let : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
        isQuasicoherent_underlyingModule R U π
    IsFinite (Scheme.RelativeSpec.toBase
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))) := by
  have : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
    isQuasicoherent_underlyingModule R U π
  have : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsFiniteType :=
    isFiniteType_underlyingModule R U π hdepth
  apply Scheme.RelativeSpec.isFinite_toBase
  intro W
  exact moduleFinite_sections_of_isFiniteType
    (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))) W.1 W.2

end EtaleFundamentalGroups.AffineReflexiveExtension
