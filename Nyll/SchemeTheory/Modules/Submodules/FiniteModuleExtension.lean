/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Submodules.FiniteSubmoduleExtension
public import Nyll.SchemeTheory.Modules.Submodules.SubmoduleTopRestriction
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeSchemeRestriction
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPushforward
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality

/-!
# Finite quasicoherent extensions of actual modules on a compact open

The original module is first pushed forward along the open immersion.
A finite quasicoherent submodule is then extracted with the same whole
restriction. Its actual inclusion, followed by the restriction counit,
recovers the given module. No finiteness of the direct image is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module on a compact open of a qcqs scheme
has an actual finite-type quasicoherent extension, together with an
isomorphism of its restriction with the prescribed module. -/
theorem exists_finiteType_extension_of_qcqs
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (V : U.toScheme.Modules) [V.IsQuasicoherent] [V.IsFiniteType] :
    ∃ F : X.Modules, F.IsQuasicoherent ∧ F.IsFiniteType ∧
      Nonempty (F.restrict U.ι ≅ V) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact U.ι := inferInstance
  let P : X.Modules := (pushforward U.ι).obj V
  have : P.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_openImmersion U.ι V
  let ε : P.restrict U.ι ≅ V :=
    asIso (C := U.toScheme.Modules) ((restrictAdjunction U.ι).counit.app V)
  have hPft : (P.restrict U.ι).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (C := U.toScheme.Opens) (R := U.toScheme.ringCatSheaf)
      ((sheafOfModulesEquivalence U.toScheme).functor.mapIso ε.symm)
      (inferInstanceAs V.IsFiniteType)
  have hPover : (P.over U).IsFiniteType := isFiniteType_over_of_restrict P U hPft
  let P' : SheafOfModules.{u} X.ringCatSheaf :=
    (sheafOfModulesEquivalence X).functor.obj P
  let H : P'.Submodule := ⊤
  let e : H.toSheafOfModules ≅ P' :=
    SheafOfModules.Submodule.topIso P'
  have hHqc : H.toSheafOfModules.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm
      (inferInstanceAs P.IsQuasicoherent)
  have hHft : (H.toSheafOfModules.over U).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (C := Over U) (R := X.ringCatSheaf.over U)
      ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e.symm) hPover
  obtain ⟨N, hNqc, hNft, hNU⟩ :=
    @exists_finiteType_submodule_eq_over_of_qcqs X inferInstance inferInstance
      P inferInstance H hHqc U hU hHft
  let F : X.Modules := submoduleAsModule N
  let n : F ⟶ P := submoduleAsModuleInclusion N
  have hn : IsIso ((restrictFunctor U.ι).map n) :=
    isIso_restrictSubmoduleInclusion_of_over_eq_top N U hNU
  exact ⟨F, hNqc, hNft, ⟨asIso ((restrictFunctor U.ι).map n) ≪≫ ε⟩⟩

end AlgebraicGeometry.Scheme.Modules
