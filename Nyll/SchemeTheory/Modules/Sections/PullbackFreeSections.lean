/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Final

/-!
# Original free generators under pullback

The existing pullback comparison for free module sheaves sends each
original pulled-back free generator to the corresponding generator.
The calculation uses the actual adjunction unit and the actual
coproduct inclusion, with no choice of bases or extra trivialization.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_pullback.AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

private theorem pullbackUnitToUnit_app_one (U : Y.Opens) :
    let _h : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
      (pullbackPushforwardAdjunction f).isRightAdjoint
    (show (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) from
      SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom).app (f ⁻¹ᵁ U)
        (pullbackLocalSection f
          (show Γ(SheafOfModules.unit Y.ringCatSheaf, U) from (1 : Γ(Y, U)))) =
      (show Γ(SheafOfModules.unit X.ringCatSheaf, f ⁻¹ᵁ U) from (1 : Γ(X, f ⁻¹ᵁ U))) := by
  intro h
  let v : (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  have hv := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  have he : (pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫ (pushforward f).map v =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    ((pullbackPushforwardAdjunction f).homEquiv_unit (f := v)).symm.trans hv
  have hx := congrArg
    (fun a : (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) ⟶
      (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) =>
        a.app U (show Γ(SheafOfModules.unit Y.ringCatSheaf, U) from (1 : Γ(Y, U)))) he
  exact hx.trans (f.app U).hom.map_one

/-- The original free pullback comparison preserves each original
free generator on every inverse-image open. -/
theorem pullbackFreeIso_hom_app_pullback_freeSection (I : Type u) (i : I) (U : Y.Opens) :
    (pullbackFreeIso f I).hom.app (f ⁻¹ᵁ U)
        (pullbackLocalSection f
          ((SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op U))) =
      (SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op (f ⁻¹ᵁ U)) := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  have : (TopologicalSpace.Opens.map f.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  let a : (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) ⟶
      (show Y.Modules from SheafOfModules.free I) := SheafOfModules.ιFree i
  let b : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶
      (show X.Modules from SheafOfModules.free I) := SheafOfModules.ιFree i
  let v : (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  have hi : (pullback f).map a ≫ (pullbackFreeIso f I).hom = v ≫ b :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom f.toRingCatSheafHom i
  have hs := pullbackLocalSection_app f a
    (show Γ(SheafOfModules.unit Y.ringCatSheaf, U) from (1 : Γ(Y, U)))
  have ht := congrArg
    (fun c : (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      (show X.Modules from SheafOfModules.free I) => c.app (f ⁻¹ᵁ U)
        (pullbackLocalSection f
          (show Γ(SheafOfModules.unit Y.ringCatSheaf, U) from (1 : Γ(Y, U))))) hi
  have hu : v.app (f ⁻¹ᵁ U)
        (pullbackLocalSection f
          (show Γ(SheafOfModules.unit Y.ringCatSheaf, U) from (1 : Γ(Y, U)))) =
      (show Γ(SheafOfModules.unit X.ringCatSheaf, f ⁻¹ᵁ U) from (1 : Γ(X, f ⁻¹ᵁ U))) :=
    pullbackUnitToUnit_app_one f U
  exact (congrArg ((pullbackFreeIso f I).hom.app (f ⁻¹ᵁ U)) hs).trans
    (ht.trans (congrArg (b.app (f ⁻¹ᵁ U)) hu))

end AlgebraicGeometry.Scheme.Modules
