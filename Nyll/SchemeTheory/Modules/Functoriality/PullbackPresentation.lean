/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Sheaves.Module

/-!
# Actual presentations under scheme pullback and open restriction

Pullback preserves the original cokernel presentation and the tensor
unit. Mapping an actual presentation therefore constructs an actual
presentation of its pullback, with the same generator index set.

The original composition and restriction isomorphisms identify the
pullback over the inverse image of an affine open with pullback from its
canonical affine spectrum. Finally, the native open-to-slice equivalence
transports an actual restricted presentation to the corresponding local
presentation on the original scheme.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Map an actual cokernel presentation along the original scheme
pullback, using its proved colimit preservation and unit comparison. -/
def presentationPullback {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (P : M.Presentation) : ((pullback f).obj M).Presentation := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  let F : SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} X.ringCatSheaf :=
    SheafOfModules.pullback f.toRingCatSheafHom
  have : PreservesColimitsOfSize.{u, u} F :=
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).leftAdjoint_preservesColimits
  let η : SheafOfModules.unit X.ringCatSheaf ≅ F.obj (SheafOfModules.unit Y.ringCatSheaf) :=
    ((sheafOfModulesEquivalence X).functor.mapIso (pullbackTensorUnitObjIso f)).symm
  exact P.map F η

/-- The constructed pullback presentation retains the original generator indices. -/
theorem presentationPullback_generators_I {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (P : M.Presentation) :
    (presentationPullback f P).generators.I = P.generators.I := rfl

/-- Finite generators of the original presentation remain finite in
the actual pullback presentation; finiteness of relations is not required. -/
theorem presentationPullback_finite_generators {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (P : M.Presentation) [P.generators.IsFiniteType] :
    (presentationPullback f P).generators.IsFiniteType := by
  constructor
  rw [presentationPullback_generators_I]
  exact SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := P.generators)

/-- The native pullback restricted to the inverse image of an affine
open is the actual pullback of its canonical spectrum restriction. -/
def affinePullbackRestrictionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (M : Y.Modules) :
    ((pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
      (pullback ((f ∣_ U) ≫ hU.isoSpec.hom)).obj (M.restrict hU.fromSpec) := by
  let i : (f ⁻¹ᵁ U).toScheme ⟶ X := (f ⁻¹ᵁ U).ι
  let j : Spec Γ(Y, U) ⟶ Y := hU.fromSpec
  let g : (f ⁻¹ᵁ U).toScheme ⟶ Spec Γ(Y, U) := (f ∣_ U) ≫ hU.isoSpec.hom
  have hcomp : i ≫ f = g ≫ j := by
    change (f ⁻¹ᵁ U).ι ≫ f = ((f ∣_ U) ≫ hU.isoSpec.hom) ≫ hU.fromSpec
    rw [Category.assoc, hU.isoSpec_hom_fromSpec]
    exact (morphismRestrict_ι f U).symm
  exact (restrictFunctorIsoPullback i).app ((pullback f).obj M) ≪≫
    (pullbackComp i f).app M ≪≫ (pullbackCongr hcomp).app M ≪≫
      ((pullbackComp g j).app M).symm ≪≫
        (pullback g).mapIso ((restrictFunctorIsoPullback j).app M).symm

/-- Transport an actual presentation on an open subscheme to the
native slice site over that open, through the original equivalence. -/
def presentationOverOfRestrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let e : (overEquiv U).inverse.obj (M.restrict U.ι) ≅ M.over U :=
    (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M).symm ≪≫
      ((overEquiv U).unitIso.app (M.over U)).symm
  let F := (sheafOfModulesEquivalence U.toScheme).inverse ⋙ (overEquiv U).inverse
  have : PreservesColimitsOfSize.{u, u} (sheafOfModulesEquivalence U.toScheme).inverse :=
    (sheafOfModulesEquivalence U.toScheme).symm.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} (overEquiv U).inverse :=
    (overEquiv U).symm.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} F := comp_preservesColimits _ _
  let Q : ((overEquiv U).inverse.obj (M.restrict U.ι)).Presentation :=
    P.map F (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  exact Q.ofIsIso e.hom

/-- The open-to-slice presentation transport keeps the actual generator indices. -/
theorem presentationOverOfRestrict_generators_I {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (P : (M.restrict U.ι).Presentation) :
    (presentationOverOfRestrict M U P).generators.I = P.generators.I := rfl

/-- Finite generators are retained by the actual open-to-slice transport. -/
theorem presentationOverOfRestrict_finite_generators {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (P : (M.restrict U.ι).Presentation) [P.generators.IsFiniteType] :
    (presentationOverOfRestrict M U P).generators.IsFiniteType := by
  constructor
  rw [presentationOverOfRestrict_generators_I]
  exact SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := P.generators)

end AlgebraicGeometry.Scheme.Modules
