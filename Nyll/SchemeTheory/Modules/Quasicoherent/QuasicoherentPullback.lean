/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.PullbackPresentation
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Topology.Sheaves.Module

/-!
# Quasicoherence of the actual scheme pullback

On each canonical affine spectrum of the target, the original affine
counit transports the cokernel presentation of a spanning family of
sections to the actual restricted sheaf. Pulling back that presentation
and using the original composition and open-restriction comparisons gives
a presentation on the inverse-image open in the source.

These presentations form quasicoherent data on the inverse image of the
target's canonical affine cover. Generator index sets are retained, so
the same construction also supports finite-type pullback without assuming
finite presentation of the source sheaf.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The original affine counit transports the actual presentation of
a spanning family of native affine sections to the restricted sheaf. -/
def affineRestrictionPresentationOfGenerators {Y : Scheme.{u}} (M : Y.Modules)
    [M.IsQuasicoherent] (U : Y.Opens) (hU : IsAffineOpen U)
    (s : Set ((moduleSpecΓFunctor (R := Γ(Y, U))).obj (M.restrict hU.fromSpec)))
    (hs : Submodule.span Γ(Y, U) s = ⊤) : (M.restrict hU.fromSpec).Presentation := by
  let R : CommRingCat.{u} := Γ(Y, U)
  let N : (Spec R).Modules := M.restrict hU.fromSpec
  have : N.IsQuasicoherent := isQuasicoherent_restrictFunctor hU.fromSpec M
  let G : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj N
  let A : SheafOfModules.{u} (Spec R).ringCatSheaf := tilde (R := R) G
  let B : SheafOfModules.{u} (Spec R).ringCatSheaf := N
  let P : A.Presentation :=
    presentationTilde (R := R) G s hs _ (Submodule.span_eq _)
  let ε : (tilde (R := R) G : (Spec R).Modules) ⟶ N := fromTildeΓ (R := R) N
  have hε : IsIso (C := (Spec R).Modules) ε :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) N
  let eScheme : (tilde (R := R) G : (Spec R).Modules) ≅ N :=
    asIso (C := (Spec R).Modules) ε
  let e : A ≅ B := (sheafOfModulesEquivalence (Spec R)).functor.mapIso eScheme
  have : IsIso e.hom := inferInstance
  exact P.ofIsIso e.hom

/-- The affine presentation uses precisely the supplied spanning family. -/
theorem affineRestrictionPresentationOfGenerators_generators_I
    {Y : Scheme.{u}} (M : Y.Modules) [M.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U)
    (s : Set ((moduleSpecΓFunctor (R := Γ(Y, U))).obj (M.restrict hU.fromSpec)))
    (hs : Submodule.span Γ(Y, U) s = ⊤) :
    (affineRestrictionPresentationOfGenerators M U hU s hs).generators.I = s := rfl

/-- Pull back the actual affine presentation and transport it to the
native slice over the inverse-image open, using the original comparisons. -/
def pullbackAffineLocalPresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (hU : IsAffineOpen U)
    (P : (M.restrict hU.fromSpec).Presentation) :
    (((pullback f).obj M).over (f ⁻¹ᵁ U)).Presentation := by
  let g : (f ⁻¹ᵁ U).toScheme ⟶ Spec Γ(Y, U) := (f ∣_ U) ≫ hU.isoSpec.hom
  let N : X.Modules := (pullback f).obj M
  let A : SheafOfModules.{u} (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    (pullback g).obj (M.restrict hU.fromSpec)
  let B : SheafOfModules.{u} (f ⁻¹ᵁ U).toScheme.ringCatSheaf := N.restrict (f ⁻¹ᵁ U).ι
  let e : A ≅ B := (sheafOfModulesEquivalence (f ⁻¹ᵁ U).toScheme).functor.mapIso
    (affinePullbackRestrictionIso f U hU M).symm
  let Q : B.Presentation := (presentationPullback g P).ofIsIso e.hom
  exact presentationOverOfRestrict N (f ⁻¹ᵁ U) Q

/-- The actual local pullback presentation retains the original generator indices. -/
theorem pullbackAffineLocalPresentation_generators_I {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (hU : IsAffineOpen U)
    (P : (M.restrict hU.fromSpec).Presentation) :
    (pullbackAffineLocalPresentation f M U hU P).generators.I = P.generators.I := rfl

/-- Finite generators remain finite in the constructed local pullback presentation. -/
theorem pullbackAffineLocalPresentation_finite_generators {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (hU : IsAffineOpen U)
    (P : (M.restrict hU.fromSpec).Presentation) [P.generators.IsFiniteType] :
    (pullbackAffineLocalPresentation f M U hU P).generators.IsFiniteType := by
  constructor
  rw [pullbackAffineLocalPresentation_generators_I]
  exact SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := P.generators)

/-- The original pullback of a quasicoherent sheaf is quasicoherent,
with actual local presentations on the inverse image of the affine cover. -/
theorem isQuasicoherent_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] : ((pullback f).obj M).IsQuasicoherent := by
  let q : ((pullback f).obj M).QuasicoherentData :=
    { I := Y.affineOpens
      X := fun U => f ⁻¹ᵁ U.1
      coversTop := by
        rw [Opens.coversTop_iff]
        exact TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.hom
      presentation := fun U =>
        pullbackAffineLocalPresentation f M U.1 U.2
          (affineRestrictionPresentationOfGenerators M U.1 U.2 Set.univ
            Submodule.span_univ) }
  exact q.isQuasicoherent

end AlgebraicGeometry.Scheme.Modules
