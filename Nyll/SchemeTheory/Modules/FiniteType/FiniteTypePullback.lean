/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite generators under the actual scheme pullback

A finite-type quasicoherent sheaf has a finite spanning family of actual
sections on each affine open. The affine counit supplies a presentation
with this finite generator set. The constructed local pullback
presentation keeps exactly that set, yielding finite local generating
data on the inverse-image affine cover.

The construction uses neither finite generation of the relations nor
Noetherian, separation, or flatness assumptions.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Actual finite affine sections supply an affine presentation with
finite generators, without imposing finiteness on the relations. -/
theorem exists_affineRestrictionPresentation_finite_generators
    {Y : Scheme.{u}} (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ P : (M.restrict hU.fromSpec).Presentation, P.generators.IsFiniteType := by
  let R : CommRingCat.{u} := Γ(Y, U)
  let j : Spec R ⟶ Y := hU.fromSpec
  let G : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj (M.restrict j)
  have hImage : j ''ᵁ ⊤ = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have hUFinite : Module.Finite Γ(Y, U) Γ(M, U) :=
    moduleFinite_sections_of_isFiniteType M U hU
  have hImageFinite : Module.Finite Γ(Y, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) :=
    Eq.mp (congrArg (fun W : Y.Opens => Module.Finite Γ(Y, W) Γ(M, W)) hImage.symm)
      hUFinite
  have : Module.Finite R G := moduleFinite_moduleSpecΓ_restrict_of_finite_sections M j
  obtain ⟨s, hsFinite, hs⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := R) (M := G))
  let P := affineRestrictionPresentationOfGenerators M U hU s hs
  refine ⟨P, ?_⟩
  constructor
  rw [affineRestrictionPresentationOfGenerators_generators_I]
  exact hsFinite.to_subtype

/-- The original pullback preserves finite type of quasicoherent
sheaves, by the actual finite affine generators and their pulled-back presentations. -/
theorem isFiniteType_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType := by
  apply SheafOfModules.IsFiniteType.of_coversTop ((pullback f).obj M)
    (fun U : Y.affineOpens => f ⁻¹ᵁ U.1)
    ((Opens.coversTop_iff X _).mpr
      (TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top Y) f.base.hom))
  intro U
  obtain ⟨P, hP⟩ := exists_affineRestrictionPresentation_finite_generators M U.1 U.2
  let Q := pullbackAffineLocalPresentation f M U.1 U.2 P
  have hQ : Q.generators.IsFiniteType :=
    pullbackAffineLocalPresentation_finite_generators f M U.1 U.2 P
  let q := Q.generators.localGeneratorsData
  have hq : q.IsFiniteType := by
    constructor
    intro V
    constructor
    exact SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := Q.generators)
  exact q.isFiniteType hq

end AlgebraicGeometry.Scheme.Modules
