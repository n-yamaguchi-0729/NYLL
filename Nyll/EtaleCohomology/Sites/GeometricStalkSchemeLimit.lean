/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-!
# The actual strict-local base change as an inverse limit of schemes

The existing filtered colimit of pointed-neighborhood algebras yields an
inverse limit after applying `Spec`. Pullback preserves this limit, and the
connected index allows forgetting the structure map. All cone projections
are the actual germ maps, with native scheme pullbacks.

The intermediate affine schemes are spectra of sections of possibly
nonaffine neighborhoods. They need not be étale over the original base.
Scheme finite-data descent is applied to them before refining the final
neighborhood to an affine étale one.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

namespace EtaleCohomology

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω)

private def geometricStalkCoefficientSpec :
    (Under (CommRingCat.of R))ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) :=
  (Over.opEquivOpUnder (CommRingCat.of R)).inverse ⋙ Over.post Scheme.Spec

/-- Spectra of the actual pointed-neighborhood algebras, over the original base. -/
def geometricStalkSpecDiagram :
    (GeometricStalkAlgebraIndex φ)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) :=
  (geometricStalkSmallAlgebraDiagram φ).op ⋙ geometricStalkCoefficientSpec

/-- The actual geometric-stalk spectrum and its germ projections. -/
def geometricStalkSpecCone : Cone (geometricStalkSpecDiagram φ) :=
  geometricStalkCoefficientSpec.mapCone (geometricStalkSmallAlgebraCocone φ).op

/-- The actual germ cone is limiting, by the already constructed algebra colimit. -/
def geometricStalkSpecConeIsLimit : IsLimit (geometricStalkSpecCone φ) := by
  let F := (geometricStalkSmallAlgebraDiagram φ).op
  have : PreservesLimit F (geometricStalkCoefficientSpec (R := R)) :=
    inferInstanceAs (PreservesLimit F
      ((Over.opEquivOpUnder (CommRingCat.of R)).inverse ⋙ Over.post Scheme.Spec))
  exact isLimitOfPreserves geometricStalkCoefficientSpec
    (geometricStalkSmallAlgebraCoconeIsColimit φ).op

/-- The native pullbacks of the coefficient stages to an arbitrary scheme over the base. -/
abbrev geometricStalkSchemeDiagram {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :=
  AffineTransitionHom.diagram (geometricStalkSpecDiagram φ) f

/-- The native strict-local pullback, with its maps to the coefficient stages. -/
abbrev geometricStalkSchemeCone {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :=
  AffineTransitionHom.cone (geometricStalkSpecDiagram φ) (geometricStalkSpecCone φ) f

/-- Strict-local base change is the actual inverse limit of its coefficient stages. -/
def geometricStalkSchemeConeIsLimit {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    IsLimit (geometricStalkSchemeCone φ f) :=
  AffineTransitionHom.coneIsLimit (geometricStalkSpecDiagram φ) (geometricStalkSpecCone φ)
    (geometricStalkSpecConeIsLimit φ) f

/-- Every stage transition is an affine morphism. -/
theorem geometricStalkSchemeDiagram_map_isAffineHom
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {i j : (GeometricStalkAlgebraIndex φ)ᵒᵖ} (a : i ⟶ j) :
    IsAffineHom ((geometricStalkSchemeDiagram φ f).map a) := by
  have : ∀ {i j : (GeometricStalkAlgebraIndex φ)ᵒᵖ} (a : i ⟶ j),
      IsAffineHom ((geometricStalkSpecDiagram φ).map a).left :=
    fun a => inferInstanceAs
      (IsAffineHom (Spec.map ((geometricStalkSmallAlgebraDiagram φ).map a.unop).right))
  exact AffineTransitionHom.diagram_map_isAffineHom (geometricStalkSpecDiagram φ) f a

/-- Quasi-compactness of the original source supplies quasi-compact stages. -/
theorem geometricStalkSchemeDiagram_obj_compactSpace
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (i : (GeometricStalkAlgebraIndex φ)ᵒᵖ) :
    CompactSpace ((geometricStalkSchemeDiagram φ f).obj i) := by
  have : ∀ i : (GeometricStalkAlgebraIndex φ)ᵒᵖ,
      CompactSpace ((geometricStalkSpecDiagram φ).obj i).left :=
    fun i => inferInstanceAs
      (CompactSpace (Spec ((geometricStalkSmallAlgebraDiagram φ).obj i.unop).right))
  exact AffineTransitionHom.diagram_obj_compactSpace (geometricStalkSpecDiagram φ) f i

/-- Quasi-separatedness of the original source supplies quasi-separated stages. -/
theorem geometricStalkSchemeDiagram_obj_quasiSeparatedSpace
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiSeparated f]
    (i : (GeometricStalkAlgebraIndex φ)ᵒᵖ) :
    QuasiSeparatedSpace ((geometricStalkSchemeDiagram φ f).obj i) := by
  have : ∀ i : (GeometricStalkAlgebraIndex φ)ᵒᵖ,
      QuasiSeparatedSpace ((geometricStalkSpecDiagram φ).obj i).left :=
    fun i => inferInstanceAs
      (QuasiSeparatedSpace (Spec ((geometricStalkSmallAlgebraDiagram φ).obj i.unop).right))
  exact AffineTransitionHom.diagram_obj_quasiSeparatedSpace (geometricStalkSpecDiagram φ) f i

/-- The cone projections commute with the native projection to the original scheme. -/
theorem geometricStalkSchemeCone_π_snd
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (i : (GeometricStalkAlgebraIndex φ)ᵒᵖ) :
    (geometricStalkSchemeCone φ f).π.app i ≫
        pullback.snd ((geometricStalkSpecDiagram φ).obj i).hom f =
      pullback.snd (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f :=
  AffineTransitionHom.cone_map_snd (geometricStalkSpecDiagram φ) (geometricStalkSpecCone φ) f i

/-- The first projection is the actual germ map on coefficient spectra. -/
theorem geometricStalkSchemeCone_π_fst
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (i : (GeometricStalkAlgebraIndex φ)ᵒᵖ) :
    (geometricStalkSchemeCone φ f).π.app i ≫
        pullback.fst ((geometricStalkSpecDiagram φ).obj i).hom f =
      pullback.fst (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f ≫
        ((geometricStalkSpecCone φ).π.app i).left :=
  AffineTransitionHom.cone_map_fst (geometricStalkSpecDiagram φ) (geometricStalkSpecCone φ) f i

/-- An affine open of the actual strict-local pullback descends to an affine
open of a coefficient stage, with equality of its actual inverse image. -/
theorem geometricStalk_exists_affineOpen_stage
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [QuasiSeparated f]
    (U : (pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f).Opens)
    (hU : IsAffineOpen U) :
    ∃ (i : (GeometricStalkAlgebraIndex φ)ᵒᵖ)
      (V : ((geometricStalkSchemeDiagram φ f).obj i).Opens),
      IsAffineOpen V ∧ (geometricStalkSchemeCone φ f).π.app i ⁻¹ᵁ V = U := by
  have : ∀ {i j : (GeometricStalkAlgebraIndex φ)ᵒᵖ} (a : i ⟶ j),
      IsAffineHom ((geometricStalkSchemeDiagram φ f).map a) :=
    fun a => geometricStalkSchemeDiagram_map_isAffineHom φ f a
  have : ∀ i : (GeometricStalkAlgebraIndex φ)ᵒᵖ,
      QuasiSeparatedSpace ((geometricStalkSchemeDiagram φ f).obj i) :=
    geometricStalkSchemeDiagram_obj_quasiSeparatedSpace φ f
  exact exists_isAffineOpen_preimage_eq (geometricStalkSchemeDiagram φ f)
    (geometricStalkSchemeCone φ f) (geometricStalkSchemeConeIsLimit φ f) U hU

end EtaleCohomology
