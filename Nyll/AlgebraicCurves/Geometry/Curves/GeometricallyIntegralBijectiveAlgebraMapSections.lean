/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Nyll.SchemeTheory.Affine.ConnectedOfGlobalSections
public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Nyll.SchemeTheory.LocalGeometry.IntegralSmooth

/-!
# geometrically Integral of bijective algebra Map sections of smooth
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (GeometricallyIntegral Spec IsIntegral Scheme Smooth
  geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms IsIntegral.of_isIso
  Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom isIntegral_of_smooth_of_preconnectedSpace)

namespace Ws35Q1

open _root_.AlgebraicGeometry


theorem connectedSpace_of_forall_isIdempotentElem {X : Scheme.{u}} [Nontrivial Γ(X, ⊤)]
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) : ConnectedSpace X :=
  _root_.AlgebraicGeometry.Scheme.connectedSpace_of_globalSections_idempotents X h

theorem connectedSpace_of_bijective {K : Type u} [Field K] {X : Scheme.{u}} (φ : K →+* Γ(X, ⊤))
    (hφ : Function.Bijective φ) : ConnectedSpace X :=
  _root_.AlgebraicGeometry.Scheme.connectedSpace_of_bijective_globalSections X φ hφ

scoped instance isClosedUnderIsomorphisms_isIntegral :
    ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (fun X : Scheme.{u} => IsIntegral X)
      :=
  ⟨fun e h => by have := h; exact IsIntegral.of_isIso e.hom⟩

end AlgebraicGeometry.Ws35Q1

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth in
attribute [local instance]
  AlgebraicGeometry.Ws35Q1.isClosedUnderIsomorphisms_isIntegral



open AlgebraicGeometry.Ws35Q1 in
theorem _root_.AlgebraicGeometry.geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [Smooth c]
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
        ⊤))) :
    GeometricallyIntegral c := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms (P := fun X : Scheme.{u} =>
    IsIntegral X)).mpr ?_⟩
  intro K _ _
  let := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) ⊤
  have : ConnectedSpace ↥(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)) :=
    connectedSpace_of_bijective (algebraMap K _) (hH0 K)
  exact AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
end geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
