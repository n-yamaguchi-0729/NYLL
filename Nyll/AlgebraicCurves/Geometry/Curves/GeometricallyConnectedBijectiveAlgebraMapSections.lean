/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Nyll.SchemeTheory.Affine.ConnectedOfGlobalSections
public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Batteries.Tactic.Init
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

/-!
# geometrically Connected of bijective algebra Map sections
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace geometricallyConnected_of_bijective_algebraMap_sections

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Spec IsIntegral Scheme
  geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms GeometricallyConnected
  IsIntegral.of_isIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom)

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

attribute [local instance] AlgebraicGeometry.Ws35Q1.isClosedUnderIsomorphisms_isIntegral



open AlgebraicGeometry.Ws35Q1 in
theorem _root_.AlgebraicGeometry.geometricallyConnected_of_bijective_algebraMap_sections
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (hH0 : ∀ (A : Type u) [CommRing A] [Algebra R A],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
      Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A),
        ⊤))) :
    GeometricallyConnected c := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms (P := (ConnectedSpace
    ·))).mpr ?_⟩
  intro K _ _
  let := Scheme.TwoAffineOpenCover.algebraOfHom
    (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K)) ⊤
  exact connectedSpace_of_bijective (algebraMap K Γ(Limits.pullback c
    (Scheme.TwoAffineOpenCover.specMap R K), ⊤)) (hH0 K)
end AlgebraicCurves.Geometry.Curves.Proofs.geometricallyConnected_of_bijective_algebraMap_sections
end ProofImplementation
