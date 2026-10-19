/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FiniteCurveTrace
import Nyll.AlgebraicCurves.Models.Charts.FiniteComplIsOpen
import Nyll.AlgebraicCurves.Models.Points.InfinitePlace
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # The actual domain of a finite curve trace

The trace is defined precisely away from the image of the excluded source
points. For a nonempty open in a proper curve this image is finite; on a
geometric smooth proper target curve its complement is nonempty and dense.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.GeneralizedJacobian

section Domain

variable {C B S : Scheme.{u}} (c : C ⟶ S) (b : B ⟶ S)
  (π : C ⟶ B) (hπ : π ≫ b = c)
  [IsSeparated b] [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (n : ℕ) (hn : ∀ y : B, π.finrank y = n) (U : C.Opens)

/-- The trace domain consists exactly of the points with full fibre in the
original domain; the graph-ideal construction imposes no extra exclusion. -/
theorem mem_finiteMapTraceLocus_iff (y : B) :
    y ∈ finiteMapTraceLocus c b π hπ n hn U ↔ ∀ x : C, π x = y → x ∈ U := by
  let γ := finiteMapGraph c b π hπ
  have : IsClosedImmersion γ := finiteMapGraph_isClosedImmersion c b π hπ
  have hfst (x : C) : pullback.fst c b (γ.imageι (γ.toImage x)) = x := by
    have h := congrArg (fun f : C ⟶ C => f x)
      ((Scheme.Hom.toImage_imageι_assoc γ (pullback.fst c b)).trans
        (finiteMapGraph_fst c b π hπ))
    exact h
  have hsnd (x : C) : pullback.snd c b (γ.imageι (γ.toImage x)) = π x := by
    have h := congrArg (fun f : C ⟶ B => f x)
      ((Scheme.Hom.toImage_imageι_assoc γ (pullback.snd c b)).trans
        (finiteMapGraph_snd c b π hπ))
    exact h
  change (∀ z : γ.ker.subscheme,
    (γ.ker.subschemeι ≫ pullback.snd c b) z = y →
      pullback.fst c b (γ.ker.subschemeι z) ∈ U) ↔ _
  constructor
  · intro hy x hx
    have hz := hy (γ.toImage x) ((hsnd x).trans hx)
    exact (hfst x) ▸ hz
  · intro hy z hz
    obtain ⟨x, rfl⟩ := γ.toImage.surjective z
    rw [hfst]
    exact hy x ((hsnd x).symm.trans hz)

/-- The omitted target points are exactly the image of the omitted source
points, rather than a larger auxiliary closed subset. -/
theorem finiteMapTraceLocus_compl :
    ((finiteMapTraceLocus c b π hπ n hn U : Set B)ᶜ) = π '' (U : Set C)ᶜ := by
  classical
  ext y
  have hy : (y ∈ (finiteMapTraceLocus c b π hπ n hn U : Set B)) ↔
      ∀ x : C, π x = y → x ∈ U := mem_finiteMapTraceLocus_iff c b π hπ n hn U y
  rw [Set.mem_compl_iff, hy]
  simp only [not_forall, Set.mem_image, Set.mem_compl_iff]
  exact ⟨fun ⟨x, hx, hU⟩ => ⟨x, hU, hx⟩, fun ⟨x, hU, hx⟩ => ⟨x, hx, hU⟩⟩

end Domain

section Curves

variable {K : Type u} [Field K] {C B : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (b : B ⟶ Spec (CommRingCat.of K)) [IsSeparated b]
  (π : C ⟶ B) (hπ : π ≫ b = c)
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (n : ℕ) (hn : ∀ y : B, π.finrank y = n)
  (U : C.Opens) (hU : (U : Set C).Nonempty)

include hU in
/-- A nonempty curve domain excludes only finitely many target points from
the trace. -/
theorem finite_finiteMapTraceLocus_compl :
    ((finiteMapTraceLocus c b π hπ n hn U : Set B)ᶜ).Finite := by
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  rw [finiteMapTraceLocus_compl]
  exact (AlgebraicCurve.finite_compl_of_isOpen c U hU).image π

end Curves

section GeometricCurves

variable {K : Type u} [Field K] [IsAlgClosed K] {C B : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (b : B ⟶ Spec (CommRingCat.of K))
  [IsProper b] [SmoothOfRelativeDimension 1 b] [GeometricallyIntegral b]
  (π : C ⟶ B) (hπ : π ≫ b = c)
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (n : ℕ) (hn : ∀ y : B, π.finrank y = n)
  (U : C.Opens) (hU : (U : Set C).Nonempty)

include hU in
/-- Over an algebraically closed field, the trace of a rational curve map
has a genuinely nonempty domain on the smooth proper target curve. -/
theorem finiteMapTraceLocus_nonempty :
    (finiteMapTraceLocus c b π hπ n hn U : Set B).Nonempty := by
  have : IsIntegral B := GeometricallyIntegral.isIntegral_of_subsingleton b
  let _ : Algebra K B.functionField := (AlgebraicCurve.baseToFunctionField b).toAlgebra
  let M := AlgebraicCurve.CurveModel.ofSmoothProperCurve b
  have : Infinite (AlgebraicCurve.Place K B.functionField) := M.infinite_place
  have : Infinite B := Infinite.of_injective
    (fun v : AlgebraicCurve.Place K B.functionField => (M.placeEquiv.symm v).1)
    (Subtype.val_injective.comp M.placeEquiv.symm.injective)
  obtain ⟨y, hy⟩ := (finite_finiteMapTraceLocus_compl c b π hπ n hn U hU).exists_notMem
  exact ⟨y, by simpa only [Set.mem_compl_iff, not_not] using hy⟩

include hU in
/-- The constructed regular trace represents a rational map: its actual
domain is dense in the integral target curve. -/
theorem finiteMapTraceLocus_dense :
    Dense (finiteMapTraceLocus c b π hπ n hn U : Set B) := by
  have : IsIntegral B := GeometricallyIntegral.isIntegral_of_subsingleton b
  exact (finiteMapTraceLocus c b π hπ n hn U).isOpen.dense
    (finiteMapTraceLocus_nonempty c b π hπ n hn U hU)

end GeometricCurves

end AlgebraicGeometry.GeneralizedJacobian
