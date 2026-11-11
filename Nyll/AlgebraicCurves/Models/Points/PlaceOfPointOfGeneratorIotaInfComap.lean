/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_placeOfPoint_ofGenerator_iotaInf_comap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Construction.Construction
import Nyll.AlgebraicCurves.Models.Points.PlaceOfPointOfGeneratorIota0Comap

/-!
# Curve Model place Of Point of Generator iota Inf comap
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_placeOfPoint_ofGenerator_iotaInf_comap

universe u

open CategoryTheory AlgebraicGeometry IntermediateField IsDedekindDomain

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

-- Retain the existing names through the common specified-prime comparison.
export CurveModel_placeOfPoint_ofGenerator_iota0_comap.AlgebraicCurve.Place
  (mem_valuationSubring_iff_exists
    toSubring_ofHeightOneSpectrum_comap)

end AlgebraicCurve.Place

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace CurveModel
open _root_.AlgebraicCurve.CurveModel
open _root_.AlgebraicCurve.CurveModel
open _root_.AlgebraicCurve

-- Retain the existing names through the common specified-prime comparison.
export CurveModel_placeOfPoint_ofGenerator_iota0_comap.AlgebraicCurve.CurveModel
  (gluedPlaceOfPoint_ι₀_comap
    gluedPlaceOfPoint_ιInf_comap)

theorem placeOfPoint_ofGenerator_iota0_comap
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀} : Set L₀) →+* chartRing K ({t} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀} : Set L₀), φ (a : L₀) = (ψ a : L))
    (xb : X₀ K t) (hxb : (ι₀ K t).base xb ∈ closedPoints (CurveModel.ofGenerator K t ht).C)
    (yb : X₀ K₀ t₀) (hyb : (ι₀ K₀ t₀).base yb ∈ closedPoints (CurveModel.ofGenerator K₀ t₀ ht₀).C)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    ((CurveModel.ofGenerator K t ht).placeOfPoint ⟨(ι₀ K t).base xb,
      hxb⟩).toValuationSubring.toSubring.comap φ =
      ((CurveModel.ofGenerator K₀ t₀ ht₀).placeOfPoint ⟨(ι₀ K₀ t₀).base yb,
        hyb⟩).toValuationSubring.toSubring :=
  gluedPlaceOfPoint_ι₀_comap K₀ t₀ K t ht₀ ht φ ψ hφψ xb hxb yb hyb h

theorem placeOfPoint_ofGenerator_iotaInf_comap'
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀⁻¹} : Set L₀) →+* chartRing K ({t⁻¹} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀⁻¹} : Set L₀), φ (a : L₀) = (ψ a : L))
    (x : closedPoints (CurveModel.ofGenerator K t ht).C) (hx : x.1 ∉ Set.range (ι₀ K t).base)
    (xb : XInf K t) (hxb : (ιInf K t).base xb = x.1)
    (y : closedPoints (CurveModel.ofGenerator K₀ t₀ ht₀).C) (hy : y.1 ∉ Set.range (ι₀ K₀ t₀).base)
    (yb : XInf K₀ t₀) (hyb : (ιInf K₀ t₀).base yb = y.1)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    ((CurveModel.ofGenerator K t ht).placeOfPoint x).toValuationSubring.toSubring.comap φ =
      ((CurveModel.ofGenerator K₀ t₀ ht₀).placeOfPoint y).toValuationSubring.toSubring :=
  gluedPlaceOfPoint_ιInf_comap K₀ t₀ K t ht₀ ht φ ψ hφψ x hx xb hxb y hy yb hyb h

end AlgebraicCurve.CurveModel


open _root_.AlgebraicCurve
open _root_.AlgebraicCurve.CurveModel

theorem _root_.AlgebraicCurve.CurveModel.placeOfPoint_ofGenerator_iotaInf_comap
    (K₀ : Type u) [Field K₀] {L₀ : Type u} [Field L₀] [Algebra K₀ L₀] (t₀ : L₀)
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K₀] [Fact (t₀ ≠ 0)] [FiniteDimensional K₀⟮t₀⟯ L₀] [FiniteDimensional K₀⟮t₀⁻¹⟯ L₀]
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht₀ : Transcendental K₀ t₀) (ht : Transcendental K t)
    (φ : L₀ →+* L) (ψ : chartRing K₀ ({t₀⁻¹} : Set L₀) →+* chartRing K ({t⁻¹} : Set L))
    (hφψ : ∀ a : chartRing K₀ ({t₀⁻¹} : Set L₀), φ (a : L₀) = (ψ a : L))
    (x : closedPoints (CurveModel.ofGenerator K t ht).C) (hx : x.1 ∉ Set.range (ι₀ K t).base)
    (xb : XInf K t) (hxb : (ιInf K t).base xb = x.1)
    (y : closedPoints (CurveModel.ofGenerator K₀ t₀ ht₀).C) (hy : y.1 ∉ Set.range (ι₀ K₀ t₀).base)
    (yb : XInf K₀ t₀) (hyb : (ιInf K₀ t₀).base yb = y.1)
    (h : yb.asIdeal = xb.asIdeal.comap ψ) :
    ((CurveModel.ofGenerator K t ht).placeOfPoint x).toValuationSubring.toSubring.comap φ =
      ((CurveModel.ofGenerator K₀ t₀ ht₀).placeOfPoint y).toValuationSubring.toSubring :=
  AlgebraicCurve.CurveModel.placeOfPoint_ofGenerator_iotaInf_comap' K₀ t₀ K t ht₀ ht φ ψ hφψ x hx
    xb hxb y hy yb hyb h
end AlgebraicCurves.Models.Proofs.CurveModel_placeOfPoint_ofGenerator_iotaInf_comap
end ProofImplementation
