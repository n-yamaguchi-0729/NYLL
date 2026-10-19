/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The actual generic and closed fibres cover a scheme over a DVR

Every point lies in the image of the generic open obtained by inverting
a uniformizer or in the image of the residue-field fibre. Membership of
the uniformizer in the image prime decides the two cases. If it belongs
to that prime, maximality forces the prime to be the closed point.

The pullback range theorem then lifts this elementary spectrum
calculation to the actual scheme fibres. This is the covering argument
used to combine the normalized root charts along the closed fibre with
the original finite étale cover on the generic open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SchemeTheory

universe u

/-- The actual away fibre and the actual residue fibre account for every
point of a scheme over a DVR. No lifting of points is assumed. -/
theorem mem_genericFiber_or_closedFiber_of_DVR
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) (π : B) (hπ : Prime π) (x : X) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away π)))
    let s := Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
    x ∈ Set.range (pullback.fst f η : pullback f η ⟶ X) ∨
      x ∈ Set.range (pullback.fst f s : pullback f s ⟶ X) := by
  intro η s
  rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
  change f x ∈ Set.range η ∨ f x ∈ Set.range s
  by_cases h : π ∈ (f x).asIdeal
  · right
    have hle : IsLocalRing.maximalIdeal B ≤ (f x).asIdeal := by
      rw [hπ.irreducible.maximalIdeal_eq]
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
    have hEq : IsLocalRing.maximalIdeal B = (f x).asIdeal :=
      (IsLocalRing.maximalIdeal.isMaximal B).eq_of_le (f x).isPrime.ne_top hle
    have hPoint : IsLocalRing.closedPoint B = f x := PrimeSpectrum.ext hEq
    refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField B), ?_⟩
    change PrimeSpectrum.comap (IsLocalRing.residue B)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField B)) = f x
    exact (IsLocalRing.PrimeSpectrum.comap_residue B _).trans hPoint
  · left
    let p : PrimeSpectrum B := f x
    have hp : p ∈ PrimeSpectrum.basicOpen π := h
    have hRange : Set.range
        (PrimeSpectrum.comap (algebraMap B (Localization.Away π))) =
        (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum B)) :=
      PrimeSpectrum.localization_away_comap_range (Localization.Away π) π
    have hpRange : p ∈ Set.range
        (PrimeSpectrum.comap (algebraMap B (Localization.Away π))) := hRange.symm ▸ hp
    exact hpRange

end SchemeTheory
