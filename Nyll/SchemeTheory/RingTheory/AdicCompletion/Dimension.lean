/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian
import Nyll.SchemeTheory.RingTheory.AdicCompletion.LocalRingLocalRingAdicCompletionIsAdicCompleteMapMaximalIdealEq
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FaithfullyFlat
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Is Local Ring ring Krull Dim adic Completion maximal Ideal eq
-/

section IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq

open IsLocalRing in
theorem _root_.IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) = ringKrullDim R := by
  classical
  obtain ⟨hloc, hhom, -, hmap, -⟩ :=
    IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq R
  have : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isNoetherianRing_of_isNoetherianRing (maximalIdeal R)
  have : Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R
  refine le_antisymm ?_ ?_
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := AdicCompletion (maximalIdeal R) R),
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)]
    refine WithBot.coe_le_coe.2 ?_
    obtain ⟨s, hmin, hcard⟩ := Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal
      R)
    rw [← hcard]
    have hsle : Ideal.span (s : Set R) ≤ maximalIdeal R := hmin.1.2
    have hrad : maximalIdeal R ≤ (Ideal.span (s : Set R)).radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro P ⟨hsP, hP⟩
      exact hmin.2 ⟨hP, hsP⟩ (IsLocalRing.le_maximalIdeal hP.ne_top)
    obtain ⟨N, hN⟩ := Ideal.exists_radical_pow_le_of_fg (Ideal.span (s : Set R))
      (IsNoetherian.noetherian _)
    have hN' : maximalIdeal R ^ (N + 1) ≤ Ideal.span (s : Set R) :=
      (Ideal.pow_le_pow_right (Nat.le_succ N)).trans ((Ideal.pow_right_mono hrad N).trans hN)
    let s' : Finset (AdicCompletion (maximalIdeal R) R) := s.image (algebraMap R (AdicCompletion
      (maximalIdeal R) R))
    have hspan : Ideal.span (s' : Set (AdicCompletion (maximalIdeal R) R)) =
        (Ideal.span (s : Set R)).map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
      rw [Ideal.map_span, Finset.coe_image]
    have hpow : maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ (N + 1) ≤
        Ideal.span (s' : Set (AdicCompletion (maximalIdeal R) R)) := by
      rw [hspan, ← hmap, ← Ideal.map_pow]
      exact Ideal.map_mono hN'
    have hmin' : maximalIdeal (AdicCompletion (maximalIdeal R) R) ∈
        (Ideal.span (s' : Set (AdicCompletion (maximalIdeal R) R))).minimalPrimes := by
      refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal _).isPrime, ?_⟩, fun q hq _ => ?_⟩
      · rw [hspan, ← hmap]
        exact Ideal.map_mono hsle
      · have := hq.1
        exact (Ideal.IsPrime.pow_le_iff (Nat.succ_ne_zero N)).1 (hpow.trans hq.2)
    exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin').trans (Nat.cast_le.2
      Finset.card_image_le)
  · refine (iSup_le fun l => ?_ : Order.krullDim (PrimeSpectrum R) ≤ _)
    obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
      (A := R) (B := AdicCompletion (maximalIdeal R) R) l.last
    have : Q.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [← hQ]; rfl⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q.asIdeal
    rw [← hL]
    exact Order.LTSeries.length_le_krullDim L
end IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

end IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq

section IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le

/-!
# Is Local Ring two le ring Krull Dim adic Completion of two le
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le

theorem _root_.IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  have : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R
  have h2 : (2 : ℕ) ≤ Order.krullDim (PrimeSpectrum R) := by
    change ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R
    exact h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h2
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := AdicCompletion (IsLocalRing.maximalIdeal R) R) l.last
  have : Q.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [← hQ]; rfl⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q.asIdeal
  have := Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩
  exact this
end IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation

end IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
