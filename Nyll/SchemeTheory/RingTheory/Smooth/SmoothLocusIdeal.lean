/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Smooth.Locus

/-!
# The radical ideal defining the nonsmooth locus

The vanishing ideal of the actual nonsmooth locus is the smoothness ideal
used in desingularization. For finitely presented algebras, native openness
of the smooth locus identifies its zero locus exactly. This gives prime
avoidance for its image under an actual ring map, and translates pointwise
smoothness propagation into inclusion of the radical image ideals in a
common target. The two source algebras may have different base rings.
-/

@[expose] public section

noncomputable section

namespace Algebra

/-- The radical ideal whose zero locus is the nonsmooth locus for a
finitely presented algebra. The definition uses the actual smooth locus. -/
def smoothLocusIdeal (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] : Ideal B :=
  PrimeSpectrum.vanishingIdeal ((smoothLocus R B)ᶜ)

/-- The ideal of the nonsmooth locus is radical. -/
theorem smoothLocusIdeal_isRadical
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] :
    (smoothLocusIdeal R B).IsRadical :=
  PrimeSpectrum.isRadical_vanishingIdeal _

/-- Finite presentation makes the actual nonsmooth locus closed, so its
vanishing ideal cuts out that locus exactly. -/
theorem zeroLocus_smoothLocusIdeal
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [FinitePresentation R B] :
    PrimeSpectrum.zeroLocus (smoothLocusIdeal R B : Set B) = (smoothLocus R B)ᶜ := by
  change PrimeSpectrum.zeroLocus
    (PrimeSpectrum.vanishingIdeal ((smoothLocus R B)ᶜ) : Set B) = _
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (isOpen_smoothLocus (R := R) (A := B)).isClosed_compl.closure_eq

/-- A prime avoids the smoothness ideal precisely when the original
algebra is smooth at that prime. -/
theorem smoothLocusIdeal_not_le_iff
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [FinitePresentation R B]
    (p : PrimeSpectrum B) :
    ¬ smoothLocusIdeal R B ≤ p.asIdeal ↔ p ∈ smoothLocus R B := by
  have hz : p ∈ PrimeSpectrum.zeroLocus (smoothLocusIdeal R B : Set B) ↔
      smoothLocusIdeal R B ≤ p.asIdeal := PrimeSpectrum.mem_zeroLocus p _
  rw [← hz, zeroLocus_smoothLocusIdeal, Set.mem_compl_iff, not_not]

/-- Prime avoidance for the actual image of the smoothness ideal is
equivalent to smoothness at the contracted prime of the original source. -/
theorem map_smoothLocusIdeal_not_le_iff
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [FinitePresentation R B]
    {L : Type*} [CommRing L] (β : B →+* L) (q : PrimeSpectrum L) :
    ¬ (smoothLocusIdeal R B).map β ≤ q.asIdeal ↔
      PrimeSpectrum.comap β q ∈ smoothLocus R B := by
  rw [Ideal.map_le_iff_le_comap]
  exact smoothLocusIdeal_not_le_iff R B (PrimeSpectrum.comap β q)

/-- Taking the radical of the image preserves the exact prime-avoidance
criterion for the original map. -/
theorem radical_map_smoothLocusIdeal_not_le_iff
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] [FinitePresentation R B]
    {L : Type*} [CommRing L] (β : B →+* L) (q : PrimeSpectrum L) :
    ¬ ((smoothLocusIdeal R B).map β).radical ≤ q.asIdeal ↔
      PrimeSpectrum.comap β q ∈ smoothLocus R B := by
  rw [q.2.radical_le_iff]
  exact map_smoothLocusIdeal_not_le_iff R B β q

/-- Actual pointwise propagation along a ring map sends the original
smoothness ideal into the target smoothness ideal. No closedness or
Noetherian assumption is needed for this implication. -/
theorem map_smoothLocusIdeal_le_of_smoothLocus_comap
    (R S B E : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing E]
    [Algebra R B] [Algebra S E] (θ : B →+* E)
    (hprop : ∀ p : PrimeSpectrum E,
      PrimeSpectrum.comap θ p ∈ smoothLocus R B → p ∈ smoothLocus S E) :
    (smoothLocusIdeal R B).map θ ≤ smoothLocusIdeal S E := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro b hb
  change θ b ∈ PrimeSpectrum.vanishingIdeal ((smoothLocus S E)ᶜ)
  apply (PrimeSpectrum.mem_vanishingIdeal _ _).mpr
  intro p hp
  have hnot : PrimeSpectrum.comap θ p ∈ (smoothLocus R B)ᶜ := by
    intro hs
    exact hp (hprop p hs)
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hb (PrimeSpectrum.comap θ p) hnot

/-- Inclusion of the radical smoothness-ideal images in a common target
is exactly pointwise propagation of smoothness at its contracted primes.
The equivalence is derived from the actual closed nonsmooth loci. -/
theorem radical_map_smoothLocusIdeal_le_iff
    (R S B E : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing E]
    [Algebra R B] [Algebra S E] [FinitePresentation R B] [FinitePresentation S E]
    {L : Type*} [CommRing L] (β : B →+* L) (δ : E →+* L) :
    ((smoothLocusIdeal R B).map β).radical ≤
        ((smoothLocusIdeal S E).map δ).radical ↔
      ∀ q : PrimeSpectrum L,
        PrimeSpectrum.comap β q ∈ smoothLocus R B →
          PrimeSpectrum.comap δ q ∈ smoothLocus S E := by
  constructor
  · intro h q hq
    apply (radical_map_smoothLocusIdeal_not_le_iff S E δ q).mp
    intro hE
    exact ((radical_map_smoothLocusIdeal_not_le_iff R B β q).mpr hq) (h.trans hE)
  · intro h
    apply Ideal.radical_le_radical_iff.mpr
    apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
      ((smoothLocusIdeal S E).map δ) ((smoothLocusIdeal R B).map β)).mp
    intro q hq
    apply (PrimeSpectrum.mem_zeroLocus q _).mpr
    change (smoothLocusIdeal R B).map β ≤ q.asIdeal
    by_contra hB
    have hsB := (map_smoothLocusIdeal_not_le_iff R B β q).mp hB
    have hsE := h q hsB
    have hE : (smoothLocusIdeal S E).map δ ≤ q.asIdeal :=
      (PrimeSpectrum.mem_zeroLocus q _).mp hq
    exact ((map_smoothLocusIdeal_not_le_iff S E δ q).mpr hsE) hE

/-- A genuine factorization and actual smoothness propagation along its
first map yield the corresponding inclusion of radical image ideals in the
original target. The equality retains the originally specified map `β`. -/
theorem radical_map_smoothLocusIdeal_le_of_factorization
    (R S B E : Type*) [CommRing R] [CommRing S] [CommRing B] [CommRing E]
    [Algebra R B] [Algebra S E] {L : Type*} [CommRing L]
    (θ : B →+* E) (δ : E →+* L) (β : B →+* L)
    (hβ : δ.comp θ = β)
    (hprop : ∀ p : PrimeSpectrum E,
      PrimeSpectrum.comap θ p ∈ smoothLocus R B → p ∈ smoothLocus S E) :
    ((smoothLocusIdeal R B).map β).radical ≤
      ((smoothLocusIdeal S E).map δ).radical := by
  have hinc := map_smoothLocusIdeal_le_of_smoothLocus_comap R S B E θ hprop
  have hmap := Ideal.map_mono (f := δ) hinc
  rw [Ideal.map_map, hβ] at hmap
  exact Ideal.radical_mono hmap

end Algebra
