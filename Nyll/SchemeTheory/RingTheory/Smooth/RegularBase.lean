/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalLocalizationAtPrimeEtale
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Smooth algebras over regular rings

A standard smooth algebra is étale over a polynomial algebra on finitely
many variables. Polynomial rings over a regular base are regular, and
étale morphisms preserve regularity of the corresponding local rings.
Passing to the standard smooth neighbourhood of each prime proves the
same result for an arbitrary smooth algebra.

This supplies regularity after smooth base change to a DVR, as needed
before the purity argument in Stacks Project, Proposition 58.30.2.
No regularity assertion about the fibres or the source is an additional
hypothesis.
https://stacks.math.columbia.edu/tag/0C0Q
-/

noncomputable section

namespace Algebra

universe u v

/-- A standard smooth algebra over a regular ring is regular. -/
theorem IsStandardSmooth.isRegularRing_of_isRegularRing
    (R : Type u) (S : Type v) [CommRing R] [IsRegularRing R]
    [CommRing S] [Algebra R S] [IsStandardSmooth R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  obtain ⟨n, g, _hbase, hg⟩ :=
    (RingHom.isStandardSmooth_algebraMap.mpr
      (inferInstance : IsStandardSmooth R S)).exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin n) R) S := g.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) R) S := RingHom.etale_algebraMap.mp hg
  apply isRegularRing_iff.mpr
  intro q hq
  exact isRegularLocalRing_localization_atPrime_of_etale_of_comap
    (MvPolynomial (Fin n) R) S q
    (IsRegularRing.isRegularLocalRing_localization
      (q.comap (algebraMap (MvPolynomial (Fin n) R) S)))

/-- Every prime localization of a smooth algebra over a regular ring is
regular, without a smooth-fibre regularity assumption. -/
theorem Smooth.isRegularRing_of_isRegularRing
    (R : Type u) (S : Type v) [CommRing R] [IsRegularRing R]
    [CommRing S] [Algebra R S] [Smooth R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isRegularRing_iff.mpr
  intro p hp
  obtain ⟨f, hf, hstandard⟩ := IsSmoothAt.exists_notMem_isStandardSmooth R p
  let Sf := Localization.Away f
  have : IsStandardSmooth R Sf := hstandard
  have : IsRegularRing Sf := IsStandardSmooth.isRegularRing_of_isRegularRing R Sf
  have hdisjoint : Disjoint (Submonoid.powers f : Set S) (p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let q := p.map (algebraMap S Sf)
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) Sf p hp hdisjoint
  have hcomap : q.comap (algebraMap S Sf) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) Sf hp hdisjoint
  have : IsLocalization p.primeCompl (Localization.AtPrime q) := by
    simpa only [hcomap] using
      (inferInstance : IsLocalization (q.comap (algebraMap S Sf)).primeCompl
        (Localization.AtPrime q))
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl
      (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv

end Algebra
