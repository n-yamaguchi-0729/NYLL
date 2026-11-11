/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.SmoothPrimeStrictStandardData
public import Mathlib.RingTheory.Smooth.Locus

/-!
# A finite strictly-standard cover in the original presentation

For a smooth principal open, the actual smooth-prime selector produces
original polynomial parameters outside every prime of that open. Multiply
each parameter by a polynomial lift of the principal-open parameter, so
all selected opens remain inside the given smooth open. The prime-radical
criterion and finite-span extraction produce a finite family whose images
generate an ideal containing a positive power of the original parameter.
No Noetherian hypothesis or change of presentation is used.
-/

@[expose] public section

noncomputable section

universe u v w t

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- A smooth principal open has a finite cover by actual strictly-standard
parameters in the original finite presentation. Each parameter retains its
own selected original relations. Their image ideal contains a positive power
of the principal-open parameter, and every selected open is smooth and lies
inside the original open. -/
theorem Presentation.exists_finite_strictStandard_cover_of_smooth_away
    {ι : Type w} {σ : Type t} [Finite ι] [Finite σ] (P : Presentation R B ι σ)
    (d : B) [Smooth R (Localization.Away d)] :
    ∃ (s : Finset P.Ring) (N : ℕ), 0 < N ∧
      d ^ N ∈ Ideal.span ((algebraMap P.Ring B) '' (s : Set P.Ring)) ∧
      (∀ q ∈ s,
        algebraMap P.Ring B q ∈ Ideal.span {d} ∧
        Smooth R (Localization.Away (algebraMap P.Ring B q)) ∧
        ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → σ),
          q ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
            ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
              _root_.id c).det)) ∧
          ∀ j, q * P.relation j ∈
            Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2) ∧
      ∀ p : PrimeSpectrum B,
        d ∉ p.asIdeal ↔ ∃ q ∈ s, algebraMap P.Ring B q ∉ p.asIdeal := by
  classical
  have : FinitePresentation R B := P.finitePresentation_of_isFinite
  have hopen : (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum B)) ⊆ smoothLocus R B :=
    (basicOpen_subset_smoothLocus_iff_smooth (R := R)).mpr inferInstance
  obtain ⟨e, he⟩ := P.algebraMap_surjective d
  let T : Set P.Ring := {q |
    algebraMap P.Ring B q ∈ Ideal.span {d} ∧
      ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → σ),
        q ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
          ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
            _root_.id c).det)) ∧
        ∀ j, q * P.relation j ∈
          Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2}
  let J : Ideal B := (Ideal.span T).map (algebraMap P.Ring B)
  have hradical : d ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hJp, hp⟩
    by_contra hdp
    have : p.IsPrime := hp
    have : IsSmoothAt R p := hopen
      ((PrimeSpectrum.mem_basicOpen d (⟨p, hp⟩ : PrimeSpectrum B)).mpr hdp)
    obtain ⟨κ, hκ, hκdec, a, q, hq, hminor, hrelations⟩ :=
      P.exists_strictStandard_data_at_smoothPrime p
    let _ : Fintype κ := hκ
    let _ : DecidableEq κ := hκdec
    have heq : algebraMap P.Ring B (e * q) = d * algebraMap P.Ring B q := by
      rw [map_mul, he]
    have hT : e * q ∈ T := by
      refine ⟨Ideal.mem_span_singleton.mpr ⟨algebraMap P.Ring B q, heq⟩,
        κ, hκ, hκdec, a, ?_, fun j => ?_⟩
      · exact (P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
          ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
            _root_.id c).det))).mul_mem_left e hminor
      · have hj := (Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2).mul_mem_left
          e (hrelations j)
        simpa only [mul_assoc] using hj
    have hnot : algebraMap P.Ring B (e * q) ∉ p := by
      rw [heq]
      exact p.primeCompl.mul_mem hdp hq
    exact hnot (hJp (Ideal.mem_map_of_mem (algebraMap P.Ring B) (Ideal.subset_span hT)))
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hradical
  have hN' : d ^ (N + 1) ∈ J := by
    rw [pow_succ']
    exact J.mul_mem_left d hN
  obtain ⟨q, hq, hqeq⟩ :=
    (Ideal.mem_map_iff_of_surjective (algebraMap P.Ring B) P.algebraMap_surjective).mp hN'
  obtain ⟨s, hs, hqs⟩ := Submodule.mem_span_finite_of_mem_span hq
  have hpower : d ^ (N + 1) ∈
      Ideal.span ((algebraMap P.Ring B) '' (s : Set P.Ring)) := by
    rw [← Ideal.map_span, ← hqeq]
    exact Ideal.mem_map_of_mem (algebraMap P.Ring B) hqs
  have hdata (q : P.Ring) (hq : q ∈ s) :
      algebraMap P.Ring B q ∈ Ideal.span {d} ∧
      Smooth R (Localization.Away (algebraMap P.Ring B q)) ∧
      ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → σ),
        q ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
          ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
            _root_.id c).det)) ∧
        ∀ j, q * P.relation j ∈
          Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2 := by
    have hqT := hs hq
    have hsub : (PrimeSpectrum.basicOpen (algebraMap P.Ring B q) : Set (PrimeSpectrum B)) ⊆
        PrimeSpectrum.basicOpen d := by
      intro p hp
      change d ∉ p.asIdeal
      intro hdp
      exact hp ((p.asIdeal.span_singleton_le_iff_mem.mpr hdp) hqT.1)
    exact ⟨hqT.1, (basicOpen_subset_smoothLocus_iff_smooth (R := R)).mp
      (hsub.trans hopen), hqT.2⟩
  refine ⟨s, N + 1, Nat.zero_lt_succ N, hpower, hdata, ?_⟩
  intro p
  constructor
  · intro hdp
    by_contra hn
    have hle : Ideal.span ((algebraMap P.Ring B) '' (s : Set P.Ring)) ≤ p.asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨q, hq, rfl⟩
      by_contra hqp
      exact hn ⟨q, hq, hqp⟩
    exact hdp (p.isPrime.mem_of_pow_mem (N + 1) (hle hpower))
  · rintro ⟨q, hq, hqp⟩ hdp
    exact hqp ((p.asIdeal.span_singleton_le_iff_mem.mpr hdp) (hdata q hq).1)

end Algebra
