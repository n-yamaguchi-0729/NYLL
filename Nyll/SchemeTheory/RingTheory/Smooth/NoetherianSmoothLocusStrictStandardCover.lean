/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.SmoothPrimeExactStrictStandardData
public import Nyll.SchemeTheory.RingTheory.Smooth.StrictStandardSmoothConverse
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# A finite original strictly-standard cover of the entire smooth locus

For a finite presentation with Noetherian target, form the ideal generated
by the images of all genuine strictly-standard parameters in that same
presentation, with exact original relation memberships. Finite generation
extracts finitely many of those parameters.
The smooth-prime selector and its converse identify the union of their
principal opens with the entire smooth locus. No open subset is supplied
as an input, and the original variables and relations are retained.
-/

@[expose] public section

noncomputable section

universe u v w t

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- The entire smooth locus of a finite presentation with Noetherian target
has a finite principal-open cover by actual strictly-standard parameters
in the original presentation. Each parameter retains its selected original
relations and its Jacobian-minor membership; its product with every
original relation belongs to the selected relation ideal itself. -/
theorem Presentation.exists_finite_strictStandard_cover_of_smoothLocus
    {ι : Type w} {σ : Type t} [Finite ι] [Finite σ] [IsNoetherianRing B]
    (P : Presentation R B ι σ) :
    ∃ s : Finset P.Ring,
      (∀ q ∈ s,
        Smooth R (Localization.Away (algebraMap P.Ring B q)) ∧
        ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → σ),
          Function.Injective a ∧
          q ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
            ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
              _root_.id c).det)) ∧
          ∀ j, q * P.relation j ∈
            Ideal.span (Set.range (fun i => P.relation (a i)))) ∧
      ∀ p : PrimeSpectrum B,
        p ∈ smoothLocus R B ↔ ∃ q ∈ s, algebraMap P.Ring B q ∉ p.asIdeal := by
  classical
  have : FinitePresentation R B := P.finitePresentation_of_isFinite
  let T : Set P.Ring := {q |
    ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → σ),
      Function.Injective a ∧
      q ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
        ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
          _root_.id c).det)) ∧
      ∀ j, q * P.relation j ∈
        Ideal.span (Set.range (fun i => P.relation (a i)))}
  have hfg : (Ideal.span ((algebraMap P.Ring B) '' T)).FG :=
    Ideal.fg_of_isNoetherianRing _
  obtain ⟨u, hu, heu⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset ((algebraMap P.Ring B) '' T)).mp hfg
  obtain ⟨s, hs, hsu⟩ := Finset.subset_set_image_iff.mp hu
  have hspan : Ideal.span ((algebraMap P.Ring B) '' T) =
      Ideal.span ((algebraMap P.Ring B) '' (s : Set P.Ring)) := by
    rw [← Finset.coe_image, hsu]
    exact heu
  have hdata (q : P.Ring) (hq : q ∈ s) :
      Smooth R (Localization.Away (algebraMap P.Ring B q)) ∧
      ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → σ),
        Function.Injective a ∧
        q ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
          ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
            _root_.id c).det)) ∧
        ∀ j, q * P.relation j ∈
          Ideal.span (Set.range (fun i => P.relation (a i))) := by
    obtain ⟨κ, hκ, hκdec, a, ha, hminor, hrelations⟩ := hs hq
    let _ : Fintype κ := hκ
    let _ : DecidableEq κ := hκdec
    have hresidual : ∀ j, q * P.relation j ∈
        Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2 := by
      intro j
      exact (show Ideal.span (Set.range (fun i => P.relation (a i))) ≤
        Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2 from
          le_sup_left) (hrelations j)
    exact ⟨P.smooth_away_of_strictStandard_data a q hminor hresidual,
      κ, hκ, hκdec, a, ha, hminor, hrelations⟩
  refine ⟨s, hdata, ?_⟩
  intro p
  constructor
  · intro hp
    have : IsSmoothAt R p.asIdeal := hp
    obtain ⟨κ, hκ, hκdec, a, q, hq, hminor, hrelations⟩ :=
      P.exists_strictStandard_exact_data_at_smoothPrime p.asIdeal
    have ha : Function.Injective a :=
      P.injective_selection_of_strictStandard_minor_notMem p.asIdeal a q hq hminor
    have hqT : q ∈ T := ⟨κ, hκ, hκdec, a, ha, hminor, hrelations⟩
    have hmem : algebraMap P.Ring B q ∈
        Ideal.span ((algebraMap P.Ring B) '' (s : Set P.Ring)) := by
      rw [← hspan]
      exact Ideal.subset_span ⟨q, hqT, rfl⟩
    by_contra hn
    have hle : Ideal.span ((algebraMap P.Ring B) '' (s : Set P.Ring)) ≤ p.asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨r, hr, rfl⟩
      by_contra hrp
      exact hn ⟨r, hr, hrp⟩
    exact hq (hle hmem)
  · rintro ⟨q, hq, hqp⟩
    have hopen :
        (PrimeSpectrum.basicOpen (algebraMap P.Ring B q) : Set (PrimeSpectrum B)) ⊆
          smoothLocus R B :=
      (basicOpen_subset_smoothLocus_iff_smooth (R := R)).mpr (hdata q hq).1
    exact hopen ((PrimeSpectrum.mem_basicOpen (algebraMap P.Ring B q) p).mpr hqp)

end Algebra
