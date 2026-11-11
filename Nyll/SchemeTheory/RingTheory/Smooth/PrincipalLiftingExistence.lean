/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingSourceData
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingFiniteData
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingReductionMap
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingLocalization
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingLocalSmooth
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingRelativeSmooth

/-!
# Principal lifting with the original source and target maps

Starting with the original finite presentation over `R/(π²)` and its map
to `L/(π²)`, construct the finitely presented lifting algebra, its map to
`L`, and the original source map modulo `π`. Both polynomial triangles and
the resulting source-target triangle modulo `π` are retained. The actual
finite strictly-standard cover supplies smoothness at the corresponding
primes above `π`; smoothness away from `π` follows from elimination of the
new variables. The actual reduction map is also smooth over the original
source modulo the parameter at every prime above its original smooth locus.

This is the algebra and smooth-locus part of the Stacks Project lifting
construction: https://stacks.math.columbia.edu/tag/07CP
-/

@[expose] public section

noncomputable section

universe u v w t z

namespace Algebra

open MvPolynomial

private theorem exists_principal_quotient_triangles
    {R L D B n : Type*} [CommRing R] [CommRing L] [CommRing D] [CommRing B]
    [Algebra R L] [Algebra R D] (π : R)
    (σ : MvPolynomial n R →+* B) (hσ : Function.Surjective σ)
    (β : D →ₐ[R] L) (ξ : MvPolynomial n R →ₐ[R] D)
    (γ : B →+* D ⧸ Ideal.span {algebraMap R D π})
    (α : B →+* L ⧸ Ideal.span {(algebraMap R L π) ^ 2})
    (hγ : γ.comp σ = (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})).comp
      ξ.toRingHom)
    (hα : (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})).comp
      (β.comp ξ).toRingHom = α.comp σ) :
    ∃ (δ : (D ⧸ Ideal.span {algebraMap R D π}) →+*
          L ⧸ Ideal.span {algebraMap R L π})
      (ε : (L ⧸ Ideal.span {(algebraMap R L π) ^ 2}) →+*
          L ⧸ Ideal.span {algebraMap R L π}),
      δ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) =
        (Ideal.Quotient.mk (Ideal.span {algebraMap R L π})).comp β.toRingHom ∧
      ε.comp (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})) =
        Ideal.Quotient.mk (Ideal.span {algebraMap R L π}) ∧
      δ.comp γ = ε.comp α := by
  have hβ : Ideal.span {algebraMap R D π} ≤
      (Ideal.span {algebraMap R L π}).comap β.toRingHom := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change β (algebraMap R D π) ∈ Ideal.span {algebraMap R L π}
    rw [β.commutes]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hpow : Ideal.span {(algebraMap R L π) ^ 2} ≤
      Ideal.span {algebraMap R L π} := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [pow_two]
    exact (Ideal.span {algebraMap R L π}).mul_mem_left _
      (Ideal.subset_span (Set.mem_singleton _))
  let δ := Ideal.quotientMap (Ideal.span {algebraMap R L π}) β.toRingHom hβ
  let ε := Ideal.Quotient.factor hpow
  refine ⟨δ, ε, Ideal.quotientMap_comp_mk hβ, Ideal.Quotient.factor_comp_mk hpow, ?_⟩
  apply RingHom.ext
  intro b
  obtain ⟨p, rfl⟩ := hσ b
  change δ (γ (σ p)) = ε (α (σ p))
  have hγp := RingHom.congr_fun hγ p
  change γ (σ p) = Ideal.Quotient.mk _ (ξ p) at hγp
  have hαp := RingHom.congr_fun hα p
  change Ideal.Quotient.mk _ (β (ξ p)) = α (σ p) at hαp
  calc
    δ (γ (σ p)) = δ (Ideal.Quotient.mk _ (ξ p)) := congrArg δ hγp
    _ = Ideal.Quotient.mk _ (β (ξ p)) := Ideal.quotientMap_mk
    _ = ε (Ideal.Quotient.mk _ (β (ξ p))) :=
      (Ideal.Quotient.factor_mk hpow (β (ξ p))).symm
    _ = ε (α (σ p)) := congrArg ε hαp

/-- Construct the principal lifting algebra from the actual original
presentation and approximate target map. Its finite smooth-cover parameters
retain their images under the original reduction map, and yield actual
smoothness at all primes above `π` which avoid one of these parameters. -/
theorem Presentation.exists_principal_lifting
    {R : Type u} {L : Type v} [CommRing R] [CommRing L] [Algebra R L]
    (π : R) (hstableR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (hstableL : ∀ x : L, (algebraMap R L π) ^ 2 * x = 0 →
      algebraMap R L π * x = 0)
    {B : Type w} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    [IsNoetherianRing B] {n : Type t} {m : Type z} [Finite n] [Finite m]
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (α : B →+* L ⧸ Ideal.span {(algebraMap R L π) ^ 2})
    (hα : ∀ r : R,
      α (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2}) (algebraMap R L r)) :
    ∃ (D : Type (max u t z)) (_ : CommRing D) (_ : Algebra R D),
      FinitePresentation R D ∧
      Smooth R (Localization.Away (algebraMap R D π)) ∧
      ∃ (β : D →ₐ[R] L) (ξ : MvPolynomial n R →ₐ[R] D)
        (γ : B →+* D ⧸ Ideal.span {algebraMap R D π}),
        (∀ i, γ (P.val i) = Ideal.Quotient.mk _ (ξ (X i))) ∧
        (∀ i, Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})
          (β (ξ (X i))) = α (P.val i)) ∧
        (∀ r : R, γ (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (algebraMap R D r)) ∧
        γ.comp ((algebraMap P.Ring B).comp
          (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})))) =
          (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})).comp ξ.toRingHom ∧
        (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})).comp
          (β.comp ξ).toRingHom =
          α.comp ((algebraMap P.Ring B).comp
            (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})))) ∧
        (∃ (δ : (D ⧸ Ideal.span {algebraMap R D π}) →+*
              L ⧸ Ideal.span {algebraMap R L π})
            (ε : (L ⧸ Ideal.span {(algebraMap R L π) ^ 2}) →+*
              L ⧸ Ideal.span {algebraMap R L π}),
          δ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) =
            (Ideal.Quotient.mk (Ideal.span {algebraMap R L π})).comp β.toRingHom ∧
          ε.comp (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})) =
            Ideal.Quotient.mk (Ideal.span {algebraMap R L π}) ∧
          δ.comp γ = ε.comp α) ∧
        ∃ (s : Finset P.Ring) (E : s → D),
          (∀ t, γ (algebraMap P.Ring B t.val) =
            Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (E t)) ∧
          (∀ p : PrimeSpectrum B,
            p ∈ smoothLocus (R ⧸ Ideal.span {π ^ 2}) B ↔
              ∃ t : s, algebraMap P.Ring B t.val ∉ p.asIdeal) ∧
          (∀ (t : s) (p : PrimeSpectrum D), algebraMap R D π ∈ p.asIdeal →
            E t ∉ p.asIdeal → IsSmoothAt R p.asIdeal) ∧
          let bπ := algebraMap (R ⧸ Ideal.span {π ^ 2}) B
            (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)
          let Bbar := B ⧸ Ideal.span {bπ}
          ∃ γbar : Bbar →+* D ⧸ Ideal.span {algebraMap R D π},
            γbar.comp (Ideal.Quotient.mk (Ideal.span {bπ})) = γ ∧
            let _ : Algebra Bbar (D ⧸ Ideal.span {algebraMap R D π}) :=
              RingHom.toAlgebra (R := Bbar) (S := D ⧸ Ideal.span {algebraMap R D π}) γbar
            ∀ p : PrimeSpectrum (D ⧸ Ideal.span {algebraMap R D π}),
              PrimeSpectrum.comap γ p ∈ smoothLocus (R ⧸ Ideal.span {π ^ 2}) B →
              IsSmoothAt Bbar (A := D ⧸ Ideal.span {algebraMap R D π}) p.asIdeal := by
  classical
  let _ : Fintype m := Fintype.ofFinite m
  obtain ⟨f, xval, μ, hf, hxval, hμ, heval⟩ :=
    P.exists_principal_lifting_source_data π α hα
  obtain ⟨s, A, H, g, hA, hrel, hselected, hcover⟩ :=
    P.exists_finite_normalized_principal_lifting_data π f hf
  let J := principalLiftingIdeal π f A H g
  let D := MvPolynomial (n ⊕ m) R ⧸ J
  let θ : MvPolynomial (n ⊕ m) R →ₐ[R] D := Ideal.Quotient.mkₐ R J
  have hJ : J.FG :=
    (Submodule.fg_span (Set.finite_range _)).sup
      (Submodule.fg_span (Set.finite_range _))
  have : FinitePresentation R D := FinitePresentation.quotient hJ
  let β : D →ₐ[R] L := Ideal.Quotient.liftₐ J
    (aeval (Sum.elim xval (fun j => algebraMap R L π * μ j)))
    (fun _ hx => principalLiftingIdeal_le_ker_aeval
      π f A H g hrel xval μ hμ hstableL hx)
  let ξ : MvPolynomial n R →ₐ[R] D := θ.comp (rename Sum.inl)
  have hβθ : β.comp θ =
      aeval (Sum.elim xval (fun j => algebraMap R L π * μ j)) :=
    Ideal.Quotient.liftₐ_comp _ _ _
  have hβξ : β.comp ξ = aeval xval := by
    apply AlgHom.ext
    intro p
    change β (θ (rename Sum.inl p)) = aeval xval p
    calc
      _ = aeval (Sum.elim xval (fun j => algebraMap R L π * μ j))
          (rename Sum.inl p) := AlgHom.congr_fun hβθ _
      _ = aeval xval p := aeval_rename Sum.inl _ p
  have hθ (j : m) : θ (principalLiftingRelation π f j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span (Set.range (principalLiftingRelation π f)) ≤ J from
        le_sup_left) (Ideal.subset_span ⟨j, rfl⟩))
  obtain ⟨γ, hγgen, hγcoeff, hγ⟩ :=
    P.exists_principal_lifting_reductionMap π f hf θ hθ
  have hαξ : (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})).comp
      (β.comp ξ).toRingHom =
      α.comp ((algebraMap P.Ring B).comp
        (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})))) := by
    rw [hβξ]
    exact heval
  let σ : MvPolynomial n R →+* B := (algebraMap P.Ring B).comp
    (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})))
  have hσ : Function.Surjective σ :=
    P.algebraMap_surjective.comp (map_surjective _ Ideal.Quotient.mk_surjective)
  have htriangle := exists_principal_quotient_triangles π σ hσ β ξ γ α hγ hαξ
  let E : s → D := fun t => ξ (A t)
  have hE (t : s) : γ (algebraMap P.Ring B t.val) =
      Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (E t) := by
    have ht := RingHom.congr_fun hγ (A t)
    change γ (algebraMap P.Ring B
      (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t))) =
        Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (E t) at ht
    rw [hA t] at ht
    exact ht
  refine ⟨D, inferInstance, inferInstance, inferInstance,
    smooth_principalLifting_localization π f A H g hrel,
    β, ξ, γ, ?_, ?_, hγcoeff, hγ, hαξ, htriangle, s, E, hE, hcover, ?_, ?_⟩
  · intro i
    change γ (P.val i) = Ideal.Quotient.mk _ (θ (rename Sum.inl (X i)))
    rw [rename_X]
    exact hγgen i
  · intro i
    have hi := AlgHom.congr_fun hβξ (X i)
    change β (ξ (X i)) = aeval xval (X i) at hi
    rw [hi, aeval_X]
    exact hxval i
  · intro t p hπ hEt
    obtain ⟨κ, hκ, hκdec, a, ha, hdiag, hsupport, hzero, hminor⟩ := hselected t
    let _ : Fintype κ := hκ
    let _ : DecidableEq κ := hκdec
    have hminor' : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
        P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
          ((Matrix.of fun j i => pderiv i (P.relation (a j))).submatrix _root_.id b).det) := by
      rw [hA t]
      exact hminor
    exact isSmoothAt_principalLifting_of_strictStandard π hstableR P f
      (fun j => (hf j).symm) A H g hrel t a ha hdiag hsupport hzero hminor' p hπ hEt
  · intro bπ Bbar
    have hγ' (p : MvPolynomial n R) :
        γ (algebraMap P.Ring B (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) p)) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
            (Ideal.Quotient.mk J (rename Sum.inl p)) := RingHom.congr_fun hγ p
    obtain ⟨_eC, _eD, γbar, _heC, _heD, hγbar, _hcomm⟩ :=
      P.exists_principal_lifting_reduction_comparison π f hf A H g γ hγ'
    refine ⟨γbar, hγbar, ?_⟩
    intro hBD p hp
    obtain ⟨t, ht⟩ := (hcover (PrimeSpectrum.comap γ p)).mp hp
    have htD : Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
        (Ideal.Quotient.mk J (rename Sum.inl (A t))) ∉ p.asIdeal := by
      intro hmem
      apply ht
      change γ (algebraMap P.Ring B t.val) ∈ p.asIdeal
      rw [hE t]
      exact hmem
    obtain ⟨κ, hκ, hκdec, a, ha, hdiag, hsupport, _hzero, hminor⟩ := hselected t
    let _ : Fintype κ := hκ
    let _ : DecidableEq κ := hκdec
    have hminor' : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
        P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
          ((Matrix.of fun j i => pderiv i (P.relation (a j))).submatrix _root_.id b).det) := by
      rw [hA t]
      exact hminor
    exact P.isSmoothAt_principal_lifting_reduction_of_strictStandard
      π f hf A H g hrel t a ha hdiag hsupport hminor' γ hγ' γbar hγbar p htD

/-- Principal lifting is smooth above the original source's smooth locus.
The construction retains its coefficient map and the exact source-target
square modulo the parameter, without a choice of cover in the conclusion. -/
theorem Presentation.exists_principal_lifting_with_source_smoothLocus
    {R : Type u} {L : Type v} [CommRing R] [CommRing L] [Algebra R L]
    (π : R) (hstableR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (hstableL : ∀ x : L, (algebraMap R L π) ^ 2 * x = 0 →
      algebraMap R L π * x = 0)
    {B : Type w} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    [IsNoetherianRing B] {n : Type t} {m : Type z} [Finite n] [Finite m]
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (α : B →+* L ⧸ Ideal.span {(algebraMap R L π) ^ 2})
    (hα : ∀ r : R,
      α (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2}) (algebraMap R L r)) :
    ∃ (D : Type (max u t z)) (_ : CommRing D) (_ : Algebra R D),
      FinitePresentation R D ∧
      Smooth R (Localization.Away (algebraMap R D π)) ∧
      ∃ (β : D →ₐ[R] L) (γ : B →+* D ⧸ Ideal.span {algebraMap R D π}),
        (∀ r : R, γ (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (algebraMap R D r)) ∧
        (∃ (δ : (D ⧸ Ideal.span {algebraMap R D π}) →+*
              L ⧸ Ideal.span {algebraMap R L π})
            (ε : (L ⧸ Ideal.span {(algebraMap R L π) ^ 2}) →+*
              L ⧸ Ideal.span {algebraMap R L π}),
          δ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) =
            (Ideal.Quotient.mk (Ideal.span {algebraMap R L π})).comp β.toRingHom ∧
          ε.comp (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})) =
            Ideal.Quotient.mk (Ideal.span {algebraMap R L π}) ∧
          δ.comp γ = ε.comp α) ∧
        ∀ p : PrimeSpectrum (D ⧸ Ideal.span {algebraMap R D π}),
          PrimeSpectrum.comap γ p ∈ smoothLocus (R ⧸ Ideal.span {π ^ 2}) B →
          IsSmoothAt R (PrimeSpectrum.comap
            (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) p).asIdeal := by
  obtain ⟨D, hD, hRD, hfp, haway, β, ξ, γ, _hγgen, _hβgen, hcoeff,
    _hγpoly, _hαpoly, htriangle, s, E, hE, hcover, hsmooth, _hrelative⟩ :=
    P.exists_principal_lifting π hstableR hstableL α hα
  let _ : CommRing D := hD
  let _ : Algebra R D := hRD
  refine ⟨D, hD, hRD, hfp, haway, β, γ, hcoeff, htriangle, ?_⟩
  intro p hp
  obtain ⟨t, ht⟩ := (hcover (PrimeSpectrum.comap γ p)).mp hp
  let pD := PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) p
  have hπ : algebraMap R D π ∈ pD.asIdeal := by
    change Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
      (algebraMap R D π) ∈ p.asIdeal
    have hzero : Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
        (algebraMap R D π) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
    rw [hzero]
    exact p.asIdeal.zero_mem
  have htD : E t ∉ pD.asIdeal := by
    intro hmem
    apply ht
    change γ (algebraMap P.Ring B t.val) ∈ p.asIdeal
    rw [hE t]
    exact hmem
  exact hsmooth t pD hπ htD

/-- A finitely presented algebra over a Noetherian principal-square quotient
admits the actual principal lifting, smooth away from the parameter and
above its original smooth locus. No presentation is supplied as input. -/
theorem exists_principal_lifting_with_source_smoothLocus
    {R : Type u} {L : Type v} [CommRing R] [CommRing L] [Algebra R L]
    [IsNoetherianRing R]
    (π : R) (hstableR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (hstableL : ∀ x : L, (algebraMap R L π) ^ 2 * x = 0 →
      algebraMap R L π * x = 0)
    {B : Type w} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    [FinitePresentation (R ⧸ Ideal.span {π ^ 2}) B]
    (α : B →+* L ⧸ Ideal.span {(algebraMap R L π) ^ 2})
    (hα : ∀ r : R,
      α (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2}) (algebraMap R L r)) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      FinitePresentation R D ∧
      Smooth R (Localization.Away (algebraMap R D π)) ∧
      ∃ (β : D →ₐ[R] L) (γ : B →+* D ⧸ Ideal.span {algebraMap R D π}),
        (∀ r : R, γ (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (algebraMap R D r)) ∧
        (∃ (δ : (D ⧸ Ideal.span {algebraMap R D π}) →+*
              L ⧸ Ideal.span {algebraMap R L π})
            (ε : (L ⧸ Ideal.span {(algebraMap R L π) ^ 2}) →+*
              L ⧸ Ideal.span {algebraMap R L π}),
          δ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) =
            (Ideal.Quotient.mk (Ideal.span {algebraMap R L π})).comp β.toRingHom ∧
          ε.comp (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})) =
            Ideal.Quotient.mk (Ideal.span {algebraMap R L π}) ∧
          δ.comp γ = ε.comp α) ∧
        ∀ p : PrimeSpectrum (D ⧸ Ideal.span {algebraMap R D π}),
          PrimeSpectrum.comap γ p ∈ smoothLocus (R ⧸ Ideal.span {π ^ 2}) B →
          IsSmoothAt R (PrimeSpectrum.comap
            (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) p).asIdeal := by
  have : IsNoetherianRing B := FiniteType.isNoetherianRing (R ⧸ Ideal.span {π ^ 2}) B
  exact Presentation.exists_principal_lifting_with_source_smoothLocus
    π hstableR hstableL
    (Presentation.ofFinitePresentation (R ⧸ Ideal.span {π ^ 2}) B) α hα

/-- The principal lifting construction, including relative smoothness of its
actual reduction map over `B/(π)`. It gives a finite presentation, smoothness
away from `π`, smoothness over the original base above the source smooth locus,
and relative smoothness of the original reduction map on that same locus. -/
theorem exists_principal_lifting_with_relative_smoothLocus
    {R : Type u} {L : Type v} [CommRing R] [CommRing L] [Algebra R L]
    [IsNoetherianRing R]
    (π : R) (hstableR : ∀ x : R, π ^ 2 * x = 0 → π * x = 0)
    (hstableL : ∀ x : L, (algebraMap R L π) ^ 2 * x = 0 →
      algebraMap R L π * x = 0)
    {B : Type w} [CommRing B] [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    [FinitePresentation (R ⧸ Ideal.span {π ^ 2}) B]
    (α : B →+* L ⧸ Ideal.span {(algebraMap R L π) ^ 2})
    (hα : ∀ r : R,
      α (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
        (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2}) (algebraMap R L r)) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      FinitePresentation R D ∧
      Smooth R (Localization.Away (algebraMap R D π)) ∧
      ∃ (β : D →ₐ[R] L) (γ : B →+* D ⧸ Ideal.span {algebraMap R D π}),
        (∀ r : R, γ (algebraMap (R ⧸ Ideal.span {π ^ 2}) B
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) r)) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R D π}) (algebraMap R D r)) ∧
        (∃ (δ : (D ⧸ Ideal.span {algebraMap R D π}) →+*
              L ⧸ Ideal.span {algebraMap R L π})
            (ε : (L ⧸ Ideal.span {(algebraMap R L π) ^ 2}) →+*
              L ⧸ Ideal.span {algebraMap R L π}),
          δ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) =
            (Ideal.Quotient.mk (Ideal.span {algebraMap R L π})).comp β.toRingHom ∧
          ε.comp (Ideal.Quotient.mk (Ideal.span {(algebraMap R L π) ^ 2})) =
            Ideal.Quotient.mk (Ideal.span {algebraMap R L π}) ∧
          δ.comp γ = ε.comp α) ∧
        (∀ p : PrimeSpectrum (D ⧸ Ideal.span {algebraMap R D π}),
          PrimeSpectrum.comap γ p ∈ smoothLocus (R ⧸ Ideal.span {π ^ 2}) B →
          IsSmoothAt R (PrimeSpectrum.comap
            (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) p).asIdeal) ∧
        let bπ := algebraMap (R ⧸ Ideal.span {π ^ 2}) B
          (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)
        let Bbar := B ⧸ Ideal.span {bπ}
        ∃ γbar : Bbar →+* D ⧸ Ideal.span {algebraMap R D π},
          γbar.comp (Ideal.Quotient.mk (Ideal.span {bπ})) = γ ∧
          let _ : Algebra Bbar (D ⧸ Ideal.span {algebraMap R D π}) :=
              RingHom.toAlgebra (R := Bbar) (S := D ⧸ Ideal.span {algebraMap R D π}) γbar
          ∀ p : PrimeSpectrum (D ⧸ Ideal.span {algebraMap R D π}),
            PrimeSpectrum.comap γ p ∈ smoothLocus (R ⧸ Ideal.span {π ^ 2}) B →
            IsSmoothAt Bbar (A := D ⧸ Ideal.span {algebraMap R D π}) p.asIdeal := by
  have : IsNoetherianRing B := FiniteType.isNoetherianRing (R ⧸ Ideal.span {π ^ 2}) B
  let P := Presentation.ofFinitePresentation (R ⧸ Ideal.span {π ^ 2}) B
  obtain ⟨D, hD, hRD, hfp, haway, β, ξ, γ, _hγgen, _hβgen, hcoeff,
    _hγpoly, _hαpoly, htriangle, s, E, hE, hcover, hsmooth, hrelative⟩ :=
    P.exists_principal_lifting π hstableR hstableL α hα
  let _ : CommRing D := hD
  let _ : Algebra R D := hRD
  refine ⟨D, hD, hRD, hfp, haway, β, γ, hcoeff, htriangle, ?_, hrelative⟩
  intro p hp
  obtain ⟨t, ht⟩ := (hcover (PrimeSpectrum.comap γ p)).mp hp
  let pD := PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {algebraMap R D π})) p
  have hπ : algebraMap R D π ∈ pD.asIdeal := by
    change Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
      (algebraMap R D π) ∈ p.asIdeal
    have hzero : Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
        (algebraMap R D π) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
    rw [hzero]
    exact p.asIdeal.zero_mem
  have htD : E t ∉ pD.asIdeal := by
    intro hmem
    apply ht
    change γ (algebraMap P.Ring B t.val) ∈ p.asIdeal
    rw [hE t]
    exact hmem
  exact hsmooth t pD hπ htD

end Algebra
