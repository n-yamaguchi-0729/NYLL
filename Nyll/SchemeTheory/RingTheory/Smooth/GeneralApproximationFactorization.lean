/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingExistence
public import Nyll.SchemeTheory.RingTheory.Smooth.RelativeQuotientSmoothFactorization

/-!
# Desingularization from a finitely presented principal approximation

An actual finitely presented factorization modulo a sufficiently high power
supplies the principal lifting algebra and its original smooth-locus data.
Relative residual correction produces an exact factorization of the original
map, smooth away from the parameter and above the quotient source's smooth
locus. The constructed quotient-source map retains its target triangle.

This is the pointwise form of Stacks, `lemma-desingularize-lifting-apply`.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace Algebra

/-- Lift an actual square-modulus factorization through a finitely presented
quotient algebra. Retain its source map, smooth locus, and target triangles. -/
theorem exists_principal_lift_of_quotient_factorization
    {R : Type u} {L : Type v} {A : Type w} {Cbar : Type z}
    [CommRing R] [CommRing L] [CommRing A] [CommRing Cbar]
    [Algebra R L] [Algebra R A] [Algebra R Cbar] [IsNoetherianRing R]
    (q : R) [Algebra (R ⧸ Ideal.span {q ^ 2}) Cbar]
    [IsScalarTower R (R ⧸ Ideal.span {q ^ 2}) Cbar]
    [FinitePresentation (R ⧸ Ideal.span {q ^ 2}) Cbar]
    (hstableR : ∀ x : R, q ^ 2 * x = 0 → q * x = 0)
    (hstableL : ∀ x : L, (algebraMap R L q) ^ 2 * x = 0 →
      algebraMap R L q * x = 0)
    (σ : (A ⧸ Ideal.span {(algebraMap R A q) ^ 2}) →ₐ[R] Cbar)
    (α : Cbar →ₐ[R] L ⧸ Ideal.span {(algebraMap R L q) ^ 2})
    (φ : A →ₐ[R] L)
    (hfactor : α.comp (σ.comp
        (Ideal.Quotient.mkₐ R (Ideal.span {(algebraMap R A q) ^ 2}))) =
      (Ideal.Quotient.mkₐ R (Ideal.span {(algebraMap R L q) ^ 2})).comp φ) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      FinitePresentation R D ∧ Smooth R (Localization.Away (algebraMap R D q)) ∧
      ∃ (β : D →ₐ[R] L) (ρ : A →ₐ[R] D ⧸ Ideal.span {algebraMap R D q})
        (γ : Cbar →ₐ[R] D ⧸ Ideal.span {algebraMap R D q})
        (δ : (D ⧸ Ideal.span {algebraMap R D q}) →+*
          L ⧸ Ideal.span {algebraMap R L q})
        (ε : (L ⧸ Ideal.span {(algebraMap R L q) ^ 2}) →+*
          L ⧸ Ideal.span {algebraMap R L q}),
        δ.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R D q})) =
          (Ideal.Quotient.mk (Ideal.span {algebraMap R L q})).comp β.toRingHom ∧
        ε.comp (Ideal.Quotient.mk (Ideal.span {(algebraMap R L q) ^ 2})) =
          Ideal.Quotient.mk (Ideal.span {algebraMap R L q}) ∧
        δ.comp γ.toRingHom = ε.comp α.toRingHom ∧
        δ.comp ρ.toRingHom =
          (Ideal.Quotient.mk (Ideal.span {algebraMap R L q})).comp φ.toRingHom ∧
        ∀ p : PrimeSpectrum (D ⧸ Ideal.span {algebraMap R D q}),
          PrimeSpectrum.comap γ.toRingHom p ∈
            smoothLocus (R ⧸ Ideal.span {q ^ 2}) Cbar →
          IsSmoothAt R (PrimeSpectrum.comap
            (Ideal.Quotient.mk (Ideal.span {algebraMap R D q})) p).asIdeal := by
  have hα (r : R) : α (algebraMap (R ⧸ Ideal.span {q ^ 2}) Cbar
        (Ideal.Quotient.mk (Ideal.span {q ^ 2}) r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap R L q) ^ 2}) (algebraMap R L r) := by
    change α (algebraMap (R ⧸ Ideal.span {q ^ 2}) Cbar
      (algebraMap R (R ⧸ Ideal.span {q ^ 2}) r)) = _
    rw [← IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {q ^ 2}) Cbar]
    exact α.commutes r
  obtain ⟨D, _, _, hfp, haway, β, γ, hγ, ⟨δ, ε, hδ, hε, htriangle⟩, hclosed⟩ :=
    exists_principal_lifting_with_source_smoothLocus q hstableR hstableL α.toRingHom hα
  let γₐ : Cbar →ₐ[R] D ⧸ Ideal.span {algebraMap R D q} :=
    { γ with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {q ^ 2}) Cbar]
        exact hγ r }
  let ρ := γₐ.comp (σ.comp
    (Ideal.Quotient.mkₐ R (Ideal.span {(algebraMap R A q) ^ 2})))
  refine ⟨D, inferInstance, inferInstance, hfp, haway,
    β, ρ, γₐ, δ, ε, hδ, hε, htriangle, ?_, hclosed⟩
  apply RingHom.ext
  intro x
  have htri := RingHom.congr_fun htriangle
    (σ (Ideal.Quotient.mk (Ideal.span {(algebraMap R A q) ^ 2}) x))
  have hfact := AlgHom.congr_fun hfactor x
  change α (σ (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ (φ x) at hfact
  change δ (γ (σ (Ideal.Quotient.mk _ x))) =
    ε (α (σ (Ideal.Quotient.mk _ x))) at htri
  change δ (γ (σ (Ideal.Quotient.mk _ x))) = Ideal.Quotient.mk _ (φ x)
  rw [htri, hfact]
  exact RingHom.congr_fun hε (φ x)

open MvPolynomial

/-- Choose the exponent before the actual finitely presented quotient
factorization. Construct an exact factorization, smooth away from the original
parameter, and retain pointwise smoothness above the original quotient source.
The map from that source into the corrected algebra modulo the parameter is
constructed through the principal lifting algebra. -/
theorem exists_uniform_power_desingularization_of_quotient_factorization
    {R L m n k : Type u}
    [CommRing R] [CommRing L] [Algebra R L] [IsLocalRing L]
    [IsNoetherianRing R] [IsNoetherianRing L]
    [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : algebraMap R L π ∈ IsLocalRing.maximalIdeal L) :
    ∃ N : ℕ, 0 < N ∧
      let q := π ^ (4 * N)
      let A := MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))
      ∀ (Cbar : Type u) [CommRing Cbar]
        [Algebra (R ⧸ Ideal.span {q ^ 2}) Cbar]
        [FinitePresentation (R ⧸ Ideal.span {q ^ 2}) Cbar],
        let _ : Algebra R Cbar :=
          ((algebraMap (R ⧸ Ideal.span {q ^ 2}) Cbar).comp
            (algebraMap R (R ⧸ Ideal.span {q ^ 2}))).toAlgebra
        ∀ (σ : (A ⧸ Ideal.span {(algebraMap R A q) ^ 2}) →ₐ[R] Cbar)
          (α : Cbar →ₐ[R] L ⧸ Ideal.span {(algebraMap R L q) ^ 2})
          (φ : A →ₐ[R] L),
          α.comp (σ.comp (Ideal.Quotient.mkₐ R
              (Ideal.span {(algebraMap R A q) ^ 2}))) =
            (Ideal.Quotient.mkₐ R (Ideal.span {(algebraMap R L q) ^ 2})).comp φ →
          ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
            FinitePresentation R E ∧ Smooth R (Localization.Away (algebraMap R E π)) ∧
            ∃ (a : A →ₐ[R] E) (c : E →ₐ[R] L), c.comp a = φ ∧
              ∃ (Γ : Cbar →ₐ[R] E ⧸ Ideal.span {algebraMap R E q})
                (δE : (E ⧸ Ideal.span {algebraMap R E q}) →+*
                  L ⧸ Ideal.span {algebraMap R L q})
                (ε : (L ⧸ Ideal.span {(algebraMap R L q) ^ 2}) →+*
                  L ⧸ Ideal.span {algebraMap R L q}),
                δE.comp (Ideal.Quotient.mk (Ideal.span {algebraMap R E q})) =
                  (Ideal.Quotient.mk (Ideal.span {algebraMap R L q})).comp c.toRingHom ∧
                ε.comp (Ideal.Quotient.mk (Ideal.span {(algebraMap R L q) ^ 2})) =
                  Ideal.Quotient.mk (Ideal.span {algebraMap R L q}) ∧
                δE.comp Γ.toRingHom = ε.comp α.toRingHom ∧
                ∀ p : PrimeSpectrum (E ⧸ Ideal.span {algebraMap R E q}),
                  PrimeSpectrum.comap Γ.toRingHom p ∈
                    smoothLocus (R ⧸ Ideal.span {q ^ 2}) Cbar →
                  IsSmoothAt R (PrimeSpectrum.comap
                    (Ideal.Quotient.mk (Ideal.span {algebraMap R E q})) p).asIdeal := by
  classical
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp
    ((eventually_annihilator_pow_stable π).and
      (eventually_annihilator_pow_stable (algebraMap R L π)))
  let e := b + 1
  have he : 0 < e := Nat.zero_lt_succ b
  have hminorE : C (π ^ e) ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det) := by
    rw [map_pow, show e = b + 1 from rfl, pow_succ]
    exact (_ : Ideal (MvPolynomial n R)).mul_mem_left _ hminor
  have hrelationsE (j : k) : C (π ^ e) * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2 := by
    rw [map_pow, show e = b + 1 from rfl, pow_succ (C π) b, mul_assoc]
    exact (_ : Ideal (MvPolynomial n R)).mul_mem_left _ (hrelations j)
  have hπE : algebraMap R L (π ^ e) ∈ IsLocalRing.maximalIdeal L := by
    rw [map_pow, show e = b + 1 from rfl, pow_succ]
    exact (IsLocalRing.maximalIdeal L).mul_mem_left _ hπ
  obtain ⟨M, hM, hcorrect⟩ := exists_uniform_power_relative_residual_factorization
    (L := L) (π ^ e) f h hminorE hrelationsE hπE
  let N := e * M
  refine ⟨N, Nat.mul_pos he hM, ?_⟩
  intro q A Cbar _ _ _ hRCbar σ α φ hfactor
  have : IsScalarTower R (R ⧸ Ideal.span {q ^ 2}) Cbar :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hbN : b ≤ 4 * N := by
    have heN : e ≤ N := Nat.le_mul_of_pos_right e hM
    have hN4 : N ≤ 4 * N := Nat.le_mul_of_pos_left N (by decide)
    exact (Nat.le_succ b).trans (heN.trans hN4)
  obtain ⟨hstableR, hstableL⟩ := hb (4 * N) hbN
  have hstableL' : ∀ x : L, (algebraMap R L q) ^ 2 * x = 0 →
      algebraMap R L q * x = 0 := by
    simpa only [q, map_pow] using hstableL
  obtain ⟨D, _, _, hD, haway, β, ρ, γ, δ, ε, hδ, hε, htriangle, hρ, hclosed⟩ :=
    exists_principal_lift_of_quotient_factorization q hstableR hstableL' σ α φ hfactor
  have : FinitePresentation R D := hD
  let _ : Algebra D L := β.toRingHom.toAlgebra
  have : IsScalarTower R D L := IsScalarTower.of_algHom β
  have hq : q = ((π ^ e) ^ M) ^ 4 := by
    dsimp only [q, N]
    simp only [← pow_mul]
    congr 1
    ac_rfl
  let K : Ideal D := Ideal.span {(algebraMap R D ((π ^ e) ^ M)) ^ 4}
  let J : Ideal L := K.map (algebraMap D L)
  have hK : Ideal.span {algebraMap R D q} = K := by
    dsimp only [K]
    rw [hq, map_pow]
  have hJ : J = Ideal.span {algebraMap R L q} := by
    dsimp only [J, K]
    rw [Ideal.map_span, Set.image_singleton, map_pow,
      ← IsScalarTower.algebraMap_apply R D L, ← map_pow, ← hq]
  let eD := Ideal.quotientEquivAlgOfEq R hK
  let eL := Ideal.quotientEquivAlgOfEq R hJ.symm
  let δ₀ : D ⧸ K →+* L ⧸ J :=
    Ideal.quotientMap J (algebraMap D L) Ideal.le_comap_map
  have hcompare (x : D ⧸ Ideal.span {algebraMap R D q}) :
      δ₀ (eD x) = eL (δ x) := by
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientMap_mk]
    have hd := RingHom.congr_fun hδ d
    change δ (Ideal.Quotient.mk _ d) = Ideal.Quotient.mk _ (β d) at hd
    rw [hd, Ideal.quotientEquivAlgOfEq_mk]
    rfl
  let ρ' := eD.toAlgHom.comp ρ
  have hcompat : (Ideal.Quotient.mkₐ R J).comp φ =
      ((Ideal.quotientMapₐ J (Algebra.ofId D L)
        Ideal.le_comap_map).restrictScalars R).comp ρ' := by
    apply AlgHom.ext
    intro x
    change Ideal.Quotient.mk J (φ x) = δ₀ (eD (ρ x))
    rw [hcompare]
    have hx := RingHom.congr_fun hρ x
    change δ (ρ x) = Ideal.Quotient.mk _ (φ x) at hx
    rw [hx, Ideal.quotientEquivAlgOfEq_mk]
  obtain ⟨F, _, _, _, _, _hF, Jres, _hJfg, _hJ, _hrel,
      _hfpD, hfpR, _hlocal, habsolute, a, c, hca⟩ := hcorrect D ρ' φ hcompat
  let E := F ⧸ Jres
  have : FinitePresentation R E := hfpR
  let cR : E →ₐ[R] L := c.restrictScalars R
  let u : D →ₐ[R] E := (Algebra.ofId D E).restrictScalars R
  have huq : Ideal.span {algebraMap R D q} ≤
      (Ideal.span {algebraMap R E q}).comap u.toRingHom := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change u (algebraMap R D q) ∈ Ideal.span {algebraMap R E q}
    rw [u.commutes]
    exact Ideal.subset_span (Set.mem_singleton _)
  let τ : (D ⧸ Ideal.span {algebraMap R D q}) →ₐ[R]
      E ⧸ Ideal.span {algebraMap R E q} :=
    Ideal.quotientMapₐ (Ideal.span {algebraMap R E q}) u huq
  let Γ := τ.comp γ
  have hcq : Ideal.span {algebraMap R E q} ≤
      (Ideal.span {algebraMap R L q}).comap cR.toRingHom := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change cR (algebraMap R E q) ∈ Ideal.span {algebraMap R L q}
    rw [cR.commutes]
    exact Ideal.subset_span (Set.mem_singleton _)
  let δE : (E ⧸ Ideal.span {algebraMap R E q}) →+*
      L ⧸ Ideal.span {algebraMap R L q} :=
    Ideal.quotientMap (Ideal.span {algebraMap R L q}) cR.toRingHom hcq
  have hδEτ : δE.comp τ.toRingHom = δ := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro d
    change Ideal.Quotient.mk _ (cR (algebraMap D E d)) = δ (Ideal.Quotient.mk _ d)
    have hcd : cR (algebraMap D E d) = β d := c.commutes d
    rw [hcd]
    exact (RingHom.congr_fun hδ d).symm
  have hΓ : δE.comp Γ.toRingHom = ε.comp α.toRingHom := by
    apply RingHom.ext
    intro x
    change δE (τ (γ x)) = ε (α x)
    rw [show δE (τ (γ x)) = δ (γ x) from RingHom.congr_fun hδEτ (γ x)]
    exact RingHom.congr_fun htriangle x
  have hawayE : Smooth R (Localization.Away (algebraMap R E π)) := by
    apply (basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := E)).mp
    intro p hp
    let pD := PrimeSpectrum.comap (algebraMap D E) p
    have hqD : algebraMap R D q ∉ pD.asIdeal := by
      change algebraMap D E (algebraMap R D q) ∉ p.asIdeal
      rw [← IsScalarTower.algebraMap_apply R D E, show q = π ^ (4 * N) from rfl,
        map_pow]
      intro hh
      exact hp (p.isPrime.mem_of_pow_mem (4 * N) hh)
    have hsmD : IsSmoothAt R pD.asIdeal :=
      (basicOpen_subset_smoothLocus_iff_smooth (R := R) (A := D)).mpr haway hqD
    exact habsolute p.asIdeal hsmD
  refine ⟨E, inferInstance, inferInstance, hfpR, hawayE,
    a, cR, hca, Γ, δE, ε, Ideal.quotientMap_comp_mk hcq, hε, hΓ, ?_⟩
  intro p hp
  let pD := PrimeSpectrum.comap τ.toRingHom p
  have hsource : PrimeSpectrum.comap γ.toRingHom pD ∈
      smoothLocus (R ⧸ Ideal.span {q ^ 2}) Cbar := hp
  have hsmD := hclosed pD hsource
  let pE := PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {algebraMap R E q})) p
  have hprime : pE.asIdeal.comap (algebraMap D E) =
      (PrimeSpectrum.comap
        (Ideal.Quotient.mk (Ideal.span {algebraMap R D q})) pD).asIdeal := by
    ext d
    change (Ideal.Quotient.mk _ (algebraMap D E d) ∈ p.asIdeal) ↔
      τ (Ideal.Quotient.mk _ d) ∈ p.asIdeal
    rfl
  apply habsolute pE.asIdeal
  have hprime' : PrimeSpectrum.comap (algebraMap D E) pE =
      PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {algebraMap R D q})) pD :=
    PrimeSpectrum.ext hprime
  exact (congrArg (fun z : PrimeSpectrum D => IsSmoothAt R z.asIdeal) hprime').mpr hsmD

end Algebra
