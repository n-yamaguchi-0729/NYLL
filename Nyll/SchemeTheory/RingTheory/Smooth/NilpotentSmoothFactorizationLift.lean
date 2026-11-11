/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.FiniteIdealPolynomialCorrection
public import Nyll.SchemeTheory.RingTheory.Smooth.StandardSmoothNilpotentPresentation
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Lifting a finite smooth factorization modulo a nilpotent ideal

Starting with the actual standard smooth factorization after a nilpotent
base quotient, lift the smooth algebra and its map to the target.
Polynomial corrections give exact images for the original finite family
of generators. Quotienting by the images of their original relations
then produces an actual factorization through a finitely generated
quotient of a smooth algebra.

This is the finite-stage lifting assertion used in Stacks Project,
Lemma 16.5.1: https://stacks.math.columbia.edu/tag/07CK
No factorization through the original unquotiented smooth algebra is
assumed.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w z

namespace Algebra

private theorem presentation_quotient_factorization
    {R A D L : Type*} [CommRing R] [CommRing A] [CommRing D] [CommRing L]
    [Algebra R A] [Algebra R D] [Algebra R L]
    {ι τ : Type*} [Finite τ] (P : Presentation R A ι τ)
    (K : Ideal D) (φ : A →ₐ[R] L) (β : D →ₐ[R] L)
    (γ : A →ₐ[R] D ⧸ K) (x : ι → D)
    (hβ : ∀ i, β (x i) = φ (P.val i))
    (hγ : ∀ i, Ideal.Quotient.mk K (x i) = γ (P.val i)) :
    ∃ J : Ideal D, J.FG ∧ J ≤ K ∧
      ∃ (α : A →ₐ[R] D ⧸ J) (β' : D ⧸ J →ₐ[R] L),
        β'.comp α = φ := by
  classical
  let d : P.Ring →ₐ[R] D := MvPolynomial.aeval x
  let J : Ideal D := Ideal.span (Set.range fun j => d (P.relation j))
  have hJfg : J.FG := by
    exact ⟨(Set.finite_range (fun j => d (P.relation j))).toFinset,
      by rw [Set.Finite.coe_toFinset]⟩
  have hβd : β.comp d = φ.comp (MvPolynomial.aeval P.val) := by
    ext i
    change β (MvPolynomial.aeval x (MvPolynomial.X i)) =
      φ (MvPolynomial.aeval P.val (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact hβ i
  have hγd : (Ideal.Quotient.mkₐ R K).comp d =
      γ.comp (MvPolynomial.aeval P.val) := by
    ext i
    change Ideal.Quotient.mk K (MvPolynomial.aeval x (MvPolynomial.X i)) =
      γ (MvPolynomial.aeval P.val (MvPolynomial.X i))
    rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact hγ i
  have hJK : J ≤ K := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := AlgHom.congr_fun hγd (P.relation j)
    change Ideal.Quotient.mk K (d (P.relation j)) =
      γ (MvPolynomial.aeval P.val (P.relation j)) at h
    rw [P.aeval_val_relation, map_zero] at h
    exact h
  have hJβ : J ≤ RingHom.ker β.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have h := AlgHom.congr_fun hβd (P.relation j)
    change β (d (P.relation j)) =
      φ (MvPolynomial.aeval P.val (P.relation j)) at h
    rw [P.aeval_val_relation, map_zero] at h
    exact h
  let qd : P.Ring →ₐ[R] D ⧸ J := (Ideal.Quotient.mkₐ R J).comp d
  have hker : RingHom.ker (MvPolynomial.aeval P.val).toRingHom ≤
      RingHom.ker qd.toRingHom := by
    change RingHom.ker (MvPolynomial.aeval P.val) ≤ RingHom.ker qd
    rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  let α : A →ₐ[R] D ⧸ J :=
    AlgHom.liftOfSurjective (MvPolynomial.aeval P.val) P.aeval_val_surjective qd hker
  let β' : D ⧸ J →ₐ[R] L := Ideal.Quotient.liftₐ J β hJβ
  refine ⟨J, hJfg, hJK, α, β', ?_⟩
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := P.aeval_val_surjective a
  change β' (α (MvPolynomial.aeval P.val p)) =
    φ (MvPolynomial.aeval P.val p)
  rw [AlgHom.liftOfSurjective_apply]
  exact AlgHom.congr_fun hβd p

/-- An actual standard smooth factorization after a nilpotent base
quotient lifts to a factorization through `B/J`, where `B` is smooth and
`J` is finitely generated and contained in `I B`. -/
theorem exists_smooth_quotient_factorization_of_nilpotent
    {R : Type u} {A : Type v} {L : Type w} {C₀ : Type z}
    [CommRing R] [CommRing A] [CommRing L] [CommRing C₀]
    [Algebra R A] [Algebra R L] [Algebra R C₀]
    [FinitePresentation R A] (I : Ideal R) (hI : IsNilpotent I)
    [Algebra (R ⧸ I) C₀] [IsScalarTower R (R ⧸ I) C₀]
    [IsStandardSmooth (R ⧸ I) C₀]
    (φ : A →ₐ[R] L) (α₀ : A →ₐ[R] C₀)
    (β₀ : C₀ →ₐ[R] L ⧸ I.map (algebraMap R L))
    (hfac : β₀.comp α₀ =
      (Ideal.Quotient.mkₐ R (I.map (algebraMap R L))).comp φ) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ J : Ideal B, J.FG ∧ J ≤ I.map (algebraMap R B) ∧
        ∃ (α : A →ₐ[R] B ⧸ J) (β : B ⧸ J →ₐ[R] L), β.comp α = φ := by
  classical
  let IL := I.map (algebraMap R L)
  let qL : L →ₐ[R] L ⧸ IL := Ideal.Quotient.mkₐ R IL
  obtain ⟨C, _, _, hC, ⟨e⟩⟩ :=
    IsStandardSmooth.exists_lift_of_surjective
      (R := R ⧸ I) (S := C₀) R Ideal.Quotient.mk_surjective
  have : IsStandardSmooth R C := hC
  let IC := I.map (algebraMap R C)
  let eC : (C ⧸ IC) ≃ₐ[R] C₀ :=
    ((TensorProduct.quotIdealMapEquivQuotTensor C I).trans e).restrictScalars R
  let gC : C →ₐ[R] C₀ := eC.toAlgHom.comp (Ideal.Quotient.mkₐ R IC)
  have hgC : Function.Surjective gC :=
    eC.surjective.comp Ideal.Quotient.mk_surjective
  have hIL : IsNilpotent IL := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    change I.map (algebraMap R L) ^ n = 0
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
    exact Ideal.zero_eq_bot.symm
  obtain ⟨ψ, hψ⟩ := FormallySmooth.exists_lift IL hIL (β₀.comp gC)
  obtain ⟨n, m, ⟨P⟩⟩ := Presentation.exists_presentation_fin R A
  choose c hc using fun i : Fin n => hgC (α₀ (P.val i))
  have hx : ∀ i : Fin n, φ (P.val i) - ψ (c i) ∈ IL := by
    intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qL (φ (P.val i) - ψ (c i)) = 0
    rw [map_sub]
    have ha := AlgHom.congr_fun hfac (P.val i)
    have hb := AlgHom.congr_fun hψ (c i)
    change β₀ (α₀ (P.val i)) = qL (φ (P.val i)) at ha
    change qL (ψ (c i)) = β₀ (gC (c i)) at hb
    rw [← ha, hb, hc, sub_self]
  obtain ⟨σ, _, y, p, hp⟩ := I.exists_finite_polynomial_corrections
    (fun i : Fin n => φ (P.val i) - ψ (c i)) hx
  let D := MvPolynomial σ C
  let ID := I.map (algebraMap R D)
  let qD : D →ₐ[R] D ⧸ ID := Ideal.Quotient.mkₐ R ID
  let mp : MvPolynomial σ R →ₐ[R] D :=
    MvPolynomial.mapAlgHom (Algebra.ofId R C)
  let βD : D →ₐ[R] L := MvPolynomial.aevalTower ψ y
  have hβmp : βD.comp mp = MvPolynomial.aeval y := by
    ext j
    change MvPolynomial.aevalTower ψ y
      (MvPolynomial.map (algebraMap R C) (MvPolynomial.X j)) =
        MvPolynomial.aeval y (MvPolynomial.X j)
    rw [MvPolynomial.map_X, MvPolynomial.aevalTower_X, MvPolynomial.aeval_X]
  have hβC (c' : C) : βD (MvPolynomial.C c') = ψ c' :=
    MvPolynomial.aevalTower_C ψ y c'
  have hpmem (i : Fin n) : mp (p i) ∈ ID := by
    have hle : I.map (algebraMap R (MvPolynomial σ R)) ≤
        ID.comap mp.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change mp (algebraMap R (MvPolynomial σ R) r) ∈ ID
      rw [mp.commutes]
      exact Ideal.mem_map_of_mem (algebraMap R D) hr
    exact hle (hp i).1
  let qC : C →ₐ[R] D ⧸ ID :=
    qD.comp (IsScalarTower.toAlgHom R C D)
  have hIC : IC ≤ RingHom.ker qC.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change qC (algebraMap R C r) = 0
    rw [qC.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (algebraMap R D) hr)
  let γ : C₀ →ₐ[R] D ⧸ ID :=
    (Ideal.Quotient.liftₐ IC qC hIC).comp eC.symm.toAlgHom
  have hγ (c' : C) : γ (gC c') = qC c' := by
    change (Ideal.Quotient.liftₐ IC qC hIC)
      (eC.symm (eC (Ideal.Quotient.mk IC c'))) = qC c'
    rw [eC.symm_apply_apply]
    rfl
  let x : Fin n → D := fun i => MvPolynomial.C (c i) + mp (p i)
  have hβx (i : Fin n) : βD (x i) = φ (P.val i) := by
    change βD (MvPolynomial.C (c i) + mp (p i)) = φ (P.val i)
    rw [map_add, hβC,
      show βD (mp (p i)) = MvPolynomial.aeval y (p i) from
        AlgHom.congr_fun hβmp (p i), (hp i).2]
    rw [← add_sub_assoc, add_sub_cancel_left]
  have hγx (i : Fin n) : Ideal.Quotient.mk ID (x i) =
      (γ.comp α₀) (P.val i) := by
    change qD (MvPolynomial.C (c i) + mp (p i)) = γ (α₀ (P.val i))
    rw [map_add, show qD (mp (p i)) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (hpmem i), add_zero]
    change qC (c i) = γ (α₀ (P.val i))
    rw [← hγ, hc]
  obtain ⟨J, hJfg, hJI, α, β, hαβ⟩ :=
    presentation_quotient_factorization P ID φ βD (γ.comp α₀) x hβx hγx
  have : Smooth R D := Smooth.comp R C D
  exact ⟨D, inferInstance, inferInstance, inferInstance, J, hJfg, hJI, α, β, hαβ⟩

end Algebra
