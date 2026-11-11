/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ArtinSchreier.WittAdditiveHilbert90
public import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousCharacters
public import Mathlib.Algebra.CharP.IntermediateField
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters

/-!
# Every continuous prime-power character is an Artin–Schreier–Witt character

Finite Galois factorization and the concrete Witt additive Hilbert 90
construction realize every continuous cyclic character by an actual Witt
root. Coefficientwise Galois descent supplies its equation over the base
field; the character comparison is proved from its root differences.
-/

@[expose] public section

noncomputable section

namespace ArtinSchreierWittTheory

variable (p m : ℕ) [Fact p.Prime]

/-- Prime-power constants are preserved by coefficient homomorphisms. -/
theorem constantCast_natural {L M : Type*} [CommRing L] [CommRing M] [CharP L p] [CharP M p]
    (f : L →+* M) (z : ZMod (p ^ m)) :
    TruncatedWittVector.map f (constantCast p m L z) = constantCast p m M z := by
  change TruncatedWittVector.map f
    (TruncatedWittVector.map (ZMod.castHom (dvd_refl p) L)
      ((TruncatedWittVector.zmodEquivTrunc p m) z)) =
      TruncatedWittVector.map (ZMod.castHom (dvd_refl p) M)
        ((TruncatedWittVector.zmodEquivTrunc p m) z)
  apply TruncatedWittVector.ext
  intro i
  simp only [TruncatedWittVector.map_coeff, ZMod.castHom_apply, ZMod.cast_eq_val, map_natCast]

variable {K Ω : Type*} [Field K] [Field Ω] [CharP Ω p] [Algebra K Ω] [IsGalois K Ω]

omit [CharP Ω p] in
/-- A fixed finite Witt vector descends coefficientwise to the base field. -/
theorem exists_base_of_fixed (x : TruncatedWittVector p m Ω)
    (hx : ∀ σ : Gal(Ω/K), TruncatedWittVector.map σ.toRingHom x = x) :
    ∃ a : TruncatedWittVector p m K, TruncatedWittVector.map (algebraMap K Ω) a = x := by
  have hcoeff (i : Fin m) : ∀ σ : Gal(Ω/K), σ (x.coeff i) = x.coeff i := by
    intro σ
    have h := congrArg (TruncatedWittVector.coeff i) (hx σ)
    rw [TruncatedWittVector.map_coeff] at h
    change σ (x.coeff i) = x.coeff i at h
    exact h
  choose a ha using fun i : Fin m =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (x.coeff i)).mpr (hcoeff i)
  refine ⟨TruncatedWittVector.mk p a, ?_⟩
  apply TruncatedWittVector.ext
  intro i
  rw [TruncatedWittVector.map_coeff, TruncatedWittVector.coeff_mk]
  exact ha i

/-- Every continuous cyclic `p ^ m`-character is the character of an actual
Artin–Schreier–Witt equation over the original base field. -/
theorem exists_rootCharacter_eq (χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod (p ^ m))) :
    ∃ (a : TruncatedWittVector p m K) (β : TruncatedWittVector p m Ω)
      (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
        TruncatedWittVector.map (algebraMap K Ω) a), rootCharacter p m Ω a β hβ = χ := by
  obtain ⟨E, χE, hχ⟩ := KummerTheory.continuousCharacter_factors_through_finiteGalois χ
  let c : Gal(E/K) → TruncatedWittVector p m E := fun σ =>
    constantCast p m E (χE σ).toAdd
  have hc : ∀ σ τ : Gal(E/K), c (σ * τ) =
      TruncatedWittVector.map σ.toRingHom (c τ) + c σ := by
    intro σ τ
    change constantCast p m E (χE (σ * τ)).toAdd =
      TruncatedWittVector.map σ.toRingHom (constantCast p m E (χE τ).toAdd) +
        constantCast p m E (χE σ).toAdd
    rw [map_constantCast, map_mul]
    change constantCast p m E ((χE σ).toAdd + (χE τ).toAdd) = _
    rw [map_add, add_comm]
  obtain ⟨βE, hβE⟩ := additiveHilbert90_finite p m c hc
  let β : TruncatedWittVector p m Ω := TruncatedWittVector.map (algebraMap E Ω) βE
  have hdiff (σ : Gal(Ω/K)) : TruncatedWittVector.map σ.toRingHom β - β =
      constantCast p m Ω (χ σ).toAdd := by
    let r : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
    have hact : TruncatedWittVector.map σ.toRingHom β =
        TruncatedWittVector.map (algebraMap E Ω) (TruncatedWittVector.map (r σ).toRingHom βE) := by
      apply TruncatedWittVector.ext
      intro i
      simp only [β, TruncatedWittVector.map_coeff]
      exact (AlgEquiv.restrictNormalHom_apply E.toIntermediateField σ (βE.coeff i)).symm
    have hχσ : χE (r σ) = χ σ := congrArg
      (fun f : Gal(Ω/K) →* Multiplicative (ZMod (p ^ m)) => f σ) hχ
    calc
      TruncatedWittVector.map σ.toRingHom β - β =
          TruncatedWittVector.map (algebraMap E Ω)
            (TruncatedWittVector.map (r σ).toRingHom βE - βE) := by
        rw [map_sub, hact]
      _ = TruncatedWittVector.map (algebraMap E Ω) (c (r σ)) := by rw [hβE]
      _ = constantCast p m Ω (χ σ).toAdd := by
        change TruncatedWittVector.map (algebraMap E Ω)
          (constantCast p m E (χE (r σ)).toAdd) = _
        rw [constantCast_natural, hχσ]
  have hfixed : ∀ σ : Gal(Ω/K), TruncatedWittVector.map σ.toRingHom
      (TruncatedWittVector.map (frobenius Ω p) β - β) =
        TruncatedWittVector.map (frobenius Ω p) β - β := by
    intro σ
    have hshift : TruncatedWittVector.map σ.toRingHom β =
        constantCast p m Ω (χ σ).toAdd + β := (sub_eq_iff_eq_add).mp (hdiff σ)
    rw [map_sub, ← TruncatedWittVector.map_frobenius, hshift, map_add, constantCast_natural]
    ring
  obtain ⟨a, ha⟩ := exists_base_of_fixed p m _ hfixed
  refine ⟨a, β, ha.symm, ?_⟩
  apply ContinuousMonoidHom.ext
  intro σ
  change (rootCharacter p m Ω a β ha.symm σ).toAdd = (χ σ).toAdd
  apply constantCast_injective p m Ω
  exact (rootCharacter_cast p m Ω a β ha.symm σ).trans (hdiff σ)

end ArtinSchreierWittTheory
