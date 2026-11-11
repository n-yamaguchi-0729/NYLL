/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacterSurjectivity
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology
public import Nyll.GaloisCohomology.ArtinSchreier.WittCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation

/-!
# Additivity and semilinear naturality of actual Witt root characters

Subtracting roots subtracts their characters. Transporting a root by an
actual semilinear field automorphism gives the corresponding conjugated
Galois character. Prime-power Witt constants are fixed by the coefficient
transport, so no cyclotomic scalar occurs.
-/

@[expose] public section

noncomputable section

namespace ArtinSchreierWittTheory

variable (p m : ℕ) [Fact p.Prime]
  {K Ω : Type*} [Field K] [Field Ω] [CharP Ω p] [Algebra K Ω]

/-- The difference of two original roots solves the difference equation. -/
theorem wittRoot_sub (a b : TruncatedWittVector p m K)
    (β γ : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a)
    (hγ : TruncatedWittVector.map (frobenius Ω p) γ - γ =
      TruncatedWittVector.map (algebraMap K Ω) b) :
    TruncatedWittVector.map (frobenius Ω p) (β - γ) - (β - γ) =
      TruncatedWittVector.map (algebraMap K Ω) (a - b) := by
  rw [map_sub, map_sub]
  linear_combination hβ - hγ

/-- The original coefficient and root are transported by the specified
semilinear field automorphism. -/
theorem wittRoot_semilinear (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (a : TruncatedWittVector p m K) (β : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a) :
    TruncatedWittVector.map (frobenius Ω p) (TruncatedWittVector.map e.toRingHom β) -
      TruncatedWittVector.map e.toRingHom β =
        TruncatedWittVector.map (algebraMap K Ω) (TruncatedWittVector.map τ.toRingHom a) := by
  rw [TruncatedWittVector.map_frobenius, ← map_sub, hβ]
  apply TruncatedWittVector.ext
  intro i
  simp only [TruncatedWittVector.map_coeff]
  exact he (a.coeff i)

variable [Algebra.IsIntegral K Ω]

/-- Subtraction of actual Witt roots becomes division of their continuous
cyclic characters. -/
theorem rootCharacter_sub (a b : TruncatedWittVector p m K)
    (β γ : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a)
    (hγ : TruncatedWittVector.map (frobenius Ω p) γ - γ =
      TruncatedWittVector.map (algebraMap K Ω) b) :
    rootCharacter p m Ω (a - b) (β - γ) (wittRoot_sub p m a b β γ hβ hγ) =
      rootCharacter p m Ω a β hβ / rootCharacter p m Ω b γ hγ := by
  apply ContinuousMonoidHom.ext
  intro σ
  change (rootCharacter p m Ω (a - b) (β - γ) (wittRoot_sub p m a b β γ hβ hγ) σ).toAdd =
    (rootCharacter p m Ω a β hβ σ).toAdd - (rootCharacter p m Ω b γ hγ σ).toAdd
  apply constantCast_injective p m Ω
  rw [map_sub, rootCharacter_cast, rootCharacter_cast, rootCharacter_cast, map_sub]
  ring

/-- Transport by an actual semilinear automorphism agrees with the original
Galois conjugation, with trivial action on the cyclic Witt constants. -/
theorem rootCharacter_semilinear (τ : K ≃+* K) (e : Ω ≃+* Ω)
    (he : ∀ k : K, e (algebraMap K Ω k) = algebraMap K Ω (τ k))
    (a : TruncatedWittVector p m K) (β : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a) (σ : Gal(Ω/K)) :
    rootCharacter p m Ω (TruncatedWittVector.map τ.toRingHom a)
      (TruncatedWittVector.map e.toRingHom β) (wittRoot_semilinear p m τ e he a β hβ)
      (KummerTheory.semilinearGaloisConjugate τ e he σ) =
        rootCharacter p m Ω a β hβ σ := by
  change (rootCharacter p m Ω (TruncatedWittVector.map τ.toRingHom a)
      (TruncatedWittVector.map e.toRingHom β) (wittRoot_semilinear p m τ e he a β hβ)
      (KummerTheory.semilinearGaloisConjugate τ e he σ)).toAdd =
    (rootCharacter p m Ω a β hβ σ).toAdd
  apply constantCast_injective p m Ω
  rw [rootCharacter_cast]
  have hconj : TruncatedWittVector.map
      (KummerTheory.semilinearGaloisConjugate τ e he σ).toRingHom
      (TruncatedWittVector.map e.toRingHom β) =
        TruncatedWittVector.map e.toRingHom (TruncatedWittVector.map σ.toRingHom β) := by
    apply TruncatedWittVector.ext
    intro i
    simp only [TruncatedWittVector.map_coeff]
    change e (σ (e.symm (e (β.coeff i)))) = e (σ (β.coeff i))
    rw [e.symm_apply_apply]
  rw [hconj, ← map_sub, ← rootCharacter_cast p m Ω a β hβ σ, constantCast_natural]

end ArtinSchreierWittTheory
