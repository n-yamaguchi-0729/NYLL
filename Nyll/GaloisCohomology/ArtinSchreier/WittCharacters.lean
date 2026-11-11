/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ArtinSchreier.RootCharacter
public import Mathlib.RingTheory.WittVector.Compare
public import Mathlib.Tactic.LinearCombination
public import Nyll.GaloisCohomology.Topology.AlgebraicGaloisOrbits

/-!
# Artin–Schreier–Witt root characters

The Frobenius-fixed vectors of length `m` over a field of characteristic `p`
are exactly the embedded ring `ZMod (p ^ m)`. Differences of Galois translates
of an Artin–Schreier–Witt root therefore define actual continuous cyclic
characters, with kernel exactly the stabilizer of the root.
-/

@[expose] public section

noncomputable section

namespace TruncatedWittVector

variable {p n : ℕ} [Fact p.Prime]
  {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The coefficientwise ring homomorphism on finite Witt vectors. -/
def map (f : R →+* S) : TruncatedWittVector p n R →+* TruncatedWittVector p n S :=
  RingHom.liftOfRightInverse (WittVector.truncate n) out truncateFun_out
    ⟨(WittVector.truncate n).comp (WittVector.map f), by
      intro x hx
      rw [WittVector.mem_ker_truncate] at hx
      change WittVector.truncate n (WittVector.map f x) = 0
      apply TruncatedWittVector.ext
      intro i
      rw [WittVector.coeff_truncate, WittVector.map_coeff, hx i i.is_lt,
        map_zero, coeff_zero]⟩

@[simp]
theorem map_wittVector_truncate (f : R →+* S) (x : WittVector p R) :
    map f (WittVector.truncate n x) = WittVector.truncate n (WittVector.map f x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ _

@[simp]
theorem map_coeff (f : R →+* S) (x : TruncatedWittVector p n R) (i : Fin n) :
    (map f x).coeff i = f (x.coeff i) := by
  obtain ⟨y, rfl⟩ := WittVector.truncate_surjective p n R x
  rw [map_wittVector_truncate, WittVector.coeff_truncate, WittVector.map_coeff,
    WittVector.coeff_truncate]

theorem map_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (map f : TruncatedWittVector p n R → TruncatedWittVector p n S) := by
  intro x y h
  apply TruncatedWittVector.ext
  intro i
  apply hf
  exact (map_coeff f x i).symm.trans
    ((congrArg (TruncatedWittVector.coeff i) h).trans (map_coeff f y i))

theorem map_map (g : S →+* T) (f : R →+* S) (x : TruncatedWittVector p n R) :
    map g (map f x) = map (g.comp f) x := by
  apply TruncatedWittVector.ext
  intro i
  rw [map_coeff, map_coeff, map_coeff, RingHom.comp_apply]

theorem map_frobenius [CharP R p] [CharP S p] (f : R →+* S)
    (x : TruncatedWittVector p n R) :
    map (frobenius S p) (map f x) = map f (map (frobenius R p) x) := by
  apply TruncatedWittVector.ext
  intro i
  simp only [map_coeff, frobenius_def, map_pow]

end TruncatedWittVector

namespace ArtinSchreierWittTheory

open TruncatedWittVector

section Constants

variable (p m : ℕ) [Fact p.Prime] (Ω : Type*) [CommRing Ω] [CharP Ω p]

/-- The canonical copy of `ZMod (p ^ m)` in the length-`m` Witt ring. -/
def constantCast : ZMod (p ^ m) →+* TruncatedWittVector p m Ω :=
  (TruncatedWittVector.map (ZMod.castHom (dvd_refl p) Ω)).comp
    (zmodEquivTrunc p m).toRingHom

theorem constantCast_injective [Nontrivial Ω] : Function.Injective (constantCast p m Ω) :=
  (TruncatedWittVector.map_injective _ (ZMod.castHom (dvd_refl p) Ω).injective).comp
    (zmodEquivTrunc p m).injective

end Constants

variable (p m : ℕ) [Fact p.Prime] (Ω : Type*) [Field Ω] [CharP Ω p]

/-- Frobenius-fixed Witt vectors are precisely the prime-power constants. -/
theorem exists_constant_of_frobenius_eq (x : TruncatedWittVector p m Ω)
    (hx : TruncatedWittVector.map (frobenius Ω p) x = x) :
    ∃ z : ZMod (p ^ m), constantCast p m Ω z = x := by
  have hcoeff (i : Fin m) : (x.coeff i) ^ p = x.coeff i := by
    simpa only [TruncatedWittVector.map_coeff, frobenius_def] using
      congrArg (TruncatedWittVector.coeff i) hx
  choose z hz using fun i : Fin m =>
    ArtinSchreierTheory.exists_zmod_of_pow_eq p Ω (hcoeff i)
  refine ⟨(zmodEquivTrunc p m).symm (TruncatedWittVector.mk p z), ?_⟩
  change TruncatedWittVector.map (ZMod.castHom (dvd_refl p) Ω)
    ((zmodEquivTrunc p m) ((zmodEquivTrunc p m).symm _)) = x
  rw [RingEquiv.apply_symm_apply]
  apply TruncatedWittVector.ext
  intro i
  rw [TruncatedWittVector.map_coeff, coeff_mk]
  exact hz i

variable {K : Type*} [Field K] [Algebra K Ω]

theorem map_constantCast (σ : Gal(Ω/K)) (z : ZMod (p ^ m)) :
    TruncatedWittVector.map σ.toRingHom (constantCast p m Ω z) =
      constantCast p m Ω z := by
  apply TruncatedWittVector.ext
  intro i
  rw [TruncatedWittVector.map_coeff]
  change σ ((TruncatedWittVector.map (ZMod.castHom (dvd_refl p) Ω)
    ((zmodEquivTrunc p m) z)).coeff i) =
      (TruncatedWittVector.map (ZMod.castHom (dvd_refl p) Ω)
        ((zmodEquivTrunc p m) z)).coeff i
  simp only [TruncatedWittVector.map_coeff, ZMod.castHom_apply, ZMod.cast_eq_val,
    map_natCast]

omit [CharP Ω p] in
private theorem map_base (σ : Gal(Ω/K)) (a : TruncatedWittVector p m K) :
    TruncatedWittVector.map σ.toRingHom (TruncatedWittVector.map (algebraMap K Ω) a) =
      TruncatedWittVector.map (algebraMap K Ω) a := by
  apply TruncatedWittVector.ext
  intro i
  simp only [TruncatedWittVector.map_coeff]
  exact σ.commutes (a.coeff i)

/-- The difference of a Witt root and its Galois translate is Frobenius fixed. -/
theorem rootDifference_frobenius_eq (a : TruncatedWittVector p m K)
    (β : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a) (σ : Gal(Ω/K)) :
    TruncatedWittVector.map (frobenius Ω p) (TruncatedWittVector.map σ.toRingHom β - β) =
      TruncatedWittVector.map σ.toRingHom β - β := by
  have hσ := congrArg (TruncatedWittVector.map σ.toRingHom) hβ
  rw [map_sub, map_base, ← TruncatedWittVector.map_frobenius] at hσ
  rw [map_sub]
  linear_combination hσ - hβ

/-- The prime-power coordinate of the difference of a root and its translate. -/
def rootCharacterValue (a : TruncatedWittVector p m K) (β : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a) (σ : Gal(Ω/K)) : ZMod (p ^ m) :=
  (exists_constant_of_frobenius_eq p m Ω _
    (rootDifference_frobenius_eq p m Ω a β hβ σ)).choose

theorem rootCharacterValue_cast (a : TruncatedWittVector p m K)
    (β : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a) (σ : Gal(Ω/K)) :
    constantCast p m Ω (rootCharacterValue p m Ω a β hβ σ) =
      TruncatedWittVector.map σ.toRingHom β - β :=
  (exists_constant_of_frobenius_eq p m Ω _
    (rootDifference_frobenius_eq p m Ω a β hβ σ)).choose_spec

variable [Algebra.IsIntegral K Ω]

/-- The actual continuous cyclic character of an Artin–Schreier–Witt root. -/
def rootCharacter (a : TruncatedWittVector p m K) (β : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a) :
    Gal(Ω/K) →ₜ* Multiplicative (ZMod (p ^ m)) where
  toFun σ := Multiplicative.ofAdd (rootCharacterValue p m Ω a β hβ σ)
  map_one' := by
    change rootCharacterValue p m Ω a β hβ 1 = 0
    apply constantCast_injective p m Ω
    rw [rootCharacterValue_cast, map_zero]
    apply sub_eq_zero.mpr
    apply TruncatedWittVector.ext
    intro i
    rw [TruncatedWittVector.map_coeff]
    rfl
  map_mul' σ τ := by
    change rootCharacterValue p m Ω a β hβ (σ * τ) =
      rootCharacterValue p m Ω a β hβ σ + rootCharacterValue p m Ω a β hβ τ
    apply constantCast_injective p m Ω
    rw [map_add, rootCharacterValue_cast, rootCharacterValue_cast, rootCharacterValue_cast]
    have hfix : TruncatedWittVector.map σ.toRingHom (TruncatedWittVector.map τ.toRingHom β - β) =
        TruncatedWittVector.map τ.toRingHom β - β := by
      rw [← rootCharacterValue_cast p m Ω a β hβ τ, map_constantCast]
    have hcomp : TruncatedWittVector.map σ.toRingHom (TruncatedWittVector.map τ.toRingHom β) =
        TruncatedWittVector.map (σ * τ).toRingHom β := by
      apply TruncatedWittVector.ext
      intro i
      simp only [TruncatedWittVector.map_coeff]
      rfl
    rw [map_sub, hcomp] at hfix
    linear_combination hfix
  continuous_toFun := by
    classical
    apply IsLocallyConstant.continuous
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro σ
    choose U hU hσ hconst using fun i : Fin m =>
      (GaloisCohomology.isLocallyConstant_galois_apply (K := K) (β.coeff i)).exists_open σ
    refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hσ, ?_⟩
    intro τ hτ
    apply congrArg Multiplicative.ofAdd
    apply constantCast_injective p m Ω
    rw [rootCharacterValue_cast, rootCharacterValue_cast]
    congr 1
    apply TruncatedWittVector.ext
    intro i
    rw [TruncatedWittVector.map_coeff, TruncatedWittVector.map_coeff]
    exact hconst i τ (Set.mem_iInter.mp hτ i)

theorem rootCharacter_cast (a : TruncatedWittVector p m K)
    (β : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a) (σ : Gal(Ω/K)) :
    constantCast p m Ω ((rootCharacter p m Ω a β hβ σ).toAdd) =
      TruncatedWittVector.map σ.toRingHom β - β :=
  rootCharacterValue_cast p m Ω a β hβ σ

/-- A Galois element is in the character kernel exactly when it fixes the Witt root. -/
theorem rootCharacter_eq_one_iff (a : TruncatedWittVector p m K)
    (β : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a) (σ : Gal(Ω/K)) :
    rootCharacter p m Ω a β hβ σ = 1 ↔ TruncatedWittVector.map σ.toRingHom β = β := by
  change (rootCharacter p m Ω a β hβ σ).toAdd = 0 ↔ _
  rw [← (constantCast_injective p m Ω).eq_iff, rootCharacter_cast, map_zero, sub_eq_zero]

/-- Changing the chosen Witt root leaves its character unchanged. -/
theorem rootCharacter_eq (a : TruncatedWittVector p m K)
    (β γ : TruncatedWittVector p m Ω)
    (hβ : TruncatedWittVector.map (frobenius Ω p) β - β =
      TruncatedWittVector.map (algebraMap K Ω) a)
    (hγ : TruncatedWittVector.map (frobenius Ω p) γ - γ =
      TruncatedWittVector.map (algebraMap K Ω) a) :
    rootCharacter p m Ω a β hβ = rootCharacter p m Ω a γ hγ := by
  have hdiff : TruncatedWittVector.map (frobenius Ω p) (β - γ) = β - γ := by
    rw [map_sub]
    linear_combination hβ - hγ
  obtain ⟨z, hz⟩ := exists_constant_of_frobenius_eq p m Ω (β - γ) hdiff
  apply ContinuousMonoidHom.ext
  intro σ
  change (rootCharacter p m Ω a β hβ σ).toAdd = (rootCharacter p m Ω a γ hγ σ).toAdd
  apply constantCast_injective p m Ω
  rw [rootCharacter_cast, rootCharacter_cast]
  have hfix : TruncatedWittVector.map σ.toRingHom (β - γ) = β - γ := by
    rw [← hz, map_constantCast]
  rw [map_sub] at hfix
  linear_combination hfix

end ArtinSchreierWittTheory
