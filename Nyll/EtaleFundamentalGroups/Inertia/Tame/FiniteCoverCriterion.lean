/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameFactorization
public import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameExactness
public import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameIndex
public import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealWildPrimary
public import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationTameExactness
public import Nyll.EtaleFundamentalGroups.Inertia.ActualWildFiniteImages
public import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaContinuity
public import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationGaloisFaithful
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueCharacteristic
public import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite normalization criteria for tame monodromy

At a finite Galois normalization, triviality of the independently defined
principal-unit wild subgroup is equivalent to a prime-to-characteristic
ramification index and a separable residue extension. Absolute wild inertia
fixes all embeddings of a finite Galois subfield exactly when its actual
finite wild image is trivial. The statements retain the original
normalization and coefficient restriction maps.
-/

@[expose] public section

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

private theorem prime_pow_eq_one_of_coprime {p n : ℕ}
    (hp : p.Prime) (h : p.Coprime (p ^ n)) : p ^ n = 1 := by
  cases n with
  | zero => exact pow_zero p
  | succ n =>
    exact False.elim ((hp.coprime_iff_not_dvd.mp h) ⟨p ^ n, pow_succ' p n⟩)

/-- Classical local tameness is detected by the actual principal-unit wild
subgroup. The residue extension is not assumed separable in advance. -/
theorem finiteIdealWildSubgroup_eq_bot_iff_coprime_and_isSeparable
    (A : Type u) (B : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    [IsGaloisGroup (B ≃ₐ[A] B) A B]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    finiteIdealWildSubgroup B (B ≃ₐ[A] B) Q hQ = ⊥ ↔
      p.Coprime (Q.ramificationIdx A) ∧
        Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q) := by
  have : Finite (B ≃ₐ[A] B) := inferInstance
  let t := finiteIdealTameOrder B (B ≃ₐ[A] B) Q hQ
  let w := finiteIdealWildOrder B (B ≃ₐ[A] B) Q hQ
  let d := Field.finInsepDegree (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q)
  have hfactor : t * w = Q.ramificationIdx A * d :=
    finiteIdealTameOrder_mul_wildOrder_eq_ramificationIdx_mul_finInsepDegree
      A B Q hQ (B ≃ₐ[A] B)
  have htunit : IsUnit (t : IsLocalRing.ResidueField A) := by
    simpa only [map_natCast] using
      (finiteIdealTameOrder_isUnit_base A B (B ≃ₐ[A] B) Q hQ).map
        (IsLocalRing.residue A)
  have htcoprime : p.Coprime t := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hpt
    exact htunit.ne_zero ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) p t).mpr hpt)
  obtain ⟨r, hr⟩ := finiteIdealWildOrder_exists_expChar_pow A B Q hQ
  have hw : w = p ^ r := by
    exact hr.trans (by rw [idealResidue_ringExpChar_eq_baseResidue A B Q,
      ringExpChar.eq (IsLocalRing.ResidueField A) p])
  have : CharP (A ⧸ IsLocalRing.maximalIdeal A) p :=
    inferInstanceAs (CharP (IsLocalRing.ResidueField A) p)
  obtain ⟨s, hs⟩ := finInsepDegree_eq_pow
    (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q) p
  have hd : d = p ^ s := hs
  rw [Subgroup.eq_bot_iff_card, finiteIdealWildSubgroup_card]
  change w = 1 ↔ _
  constructor
  · intro hw1
    have hprod : p.Coprime (Q.ramificationIdx A * d) := by
      rw [← hfactor, hw1, mul_one]
      exact htcoprime
    obtain ⟨he, hdprime⟩ := Nat.coprime_mul_iff_right.mp hprod
    have hd1 : d = 1 := hd.trans (prime_pow_eq_one_of_coprime
      (Fact.out : p.Prime) (hd ▸ hdprime))
    exact ⟨he, (isSeparable_iff_finInsepDegree_eq_one
      (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q)).mpr hd1⟩
  · rintro ⟨he, hsep⟩
    have hd1 : d = 1 := (isSeparable_iff_finInsepDegree_eq_one
      (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ Q)).mp hsep
    have hprod : p.Coprime (t * w) := by
      rw [hfactor, hd1, mul_one]
      exact he
    have hwprime : p.Coprime w := (Nat.coprime_mul_iff_right.mp hprod).2
    exact hw.trans (prime_pow_eq_one_of_coprime (Fact.out : p.Prime) (hw ▸ hwprime))

/-- The criterion at the literal normalization of a finite Galois field
extension. Its finite module, Dedekind, and Galois structures come from that
extension; no ramification comparison is an input. -/
theorem originalFiniteNormalizationWildSubgroup_eq_bot_iff_coprime_and_isSeparable
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F).carrier) [Q.IsMaximal]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p] :
    let : Q.LiesOver (IsLocalRing.maximalIdeal A) :=
      normalizationCommAlgCat_liesOver_maximalIdeal Q
    originalFiniteNormalizationWildSubgroup A K F Q = ⊥ ↔
      p.Coprime (Q.ramificationIdx A) ∧
        Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A)
          ((normalizationCommAlgCat A F).carrier ⧸ Q) := by
  intro hlying
  have : IsDedekindDomain (normalizationCommAlgCat A F).carrier :=
    nativeFieldNormalization_isDedekindDomain A K F
  have : Module.Finite A (normalizationCommAlgCat A F).carrier :=
    nativeNormalization_finite A K (CommAlgCat.of A F) (Field.toIsField F)
  have : Module.IsTorsionFree A (normalizationCommAlgCat A F).carrier :=
    nativeFieldNormalization_isTorsionFree A K F
  have : IsGaloisGroup ((normalizationCommAlgCat A F).carrier ≃ₐ[A]
      (normalizationCommAlgCat A F).carrier) A (normalizationCommAlgCat A F).carrier :=
    nativeFieldNormalization_isGaloisGroup A K F
  exact finiteIdealWildSubgroup_eq_bot_iff_coprime_and_isSeparable A
    (normalizationCommAlgCat A F).carrier Q
      (originalFiniteNormalizationPrime_ne_bot A K F Q) p

/-- For a normal intermediate field, fixing every geometric embedding is
exactly trivial restriction. The acting element need not lie in a normal
subgroup of the ambient Galois group. -/
theorem normalField_embeddings_fixed_iff
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [Normal K E] (σ : Gal(Ω/K)) :
    (∀ φ : E →ₐ[K] Ω, σ.toAlgHom.comp φ = φ) ↔
      AlgEquiv.restrictNormalHom E σ = 1 := by
  constructor
  · intro h
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact DFunLike.congr_fun (h E.val) x
  · intro h φ
    apply AlgHom.ext
    intro x
    let y : E := φ.restrictNormal E x
    have hy : (y : Ω) = φ x := φ.restrictNormal_commutes E x
    have hfix : σ (y : Ω) = (y : Ω) := by
      have h' := congrArg (fun τ : Gal(E/K) => (τ y : Ω)) h
      rw [AlgEquiv.restrictNormalHom_apply] at h'
      exact h'
    change σ (φ x) = φ x
    rw [← hy]
    exact hfix

section Absolute

variable (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsGalois K Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]

omit [IsDomain A] [IsDiscreteValuationRing A] [Q.IsMaximal] in
private theorem finiteInertiaRestriction_eq_one_iff
    (E : FiniteGaloisIntermediateField K Ω)
    (σ : (actualNormalizationInertiaGroup A K Ω Q).carrier) :
    (actualFiniteInertiaRestriction A K Ω Q E).hom' σ = 1 ↔
      AlgEquiv.restrictNormalHom E σ.val = 1 := by
  let c := (finiteNormalizationGaloisGroupMap A K Ω E).hom'
  have hc : Function.Injective c := finiteNormalizationGaloisGroupMap_injective A K Ω E
  have hcoeff : ((actualFiniteInertiaRestriction A K Ω Q E).hom' σ).val =
      c (AlgEquiv.restrictNormalHom E σ.val) :=
    actualFiniteInertiaRestriction_coefficient A K Ω Q E σ
  constructor
  · intro h
    apply hc
    exact hcoeff.symm.trans ((congrArg Subtype.val h).trans (map_one c).symm)
  · intro h
    apply Subtype.ext
    exact hcoeff.trans ((congrArg c h).trans (map_one c))

/-- Absolute wild inertia acts trivially on every geometric embedding of a
finite Galois subfield exactly when the actual finite normalization wild
subgroup is trivial. Exact finite wild images supply both implications. -/
theorem actualNormalizationWild_fixes_embeddings_iff
    (E : FiniteGaloisIntermediateField K Ω) :
    (∀ σ : (actualNormalizationWildGroup A K Ω Q).carrier,
      ∀ φ : E →ₐ[K] Ω, σ.val.val.toAlgHom.comp φ = φ) ↔
      actualFiniteWildSubgroup A K Ω Q E = ⊥ := by
  constructor
  · intro h
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro τ hτ
    obtain ⟨σ, hσ⟩ := actualNormalizationWildRestriction_surjective A K Ω Q E ⟨τ, hτ⟩
    have hrestriction : (actualFiniteInertiaRestriction A K Ω Q E).hom' σ.val = 1 :=
      (finiteInertiaRestriction_eq_one_iff A K Ω Q E σ.val).mpr
        ((normalField_embeddings_fixed_iff E.toIntermediateField σ.val.val).mp (h σ))
    have hval := congrArg Subtype.val hσ
    exact hval.symm.trans hrestriction
  · intro h σ
    apply (normalField_embeddings_fixed_iff E.toIntermediateField σ.val.val).mpr
    apply (finiteInertiaRestriction_eq_one_iff A K Ω Q E σ.val).mp
    have hmem : (actualFiniteInertiaRestriction A K Ω Q E).hom' σ.val ∈
        actualFiniteWildSubgroup A K Ω Q E :=
      ((actualNormalizationWildRestriction A K Ω Q E).hom' σ).property
    exact Subgroup.mem_bot.mp (h ▸ hmem)

end Absolute

end EtaleFundamentalGroups.Inertia
