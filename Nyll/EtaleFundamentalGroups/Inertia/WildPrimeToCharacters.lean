/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildProP
public import Nyll.ProCGroups.ProC.PrimeSeparation
public import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
public import Nyll.ProCGroups.ProC.InverseLimits.FiniteQuotients

/-!
# Prime-to-residue-characteristic characters kill native wild inertia

The wild group here is the independently defined principal-unit subgroup of
normalization inertia, with its original topology. Its pro-p theorem implies
that every continuous map to a pro-ell group is trivial for ell distinct from p.
This does not kill the geometric p-primary layer of the full fundamental group.
-/

@[expose] public section

namespace ProCGroups.ProC

universe u v

/-- Pro-prime characters kill the residual core even when their target has
a different carrier universe. Finite quotient kernels remain in the source
universe, and their actual ranges supply the prime-group condition. -/
theorem proPrimeResidualCore_le_ker_acrossUniverses
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (ℓ : ℕ) [Fact ℓ.Prime] (φ : G →ₜ* H)
    (hH : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ) H) :
    proCResidualCore (FiniteGroupClass.pGroup ℓ) G ≤ φ.toMonoidHom.ker := by
  intro g hg
  apply hH.eq_one_of_mem_all_openNormalSubgroupInClass
  intro U
  apply (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup H)) (φ g)).mp
  let q : G →ₜ* H ⧸ (U.1 : Subgroup H) := (OpenNormalSubgroup.quotientProj U.1).comp φ
  let N : OpenNormalSubgroup G := OpenNormalSubgroup.ker q
  let e : (G ⧸ (N : Subgroup G)) ≃* q.toMonoidHom.range :=
    QuotientGroup.quotientKerEquivRange q.toMonoidHom
  have : Finite (H ⧸ (U.1 : Subgroup H)) := U.property.1
  have : Finite (G ⧸ (N : Subgroup G)) :=
    Finite.of_equiv q.toMonoidHom.range e.symm.toEquiv
  have : DiscreteTopology (G ⧸ (N : Subgroup G)) :=
    QuotientGroup.discreteTopology N.isOpen'
  have hP : IsPGroup ℓ (G ⧸ (N : Subgroup G)) :=
    U.property.2.of_injective (q.toMonoidHom.range.subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective)
  have hquot : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ)
      (G ⧸ (N : Subgroup G)) :=
    HasOpenNormalBasisInClass.of_finite_discrete
      (FiniteGroupClass.pGroup_fullFormation ℓ).melnikovFormation.formation.quotientClosed
      ⟨inferInstance, hP⟩
  exact (proCResidualCore_le_of_proCQuotient (N : Subgroup G)
    (ContinuousMonoidHom.isClosed_ker q) hquot) hg

/-- A continuous homomorphism from a profinite pro-p group to a Hausdorff
pro-ell group is trivial when the two primes differ. -/
theorem continuousMonoidHom_eq_one_of_distinct_primes
    {G : Type u} {H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (hp : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) G)
    (hℓ : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ) H)
    (φ : G →ₜ* H) (g : G) : φ g = 1 := by
  apply hℓ.eq_one_of_mem_all_openNormalSubgroupInClass
  intro U
  let q : G →ₜ* H ⧸ (U.1 : Subgroup H) := (OpenNormalSubgroup.quotientProj U.1).comp φ
  have hquot := hp.quotient_mem
    (FiniteGroupClass.pGroup_fullFormation p).melnikovFormation.formation
    (OpenNormalSubgroup.ker q)
  let e : (G ⧸ q.toMonoidHom.ker) ≃* q.toMonoidHom.range :=
    QuotientGroup.quotientKerEquivRange q.toMonoidHom
  have hrange : IsPGroup p q.toMonoidHom.range :=
    hquot.2.of_surjective e.toMonoidHom e.surjective
  obtain ⟨a, ha⟩ := hrange ⟨q g, ⟨g, rfl⟩⟩
  obtain ⟨b, hb⟩ := U.property.2 (q g)
  have hpa : (q g) ^ (p ^ a) = 1 :=
    congrArg (fun z : q.toMonoidHom.range => (z : H ⧸ (U.1 : Subgroup H))) ha
  have hqg : q g = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes
      (((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mpr hpℓ).pow a b)
      (orderOf_dvd_of_pow_eq_one hpa) (orderOf_dvd_of_pow_eq_one hb))
  exact (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup H)) (φ g)).mp hqg

end ProCGroups.ProC

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory ProCGroups.ProC

universe u v

/-- Every continuous pro-ell character kills the actual normalization wild
inertia in residue characteristic p, for ell distinct from p. -/
theorem normalizationWild_proPrime_character_eq_one
    (A K Ω : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsGalois K Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) p] (hpℓ : p ≠ ℓ)
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hH : HasOpenNormalBasisInClass (ProCGroups.FiniteGroupClass.pGroup ℓ) H)
    (φ : (actualNormalizationWildGroup A K Ω Q).carrier →ₜ* H)
    (σ : (actualNormalizationWildGroup A K Ω Q).carrier) : φ σ = 1 := by
  have : CompactSpace (actualNormalizationWildGroup A K Ω Q).carrier :=
    actualNormalizationWildGroup_compactSpace A K Ω Q
  have : T2Space (actualNormalizationWildGroup A K Ω Q).carrier :=
    actualNormalizationWildGroup_t2Space A K Ω Q
  have : TotallyDisconnectedSpace (actualNormalizationWildGroup A K Ω Q).carrier :=
    actualNormalizationWildGroup_totallyDisconnectedSpace A K Ω Q
  exact continuousMonoidHom_eq_one_of_distinct_primes p ℓ hpℓ
    (actualNormalizationWildGroup_hasPGroupOpenNormalBasis A K Ω Q p) hH φ σ

end EtaleFundamentalGroups.Inertia
