/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.Local.PuncturedHomHartogs
public import Nyll.SchemeTheory.RingTheory.RegularLocal.ModuleDepthRegularQuotient
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# Hartogs extension across an arbitrary depth-two affine boundary

The vanishing ideal of the boundary contains a regular pair. Indeed,
localization of an associated prime would give depth zero at a boundary
point; after choosing the first regular element, the same argument and
the depth formula for its quotient give a second regular element.
Finite associated-prime avoidance makes the pair global. The actual
scalar restriction and restriction of morphisms into the structure
module are consequently bijective.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace RingTheory IsLocalRing Module.associatedPrimes
open scoped Pointwise
open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq

namespace AlgebraicGeometry

universe u

private theorem exists_common_regular_mem_ideal
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M N : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hM : ∀ p ∈ associatedPrimes R M, ¬ I ≤ p)
    (hN : ∀ p ∈ associatedPrimes R N, ¬ I ≤ p) :
    ∃ x ∈ I, IsSMulRegular M x ∧ IsSMulRegular N x := by
  classical
  by_contra h
  have hcover : (I : Set R) ⊆
      ⋃ p ∈ associatedPrimes R M ∪ associatedPrimes R N, (p : Set R) := by
    intro x hx
    rw [Set.biUnion_union, biUnion_associatedPrimes_eq_compl_regular R M,
      biUnion_associatedPrimes_eq_compl_regular R N]
    by_cases hxM : IsSMulRegular M x
    · exact Or.inr (fun hxN => h ⟨x, hx, hxM, hxN⟩)
    · exact Or.inl hxM
  have hfinite := (associatedPrimes.finite R M).union (associatedPrimes.finite R N)
  have hprime : ∀ p ∈ associatedPrimes R M ∪ associatedPrimes R N,
      p ≠ (⊥ : Ideal R) → p ≠ (⊥ : Ideal R) → (id p).IsPrime := by
    rintro p (hp | hp) _ _
    · exact hp.isPrime
    · exact hp.isPrime
  obtain ⟨p, hp, hIp⟩ :=
    (Ideal.subset_union_prime_finite hfinite (f := id) (I := I) ⊥ ⊥ hprime).mp
      (by simpa only [id_eq] using hcover)
  rcases hp with hp | hp
  · exact hM p hp hIp
  · exact hN p hp hIp

private theorem smul_top_eq_span_singleton
    {R : Type u} [CommRing R] (x : R) :
    x • (⊤ : Submodule R R) = Submodule.span R {x} := by
  ext a
  rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨b, _, hb⟩
    exact ⟨b, by simpa only [smul_eq_mul, mul_comm] using hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, Submodule.mem_top, by simpa only [smul_eq_mul, mul_comm] using hb⟩

/-- The ideal of an arbitrary depth-two boundary contains a regular pair;
both elements are regular on the ring itself. -/
theorem exists_regular_pair_in_boundary_ideal_of_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p)) :
    ∃ x ∈ PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ,
      ∃ y ∈ PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ,
        IsSMulRegular R x ∧ IsSMulRegular R y ∧
          IsSMulRegular (QuotSMulTop x R) y := by
  let I := PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ
  have hboundary (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) : p ∉ U := by
    have hclosed : PrimeSpectrum.zeroLocus (I : Set R) =
        (U : Set (Spec R))ᶜ := by
      exact (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure
        (U : Set (Spec R))ᶜ).trans U.isOpen.isClosed_compl.closure_eq
    have hp' : p ∈ PrimeSpectrum.zeroLocus (I : Set R) := hp
    exact (congrArg (fun Z : Set (PrimeSpectrum R) => p ∈ Z) hclosed).mp hp'
  have havoid : ∀ p ∈ associatedPrimes R R, ¬ I ≤ p := by
    intro p hp hIp
    have : p.IsPrime := hp.isPrime
    let q : Spec R := (⟨p, inferInstance⟩ : PrimeSpectrum R)
    let S : Type u := (Spec R).presheaf.stalk q
    have : IsLocalRing S :=
      inferInstanceAs (IsLocalRing ((Spec R).presheaf.stalk q))
    have : IsNoetherianRing S :=
      inferInstanceAs (IsNoetherianRing ((Spec R).presheaf.stalk q))
    let : Algebra R S :=
      StructureSheaf.stalkAlgebra (R := R) (⟨p, inferInstance⟩ : PrimeSpectrum R)
    have : IsLocalization p.primeCompl S :=
      StructureSheaf.IsLocalization.to_stalk (R := R)
        (⟨p, inferInstance⟩ : PrimeSpectrum R)
    have hass : maximalIdeal S ∈ associatedPrimes S S := by
      apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
        p.primeCompl (Algebra.linearMap R S)
      change (maximalIdeal S).under R ∈ associatedPrimes R R
      rw [IsLocalization.AtPrime.under_maximalIdeal S p]
      exact hp
    have hpositive : 0 < Module.depth S S :=
      lt_of_lt_of_le (by norm_num) (hdepth q (hboundary q hIp))
    exact Ws14Port.Module.maximalIdeal_notMem_associatedPrimes_of_depth_pos S S
      hpositive hass
  obtain ⟨x, hxI, hx, _⟩ := exists_common_regular_mem_ideal I R R havoid havoid
  have havoidQ : ∀ p ∈ associatedPrimes R (QuotSMulTop x R), ¬ I ≤ p := by
    intro p hp hIp
    have : p.IsPrime := hp.isPrime
    let q : Spec R := (⟨p, inferInstance⟩ : PrimeSpectrum R)
    let S : Type u := (Spec R).presheaf.stalk q
    have : IsLocalRing S :=
      inferInstanceAs (IsLocalRing ((Spec R).presheaf.stalk q))
    have : IsNoetherianRing S :=
      inferInstanceAs (IsNoetherianRing ((Spec R).presheaf.stalk q))
    let : Algebra R S :=
      StructureSheaf.stalkAlgebra (R := R) (⟨p, inferInstance⟩ : PrimeSpectrum R)
    have : IsLocalization p.primeCompl S :=
      StructureSheaf.IsLocalization.to_stalk (R := R)
        (⟨p, inferInstance⟩ : PrimeSpectrum R)
    let K := (x • (⊤ : Submodule R R)).localized'
      S p.primeCompl (Algebra.linearMap R S)
    let f : QuotSMulTop x R →ₗ[R] S ⧸ K :=
      (x • (⊤ : Submodule R R)).toLocalizedQuotient'
        S p.primeCompl (Algebra.linearMap R S)
    have hass : maximalIdeal S ∈ associatedPrimes S (S ⧸ K) := by
      apply mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
        p.primeCompl f
      change (maximalIdeal S).under R ∈ associatedPrimes R (QuotSMulTop x R)
      rw [IsLocalization.AtPrime.under_maximalIdeal S p]
      exact hp
    have hK : K = algebraMap R S x • (⊤ : Submodule S S) := by
      dsimp only [K]
      rw [smul_top_eq_span_singleton, Submodule.localized'_span,
        Set.image_singleton, smul_top_eq_span_singleton]
      rfl
    have hzero : Module.depth S (S ⧸ K) = 0 :=
      (Ws14Port.Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes
        S (S ⧸ K)).mpr hass
    have hzero' : Module.depth S (QuotSMulTop (algebraMap R S x) S) = 0 := by
      change Module.depth S (S ⧸ (algebraMap R S x • (⊤ : Submodule S S))) = 0
      rw [← hK]
      exact hzero
    have hxmax : algebraMap R S x ∈ maximalIdeal S :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff S p x).mpr (hIp hxI)
    have : Module.Flat R S := IsLocalization.flat S p.primeCompl
    have hxS : IsSMulRegular S (algebraMap R S x) := hx.of_flat
    have hdrop := Module.depth_quotSMulTop_succ_eq S hxmax hxS
    rw [hzero', zero_add] at hdrop
    have htwo := hdepth q (hboundary q hIp)
    change (2 : ℕ∞) ≤ Module.depth S S at htwo
    rw [← hdrop] at htwo
    norm_num at htwo
  obtain ⟨y, hyI, hy, hxy⟩ :=
    exists_common_regular_mem_ideal I R (QuotSMulTop x R) havoid havoidQ
  exact ⟨x, hxI, y, hyI, hx, hy, hxy⟩

/-- Scalar sections extend uniquely across every depth-two boundary on
an affine Noetherian spectrum, without integrality or normality. -/
theorem restrict_bijective_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p)) :
    Function.Bijective
      ((Spec R).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) := by
  let c : R ⟶ Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).inv
  let : Algebra R Γ(Spec R, ⊤) := c.hom.toAlgebra
  have : Module.Flat R Γ(Spec R, ⊤) :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso c)
  obtain ⟨x, hxI, y, hyI, hx, hy, hxy⟩ :=
    exists_regular_pair_in_boundary_ideal_of_two_le_depth R U hdepth
  have hpair : Sequence.IsWeaklyRegular R [x, y] :=
    Sequence.IsWeaklyRegular.cons hx (Sequence.IsWeaklyRegular.cons hxy
      (Sequence.IsWeaklyRegular.nil R _))
  have hpair' : Sequence.IsWeaklyRegular Γ(Spec R, ⊤)
      ([x, y].map (algebraMap R Γ(Spec R, ⊤))) := by
    apply (Sequence.isWeaklyRegular_map_algebraMap_iff Γ(Spec R, ⊤)
      Γ(Spec R, ⊤) [x, y]).mpr
    exact ((TensorProduct.lid R Γ(Spec R, ⊤)).isWeaklyRegular_congr [x, y]).mp
      hpair.isWeaklyRegular_rTensor
  simp only [List.map_cons, List.map_nil, Sequence.isWeaklyRegular_cons_iff] at hpair'
  have hbasic (r : R)
      (hr : r ∈ PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ) :
      (Spec R).basicOpen (algebraMap R Γ(Spec R, ⊤) r) ≤ U := by
    change (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r) ≤ U
    rw [basicOpen_eq_of_affine]
    intro q hq
    by_contra hqU
    exact hq ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hr q hqU)
  apply restrict_bijective_of_regular_pair (Spec R)
    (algebraMap R Γ(Spec R, ⊤) x) (algebraMap R Γ(Spec R, ⊤) y)
    hpair'.1 hy.of_flat hpair'.2.1 U
    (NoetherianSpace.isCompact _) ?_ (hbasic x hxI) (hbasic y hyI)
  intro A B _ _ _ _ _ _
  exact NoetherianSpace.isCompact _

namespace Scheme.Modules

/-- Every actual morphism into the structure module extends uniquely
across an arbitrary depth-two boundary on an affine Noetherian spectrum. -/
theorem hom_restrict_to_structure_bijective_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M : (Spec R).Modules) :
    Function.Bijective (fun f : M ⟶ SheafOfModules.unit (Spec R).ringCatSheaf =>
      (restrictFunctor U.ι).map f) :=
  hom_restrict_to_structure_bijective_of_scalar_hartogs R U
    (restrict_bijective_of_boundary_two_le_depth R U hdepth) M

end Scheme.Modules
end AlgebraicGeometry
