/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Tate.AlgebraicPoints
public import Nyll.AbelianVarieties.Geometry.RelativeDimension
public import Nyll.ValuedFieldTheory.Ramification.InertiaLifting
public import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
public import Nyll.ValuedFieldTheory.Valuation.Henselian.RingEquiv
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Nyll.AbelianVarieties.Tate.Representation

/-!
# One fixed inertia group and the torsion criterion

Over a Henselian discrete valuation ring, every valuation ring in an algebraic
extension which contains the base ring is either the fixed extension ring or the
whole field. The latter has trivial inertia. Thus the all-valuation-ring torsion
condition in the geometric reduction criterion is equivalent to triviality of the
actual Tate representation on one fixed inertia group.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem valuationRing_eq_top_of_comap_eq_top
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (A : ValuationSubring Ω) (hA : A.comap (algebraMap K Ω) = ⊤) : A = ⊤ := by
  have hKA (x : K) : algebraMap K Ω x ∈ A := by
    change x ∈ A.comap (algebraMap K Ω)
    rw [hA]
    exact ValuationSubring.mem_top x
  let : Algebra K A := ((algebraMap K Ω).codRestrict A.toSubring hKA).toAlgebra
  have : IsScalarTower K A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply top_unique
  intro x _
  have hx : IsIntegral A x :=
    IsIntegral.tower_top (Algebra.IsIntegral.isIntegral (R := K) x)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω) hx
  rw [← hy]
  exact y.property

private theorem valuationRing_eq_or_top
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [HenselianRing O (IsLocalRing.maximalIdeal O)]
    (W : ValuationSubring Ω) [O.valuation.HasExtension W.valuation]
    (A : ValuationSubring Ω) (hA : O ≤ A.comap (algebraMap K Ω)) : A = W ∨ A = ⊤ := by
  rcases ValuationSubring.eq_self_or_eq_top_of_le hA with h | h
  · left
    have : O.valuation.HasExtension A.valuation := ⟨by
      apply Valuation.isEquiv_of_val_le_one
      intro x
      change O.valuation x ≤ 1 ↔ A.valuation (algebraMap K Ω x) ≤ 1
      rw [O.valuation_le_one_iff, A.valuation_le_one_iff]
      change x ∈ O ↔ x ∈ A.comap (algebraMap K Ω)
      rw [h]⟩
    have heq := ValuationTheory.Henselian.valuationSubring_eq_of_henselianRing
      O A.valuation W.valuation
    simpa only [ValuationSubring.valuationSubring_valuation] using heq
  · exact Or.inr (valuationRing_eq_top_of_comap_eq_top A h)

open AbelianVarieties.NOSProofs.ValuationInertiaLifting.ValuationSubring.InertiaLift in
private theorem inertiaSubgroupIn_top_eq_bot
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] :
    (⊤ : ValuationSubring Ω).inertiaSubgroupIn K = ⊥ := by
  apply bot_unique
  intro σ hσ
  rw [Subgroup.mem_bot]
  ext x
  have h := smul_eq_of_mem_inertiaSubgroupIn (K := K) (⊤ : ValuationSubring Ω) hσ
  have hx := h.2 x (ValuationSubring.mem_top x)
  rw [ValuationSubring.mem_nonunits_iff_or] at hx
  exact sub_eq_zero.mp (hx.resolve_right fun hn => hn (ValuationSubring.mem_top _))

/-- Over a Henselian DVR, containment of one inertia group in a subgroup of field
    automorphisms is equivalent to containment for every valuation ring above the base. -/
theorem fixedInertia_le_iff_forall_valuationRing
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [HenselianRing O (IsLocalRing.maximalIdeal O)]
    (W : ValuationSubring Ω) [O.valuation.HasExtension W.valuation]
    (H : Subgroup (Ω ≃ₐ[K] Ω)) :
    W.inertiaSubgroupIn K ≤ H ↔
      ∀ A : ValuationSubring Ω, O ≤ A.comap (algebraMap K Ω) →
        A.inertiaSubgroupIn K ≤ H := by
  constructor
  · intro h A hA
    rcases valuationRing_eq_or_top O W A hA with rfl | rfl
    · exact h
    · rw [inertiaSubgroupIn_top_eq_bot]
      exact bot_le
  · intro h
    apply h W
    intro x hx
    change algebraMap K Ω x ∈ W
    rw [← W.valuation_le_one_iff,
      Valuation.HasExtension.val_map_le_one_iff O.valuation W.valuation,
      O.valuation_le_one_iff]
    exact hx

/-- The all-valuation-ring torsion condition used in the geometric NOS proof is
exactly unramifiedness of the Tate representation at one fixed extension of a
Henselian discrete valuation. This applies in particular to complete DVRs. -/
theorem fixedInertia_primePowerTate_iff_forall_torsion
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [IsSepClosed Ω] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [HenselianRing O (IsLocalRing.maximalIdeal O)]
    (W : ValuationSubring Ω) [O.valuation.HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (p : ℕ) [Fact p.Prime] (hp : (p : Ω) ≠ 0) :
    W.inertiaSubgroupIn K ≤ (TateModule.rep p (L.AlgPoints hc Ω) (Ω ≃ₐ[K] Ω)).ker ↔
      ∀ V : ValuationSubring Ω, O ≤ V.comap (algebraMap K Ω) →
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ V.inertiaSubgroupIn K →
          ∀ n : ℕ, ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f,
            L.IsTorsionPoint _ (p ^ n) x →
              Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by
  have : Smooth f := hA.smooth
  obtain ⟨g, hg⟩ := L.exists_smoothOfRelativeDimension_of_smooth
  rw [fixedInertia_le_iff_forall_valuationRing O W]
  constructor
  · intro h V hV σ hσ
    exact (L.geometricPrimePowerTateRep_eq_one_iff hc hA g p hp σ).mp (h V hV hσ)
  · intro h V hV σ hσ
    exact (L.geometricPrimePowerTateRep_eq_one_iff hc hA g p hp σ).mpr (h V hV σ hσ)

/-- The inertia criterion for an arbitrary Henselian DVR, represented inside its
fraction field by its canonical valuation. Containment of the base ring is stated
using its original algebra map, as required by the geometric NOS criterion. -/
theorem fixedInertia_primePowerTate_iff_forall_torsion_of_dvr
    {R K Ω : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra R Ω] [IsScalarTower R K Ω] [IsSepClosed Ω]
    (W : ValuationSubring Ω) [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (p : ℕ) [Fact p.Prime] (hp : (p : Ω) ≠ 0) :
    W.inertiaSubgroupIn K ≤ (TateModule.rep p (L.AlgPoints hc Ω) (Ω ≃ₐ[K] Ω)).ker ↔
      ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) →
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ V.inertiaSubgroupIn K →
          ∀ n : ℕ, ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f,
            L.IsTorsionPoint _ (p ^ n) x →
              Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1 := by
  let O : ValuationSubring K := (ValuationRing.valuation R K).valuationSubring
  let e : R ≃+* O := ValuationRing.equivInteger R K
  have : IsDiscreteValuationRing O :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have : HenselianRing O (IsLocalRing.maximalIdeal O) :=
    ValuationTheory.Henselian.henselianRing_maximalIdeal_of_ringEquiv e
  have : O.valuation.HasExtension W.valuation := ⟨
    (Valuation.isEquiv_valuation_valuationSubring (ValuationRing.valuation R K)).symm.trans
      (Valuation.HasExtension.val_isEquiv_comap (vR := ValuationRing.valuation R K)
        (vA := W.valuation))⟩
  rw [L.fixedInertia_primePowerTate_iff_forall_torsion O W hc hA p hp]
  apply forall_congr'
  intro V
  apply imp_congr_left
  constructor
  · intro h r
    rw [IsScalarTower.algebraMap_apply R K Ω r]
    apply h
    exact (ValuationRing.mem_integer_iff R K _).mpr ⟨r, rfl⟩
  · intro h x hx
    obtain ⟨r, rfl⟩ := (ValuationRing.mem_integer_iff R K x).mp hx
    change algebraMap K Ω (algebraMap R K r) ∈ V
    rw [← IsScalarTower.algebraMap_apply R K Ω r]
    exact h r

end GoodReductionJacobian.RelativeGroupLaw
