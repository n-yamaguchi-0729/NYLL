/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AbelianVarieties.Reduction.GoodReduction
public import Nyll.AbelianVarieties.Reduction.InertiaComparison
public import Nyll.AbelianVarieties.Reduction.Criterion
public import Nyll.AbelianVarieties.NeronModels.Existence
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPointsPullback
public import Nyll.AbelianVarieties.Geometry.AbelianSchemePullback
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.AbelianVarieties.Tate.AlgebraicPoints
public import Nyll.AbelianVarieties.Reduction.TorsionSpecialization
public import Nyll.ValuedFieldTheory.Ramification.InertiaLifting
public import Nyll.AbelianVarieties.Tate.Representation

/-! # The Néron–Ogg–Shafarevich criterion

The reverse implication constructs the Néron model and proves its properness from
unramifiedness. Neither the existence of a model nor fixedness of its torsion points
is an additional hypothesis.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
open RelativeGroupLaw_exists_isPullback_comp_eq_mul_eq_of_isPullback_of_comp_eq.DescB

namespace GoodReductionJacobian.RelativeGroupLaw

/-- An unramified prime-power Tate representation gives an abelian scheme model
of the original abelian variety over a Henselian discrete valuation ring. -/
theorem hasGoodReduction_of_inertiaSubgroupIn_le_primePowerTateKer
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (AlgebraicClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R))
    (hunr : W.inertiaSubgroupIn K ≤
      (TateModule.rep p (L.AlgPoints hc (AlgebraicClosure K))
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).ker) :
    L.HasGoodReduction R K := by
  obtain ⟨B, g, LB, e, hN, hcB, he, hemul⟩ :=
    L.exists_neronModel_of_abelian_variety (R := R) K hA
  have : IsIso e.1 := he
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hsquare : IsPullback e.1 (pullback.snd g (specGenericFibreInclusion R K)) f
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
    have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
      rw [hid]
      infer_instance
    apply IsPullback.of_horiz_isIso
    constructor
    rw [hid, Category.comp_id]
    exact e.2
  have hBK : AbelianSchemePropertyBundle K
      (pullback.snd g (specGenericFibreInclusion R K)) := hA.of_isPullback hsquare
  have hcBK : (LB.genericFibre K).IsCommutative :=
    IsCommutative.baseChange (specGenericFibreInclusion R K) hcB
  have hmul (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))) :
      ((LB.genericFibre K).mul t x y).1 ≫ e.1 =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap K K)))
          ⟨x.1 ≫ e.1, by rw [Category.assoc, hsquare.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ e.1, by rw [Category.assoc, hsquare.w, ← Category.assoc, y.2]⟩).1 := by
    refine (congrArg Subtype.val (hemul t x y)).trans ?_
    exact mul_val_congr L (by rw [hid, Category.comp_id]) _ _ _ _ rfl rfl
  let ePts := L.algPointsPullbackEquiv hc (LB.genericFibre K) hcBK e.1 hsquare hmul
    (AlgebraicClosure K)
  have hmodel : W.inertiaSubgroupIn K ≤
      (TateModule.rep p ((LB.genericFibre K).AlgPoints hcBK (AlgebraicClosure K))
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).ker := by
    intro σ hσ
    apply (TateModule.rep_eq_one_iff_of_equivariant p ePts σ σ ?_).mpr (hunr hσ)
    intro x
    exact L.algPointsPullbackEquiv_equivariant hc (LB.genericFibre K) hcBK e.1 hsquare
      hmul (AlgebraicClosure K) σ x
  have hpΩ : (p : AlgebraicClosure K) ≠ 0 := by
    have hu := hp.map (algebraMap R (AlgebraicClosure K))
    rw [map_natCast] at hu
    exact hu.ne_zero
  have hfixed :=
    (fixedInertia_primePowerTate_iff_forall_torsion_of_dvr.{u}
      (R := R) (K := K) (Ω := AlgebraicClosure K) W
      (LB.genericFibre K) hcBK hBK p hpΩ).mp hmodel
  have hB : AbelianSchemePropertyBundle R g :=
    LB.abelianScheme_of_neronModel_of_fixed_torsion
      K hcB hN hBK p (Fact.out : p.Prime) hp hfixed
  exact ⟨B, g, LB, e, hB, hcB, he, hemul⟩

/-- Good reduction is equivalent to an unramified Tate representation for any
prime invertible in the discrete valuation ring. -/
theorem hasGoodReduction_iff_inertiaSubgroupIn_le_primePowerTateKer
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (AlgebraicClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) :
    L.HasGoodReduction R K ↔ W.inertiaSubgroupIn K ≤
      (TateModule.rep p (L.AlgPoints hc (AlgebraicClosure K))
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).ker := by
  constructor
  · intro hgood
    apply hgood.inertiaSubgroupIn_le_primePowerTateKer hc p hp W
    intro r
    rw [← W.valuation_le_one_iff, IsScalarTower.algebraMap_apply R K (AlgebraicClosure K),
      Valuation.HasExtension.val_map_le_one_iff (ValuationRing.valuation R K) W.valuation]
    exact (ValuationRing.mem_integer_iff R K _).mpr ⟨r, rfl⟩
  · exact L.hasGoodReduction_of_inertiaSubgroupIn_le_primePowerTateKer W hc hA p hp

/-- A local ring admits an invertible rational prime: at least one of 2 and 3 is a unit. -/
private theorem exists_prime_isUnit (R : Type*) [CommRing R] [IsLocalRing R] :
    ∃ p : ℕ, p.Prime ∧ IsUnit (p : R) := by
  have h : (3 : R) + -(2 : R) = 1 := by norm_num
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h3 | h2
  · exact ⟨3, Nat.prime_three, h3⟩
  · exact ⟨2, Nat.prime_two, by simpa only [neg_neg, Nat.cast_ofNat] using h2.neg⟩

/-- One unramified admissible Tate representation suffices for good reduction. -/
theorem hasGoodReduction_iff_exists_unramified
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (AlgebraicClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) :
    L.HasGoodReduction R K ↔ ∃ (p : ℕ) (hprime : p.Prime),
      let : Fact p.Prime := ⟨hprime⟩
      IsUnit (p : R) ∧ W.inertiaSubgroupIn K ≤
        (TateModule.rep p (L.AlgPoints hc (AlgebraicClosure K))
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).ker := by
  constructor
  · intro hgood
    obtain ⟨p, hprime, hp⟩ := exists_prime_isUnit R
    have : Fact p.Prime := ⟨hprime⟩
    refine ⟨p, hprime, hp, ?_⟩
    exact (L.hasGoodReduction_iff_inertiaSubgroupIn_le_primePowerTateKer W hc hA p hp).mp hgood
  · rintro ⟨p, hprime, hp, hunr⟩
    have : Fact p.Prime := ⟨hprime⟩
    exact L.hasGoodReduction_of_inertiaSubgroupIn_le_primePowerTateKer W hc hA p hp hunr

/-- Good reduction is equivalent to unramifiedness for every admissible prime. -/
theorem hasGoodReduction_iff_forall_unramified
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (AlgebraicClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) :
    L.HasGoodReduction R K ↔ ∀ (p : ℕ) (hprime : p.Prime),
      let : Fact p.Prime := ⟨hprime⟩
      IsUnit (p : R) → W.inertiaSubgroupIn K ≤
        (TateModule.rep p (L.AlgPoints hc (AlgebraicClosure K))
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).ker := by
  constructor
  · intro hgood p hprime inst hp
    exact (L.hasGoodReduction_iff_inertiaSubgroupIn_le_primePowerTateKer W hc hA p hp).mp hgood
  · intro hall
    obtain ⟨p, hprime, hp⟩ := exists_prime_isUnit R
    have : Fact p.Prime := ⟨hprime⟩
    exact L.hasGoodReduction_of_inertiaSubgroupIn_le_primePowerTateKer W hc hA p hp
      (hall p hprime hp)

private theorem henselianLocalRing_of_isAdicComplete
    (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : HenselianLocalRing R :=
  { toIsLocalRing := inferInstance
    is_henselian := fun q hq a ha hder =>
      HenselianRing.is_henselian q hq a ha
        (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))) }

/-- The NOS criterion over a complete discrete valuation ring. Completeness supplies
Hensel lifting, so a Henselian structure is not required as separate input. -/
theorem hasGoodReduction_iff_unramified_of_isAdicComplete
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (AlgebraicClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) :
    L.HasGoodReduction R K ↔ W.inertiaSubgroupIn K ≤
      (TateModule.rep p (L.AlgPoints hc (AlgebraicClosure K))
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).ker := by
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete R
  exact L.hasGoodReduction_iff_inertiaSubgroupIn_le_primePowerTateKer W hc hA p hp

/-- Over a complete DVR, good reduction is equivalent to one unramified admissible
Tate representation. -/
theorem hasGoodReduction_iff_exists_unramified_of_isAdicComplete
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (AlgebraicClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) :
    L.HasGoodReduction R K ↔ ∃ (p : ℕ) (hprime : p.Prime),
      let : Fact p.Prime := ⟨hprime⟩
      IsUnit (p : R) ∧ W.inertiaSubgroupIn K ≤
        (TateModule.rep p (L.AlgPoints hc (AlgebraicClosure K))
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).ker := by
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete R
  exact L.hasGoodReduction_iff_exists_unramified W hc hA

/-- Over a complete DVR, good reduction is equivalent to unramifiedness
at every admissible prime. -/
theorem hasGoodReduction_iff_forall_unramified_of_isAdicComplete
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (AlgebraicClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) :
    L.HasGoodReduction R K ↔ ∀ (p : ℕ) (hprime : p.Prime),
      let : Fact p.Prime := ⟨hprime⟩
      IsUnit (p : R) → W.inertiaSubgroupIn K ≤
        (TateModule.rep p (L.AlgPoints hc (AlgebraicClosure K))
          (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).ker := by
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete R
  exact L.hasGoodReduction_iff_forall_unramified W hc hA

end GoodReductionJacobian.RelativeGroupLaw

namespace GoodReductionJacobian.RelativeGroupLaw

private theorem algPoints_map_injective_of_field
    {K E Ω : Type u} [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (a : E →ₐ[K] Ω) :
    Function.Injective (AlgPoints.map (L := L) (hc := hc) a) := by
  have : Epi (Spec.map (CommRingCat.ofHom a.toRingHom)) :=
    (open AbelianVarieties.NOSProofs.TorsionSpecializationInjection.TorsionInjection in
      epi_specMap_of_field a.toRingHom)
  intro x y hxy
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  apply (cancel_epi (Spec.map (CommRingCat.ofHom a.toRingHom))).mp
  exact congrArg (fun z : L.AlgPoints hc Ω => (AlgPoints.toPoint z).1) hxy

private theorem algPoints_map_equivariant_of_commutes
    {K E Ω : Type u} [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (a : E →ₐ[K] Ω)
    (σ : Ω ≃ₐ[K] Ω) (τ : E ≃ₐ[K] E)
    (h : ∀ x : E, σ (a x) = a (τ x)) (x : L.AlgPoints hc E) :
    σ • AlgPoints.map a x = AlgPoints.map a (τ • x) := by
  have he : σ.toAlgHom.comp a = a.comp τ.toAlgHom := AlgHom.ext h
  have hm := congrArg (fun b : E →ₐ[K] Ω => AlgPoints.map (L := L) (hc := hc) b x) he
  have hleft : AlgPoints.map (σ.toAlgHom.comp a) x = σ • AlgPoints.map a x :=
    congrArg (fun b : L.AlgPoints hc E →+ L.AlgPoints hc Ω => b x)
      (AlgPoints.map_comp (L := L) (hc := hc) a σ.toAlgHom)
  have hright : AlgPoints.map (a.comp τ.toAlgHom) x = AlgPoints.map a (τ • x) :=
    congrArg (fun b : L.AlgPoints hc E →+ L.AlgPoints hc Ω => b x)
      (AlgPoints.map_comp (L := L) (hc := hc) τ.toAlgHom a)
  exact hleft.symm.trans (hm.trans hright)

private theorem geometricTorsion_map_surjective
    {K E Ω : Type u} [Field K] [Field E] [Field Ω]
    [IsSepClosed E] [IsSepClosed Ω] [Algebra K E] [Algebra K Ω]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : E →ₐ[K] Ω) (n : ℕ) (hn : (n : Ω) ≠ 0)
    (x : L.AlgPoints hc Ω) (hx : x ∈ Submodule.torsionBy ℤ (L.AlgPoints hc Ω) (n : ℤ)) :
    ∃ y : L.AlgPoints hc E, y ∈ Submodule.torsionBy ℤ (L.AlgPoints hc E) (n : ℤ) ∧
      AlgPoints.map a y = x := by
  have hnE : (n : E) ≠ 0 := by
    intro h
    apply hn
    rw [← map_natCast a n, h, map_zero]
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Nat.cast_zero)
  have hE := L.natCard_geometricPoints_torsionBy (Ω := E) hc hA d n hnE
  have hΩ := L.natCard_geometricPoints_torsionBy (Ω := Ω) hc hA d n hn
  have : Finite (Submodule.torsionBy ℤ (L.AlgPoints hc Ω) (n : ℤ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hΩ]
    exact pow_ne_zero _ hn0
  let m : Submodule.torsionBy ℤ (L.AlgPoints hc E) (n : ℤ) →
      Submodule.torsionBy ℤ (L.AlgPoints hc Ω) (n : ℤ) := fun y =>
    ⟨AlgPoints.map a y.1, by
      change (n : ℤ) • AlgPoints.map a y.1 = 0
      have hy : (n : ℤ) • y.1 = 0 := y.2
      rw [← map_zsmul, hy, map_zero]⟩
  have hm : Function.Injective m := by
    intro y z hyz
    apply Subtype.ext
    exact algPoints_map_injective_of_field L hc a (congrArg Subtype.val hyz)
  have hbij : Function.Bijective m := hm.bijective_of_nat_card_le (by rw [hΩ, hE])
  obtain ⟨y, hy⟩ := hbij.surjective ⟨x, hx⟩
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

open scoped Pointwise in
open AbelianVarieties.NOSProofs.ValuationInertiaLifting.ValuationSubring.InertiaLift in
private theorem inertia_restrictNormal_mem
    {K E Ω : Type u} [Field K] [Field E] [Field Ω]
    [Algebra K E] [Algebra K Ω] [Algebra E Ω] [IsScalarTower K E Ω] [Normal K E]
    (V : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ V.inertiaSubgroupIn K) :
    σ.restrictNormal E ∈ (V.comap (algebraMap E Ω)).inertiaSubgroupIn K := by
  let τ := σ.restrictNormal E
  have hcomm (x : E) : σ (algebraMap E Ω x) = algebraMap E Ω (τ x) :=
    (σ.restrictNormal_commutes E x).symm
  obtain ⟨hV, hdiff⟩ := smul_eq_of_mem_inertiaSubgroupIn V hσ
  apply mem_inertiaSubgroupIn_of
  · calc
      τ • V.comap (algebraMap E Ω) = (σ • V).comap (algebraMap E Ω) :=
        (comap_smul_of_commutes σ τ hcomm V).symm
      _ = V.comap (algebraMap E Ω) := congrArg (fun B => B.comap (algebraMap E Ω)) hV
  · intro x hx
    apply (algebraMap_mem_nonunits_iff (V.comap (algebraMap E Ω)) rfl (τ x - x)).mp
    rw [map_sub, ← hcomm]
    exact hdiff (algebraMap E Ω x) hx

/-- The NOS criterion for the actual Tate representation on points over a fixed
separable closure. The reverse direction transports finite torsion to the
algebraic closure through the canonical field embedding. -/
theorem hasGoodReduction_iff_unramified_separableClosure
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (SeparableClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) :
    L.HasGoodReduction R K ↔ W.inertiaSubgroupIn K ≤
      (TateModule.rep p (L.AlgPoints hc (SeparableClosure K))
        (SeparableClosure K ≃ₐ[K] SeparableClosure K)).ker := by
  constructor
  · intro hgood
    apply hgood.inertiaSubgroupIn_le_primePowerTateKer hc p hp W
    intro r
    rw [← W.valuation_le_one_iff,
      IsScalarTower.algebraMap_apply R K (SeparableClosure K),
      Valuation.HasExtension.val_map_le_one_iff (ValuationRing.valuation R K) W.valuation]
    exact (ValuationRing.mem_integer_iff R K _).mpr ⟨r, rfl⟩
  · intro hunr
    obtain ⟨V, hV⟩ :=
      (open AbelianVarieties.NOSProofs.ValuationInertiaLifting.ValuationSubring.InertiaLift in
        exists_comap_eq (E := AlgebraicClosure K) W)
    have : (ValuationRing.valuation R K).HasExtension V.valuation := ⟨by
      apply Valuation.isEquiv_of_val_le_one
      intro x
      change (ValuationRing.valuation R K) x ≤ 1 ↔
        V.valuation (algebraMap K (AlgebraicClosure K) x) ≤ 1
      rw [V.valuation_le_one_iff,
        IsScalarTower.algebraMap_apply K (SeparableClosure K) (AlgebraicClosure K)]
      change (ValuationRing.valuation R K) x ≤ 1 ↔
        algebraMap K (SeparableClosure K) x ∈ V.comap _
      rw [hV, ← W.valuation_le_one_iff,
        Valuation.HasExtension.val_map_le_one_iff (ValuationRing.valuation R K) W.valuation]⟩
    apply L.hasGoodReduction_of_inertiaSubgroupIn_le_primePowerTateKer V hc hA p hp
    have : Smooth f := hA.smooth
    obtain ⟨d, hd⟩ := L.exists_smoothOfRelativeDimension_of_smooth
    have hpΩ : (p : AlgebraicClosure K) ≠ 0 := by
      have h := hp.map (algebraMap R (AlgebraicClosure K))
      rw [map_natCast] at h
      exact h.ne_zero
    have hpE : (p : SeparableClosure K) ≠ 0 := by
      intro h
      apply hpΩ
      rw [← map_natCast (algebraMap (SeparableClosure K) (AlgebraicClosure K)) p, h, map_zero]
    let a : SeparableClosure K →ₐ[K] AlgebraicClosure K :=
      IsScalarTower.toAlgHom K (SeparableClosure K) (AlgebraicClosure K)
    have hcard (n : ℕ) :
        Nat.card (Submodule.torsionBy ℤ (L.AlgPoints hc (SeparableClosure K))
          ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ (2 * d) := by
      apply L.natCard_geometricPoints_torsionBy hc hA d (p ^ n)
      rw [Nat.cast_pow]
      exact pow_ne_zero n hpE
    intro σ hσ
    change TateModule.rep p (L.AlgPoints hc (AlgebraicClosure K))
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) σ = 1
    have hτ : σ.restrictNormal (SeparableClosure K) ∈ W.inertiaSubgroupIn K := by
      rw [← hV]
      exact inertia_restrictNormal_mem V σ hσ
    have hfixed := (TateModule.rep_eq_one_iff_forall_torsionBy
      (p := p) (2 * d) hcard (σ.restrictNormal (SeparableClosure K))).mp (hunr hτ)
    apply TateModule.rep_eq_one_of_forall_torsionBy
    intro n x hx
    obtain ⟨y, hy, hxy⟩ := geometricTorsion_map_surjective L hc hA d a (p ^ n)
      (by rw [Nat.cast_pow]; exact pow_ne_zero n hpΩ) x hx
    calc
      σ • x = σ • AlgPoints.map a y := congrArg (fun z => σ • z) hxy.symm
      _ = AlgPoints.map a (σ.restrictNormal (SeparableClosure K) • y) :=
        algPoints_map_equivariant_of_commutes L hc a σ
          (σ.restrictNormal (SeparableClosure K))
          (fun z => (σ.restrictNormal_commutes (SeparableClosure K) z).symm) y
      _ = AlgPoints.map a y := congrArg (AlgPoints.map a) (hfixed n y hy)
      _ = x := hxy

/-- The NOS criterion over a complete DVR, using the actual Tate representation
on points over its fixed separable closure. -/
theorem hasGoodReduction_iff_unramified_separableClosure_of_isAdicComplete
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (SeparableClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) :
    L.HasGoodReduction R K ↔ W.inertiaSubgroupIn K ≤
      (TateModule.rep p (L.AlgPoints hc (SeparableClosure K))
        (SeparableClosure K ≃ₐ[K] SeparableClosure K)).ker := by
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete R
  exact L.hasGoodReduction_iff_unramified_separableClosure W hc hA p hp

/-- Over a complete DVR, one unramified admissible Tate representation on
separable-closure points is equivalent to good reduction. -/
theorem hasGoodReduction_iff_exists_unramified_separableClosure_of_isAdicComplete
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (SeparableClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) :
    L.HasGoodReduction R K ↔ ∃ (p : ℕ) (hprime : p.Prime),
      let : Fact p.Prime := ⟨hprime⟩
      IsUnit (p : R) ∧ W.inertiaSubgroupIn K ≤
        (TateModule.rep p (L.AlgPoints hc (SeparableClosure K))
          (SeparableClosure K ≃ₐ[K] SeparableClosure K)).ker := by
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete R
  constructor
  · intro hgood
    obtain ⟨p, hprime, hp⟩ := exists_prime_isUnit R
    have : Fact p.Prime := ⟨hprime⟩
    refine ⟨p, hprime, hp, ?_⟩
    exact (L.hasGoodReduction_iff_unramified_separableClosure W hc hA p hp).mp hgood
  · rintro ⟨p, hprime, hp, hunr⟩
    have : Fact p.Prime := ⟨hprime⟩
    exact (L.hasGoodReduction_iff_unramified_separableClosure W hc hA p hp).mpr hunr

/-- Over a complete DVR, good reduction is equivalent to unramifiedness of the
Tate representations on separable-closure points for every admissible prime. -/
theorem hasGoodReduction_iff_forall_unramified_separableClosure_of_isAdicComplete
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : ValuationSubring (SeparableClosure K))
    [(ValuationRing.valuation R K).HasExtension W.valuation]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) :
    L.HasGoodReduction R K ↔ ∀ (p : ℕ) (hprime : p.Prime),
      let : Fact p.Prime := ⟨hprime⟩
      IsUnit (p : R) → W.inertiaSubgroupIn K ≤
        (TateModule.rep p (L.AlgPoints hc (SeparableClosure K))
          (SeparableClosure K ≃ₐ[K] SeparableClosure K)).ker := by
  have : HenselianLocalRing R := henselianLocalRing_of_isAdicComplete R
  constructor
  · intro hgood p hprime inst hp
    exact (L.hasGoodReduction_iff_unramified_separableClosure W hc hA p hp).mp hgood
  · intro hall
    obtain ⟨p, hprime, hp⟩ := exists_prime_isUnit R
    have : Fact p.Prime := ⟨hprime⟩
    exact (L.hasGoodReduction_iff_unramified_separableClosure W hc hA p hp).mpr
      (hall p hprime hp)

end GoodReductionJacobian.RelativeGroupLaw
