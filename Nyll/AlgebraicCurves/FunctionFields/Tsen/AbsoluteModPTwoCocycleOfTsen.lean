/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Tsen.GaloisH2OfTsen
import Nyll.GaloisCohomology.Kummer.FiniteKummerAbsoluteLift
import Nyll.GaloisCohomology.Topology.GaloisFiniteStageFunctions
import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
import Nyll.GaloisCohomology.Topology.FinitePGroupCoefficientVanishing
import Nyll.GaloisCohomology.Topology.ContinuousRestrictionEquiv
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
import Nyll.AlgebraicCurves.FunctionFields.Tsen.NormSurjectiveOfTsen
import Nyll.GaloisCohomology.Topology.ContinuousH2FiniteIndexTrace
import Nyll.GaloisCohomology.Topology.FiniteInvariantCoefficients
import Nyll.GaloisCohomology.Topology.FiniteCoefficientPrimeDevissage
import Nyll.GaloisCohomology.Topology.FiniteCoefficientCochains
import Nyll.GaloisCohomology.Topology.ContinuousCoinducedDimensionShift
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Continuous mod-p two-cocycle primitives over curve function fields

A continuous finite-valued cocycle descends to an actual finite Galois
intermediate field. Tsen supplies vanishing of its actual field-unit H²
class. The existing Hilbert-90 and Kummer correction gives a continuous
mod-p primitive on the absolute Galois group.

This proves an absolute-Galois statement. It does not assert the still
separate comparison with higher étale cohomology of a curve.
-/

open CategoryTheory
open scoped Topology

namespace AlgebraicCurve

open ClassFieldTower.Martinet.Shafarevich

/-- Every continuous mod-p two-cocycle on the actual absolute Galois
group of a characteristic-zero curve function field is a continuous
coboundary. No finite-stage norm or vanishing hypothesis is required. -/
theorem exists_continuous_modP_twoCocycle_primitive_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (c : C(Field.absoluteGaloisGroup F × Field.absoluteGaloisGroup F,
      ULift.{0} (ZMod (p : ℕ))))
    (hc : ∀ s t u : Field.absoluteGaloisGroup F,
      c (s * t, u) + c (s, t) = c (t, u) + c (s, t * u)) :
    ∃ a : C(Field.absoluteGaloisGroup F, ULift.{0} (ZMod (p : ℕ))),
      ∀ s t, a t + a s - a (s * t) = c (s, t) := by
  classical
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨E, cE, hfac⟩ :=
    GaloisCohomology.exists_finiteGalois_factor_continuous_pair
      (K := F) (Ω := AlgebraicClosure F) c c.continuous
  let r : Gal(AlgebraicClosure F/F) →* Gal(E/F) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective _
  have hcE (s t u : Gal(E/F)) :
      cE (s * t) u + cE s t = cE t u + cE s (t * u) := by
    obtain ⟨s', rfl⟩ := hr s
    obtain ⟨t', rfl⟩ := hr t
    obtain ⟨u', rfl⟩ := hr u
    rw [← map_mul r, ← map_mul r]
    change cE (AlgEquiv.restrictNormalHom E (s' * t'))
        (AlgEquiv.restrictNormalHom E u') +
      cE (AlgEquiv.restrictNormalHom E s') (AlgEquiv.restrictNormalHom E t') =
      cE (AlgEquiv.restrictNormalHom E t') (AlgEquiv.restrictNormalHom E u') +
      cE (AlgEquiv.restrictNormalHom E s')
        (AlgEquiv.restrictNormalHom E (t' * u'))
    rw [hfac, hfac, hfac, hfac]
    exact hc s' t' u'
  let z : groupCohomology.cocycles₂
      (Rep.trivial ℤ Gal(E/F) (ULift.{0} (ZMod (p : ℕ)))) :=
    ⟨fun st => cE st.1 st.2,
      (groupCohomology.mem_cocycles₂_iff _).mpr hcE⟩
  have hmu : (primitiveRoots (p : ℕ) F).Nonempty := by
    have : NeZero (p : ℕ) := ⟨p.ne_zero⟩
    obtain ⟨zeta, hzeta⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (p : ℕ)
    exact ⟨algebraMap K F zeta,
      (mem_primitiveRoots p.pos).mpr
        (hzeta.map_of_injective (algebraMap K F).injective)⟩
  let zu := groupCohomology.mapCocycles₂ (MonoidHom.id Gal(E/F))
    (finiteKummerCoefficientRepHom F E p hmu) z
  have hz : groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F E) zu = 0 :=
    galoisUnitsH2_eq_zero_of_transcendental_of_finiteDimensional K x hx hfin E _
  obtain ⟨b, hb⟩ : ∃ b : Gal(E/F) → Additive Eˣ,
      (groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits F E)).hom b = zu.1 :=
    (groupCohomology.H2π_eq_zero_iff zu).mp hz
  obtain ⟨a, ha⟩ := exists_absoluteZModP_primitive_of_finiteKummerUnit_boundary
    F p E hmu cE (fun s => (b s).toMul) (by
      intro s t
      have h := congrArg Additive.toMul (congrFun hb (s, t))
      change Units.map (s : E →* E) (b t).toMul / (b (s * t)).toMul * (b s).toMul =
        (finiteKummerCoefficientAddHom F E p hmu (cE s t)).toMul at h
      simpa only [div_mul_eq_mul_div] using h)
  refine ⟨a, ?_⟩
  intro s t
  rw [ha]
  exact hfac s t

/-- Actual continuous degree-two cohomology with trivial mod-p coefficients
vanishes for the absolute Galois group of the curve function field. -/
theorem absoluteGalois_continuousH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (v : ClassFieldTower.Cohomology.continuousCohomologyZModPLifted
      (p : ℕ) (Field.absoluteGaloisGroup F) 2) : v = 0 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace Gal(AlgebraicClosure F/F))
  exact TopRep.TrivialDegreeTwoCocycles.continuousH2_eq_zero_of_primitive
    (ClassFieldTower.Cohomology.trivialZModPLifted (p : ℕ)
      (Field.absoluteGaloisGroup F))
    (fun _ _ => rfl)
    (fun c hc =>
      exists_continuous_modP_twoCocycle_primitive_of_transcendental_of_finiteDimensional
        K x hx hfin p c hc) v

/-- Actual integral continuous degree-two cohomology with trivial mod-p
additive coefficients vanishes for the curve function field, using the
same geometric Tsen primitive as for finite-field scalar coefficients. -/
theorem absoluteGalois_integralContinuousH2_eq_zero_of_transcendental_of_finiteDimensional
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (v : continuousCohomology 2
      (ClassFieldTower.Cohomology.trivialIntegralZModPLifted
        (p : ℕ) (Field.absoluteGaloisGroup F))) : v = 0 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace Gal(AlgebraicClosure F/F))
  exact TopRep.TrivialDegreeTwoCocycles.continuousH2_eq_zero_of_primitive
    (ClassFieldTower.Cohomology.trivialIntegralZModPLifted (p : ℕ)
      (Field.absoluteGaloisGroup F))
    (fun _ _ => rfl)
    (fun c hc =>
      exists_continuous_modP_twoCocycle_primitive_of_transcendental_of_finiteDimensional
        K x hx hfin p c hc) v

/-- Geometric Tsen vanishing extends to actual finite mod-p integral
coefficients whose absolute Galois action image is a p-group. -/
theorem absoluteGalois_finiteIntegralH2_isZero_of_pGroup_image
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (X : TopRep.{0} ℤ (Field.absoluteGaloisGroup F))
    [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2))
    (hpX : ∀ v : X, (p : ℕ) • v = 0)
    (hρ : let _ : Module ℤ X := X.hV2
      IsPGroup (p : ℕ) X.ρ.toRepresentation.asGroupHom.range) :
    CategoryTheory.Limits.IsZero
      (((TopRep.continuousModuleComplexFunctor
        (Field.absoluteGaloisGroup F)).obj X).homology 2) := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : LocallyCompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (LocallyCompactSpace Gal(AlgebraicClosure F/F))
  apply TopRep.continuousModuleH2_isZero_of_pGroup_image
    (Field.absoluteGaloisGroup F) (p : ℕ) ?_ X hX hpX hρ
  apply TopRep.continuousModuleComplex_isZero_of_cohomology_eq_zero
  intro v
  exact absoluteGalois_integralContinuousH2_eq_zero_of_transcendental_of_finiteDimensional
    K x hx hfin p v

/-- Actual finite mod-p cohomology vanishes on an open function-field
Galois subgroup when the coefficient action image is a p-group. -/
theorem openAbsoluteGalois_finiteIntegralH2_eq_zero_of_pGroup_image
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (H : OpenSubgroup (Field.absoluteGaloisGroup F))
    (X : TopRep.{0} ℤ ↥(H : Subgroup (Field.absoluteGaloisGroup F)))
    [Finite X] [DiscreteTopology X]
    (hX : Continuous
      (fun gx : ↥(H : Subgroup (Field.absoluteGaloisGroup F)) × X =>
        X.ρ gx.1 gx.2))
    (hpX : ∀ v : X, (p : ℕ) • v = 0)
    (hρ : let _ : Module ℤ X := X.hV2
      IsPGroup (p : ℕ) X.ρ.toRepresentation.asGroupHom.range)
    (v : continuousCohomology 2 X) : v = 0 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨E, hE, ⟨e₀⟩⟩ :=
    KummerTheory.exists_finiteIntermediateField_openSubgroup_equiv H
  have : FiniteDimensional F E := hE
  let : Algebra K E := ((algebraMap F E).comp (algebraMap K F)).toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsAlgClosure E (AlgebraicClosure F) :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) E⟩
  let e : Field.absoluteGaloisGroup E ≃ₜ*
      ↥(H : Subgroup (Field.absoluteGaloisGroup F)) :=
    (e₀.trans (KummerTheory.absoluteGaloisClosureEquiv E (AlgebraicClosure F))).symm
  obtain ⟨y, hy, hyfin, _⟩ :=
    exists_separating_transcendental_over_finite_extension K x hx hfin E
  let Y : TopRep.{0} ℤ (Field.absoluteGaloisGroup E) :=
    TopRep.res e.toMonoidHom X
  have hY : Continuous
      (fun gy : Field.absoluteGaloisGroup E × Y => Y.ρ gy.1 gy.2) :=
    hX.comp (e.continuous.prodMap continuous_id)
  let : Module ℤ X := X.hV2
  have hρY : IsPGroup (p : ℕ) Y.ρ.toRepresentation.asGroupHom.range := by
    have hle : Y.ρ.toRepresentation.asGroupHom.range ≤
        X.ρ.toRepresentation.asGroupHom.range := by
      rintro a ⟨g, rfl⟩
      refine ⟨e g, ?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro z
      rfl
    exact hρ.of_injective (Subgroup.inclusion hle)
      (fun a b hab => Subtype.ext
        (congrArg (fun z : X.ρ.toRepresentation.asGroupHom.range =>
          (z : Units (Module.End ℤ X))) hab))
  have hzero := absoluteGalois_finiteIntegralH2_isZero_of_pGroup_image
    K y hy hyfin p Y hY hpX hρY
  let i := TopRep.continuousModuleHomologyIso (Field.absoluteGaloisGroup E) Y 2
  have hvanish (w : continuousCohomology 2 Y) : w = 0 := by
    have hid : 𝟙 (((TopRep.continuousModuleComplexFunctor
        (Field.absoluteGaloisGroup E)).obj Y).homology 2) = 0 :=
      hzero.eq_of_src _ _
    have hw : i.inv w = 0 :=
      CategoryTheory.ConcreteCategory.congr_hom hid (i.inv w)
    calc
      w = i.hom (i.inv w) :=
        (CategoryTheory.ConcreteCategory.congr_hom i.inv_hom_id w).symm
      _ = 0 := by rw [hw]; exact map_zero i.hom.hom
  apply ContinuousCohomology.restriction_equiv_injective e X 2
  exact (hvanish _).trans
    (map_zero (ContinuousCohomology.map
      (e : Field.absoluteGaloisGroup E →ₜ*
        ↥(H : Subgroup (Field.absoluteGaloisGroup F)))
      (𝟙 Y) 2).hom).symm

/-- Geometric Tsen vanishing for all actual finite integral coefficient
representations killed by p, with no restriction on their Galois action. -/
theorem absoluteGalois_finiteIntegralH2_eq_zero_of_tsen
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (p : ℕ+) [Fact (p : ℕ).Prime]
    (X : TopRep.{0} ℤ (Field.absoluteGaloisGroup F))
    [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2))
    (hpX : ∀ v : X, (p : ℕ) • v = 0)
    (v : continuousCohomology 2 X) : v = 0 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  let : Module ℤ X := X.hV2
  obtain ⟨H, hindex, hρ⟩ :=
    TopRep.exists_openSubgroup_primeToIndex_pGroup_image
      ℤ (Field.absoluteGaloisGroup F) X hX (p : ℕ)
  apply ContinuousCohomology.H2_eq_zero_of_primeToIndex_open_restriction
    X H (p : ℕ) hpX hindex ?_ v
  intro w
  exact openAbsoluteGalois_finiteIntegralH2_eq_zero_of_pGroup_image
    K x hx hfin p H (TopRep.res H.toSubgroup.subtype X)
    (hX.comp (continuous_subtype_val.prodMap continuous_id)) hpX hρ w

/-- Tsen vanishing in degree two for every actual finite discrete integral
coefficient representation of the function field's absolute Galois group. -/
theorem absoluteGalois_finiteContinuousModuleH2_isZero_of_tsen
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (X : TopRep.{0} ℤ (Field.absoluteGaloisGroup F))
    [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2)) :
    CategoryTheory.Limits.IsZero
      (((TopRep.continuousModuleComplexFunctor
        (Field.absoluteGaloisGroup F)).obj X).homology 2) := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  apply TopRep.continuousModuleH2_isZero_of_prime_coefficients
    (Field.absoluteGaloisGroup F) ?_ X hX
  intro p hp A hAfinite hAdiscrete hA hpA
  let q : ℕ+ := ⟨p, hp.out.pos⟩
  have : Fact (q : ℕ).Prime := ⟨hp.out⟩
  apply TopRep.continuousModuleComplex_isZero_of_cohomology_eq_zero
    (Field.absoluteGaloisGroup F) A 2
  exact absoluteGalois_finiteIntegralH2_eq_zero_of_tsen K x hx hfin
    q A hA hpA

/-- All continuous cohomology in degrees at least two vanishes for actual
discrete coefficients of bounded torsion over the function field.
The finite-coefficient and dimension-shifting steps use actual cochains. -/
theorem absoluteGalois_boundedContinuousModule_isZero_of_tsen
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (X : TopRep.{0} ℤ (Field.absoluteGaloisGroup F))
    [DiscreteTopology X]
    (hX : Continuous (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2))
    (m : ℤ) (hm0 : m ≠ 0) (hm : ∀ v : X, m • v = 0) (n : ℕ) :
    CategoryTheory.Limits.IsZero
      (((TopRep.continuousModuleComplexFunctor
        (Field.absoluteGaloisGroup F)).obj X).homology (n + 2)) := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have : CompactSpace (Field.absoluteGaloisGroup F) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure F/F))
  apply TopRep.continuousModule_isZero_of_degreeTwo
    (Field.absoluteGaloisGroup F) X m ?_ hX hm n
  intro Y hYdiscrete hY hmY
  apply TopRep.continuousModule_isZero_of_finite_coefficients
    (Field.absoluteGaloisGroup F) Y hY m hm0 hmY 1
  intro A hAfinite hAdiscrete hA _hmA
  exact absoluteGalois_finiteContinuousModuleH2_isZero_of_tsen K x hx hfin A hA

end AlgebraicCurve
