/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_lSpaceOn_setOf_centre_eq_span_integralClosure_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.LocalSections.LSpaceOnSetOfCentreEqSpanIntegralClosure
import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Places.ValuationRings.MemIntegralClosureIffPlace
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField

/-!
# LSpace On set Of centre eq span integral Closure mul
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.LSpaceOnSetOfCentreSpanIntegral
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise

open LSpaceOnSetOfExistsCentreSpan

namespace LocICAux

open IsLocalRing

theorem mem_of_isIntegral {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K] (v : Place k
  K)
    {A : Type u} [CommRing A] (φ : A →+* K) (hφ : ∀ s, φ s ∈ v.toValuationSubring) (f : K)
    (hf : letI := φ.toAlgebra; IsIntegral A f) : f ∈ v.toValuationSubring := by
  let := φ.toAlgebra
  obtain ⟨p, hp, hpf⟩ := hf
  let ψ : A →+* v.toValuationSubring := φ.codRestrict v.toValuationSubring hφ
  have hint : IsIntegral v.toValuationSubring f := by
    refine ⟨p.map ψ, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpf
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := v.toValuationSubring) (K := K)).mp hint
  rw [← hy]
  exact y.2

theorem isIso_stalkSpecializes_of_eq {X : TopCat.{u}} (P : TopCat.Presheaf CommRingCat.{u} X)
    {x y : X} (e : x = y) (h : x ⤳ y) : IsIso (P.stalkSpecializes h) := by
  subst e
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  infer_instance

theorem centred_fromSpec {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsIntegral C]
    {U : C.Opens} (hUaff : IsAffineOpen U) (hη : genericPoint C ∈ U) :
    letI := (baseToFunctionField c).toAlgebra
    ∀ (v : Place k C.functionField)
      (_hAv : ∀ s : Γ(C, U), (C.presheaf.germ U (genericPoint C) hη).hom s ∈ v.toValuationSubring)
      (y : PrimeSpectrum Γ(C, U))
      (_hy : ∀ s : Γ(C, U), s ∈ y.asIdeal ↔ v.adicValuation ((C.presheaf.germ U (genericPoint C)
        hη).hom s) < 1),
    ∀ t : C.presheaf.stalk (hUaff.fromSpec y),
      v.adicValuation (algebraMap (C.presheaf.stalk (hUaff.fromSpec y)) C.functionField t) ≤ 1 ∧
      (t ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk (hUaff.fromSpec y)) →
        v.adicValuation (algebraMap (C.presheaf.stalk (hUaff.fromSpec y)) C.functionField t) < 1)
          := by
  classical
  let := (baseToFunctionField c).toAlgebra
  intro v hAv y hy
  set A := (C.presheaf.germ U (genericPoint C) hη).hom with hAdef
  set z : C := hUaff.fromSpec y with hzdef
  have hzU : z ∈ U := by
    have : z ∈ Set.range hUaff.fromSpec := ⟨y, rfl⟩
    rwa [hUaff.range_fromSpec] at this
  let := C.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  have : IsLocalization.AtPrime (C.presheaf.stalk z) y.asIdeal := hUaff.isLocalization_stalk' y hzU
  have hφ : ∀ s : Γ(C, U), algebraMap (C.presheaf.stalk z) C.functionField (algebraMap Γ(C, U)
    (C.presheaf.stalk z) s) = A s :=
    fun s => by rw [hAdef, HoloICAux.germ_eq_algebraMap_germ U hη z hzU]; rfl
  have hvalle : ∀ s : Γ(C, U), v.adicValuation (A s) ≤ 1 := fun s =>
    (Place.mem_iff_adicValuation_le_one v).mp (hAv s)
  have hval1 : ∀ s : Γ(C, U), s ∉ y.asIdeal → v.adicValuation (A s) = 1 := by
    intro s hs
    rw [hy] at hs
    exact le_antisymm (hvalle s) (not_lt.mp hs)
  intro t
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl t
  have hs : (s : Γ(C, U)) ∉ y.asIdeal := s.2
  have heq : v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField (IsLocalization.mk'
    (C.presheaf.stalk z) a s)) =
      v.adicValuation (A a) := by
    have h1 := IsLocalization.mk'_spec (C.presheaf.stalk z) a s
    have h2 := congrArg (fun w => v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField
      w)) h1
    simp only [map_mul, hφ, hval1 s hs, mul_one] at h2
    exact h2
  refine ⟨heq ▸ hvalle a, fun ht => ?_⟩
  rw [heq, ← hy]
  exact (IsLocalization.AtPrime.mk'_mem_maximal_iff (C.presheaf.stalk z) y.asIdeal a s).mp ht

end LocICAux

theorem _root_.AlgebraicCurve.lSpaceOn_setOf_centre_eq_span_integralClosure_mul
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (hpts : ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C))
    (U : C.Opens) [Nonempty U] (hUaff : IsAffineOpen U)
    (z : C) (hzU : z ∈ U) (hz : IsClosed ({z} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 :
              Divisor k C.functionField) =
      Submodule.span k ((integralClosure Γ(C, U) C.functionField : Set C.functionField) *
        Set.range (algebraMap (C.presheaf.stalk z) C.functionField)) := by
  classical
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have : IsCurveOver k C.functionField := hK
  have : PerfectField k := inferInstance
  have := AlgebraicCurve.essFiniteType_functionField c
  have hη : genericPoint C ∈ U := ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
    (by simpa only [Set.univ_inter] using (Set.nonempty_coe_sort.mp ‹Nonempty U›))
  set A : Γ(C, U) →+* C.functionField := algebraMap Γ(C, U) C.functionField with hAdef
  have hA : ∀ s, A s = (C.presheaf.germ U (genericPoint C) hη).hom s := fun s => rfl
  set φ : C.presheaf.stalk z →+* C.functionField := algebraMap (C.presheaf.stalk z)
    C.functionField with hφdef
  let 𝔭 : Ideal Γ(C, U) := (hUaff.primeIdealOf ⟨z, hzU⟩).asIdeal
  let := C.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  have : IsScalarTower Γ(C, U) (C.presheaf.stalk z) C.functionField :=
    AlgebraicGeometry.functionField_isScalarTower (U := U) (x := ⟨z, hzU⟩)
  have : IsLocalization.AtPrime (C.presheaf.stalk z) 𝔭 := hUaff.isLocalization_stalk ⟨z, hzU⟩
  have hφA : ∀ s : Γ(C, U), φ (algebraMap Γ(C, U) (C.presheaf.stalk z) s) = A s :=
    fun s => by rw [hA, HoloICAux.germ_eq_algebraMap_germ U hη z hzU]; rfl
  have hconst : ∀ a : k, ∃ t : C.presheaf.stalk z, algebraMap k C.functionField a = φ t := fun a =>
    ⟨algebraMap Γ(C, U) (C.presheaf.stalk z) ((c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso
      (CommRingCat.of k)).inv.hom a)), by
      rw [hφA, hA]; exact HoloICAux.algebraMap_eq_germ c U hη a⟩
  have hOv : ∀ v : Place k C.functionField, (∀ s : C.presheaf.stalk z,
        v.adicValuation (φ s) ≤ 1 ∧ (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
          v.adicValuation (φ s) < 1)) →
      (∀ t, φ t ∈ v.toValuationSubring) ∧ (∀ s : Γ(C, U), A s ∈ v.toValuationSubring) := by
    intro v hv
    have h1 : ∀ t, φ t ∈ v.toValuationSubring :=
      fun t => (Place.mem_iff_adicValuation_le_one v).mpr (hv t).1
    exact ⟨h1, fun s => hφA s ▸ h1 _⟩
  apply le_antisymm
  · intro f hf
    rw [AlgebraicCurve.mem_lSpaceOn_iff] at hf
    let Oz : Subalgebra k C.functionField :=
      { φ.range with
        algebraMap_mem' := fun a => by
          obtain ⟨t, ht⟩ := hconst a
          exact ⟨t, ht.symm⟩ }
    have hdomOf : ∀ v : Place k C.functionField, (∀ t, φ t ∈ v.toValuationSubring) →
        ∀ s : C.presheaf.stalk z, v.adicValuation (φ s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) → v.adicValuation (φ s) < 1) := by
      intro v hφv
      have hAv : ∀ s : Γ(C, U), (C.presheaf.germ U (genericPoint C) hη).hom s ∈
        v.toValuationSubring :=
        fun s => hA s ▸ hφA s ▸ hφv _
      let ψ : Γ(C, U) →+* v.toValuationSubring := A.codRestrict v.toValuationSubring (fun s => hA
        s ▸ hAv s)
      let 𝔮 : Ideal Γ(C, U) := Ideal.comap ψ (IsLocalRing.maximalIdeal v.toValuationSubring)
      have : 𝔮.IsPrime := Ideal.comap_isPrime _ _
      let y : PrimeSpectrum Γ(C, U) := ⟨𝔮, inferInstance⟩
      have hy : ∀ s : Γ(C, U), s ∈ y.asIdeal ↔ v.adicValuation ((C.presheaf.germ U (genericPoint
        C) hη).hom s) < 1 := by
        intro s
        rw [← hA, show A s = ((ψ s : v.toValuationSubring) : C.functionField) from rfl,
          v.adicValuation_coe,
          IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem,
            Place.heightOneSpectrum_asIdeal]
        rfl
      have hdom' := LocICAux.centred_fromSpec c hUaff hη v hAv y hy
      have hle : y ≤ hUaff.primeIdealOf ⟨z, hzU⟩ := by
        intro s hs
        by_contra hs𝔭
        have hu : IsUnit (algebraMap Γ(C, U) (C.presheaf.stalk z) s) :=
          IsLocalization.map_units (C.presheaf.stalk z) (⟨s, hs𝔭⟩ : 𝔭.primeCompl)
        have h1 : φ (↑(hu.unit⁻¹) : C.presheaf.stalk z) * A s = 1 := by
          rw [← hφA, ← map_mul, IsUnit.val_inv_mul, map_one]
        have hAs0 : A s ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
        have hinv : (A s)⁻¹ ∈ v.toValuationSubring := by
          rw [inv_eq_of_mul_eq_one_left h1]
          exact hφv _
        have hone : v.adicValuation (A s) = 1 := by
          have hm : A s ∈ v.toValuationSubring := hA s ▸ hAv s
          rw [show A s = ((⟨A s, hm⟩ : v.toValuationSubring) : C.functionField) from rfl,
            v.adicValuation_coe_eq_one_iff]
          exact isUnit_iff_exists_inv.mpr ⟨⟨(A s)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hAs0)⟩
        have hlt := (hy s).mp hs
        rw [← hA, hone] at hlt
        exact lt_irrefl _ hlt
      have hspec : hUaff.fromSpec y ⤳ z := by
        have h1 : y ⤳ hUaff.primeIdealOf ⟨z, hzU⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hle
        have h2 := h1.map hUaff.fromSpec.base.hom.continuous
        rwa [show hUaff.fromSpec.base.hom (hUaff.primeIdealOf ⟨z, hzU⟩) = z from
          hUaff.fromSpec_primeIdealOf ⟨z, hzU⟩] at h2
      rcases hpts (hUaff.fromSpec y) with h | h
      · exfalso
        apply v.ne_top'
        refine eq_top_iff.mpr fun g _ => (Place.mem_iff_adicValuation_le_one v).mpr ?_
        have hsurj : Function.Surjective (algebraMap (C.presheaf.stalk (hUaff.fromSpec y))
          C.functionField) := by
          change Function.Surjective (C.presheaf.stalkSpecializes ((genericPoint_spec
            C).specializes trivial)).hom
          have := LocICAux.isIso_stalkSpecializes_of_eq C.presheaf h.symm
            ((genericPoint_spec C).specializes (trivial : hUaff.fromSpec y ∈ (⊤ : Set C)))
          exact (asIso (C.presheaf.stalkSpecializes
            ((genericPoint_spec C).specializes (trivial : hUaff.fromSpec y ∈ (⊤ : Set
              C))))).commRingCatIsoToRingEquiv.surjective
        obtain ⟨t, rfl⟩ := hsurj g
        exact (hdom' t).1
      · have hzz : z = hUaff.fromSpec y := by
          have : z ∈ closure ({hUaff.fromSpec y} : Set C) := specializes_iff_mem_closure.mp hspec
          rwa [h.closure_eq, Set.mem_singleton_iff] at this
        clear_value φ
        subst hzz
        simpa only [hφdef] using hdom'
    have hint : f ∈ integralClosure Oz C.functionField := by
      rw [AlgebraicCurve.mem_integralClosure_iff_forall_place Oz f]
      intro v hOzv
      have hφv : ∀ t, φ t ∈ v.toValuationSubring := fun t => hOzv ⟨t, rfl⟩
      have := hf v (hdomOf v hφv)
      simp only [Finsupp.zero_apply, WithZero.exp_zero] at this
      exact (Place.mem_iff_adicValuation_le_one v).mpr this
    have hint' : IsIntegral (C.presheaf.stalk z) f := by
      have h1 := (HoloICAux.isIntegral_iff_isIntegral_range φ f).mpr hint
      exact h1
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization 𝔭.primeCompl f hint'
    have hsm : m • f = A m * f := by rw [Submonoid.smul_def, Algebra.smul_def]
    rw [hsm] at hm
    have hu : IsUnit (algebraMap Γ(C, U) (C.presheaf.stalk z) m) := IsLocalization.map_units
      (C.presheaf.stalk z) m
    have h1 : φ (↑(hu.unit⁻¹) : C.presheaf.stalk z) * A m = 1 := by
      rw [← hφA, ← map_mul, IsUnit.val_inv_mul, map_one]
    have hf' : f = (A m * f) * φ (↑(hu.unit⁻¹) : C.presheaf.stalk z) := by
      rw [mul_comm (A m) f, mul_assoc, mul_comm (A m), h1, mul_one]
    rw [hf']
    exact Submodule.subset_span (Set.mul_mem_mul hm ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, hb, _, ⟨t, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, AlgebraicCurve.mem_lSpaceOn_iff]
    intro v hv
    simp only [Finsupp.zero_apply, WithZero.exp_zero]
    obtain ⟨hφv, hAv⟩ := hOv v hv
    rw [← Place.mem_iff_adicValuation_le_one]
    refine mul_mem ?_ (hφv t)
    exact LocICAux.mem_of_isIntegral v A hAv b hb
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.LSpaceOnSetOfCentreSpanIntegral
end ProofImplementation
