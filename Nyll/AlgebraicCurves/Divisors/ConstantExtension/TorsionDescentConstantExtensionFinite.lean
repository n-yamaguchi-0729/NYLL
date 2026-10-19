/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantDescent
import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.Places.ConstantExtension.ComapAlgebraMapEqConstantExtension
import Nyll.AlgebraicCurves.Divisors.ConstantExtension.PrincipalConstantExtension
import Nyll.AlgebraicCurves.Places.Orders.OrdNegTranscendental
import Nyll.SchemeTheory.FunctionFields.AlgClosedAlgEquivApplyEqAddAlgebraMap
import Nyll.AlgebraicCurves.Divisors.Semilinear.BaseAutEqConstantExtension

/-!
# Divisor exists torsion descent of constant Field Extension of finite
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
attribute [-simp] AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open _root_.AlgebraicCurve
open scoped Pointwise

namespace AlgebraicCurve
open _root_.AlgebraicCurve

namespace TorsionDescentFin

open _root_.AlgebraicCurve.Divisor _root_.AlgebraicCurve.ConstantDescent

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_smul_eq (g : SemilinearAut K F) (w : Place K F) (f : F) :
    w.ord (g • f) = (g⁻¹ • w).ord f := by
  conv_lhs => rw [← smul_inv_smul g w]
  exact SemilinearAut.ord_smul g (g⁻¹ • w) f

theorem smul_divOf [HasPrincipalDivisors K F] (g : SemilinearAut K F) (f : F) :
    g • divOf (K := K) f = divOf (g • f) := by
  by_cases hf : f = 0
  · subst hf
    rw [smul_zero, divOf_zero, smul_zero]
  have hgf : g • f ≠ 0 := by
    intro h
    exact hf ((smul_eq_zero_iff_eq g).mp h)
  ext w
  rw [SemilinearAut.divisor_smul_apply, divOf_apply hf, divOf_apply hgf, ord_smul_eq]

theorem pow_smul_eq_self {α : Type*} [MulAction (SemilinearAut K F) α] {g : SemilinearAut K F}
    {a : α} (h : g • a = a) (k : ℕ) : g ^ k • a = a := by
  induction k with
  | zero => rw [pow_zero, one_smul]
  | succ k ih => rw [pow_succ, mul_smul, h, ih]

theorem smul_zsmul_divisor (g : SemilinearAut K F) (m : ℤ) (D : Divisor K F) :
    g • (m • D) = m • (g • D) :=
  (DistribSMul.toAddMonoidHom (Divisor K F) g).map_zsmul m D

theorem smul_mem_lSpace_iff (g : SemilinearAut K F) {D : Divisor K F} {y : F} :
    g • y ∈ LSpace (g • D) ↔ y ∈ LSpace D := by
  rw [mem_lSpace_iff_ord, mem_lSpace_iff_ord, smul_eq_zero_iff_eq]
  refine or_congr Iff.rfl ⟨fun h v => ?_, fun h w => ?_⟩
  · have := h (g • v)
    rwa [SemilinearAut.divisor_smul_apply_smul, SemilinearAut.ord_smul] at this
  · rw [SemilinearAut.divisor_smul_apply, ord_smul_eq]
    exact h _

theorem smul_reduced_eq [HasPrincipalDivisors K F] (g : SemilinearAut K F)
    {c : Divisor K F} {r : ℤ} {P : Place K F} {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ LSpace (c + r • Finsupp.single P 1))
    (huniq : ∀ h ∈ LSpace (c + r • Finsupp.single P 1), ∃ a : K, a • f = h)
    (hP : g • P = P) (hc : g • c - c ∈ Divisor.principal) :
    g • (c + r • Finsupp.single P 1 + divOf f) = c + r • Finsupp.single P 1 + divOf f := by
  obtain ⟨u, hu0, hu⟩ := mem_principal_iff_eq_divOf.mp hc
  set D := c + r • Finsupp.single P 1 with hD
  have hgc : g • c = c + divOf u := by rw [← hu]; abel
  have hgD : g • D = D + divOf u := by
    simp only [hD, smul_add, smul_zsmul_divisor, SemilinearAut.smul_single, hP, hgc]
    abel
  have h1 : g • f ∈ LSpace (g • D) := (smul_mem_lSpace_iff g).mpr hf
  rw [hgD, mem_lSpace_add_divOf_iff hu0] at h1
  obtain ⟨a, ha⟩ := huniq _ h1
  have hgf : g • f ≠ 0 := fun h => hf0 ((smul_eq_zero_iff_eq g).mp h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact mul_ne_zero hgf hu0 ha.symm
  rw [smul_add, hgD, smul_divOf, add_assoc, add_comm (divOf u), ← divOf_mul hgf hu0, ← ha,
    divOf_smul_const ha0]

end General

section Extension

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra F F']

/-- The condition that a semilinear automorphism fixes the image of the original function
field. -/
def FixesF (F : Type*) [Field F] [Algebra F F'] (g : SemilinearAut K' F') : Prop :=
  ∀ y : F, g • algebraMap F F' y = algebraMap F F' y

namespace FixesF

variable {g h : SemilinearAut K' F'}

theorem one : FixesF F (1 : SemilinearAut K' F') := fun _ => one_smul _ _

theorem mul (hg : FixesF F g) (hh : FixesF F h) : FixesF F (g * h) := fun y => by
  rw [mul_smul, hh y, hg y]

theorem inv (hg : FixesF F g) : FixesF F g⁻¹ := fun y => by
  rw [inv_smul_eq_iff, hg y]

theorem pow (hg : FixesF F g) (k : ℕ) : FixesF F (g ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact one
  | succ k ih => rw [pow_succ]; exact ih.mul hg

theorem comap_smul (hg : FixesF F g) (w' : Place K' F') :
    (g • w').toValuationSubring.comap (algebraMap F F') =
      w'.toValuationSubring.comap (algebraMap F F') := by
  ext y
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    hg.inv y]

theorem liesOver_smul_iff (hg : FixesF F g) {w' : Place K' F'} {v : Place K F} :
    LiesOver (g • w') v ↔ LiesOver w' v := by
  rw [LiesOver, LiesOver, hg.comap_smul]

theorem isGeneric_smul_iff (hg : FixesF F g) {w' : Place K' F'} :
    IsGeneric K F (g • w') ↔ IsGeneric K F w' := by
  simp only [IsGeneric, hg.liesOver_smul_iff]

theorem smul_eq_of_liesOver (hg : FixesF F g)
    (hU : ∀ (v : Place K F) (w₁ w₂ : Place K' F'), LiesOver w₁ v → LiesOver w₂ v → w₁ = w₂)
    {w' : Place K' F'} {v : Place K F} (hw : LiesOver w' v) : g • w' = w' :=
  hU v _ _ (hg.liesOver_smul_iff.mpr hw) hw

end FixesF

theorem injective_pow_smul [CharZero K'] (g : SemilinearAut K' F') (w : Place K' F') (y : F')
    (hy : InMax w y) (hg : ∀ k : ℕ, g ^ k • y = y - algebraMap K' F' k) :
    Function.Injective fun k : ℕ => g ^ k • w := by
  intro i j hij
  simp only at hij
  have hi : InMax (g ^ i • w) (y - algebraMap K' F' i) := by
    rw [← hg i]; exact (InMax.smul_iff _).mpr hy
  have hj : InMax (g ^ i • w) (y - algebraMap K' F' j) := by
    rw [hij, ← hg j]; exact (InMax.smul_iff _).mpr hy
  have h := hi.sub hj
  rw [show y - algebraMap K' F' (i : K') - (y - algebraMap K' F' (j : K')) =
      algebraMap K' F' ((j : K') - i) by rw [map_sub]; ring] at h
  have := h.eq_zero_of_algebraMap
  exact_mod_cast (sub_eq_zero.mp this).symm

theorem pow_smul_sub_algebraMap (ρ : SemilinearAut K' F') {X : F'} (hX : ρ • X = X) {t a : K'}
    (ht : SemilinearAut.baseAut ρ t = t + a) (ha : SemilinearAut.baseAut ρ a = a) (m : ℕ) :
    ρ ^ m • (X - algebraMap K' F' t) = X - algebraMap K' F' t - algebraMap K' F' (m * a) := by
  induction m with
  | zero => rw [pow_zero, one_smul, Nat.cast_zero, zero_mul, map_zero, sub_zero]
  | succ m ih =>
    rw [pow_succ', mul_smul, ih, smul_sub, smul_sub, hX, SemilinearAut.smul_algebraMap,
      SemilinearAut.smul_algebraMap, ht, map_mul, ha, map_natCast]
    push_cast
    ring

end Extension

section Pigeonhole

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem pow_mul_smul_sub_mem_principal (g : SemilinearAut K F) (D : Divisor K F) (m : ℕ)
    (h : g ^ m • D - D ∈ Divisor.principal) (q : ℕ) :
    g ^ (m * q) • D - D ∈ Divisor.principal := by
  induction q with
  | zero =>
      rw [Nat.mul_zero, pow_zero, one_smul, sub_self]
      exact zero_mem Divisor.principal
  | succ q ih =>
    have heq : g ^ (m * (q + 1)) • D - D = g ^ m • (g ^ (m * q) • D - D) + (g ^ m • D - D) := by
      rw [Nat.mul_succ, pow_add, pow_mul_comm, mul_smul, smul_sub]
      abel
    rw [heq]
    exact add_mem (SemilinearAut.smul_mem_principal _ ih) h

theorem pow_factorial_smul_sub_mem_principal (g : SemilinearAut K F) (D : Divisor K F) (n : ℕ)
    [Finite {c : Pic0 K F // n • c = 0}]
    (hdeg : ∀ k : ℕ, Divisor.degree (g ^ k • D - D) = 0)
    (htor : ∀ k : ℕ, n • (g ^ k • D - D) ∈ Divisor.principal) :
    g ^ (Nat.card {c : Pic0 K F // n • c = 0}).factorial • D - D ∈ Divisor.principal := by
  classical
  set M := Nat.card {c : Pic0 K F // n • c = 0} with hM
  let dz : ℕ → Divisor.degZero (K := K) (F := F) := fun k =>
    ⟨g ^ k • D - D, Divisor.mem_degZero.mpr (hdeg k)⟩
  have hcl0 : ∀ k, n • (Pic0.mk (dz k)) = 0 := fun k => by
    change n • (QuotientAddGroup.mk (dz k) : Pic0 K F) = 0
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact htor k
  let cl : Fin (M + 1) → {c : Pic0 K F // n • c = 0} := fun i => ⟨Pic0.mk (dz i), hcl0 i⟩
  have hnotinj : ¬ Function.Injective cl := by
    intro hinj
    have h := Nat.card_le_card_of_injective cl hinj
    rw [← hM, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    omega
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hnotinj
  have hstep : ∀ a m : ℕ, Pic0.mk (dz a) = Pic0.mk (dz (a + m)) →
      g ^ m • D - D ∈ Divisor.principal := by
    intro a m h
    have h2 : -(dz a) + dz (a + m) ∈ (Divisor.principal).addSubgroupOf Divisor.degZero :=
      QuotientAddGroup.eq.mp h
    have h3 : -(g ^ a • D - D) + (g ^ (a + m) • D - D) ∈ Divisor.principal (K := K) (F := F) :=
      AddSubgroup.mem_addSubgroupOf.mp h2
    rw [pow_add] at h3
    have h4 : (g ^ a)⁻¹ • (-(g ^ a • D - D) + ((g ^ a * g ^ m) • D - D)) = g ^ m • D - D := by
      rw [mul_smul, smul_add, smul_neg, smul_sub, smul_sub, inv_smul_smul, inv_smul_smul]
      abel
    exact h4 ▸ SemilinearAut.smul_mem_principal _ h3
  have hij' : Pic0.mk (dz i) = Pic0.mk (dz j) := congrArg Subtype.val hij
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  obtain ⟨m, hm0, hmM, hm⟩ : ∃ m : ℕ, 0 < m ∧ m ≤ M ∧ g ^ m • D - D ∈ Divisor.principal := by
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_, hstep i (j - i) ?_⟩
      · have := j.isLt; omega
      · rw [Nat.add_sub_cancel' hlt.le]; exact hij'
    · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_, hstep j (i - j) ?_⟩
      · have := i.isLt; omega
      · rw [Nat.add_sub_cancel' hlt.le]; exact hij'.symm
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hm0 hmM
  rw [hq]
  exact pow_mul_smul_sub_mem_principal g D m hm q

end Pigeonhole

section Main

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem main [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (_hn : n ≠ 0) [Finite {c : Pic0 K' F' // n • c = 0}] (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') := by
  classical
  obtain ⟨x, hx, hxfd⟩ := id hfg
  obtain ⟨x', hx', hxfd'⟩ := id hfg'
  have := hxfd
  have := hxfd'
  have : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  obtain ⟨g', hg'0, hg'⟩ := hD'
  have hnD' : (n : ℤ) • D' = divOf g' := by
    ext w
    rw [Finsupp.smul_apply, smul_eq_mul, hg' w, divOf_apply hg'0]
  set N : ℕ := (Nat.card {c : Pic0 K' F' // n • c = 0}).factorial with hN_def
  have hN : N ≠ 0 := Nat.factorial_ne_zero _
  have hlift := Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F K' F' hfg hfg' hgen
  choose lift hliftOver hliftOrd hliftUniq using hlift
  have hU : ∀ (v : Place K F) (w₁ w₂ : Place K' F'), LiesOver w₁ v → LiesOver w₂ v → w₁ = w₂ :=
    fun v w₁ w₂ h₁ h₂ => (hliftUniq v w₁ h₁).trans (hliftUniq v w₂ h₂).symm
  have hV : ∀ (w' : Place K' F') (v₁ v₂ : Place K F), LiesOver w' v₁ → LiesOver w' v₂ → v₁ = v₂ :=
    fun w' v₁ v₂ h₁ h₂ => Place.ext (h₁.symm.trans h₂)
  obtain ⟨P, -⟩ := Place.exists_ord_neg_of_transcendental x hx
  set P₀ : Place K' F' := lift P with hP₀
  have hP₀ : LiesOver P₀ P := hliftOver P
  have hdegP₀ : P₀.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P₀
  have hEfix : ∀ g : SemilinearAut K' F', FixesF F g → g ^ N • D' - D' ∈ Divisor.principal := by
    intro g _
    refine pow_factorial_smul_sub_mem_principal g D' n (fun k => ?_) (fun k => ?_)
    · rw [map_sub, SemilinearAut.degree_smul, sub_self]
    · have hgk : g ^ k • g' ≠ 0 := fun h => hg'0 ((smul_eq_zero_iff_eq _).mp h)
      refine mem_principal_iff_eq_divOf.mpr ⟨g ^ k • g' * g'⁻¹, mul_ne_zero hgk (inv_ne_zero hg'0),
        ?_⟩
      rw [← natCast_zsmul, smul_sub, ← smul_zsmul_divisor, hnD', smul_divOf,
        divOf_mul hgk (inv_ne_zero hg'0), divOf_inv]
      abel
  set d : ℤ := Divisor.degree D' with hd
  set c₀ : Divisor K' F' := D' - d • Finsupp.single P₀ 1 with hc₀
  have hc₀deg : Divisor.degree c₀ = 0 := by
    simp only [hc₀, map_sub, map_zsmul, Divisor.degree_single, hdegP₀, Nat.cast_one, mul_one,
      smul_eq_mul, hd]
    ring
  obtain ⟨r, fr, hfr0, hfrmem, hfruniq⟩ := exists_reduced (K := K') (F := F') x' hx' c₀ hc₀deg P₀
  set A : Divisor K' F' := c₀ + (r : ℤ) • Finsupp.single P₀ 1 + divOf fr with hA
  have hAfix : ∀ g : SemilinearAut K' F', FixesF F g → g ^ N • A = A := by
    intro g hg
    have hgP : g ^ N • P₀ = P₀ := (hg.pow N).smul_eq_of_liesOver hU hP₀
    apply smul_reduced_eq (g ^ N) hfr0 hfrmem hfruniq hgP
    have : g ^ N • c₀ - c₀ = g ^ N • D' - D' := by
      simp only [hc₀, smul_sub, smul_zsmul_divisor, SemilinearAut.smul_single, hgP]
      abel
    rw [this]
    exact hEfix g hg
  have hAsupp : ∀ w' ∈ A.support, ¬ IsGeneric K F w' := by
    intro w' hw' hgw
    obtain ⟨t, ht⟩ := hgw.exists_inMax_sub x
    have htK : t ∉ Set.range (algebraMap K K') := hgw.not_mem_range x hx ht
    have httr : Transcendental K t := transcendental_of_not_mem_range htK
    obtain ⟨τ, hτ⟩ := IsAlgClosed.exists_algEquiv_apply_eq_add_algebraMap_of_transcendental K K' t
      httr (N : K)⁻¹
    obtain ⟨ρ, hρτ, hρF⟩ :=
      SemilinearAut.exists_baseAut_eq_of_constantFieldExtension K F K' F' hfg hfg' hgen τ
    set σ := ρ ^ N with hσ
    have hσA : σ • A = A := hAfix ρ hρF
    set y : F' := algebraMap F F' x - algebraMap K' F' t with hy
    have hρt : SemilinearAut.baseAut ρ t = t + algebraMap K K' (N : K)⁻¹ := by rw [hρτ, hτ]
    have hρa : SemilinearAut.baseAut ρ (algebraMap K K' (N : K)⁻¹) = algebraMap K K' (N : K)⁻¹ := by
      rw [hρτ, AlgEquiv.commutes]
    have hρm : ∀ m : ℕ, ρ ^ m • y = y - algebraMap K' F' (m * algebraMap K K' (N : K)⁻¹) :=
      fun m => pow_smul_sub_algebraMap ρ (hρF x) hρt hρa m
    have hNK' : (N : K') ≠ 0 := Nat.cast_ne_zero.mpr hN
    have hσy : ∀ k : ℕ, σ ^ k • y = y - algebraMap K' F' k := by
      intro k
      rw [hσ, ← pow_mul, hρm (N * k)]
      congr 2
      rw [map_inv₀, map_natCast]
      push_cast
      field_simp
    have hinj := injective_pow_smul σ w' y ht hσy
    have hmem : ∀ k : ℕ, σ ^ k • w' ∈ (A.support : Set (Place K' F')) := by
      intro k
      have hk : σ ^ k • A = A := pow_smul_eq_self hσA k
      rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hk, SemilinearAut.divisor_smul_apply_smul]
      exact Finsupp.mem_support_iff.mp hw'
    exact Set.infinite_of_injective_forall_mem hinj hmem (A.support.finite_toSet)
  set B : Divisor K' F' := A + (d - r) • Finsupp.single P₀ 1 with hB
  have hBsupp : ∀ w' ∈ B.support, ∃ v : Place K F, LiesOver w' v := by
    intro w' hw'
    rcases Finset.mem_union.mp (Finsupp.support_add hw') with h | h
    · have := hAsupp w' h
      simp only [IsGeneric, not_forall, not_not] at this
      exact this
    · have h2 := Finsupp.support_smul h
      rw [Finsupp.mem_support_single] at h2
      exact ⟨P, h2.1 ▸ hP₀⟩
  have hD'B : D' = B + divOf fr⁻¹ := by
    rw [divOf_inv]
    simp only [hB, hA, hc₀, sub_smul]
    abel
  let π : Place K' F' → Place K F := fun w' =>
    if h : ∃ v : Place K F, LiesOver w' v then h.choose else P
  have hπ : ∀ (w' : Place K' F') (v : Place K F), LiesOver w' v → π w' = v := by
    intro w' v h
    have hex : ∃ v : Place K F, LiesOver w' v := ⟨v, h⟩
    simp only [π, dite_eq_left hex]
    exact hV w' _ _ hex.choose_spec h
  set R₀ : Divisor K F := Finsupp.mapDomain π B with hR₀
  have hR₀v : ∀ v : Place K F, R₀ v = B (lift v) := by
    intro v
    have hS : ((B.support : Finset (Place K' F')) : Set (Place K' F')) ⊆
        {w' : Place K' F' | ∃ v : Place K F, LiesOver w' v} := fun w' hw' => hBsupp w' hw'
    have hinjOn : Set.InjOn π {w' : Place K' F' | ∃ v : Place K F, LiesOver w' v} := by
      rintro w₁ ⟨v₁, h₁⟩ w₂ ⟨v₂, h₂⟩ heq
      rw [hπ w₁ v₁ h₁, hπ w₂ v₂ h₂] at heq
      subst heq
      exact hU v₁ w₁ w₂ h₁ h₂
    have := Finsupp.mapDomain_apply' _ B hS hinjOn (a := lift v) ⟨v, hliftOver v⟩
    rwa [hπ (lift v) v (hliftOver v)] at this
  have hB0 : ∀ w' : Place K' F', (∀ v : Place K F, ¬ LiesOver w' v) → B w' = 0 := by
    intro w' hw'
    by_contra hne
    obtain ⟨v, hv⟩ := hBsupp w' (Finsupp.mem_support_iff.mpr hne)
    exact hw' v hv
  have hprin : ((n : ℤ) • R₀).IsPrincipal := by
    apply Divisor.isPrincipal_of_constantFieldExtension K F K' F' hfg hfg' hgen
      ((n : ℤ) • R₀) ((n : ℤ) • B)
    · intro w' v hw'v
      have hw : w' = lift v := hU v w' (lift v) hw'v (hliftOver v)
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [hR₀v v, hw]
    · intro w' hw'
      simp only [Finsupp.smul_apply, smul_eq_mul, hB0 w' hw', mul_zero]
    · refine isPrincipal_iff_eq_divOf.mpr ⟨g' * fr ^ n, mul_ne_zero hg'0 (pow_ne_zero _ hfr0), ?_⟩
      rw [divOf_mul hg'0 (pow_ne_zero _ hfr0), divOf_pow, ← hnD']
      have : B = D' + divOf fr := by
        rw [hD'B, divOf_inv]
        abel
      rw [this, smul_add]
  obtain ⟨g, hg0, hg⟩ := hprin
  refine ⟨R₀, fr⁻¹, inv_ne_zero hfr0, ⟨g, hg0, fun v => ?_⟩, fun v v' hv' => ?_, fun v' hv' => ?_⟩
  · have := hg v
    simpa only [Finsupp.smul_apply, smul_eq_mul] using this
  · have hw : v' = lift v := hU v v' (lift v) hv' (hliftOver v)
    rw [hD'B, Finsupp.add_apply, divOf_apply (inv_ne_zero hfr0), hw, hR₀v v]
  · rw [hD'B, Finsupp.add_apply, divOf_apply (inv_ne_zero hfr0), hB0 v' hv', zero_add]

end Main

end TorsionDescentFin

end AlgebraicCurve

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension_of_finite
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set
      F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (hfin : Finite {c : Pic0 K' F' // n • c = 0}) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') :=
  have : Finite {c : Pic0 K' F' // n • c = 0} := hfin
  AlgebraicCurve.TorsionDescentFin.main hfg hfg' hgen n hn D' hD'
end Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite
end AlgebraicCurves.Divisors.Proofs
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber
attribute [-simp] AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
