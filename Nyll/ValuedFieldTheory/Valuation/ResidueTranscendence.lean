/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.Transcendence
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealHeightAddKrullDimensionQuotientEqKrullDimension

/-! # Valuation centers and residue transcendence degree -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.PrimePowerUnits


theorem _root_.IsNoetherianRing.exists_unit_mul_zpow_eq_of_span_singleton_isPrime
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : (Ideal.span {π}).IsPrime) (hπ0 : π ≠ 0)
    (a : K) (hab : ∃ (m : ℕ) (b : A), a * algebraMap A K π ^ m = algebraMap A K b)
    (hac : ∃ (m : ℕ) (c : A), a⁻¹ * algebraMap A K π ^ m = algebraMap A K c) (ha0 : a ≠ 0) :
    ∃ (n : ℤ) (u : Aˣ), a = algebraMap A K (u : A) * algebraMap A K π ^ n := by
  classical
  obtain ⟨m, b, hb⟩ := hab
  obtain ⟨m', c, hc⟩ := hac
  have hprime : Prime π := (Ideal.span_singleton_prime hπ0).mp hπ
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hP : algebraMap A K π ≠ 0 := fun h => hπ0 (hinj (by rw [h, map_zero]))
  have hbc : b * c = π ^ (m + m') := by
    apply hinj
    rw [map_mul, map_pow, ← hb, ← hc, pow_add]
    calc a * algebraMap A K π ^ m * (a⁻¹ * algebraMap A K π ^ m')
        = (a * a⁻¹) * (algebraMap A K π ^ m * algebraMap A K π ^ m') := by ring
      _ = algebraMap A K π ^ m * algebraMap A K π ^ m' := by rw [mul_inv_cancel₀ ha0, one_mul]
  have hb0 : b ≠ 0 := by
    intro h; rw [h, zero_mul] at hbc; exact pow_ne_zero _ hπ0 hbc.symm
  have hc0 : c ≠ 0 := by
    intro h; rw [h, mul_zero] at hbc; exact pow_ne_zero _ hπ0 hbc.symm
  obtain ⟨i, b₀, hb₀, rfl⟩ := WfDvdMonoid.max_power_factor' hb0 hprime.not_isUnit
  obtain ⟨j, c₀, hc₀, rfl⟩ := WfDvdMonoid.max_power_factor' hc0 hprime.not_isUnit
  have hkey : π ^ (i + j) * (b₀ * c₀) = π ^ (m + m') := by
    rw [← hbc]; ring
  have hndvd : ¬ π ∣ b₀ * c₀ := fun h => (hprime.dvd_or_dvd h).elim hb₀ hc₀
  have hunit : b₀ * c₀ = 1 := by
    rcases le_total (i + j) (m + m') with hle | hle
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add π (i + j) d] at hkey
      have h1 : b₀ * c₀ = π ^ d := mul_left_cancel₀ (pow_ne_zero _ hπ0) hkey
      rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · rw [h1, hd0, pow_zero]
      · exact absurd (h1 ▸ dvd_pow_self π hdpos.ne') hndvd
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add π (m + m') d, mul_assoc] at hkey
      have h1 : π ^ d * (b₀ * c₀) = 1 := mul_left_cancel₀ (pow_ne_zero _ hπ0) (hkey.trans (mul_one
          _).symm)
      rcases Nat.eq_zero_or_pos d with hd0 | hdpos
      · rw [hd0, pow_zero, one_mul] at h1; exact h1
      · exfalso
        apply hprime.not_isUnit
        exact isUnit_of_dvd_one (Dvd.dvd.trans (dvd_pow_self π hdpos.ne') (Dvd.intro _ h1))
  refine ⟨(i : ℤ) - (m : ℤ), Units.mkOfMulEqOne b₀ c₀ hunit, ?_⟩
  rw [Units.val_mkOfMulEqOne]
  have ha : a = algebraMap A K (π ^ i * b₀) / algebraMap A K π ^ m := by
    rw [eq_div_iff (pow_ne_zero _ hP), hb]
  rw [ha, map_mul, map_pow, zpow_sub₀ hP, zpow_natCast, zpow_natCast, div_eq_mul_inv,
      div_eq_mul_inv]
  ring

end AbelianVarieties.NOSProofs.PrimePowerUnits
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ValuationSubring_exists_algebraicIndependent_residue_of_le_trdeg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ResidueLifts


universe u v

theorem _root_.ValuationSubring.exists_algebraicIndependent_residue_of_le_trdeg
    {k : Type u} {K : Type v} [Field k] [Field K] (c : k →+* K) (O : ValuationSubring K)
    (hc : ∀ x : k, c x ∈ O) {d : ℕ} :
    let _ : Algebra k (IsLocalRing.ResidueField O) :=
      ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
    (d : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField O) →
      ∃ (g : Fin d → K) (hg : ∀ i, g i ∈ O),
        AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩) := by
  classical
  intro instAlg hd
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' k (IsLocalRing.ResidueField O)
  have hcard : (d : Cardinal) ≤ Cardinal.mk ι := by rw [hx.cardinalMk_eq_trdeg]; exact hd
  have hemb : Nonempty (Fin d ↪ ι) := by
    rw [← Cardinal.lift_mk_le']
    simpa only [Cardinal.lift_natCast, Cardinal.mk_fin, Cardinal.lift_lift,
      Cardinal.lift_id, Cardinal.lift_uzero] using hcard
  obtain ⟨e⟩ := hemb
  have hind : AlgebraicIndependent k (x ∘ e) := hx.1.comp e e.injective
  have hl : ∀ i, ∃ y : ↥O, IsLocalRing.residue ↥O y = x (e i) := fun i =>
      IsLocalRing.residue_surjective _
  choose gO hgO using hl
  refine ⟨fun i => (gO i : K), fun i => (gO i).2, ?_⟩
  have : (fun i => IsLocalRing.residue ↥O ⟨(gO i : K), (gO i).2⟩) = x ∘ e := funext fun i => hgO i
  rw [this]
  exact hind

end AbelianVarieties.NOSProofs.ResidueLifts
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ValuationSubring_eq_zero_of_valuation_eval2_lt_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ResidueEvaluation


universe u v

theorem _root_.ValuationSubring.eq_zero_of_valuation_eval2_lt_one
    {k : Type u} {K : Type v} [Field k] [Field K] (c : k →+* K) (O : ValuationSubring K)
    (hc : ∀ x : k, c x ∈ O) {d : ℕ} (g : Fin d → K) (hg : ∀ i, g i ∈ O)
    (hind :
      let : Algebra k (IsLocalRing.ResidueField O) :=
        ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
      AlgebraicIndependent k (fun i => IsLocalRing.residue O ⟨g i, hg i⟩))
    (Q : MvPolynomial (Fin d) k) (hQ : O.valuation (Q.eval₂ c g) < 1) : Q = 0 := by
  classical
  let instAlg : Algebra k (IsLocalRing.ResidueField O) :=
    ((IsLocalRing.residue O).comp (c.codRestrict O.toSubring hc)).toAlgebra
  let cO : k →+* ↥O := c.codRestrict O.toSubring hc
  let gO : Fin d → ↥O := fun j => ⟨g j, hg j⟩
  have hev : Q.eval₂ c g = algebraMap ↥O K (Q.eval₂ cO gO) := by
    rw [MvPolynomial.eval₂_comp_left]
    rfl
  rw [hev] at hQ
  have hmem : Q.eval₂ cO gO ∈ IsLocalRing.maximalIdeal ↥O := (O.valuation_lt_one_iff _).mpr hQ
  have hres : IsLocalRing.residue ↥O (Q.eval₂ cO gO) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr
      hmem
  rw [MvPolynomial.eval₂_comp_left] at hres
  rw [algebraicIndependent_iff] at hind
  apply hind Q
  rw [MvPolynomial.aeval_def]
  exact hres

end AbelianVarieties.NOSProofs.ResidueEvaluation
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ValuationSubring_trdeg_residueField_le_trdeg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ResidueBound


open Cardinal

namespace ValuationSubring
open _root_.ValuationSubring
namespace ResidueTrdeg
open _root_.ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- The restricted valuation subring. -/
abbrev B : ValuationSubring K := A.comap (algebraMap K L)

/-- The inclusion of restricted valuation rings. -/
def resHom : B K A →+* A :=
  (algebraMap K L).restrict (B K A).toSubring A.toSubring (fun _ hx => hx)

@[scoped simp] lemma coe_resHom_apply (b : B K A) : ((resHom K A b : A) : L) = algebraMap K L (b :
    K) := rfl

lemma algebraMap_comp_resHom :
    (algebraMap A L).comp (resHom K A) = (algebraMap K L).comp (algebraMap (B K A) K) := by
  ext b
  rfl

theorem algebraicIndependent_lift
    [Algebra (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : B K A,
      algebraMap (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩)
    {ι : Type*} (y : ι → A)
    (hind : AlgebraicIndependent (IsLocalRing.ResidueField (B K A))
      (fun i => IsLocalRing.residue A (y i))) :
    AlgebraicIndependent K (fun i => ((y i : A) : L)) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  have hsupp : P.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hP0
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image P.support
    (fun m => A.valuation (algebraMap K L (P.coeff m))) hsupp
  set c : K := P.coeff m₀ with hc
  have hc0 : c ≠ 0 := MvPolynomial.mem_support_iff.mp hm₀
  set Q : MvPolynomial ι K := MvPolynomial.C c⁻¹ * P with hQ
  have hQcoeff : ∀ m, Q.coeff m = c⁻¹ * P.coeff m := fun m => by
    rw [hQ, MvPolynomial.coeff_C_mul]
  have hQm₀ : Q.coeff m₀ = 1 := by rw [hQcoeff, ← hc, inv_mul_cancel₀ hc0]
  have hQeval : MvPolynomial.aeval (fun i => ((y i : A) : L)) Q = 0 := by
    rw [hQ, map_mul, hP, mul_zero]
  have hQmem : ∀ m, algebraMap K L (Q.coeff m) ∈ A := by
    intro m
    rw [← A.valuation_le_one_iff, hQcoeff, map_mul, map_mul, map_inv₀, map_inv₀]
    by_cases hm : m ∈ P.support
    · have hle := hmax m hm
      have hcv : A.valuation (algebraMap K L c) ≠ 0 := by
        rw [Ne, Valuation.zero_iff, map_eq_zero]
        exact hc0
      calc (A.valuation (algebraMap K L c))⁻¹ * A.valuation (algebraMap K L (P.coeff m))
          ≤ (A.valuation (algebraMap K L c))⁻¹ * A.valuation (algebraMap K L c) := by
            gcongr
        _ = 1 := inv_mul_cancel₀ hcv
    · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero, map_zero, mul_zero]
      exact zero_le_one
  obtain ⟨QB, hQB⟩ : Q ∈ Set.range (MvPolynomial.map (algebraMap (B K A) K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro d hd
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hd
    exact ⟨⟨Q.coeff m, hQmem m⟩, rfl⟩
  have heval : MvPolynomial.eval₂ (resHom K A) y QB = 0 := by
    have h : algebraMap A L (MvPolynomial.eval₂ (resHom K A) y QB) = 0 := by
      rw [MvPolynomial.eval₂_comp_left, algebraMap_comp_resHom, ← MvPolynomial.eval₂_map, hQB]
      exact hQeval
    apply Subtype.val_injective
    change algebraMap A L (MvPolynomial.eval₂ (resHom K A) y QB) = algebraMap A L 0
    rw [h, map_zero]
  have hres : MvPolynomial.aeval (fun i => IsLocalRing.residue A (y i))
      (MvPolynomial.map (IsLocalRing.residue (B K A)) QB) = 0 := by
    have h1 := congrArg (IsLocalRing.residue A) heval
    rw [map_zero, MvPolynomial.eval₂_comp_left] at h1
    have h2 : (IsLocalRing.residue A).comp (resHom K A) =
        (algebraMap (IsLocalRing.ResidueField (B K A)) (IsLocalRing.ResidueField A)).comp
          (IsLocalRing.residue (B K A)) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hcompat b]
      rfl
    rw [h2, ← MvPolynomial.eval₂_map] at h1
    rw [MvPolynomial.aeval_def]
    exact h1
  have hzero : MvPolynomial.map (IsLocalRing.residue (B K A)) QB = 0 :=
    (algebraicIndependent_iff.mp hind) _ hres
  have h1 : QB.coeff m₀ = 1 := by
    have h : algebraMap (B K A) K (QB.coeff m₀) = algebraMap (B K A) K 1 := by
      rw [← MvPolynomial.coeff_map, hQB, hQm₀, map_one]
    exact Subtype.val_injective h
  have h2 := congrArg (fun P : MvPolynomial ι (IsLocalRing.ResidueField (B K A)) => P.coeff m₀)
    hzero
  rw [MvPolynomial.coeff_map, h1, map_one, AddMonoidAlgebra.coeff_zero] at h2
  exact one_ne_zero h2

theorem main
    [Algebra (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : A.comap (algebraMap K L),
      algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩) :
    Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) ≤ Algebra.trdeg K L := by
  classical
  rw [Algebra.trdeg]
  refine ciSup_le' fun s => ?_
  choose y hy using fun i : s.1 => IsLocalRing.residue_surjective (R := A) (i :
      IsLocalRing.ResidueField A)
  have hind : AlgebraicIndependent (IsLocalRing.ResidueField (B K A))
      (fun i : s.1 => IsLocalRing.residue A (y i)) := by
    have : (fun i : s.1 => IsLocalRing.residue A (y i)) = fun i : s.1 => (i :
        IsLocalRing.ResidueField A) :=
      funext hy
    rw [this]
    exact s.2
  have hK := algebraicIndependent_lift K A hcompat y hind
  exact hK.cardinalMk_le_trdeg

end ValuationSubring.ResidueTrdeg

theorem _root_.ValuationSubring.trdeg_residueField_le_trdeg
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    [Algebra (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)]
    (hcompat : ∀ b : A.comap (algebraMap K L),
      algebraMap (IsLocalRing.ResidueField (A.comap (algebraMap K L))) (IsLocalRing.ResidueField A)
        (IsLocalRing.residue _ b) =
          IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩) :
    Algebra.trdeg (IsLocalRing.ResidueField (A.comap (algebraMap K L)))
        (IsLocalRing.ResidueField A) ≤ Algebra.trdeg K L :=
  ValuationSubring.ResidueTrdeg.main K A hcompat

end AbelianVarieties.NOSProofs.ResidueBound
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Ideal_exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ValuationCenters


universe u v w

open scoped nonZeroDivisors

namespace Ideal
open _root_.Ideal
namespace PrimeDivisorCentre
open _root_.Ideal

theorem exists_valuationSubring_centre {B : Type*} [CommRing B] [IsDomain B] {K : Type*} [Field K]
    [Algebra B K] [IsFractionRing B K] (Q : Ideal B) [Q.IsPrime] :
    ∃ V : ValuationSubring K, (∀ b : B, algebraMap B K b ∈ V) ∧
      ∀ b : B, V.valuation (algebraMap B K b) < 1 ↔ b ∈ Q := by
  classical
  let L : Subalgebra B K :=
    Localization.subalgebra.ofField K Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : IsLocalization.AtPrime L Q :=
    Localization.subalgebra.isLocalization_ofField K Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have hLloc : IsLocalRing L := IsLocalization.AtPrime.isLocalRing L Q
  have hne : (IsLocalRing.maximalIdeal L : Ideal L.toSubring) ≠ ⊤ :=
    (IsLocalRing.maximalIdeal.isMaximal L).ne_top
  obtain ⟨V, hLV, hnon⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := L.toSubring) (IsLocalRing.maximalIdeal L) hne
  refine ⟨V, fun b => hLV (algebraMap B L b).2, fun b => ?_⟩
  constructor
  · intro hlt
    by_contra hb
    have hu : IsUnit (algebraMap B L b) := IsLocalization.map_units L (⟨b, hb⟩ : Q.primeCompl)
    have hu' : IsUnit (⟨algebraMap B K b, hLV (algebraMap B L b).2⟩ : V) :=
      hu.map (Subring.inclusion hLV)
    have h1 := (V.valuation_eq_one_iff _).mp hu'
    change V.valuation (algebraMap B K b) = 1 at h1
    exact (lt_irrefl _) (h1 ▸ hlt)
  · intro hb
    have hmem : algebraMap B L b ∈ IsLocalRing.maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q b).mpr hb
    have : algebraMap B K b ∈ V.nonunits := hnon ⟨algebraMap B L b, hmem, rfl⟩
    exact (ValuationSubring.mem_nonunits_iff V).mp this

theorem eq_of_one_add_eq_natCast_succ {x : WithBot ℕ∞} {d : ℕ}
    (h : (1 : WithBot ℕ∞) + x = ((d + 1 : ℕ) : WithBot ℕ∞)) : x = (d : WithBot ℕ∞) := by
  rw [← WithBot.coe_natCast] at h
  induction x using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at h; exact absurd h WithBot.bot_ne_coe
  | coe y =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_inj] at h
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : (1 : ℕ∞) + ⊤ = ⊤ := add_top _
      rw [h1] at h
      exact ENat.top_ne_natCast _ h
    | coe m =>
      have h' : ((1 + m : ℕ) : ℕ∞) = ((d + 1 : ℕ) : ℕ∞) := by rw [← h]; push_cast; rfl
      have : 1 + m = d + 1 := by exact_mod_cast h'
      have hm : m = d := by omega
      subst hm; rfl

theorem exists_ringKrullDim_eq_natCast (k : Type u) [Field k] (A : Type v) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) := by
  have h := Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A
  have hfin : Algebra.trdeg k A < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  refine ⟨n, ?_⟩
  rw [h, hn]
  simp only [Cardinal.toENat_nat, WithBot.coe_natCast]

theorem trdeg_eq_natCast_of_ringKrullDim_eq (k : Type u) [Field k] (A : Type v) [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {n : ℕ}
    (h : ringKrullDim A = (n : WithBot ℕ∞)) : Algebra.trdeg k A = n := by
  have h1 := Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k A
  rw [h] at h1
  have h2 : Cardinal.toENat (Algebra.trdeg k A) = n := by
    have : ((n : ℕ∞) : WithBot ℕ∞) = (Cardinal.toENat (Algebra.trdeg k A) : WithBot ℕ∞) := by
      rw [← h1]; rfl
    exact_mod_cast this.symm
  exact (Cardinal.toENat_eq_natCast).mp h2

theorem exists_algebraicIndependent_of_ringKrullDim_eq (k : Type u) [Field k] (C : Type v)
    [CommRing C] [IsDomain C] [Algebra k C] [Algebra.FiniteType k C] {d : ℕ}
    (h : ringKrullDim C = (d : WithBot ℕ∞)) :
    ∃ x : Fin d → C, AlgebraicIndependent k x := by
  classical
  have : FaithfulSMul k C :=
    (faithfulSMul_iff_algebraMap_injective k C).mpr (algebraMap k C).injective
  have htr : Algebra.trdeg k C = d := trdeg_eq_natCast_of_ringKrullDim_eq k C h
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k C
  have hcard : Cardinal.mk s = d := by rw [hs.cardinalMk_eq_trdeg, htr]
  have hfin : (s : Set C).Finite := by
    rw [← Cardinal.lt_aleph0_iff_set_finite, hcard]
    exact Cardinal.natCast_lt_aleph0
  have : Fintype s := hfin.fintype
  have hcard' : Fintype.card s = d := by
    have : Cardinal.mk s = Fintype.card s := Cardinal.mk_fintype s
    rw [this] at hcard
    exact_mod_cast hcard
  let e : s ≃ Fin d := Fintype.equivFinOfCardEq hcard'
  exact ⟨fun i => ((e.symm i : s) : C), hs.1.comp _ e.symm.injective⟩

section Main

variable (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]
  (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]

theorem main (p : Ideal A) [hp : p.IsPrime] (hp0 : p ≠ ⊥) :
    ∃ (O : ValuationSubring K) (d : ℕ) (f : Fin d → K),
      O ≠ ⊤ ∧ (∀ a : A, algebraMap A K a ∈ O) ∧
      (∀ a : A, O.valuation (algebraMap A K a) < 1 ↔ a ∈ p) ∧
      ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A ∧
      (∀ i, f i ∈ O) ∧
      ∀ Q : MvPolynomial (Fin d) k, O.valuation (MvPolynomial.aeval f Q) < 1 → Q = 0 := by
  classical
  have hinjA : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast k A
  have hn1 : 1 ≤ n := by
    have hpos : 0 < ringKrullDim A := by
      rw [ringKrullDim, Order.krullDim_pos_iff]
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨p, hp⟩, ?_⟩
      change (⊥ : Ideal A) < p
      exact bot_lt_iff_ne_bot.mpr hp0
    rw [hn] at hpos
    have : (0 : ℕ) < n := by exact_mod_cast hpos
    omega
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  obtain ⟨V, hAV, hVcen⟩ := exists_valuationSubring_centre (K := K) p
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian p : p.FG)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hp0
    rw [← hs, Finset.coe_empty]
    exact Ideal.span_empty
  obtain ⟨a₁, ha₁s, ha₁max⟩ :=
    s.exists_max_image (fun a => V.valuation (algebraMap A K a)) hsne
  have hsp : ∀ a ∈ s, a ∈ p := fun a ha => hs ▸ Ideal.subset_span ha
  have ha₁p : a₁ ∈ p := hsp a₁ ha₁s
  have ha₁0 : a₁ ≠ 0 := by
    intro h0
    apply hp0
    rw [← hs, Ideal.span_eq_bot]
    intro a ha
    have hle := ha₁max a ha
    rw [h0, map_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at hle
    exact hinjA (by rw [hle, map_zero])
  set α₁ : K := algebraMap A K a₁ with hα₁
  have hα₁0 : α₁ ≠ 0 := fun h => ha₁0 (hinjA (by rw [← hα₁, h, map_zero]))
  have hα₁lt : V.valuation α₁ < 1 := (hVcen a₁).mpr ha₁p
  let T : Finset K := s.image fun a => algebraMap A K a / α₁
  let B : Subalgebra A K := Algebra.adjoin A (T : Set K)
  have hAB : ∀ a : A, algebraMap A K a ∈ B := fun a => B.algebraMap_mem a
  have hTV : (T : Set K) ⊆ V := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    apply V.mem_of_valuation_le_one
    rw [Valuation.map_div]
    exact div_le_one_of_le₀ (ha₁max a ha) zero_le
  let SV : Subalgebra A K :=
    { V.toSubring with
      algebraMap_mem' := fun a => hAV a }
  have hBV : B ≤ SV := Algebra.adjoin_le hTV
  have hBV' : ∀ x : B, (x : K) ∈ V := fun x => hBV x.2
  have : Algebra.FiniteType A B :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T)
  have : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq fun r => Subtype.ext (IsScalarTower.algebraMap_apply k A K r)
  have hBft : Algebra.FiniteType k B := Algebra.FiniteType.trans (inferInstance) (S := A)
      inferInstance
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hinjAB : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply hinjA
    have := congrArg (fun x : B => (x : K)) hab
    exact this
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinjAB
  have : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  have : Algebra.IsAlgebraic A B :=
    Algebra.IsAlgebraic.of_injective B.val Subtype.val_injective
  have htrB : Algebra.trdeg k B = (d + 1 : ℕ) := by
    have h1 := lift_trdeg_add_eq k A B
    rw [trdeg_eq_zero (R := A) (A := B), trdeg_eq_natCast_of_ringKrullDim_eq k A hn] at h1
    simp only [Cardinal.lift_natCast, Cardinal.lift_zero, add_zero] at h1
    exact (Cardinal.lift_eq_nat_iff.mp h1.symm)
  have hdimB : ringKrullDim B = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k B, htrB]
    simp only [Cardinal.toENat_nat, WithBot.coe_natCast]
  let ψ : B →+* V := (B.val : B →ₐ[A] K).toRingHom.codRestrict V hBV'
  let Q₁ : Ideal B := (IsLocalRing.maximalIdeal V).comap ψ
  have : Q₁.IsPrime := Ideal.comap_isPrime ψ _
  have hQ₁ : ∀ x : B, x ∈ Q₁ ↔ V.valuation (x : K) < 1 := by
    intro x
    change ψ x ∈ IsLocalRing.maximalIdeal V ↔ _
    rw [ValuationSubring.valuation_lt_one_iff]
    rfl
  let b₁ : B := algebraMap A B a₁
  have hb₁K : (b₁ : K) = α₁ := rfl
  have hb₁0 : b₁ ≠ 0 := fun h => hα₁0 (by rw [← hb₁K, h]; rfl)
  have hb₁Q₁ : b₁ ∈ Q₁ := (hQ₁ b₁).mpr (by rw [hb₁K]; exact hα₁lt)
  let I : Ideal B := Ideal.span {b₁}
  have hIQ₁ : I ≤ Q₁ := (Ideal.span_singleton_le_iff_mem _).mpr hb₁Q₁
  obtain ⟨Q, hQmin, hQQ₁⟩ := Ideal.exists_minimalPrimes_le hIQ₁
  have hQ : Q.IsPrime := hQmin.1.1
  have hIQ : I ≤ Q := hQmin.1.2
  have hb₁Q : b₁ ∈ Q := hIQ (Ideal.subset_span rfl)
  have hQht : Q.height = 1 := by
    have hle : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I Q hQmin
    have hne : Q.height ≠ 0 := by
      intro h0
      rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
        Set.mem_singleton_iff] at h0
      apply hb₁0
      have : b₁ ∈ (⊥ : Ideal B) := h0 ▸ hb₁Q
      exact this
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)
  have hQA : ∀ a : A, algebraMap A B a ∈ Q ↔ a ∈ p := by
    intro a
    constructor
    · intro ha
      have h1 : V.valuation ((algebraMap A B a : B) : K) < 1 := (hQ₁ _).mp (hQQ₁ ha)
      exact (hVcen a).mp h1
    · intro ha
      have hpI : p ≤ I.comap (algebraMap A B) := by
        rw [← hs, Ideal.span_le]
        intro a' ha'
        change algebraMap A B a' ∈ I
        have hq : algebraMap A K a' / α₁ ∈ B :=
          Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha'))
        have hfac : algebraMap A B a' = b₁ * ⟨_, hq⟩ := by
          apply Subtype.ext
          change algebraMap A K a' = α₁ * (algebraMap A K a' / α₁)
          rw [mul_div_cancel₀ _ hα₁0]
        rw [hfac]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      exact hIQ (hpI ha)
  have hdimBQ : ringKrullDim (B ⧸ Q) = (d : WithBot ℕ∞) := by
    have h := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k Q
    rw [hdimB, hQht] at h
    exact eq_of_one_add_eq_natCast_succ (by simpa only [WithBot.coe_one] using h)
  have : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  obtain ⟨x, hx⟩ := exists_algebraicIndependent_of_ringKrullDim_eq k (B ⧸ Q) hdimBQ
  let g : Fin d → B := fun i => (Ideal.Quotient.mk_surjective (x i)).choose
  have hg : ∀ i, Ideal.Quotient.mk Q (g i) = x i := fun i =>
    (Ideal.Quotient.mk_surjective (x i)).choose_spec
  let f : Fin d → K := fun i => (g i : K)
  obtain ⟨O, hBO, hOcen⟩ := exists_valuationSubring_centre (K := K) Q
  have hBO' : ∀ y : B, (y : K) ∈ O := hBO
  have hOcen' : ∀ y : B, O.valuation (y : K) < 1 ↔ y ∈ Q := hOcen
  refine ⟨O, d, f, ?_, fun a => hBO' (algebraMap A B a), fun a => ?_, hn.symm, fun i => hBO' _, ?_⟩
  · intro htop
    have hlt : O.valuation α₁ < 1 := (hOcen' b₁).mpr hb₁Q
    have hmem : α₁⁻¹ ∈ O := htop ▸ ValuationSubring.mem_top _
    have hle : O.valuation α₁⁻¹ ≤ 1 := O.valuation_le_one_iff _ |>.mpr hmem
    rw [Valuation.map_inv, inv_le_one₀ ((Valuation.pos_iff _).mpr hα₁0)] at hle
    exact (not_le.mpr hlt) hle
  · rw [← hQA a, ← hOcen' (algebraMap A B a)]
    rfl
  · intro P hP
    have hval : MvPolynomial.aeval f P = ((MvPolynomial.aeval g P : B) : K) := by
      have := MvPolynomial.comp_aeval_apply g (IsScalarTower.toAlgHom k B K) P
      exact this.symm
    rw [hval] at hP
    have hmemQ : MvPolynomial.aeval g P ∈ Q := (hOcen' _).mp hP
    have hzero : MvPolynomial.aeval x P = 0 := by
      have h1 : Ideal.Quotient.mkₐ k Q (MvPolynomial.aeval g P) = MvPolynomial.aeval x P := by
        rw [MvPolynomial.comp_aeval_apply]
        have hfun : (fun i => Ideal.Quotient.mkₐ k Q (g i)) = x := funext hg
        rw [hfun]
      rw [← h1, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hmemQ
    exact hx (by rw [hzero, map_zero])

end Main

end Ideal.PrimeDivisorCentre

open Ideal.PrimeDivisorCentre in
theorem _root_.Ideal.exists_valuationSubring_valuation_lt_one_iff_mem_of_finiteType
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    ∃ (O : ValuationSubring K) (d : ℕ) (f : Fin d → K),
      O ≠ ⊤ ∧ (∀ a : A, algebraMap A K a ∈ O) ∧
      (∀ a : A, O.valuation (algebraMap A K a) < 1 ↔ a ∈ p) ∧
      ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A ∧
      (∀ i, f i ∈ O) ∧
      ∀ Q : MvPolynomial (Fin d) k, O.valuation (MvPolynomial.aeval f Q) < 1 → Q = 0 :=
  Ideal.PrimeDivisorCentre.main k K p hp

end AbelianVarieties.NOSProofs.ValuationCenters
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Ideal_height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.HeightOne


universe u v

namespace Ideal
open _root_.Ideal
namespace HeightOneOfIndependentResidues
open _root_.Ideal

theorem algebraicIndependent_mk (k : Type u) [Field k] {A : Type v} [CommRing A] [Algebra k A]
    (p : Ideal A) {d : ℕ} (f : Fin d → A)
    (hind : ∀ Q : MvPolynomial (Fin d) k, MvPolynomial.aeval f Q ∈ p → Q = 0) :
    AlgebraicIndependent k (fun i => Ideal.Quotient.mk p (f i)) := by
  rw [AlgebraicIndependent]
  intro Q₁ Q₂ hQ
  have h1 : ∀ Q : MvPolynomial (Fin d) k,
      MvPolynomial.aeval (fun i => Ideal.Quotient.mk p (f i)) Q =
        Ideal.Quotient.mkₐ k p (MvPolynomial.aeval f Q) := by
    intro Q
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  have h2 : MvPolynomial.aeval f (Q₁ - Q₂) ∈ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := hQ
    rw [h1, h1] at this
    change Ideal.Quotient.mk p (MvPolynomial.aeval f Q₁) = Ideal.Quotient.mk p (MvPolynomial.aeval
        f Q₂)
      at this
    rw [map_sub, map_sub, this, sub_self]
  exact sub_eq_zero.mp (hind _ h2)

theorem natCast_le_ringKrullDim_of_algebraicIndependent (k : Type u) [Field k] {B : Type v}
    [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] {d : ℕ} {x : Fin d → B}
    (hx : AlgebraicIndependent k x) : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim B := by
  have h1 := Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k B
  have h2 : Cardinal.lift.{v} (Cardinal.mk (Fin d)) ≤ Cardinal.lift.{0} (Algebra.trdeg k B) :=
    hx.lift_cardinalMk_le_trdeg
  rw [Cardinal.mk_fin] at h2
  have h3 : (d : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg k B) := by
    have := (OrderHomClass.mono Cardinal.toENat) h2
    simpa only [Cardinal.toENat_lift, Cardinal.toENat_nat] using this
  rw [h1]
  exact_mod_cast h3

theorem enat_eq_one_of_add_eq_of_le {h : ℕ∞} {x : WithBot ℕ∞} {d : ℕ}
    (hsum : (h : WithBot ℕ∞) + x = ((d + 1 : ℕ) : WithBot ℕ∞)) (hle : ((d : ℕ) : WithBot ℕ∞) ≤ x)
    (hne : h ≠ 0) : h = 1 := by
  induction x using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hsum
    exact WithBot.bot_ne_coe (hsum.trans (WithBot.coe_natCast _).symm)
  | coe y =>
    have hsum' : h + y = ((d + 1 : ℕ) : ℕ∞) := by
      have : ((h + y : ℕ∞) : WithBot ℕ∞) = (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [WithBot.coe_add]
        exact hsum.trans (WithBot.coe_natCast _).symm
      exact WithBot.coe_inj.mp this
    have hle' : (d : ℕ∞) ≤ y := by
      have : (((d : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (y : WithBot ℕ∞) := by
        rw [WithBot.coe_natCast]; exact hle
      exact WithBot.coe_le_coe.mp this
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      rw [add_top] at hsum'
      exact ENat.top_ne_natCast _ hsum'
    | coe m =>
      induction h using ENat.recTopCoe with
      | top =>
        exfalso
        rw [top_add] at hsum'
        exact ENat.top_ne_natCast _ hsum'
      | coe n =>
        have e1 : n + m = d + 1 := by exact_mod_cast hsum'
        have e2 : d ≤ m := by exact_mod_cast hle'
        have e3 : n ≠ 0 := by exact_mod_cast hne
        have : n = 1 := by omega
        subst this
        rfl

end Ideal.HeightOneOfIndependentResidues

open Ideal.HeightOneOfIndependentResidues in
theorem _root_.Ideal.height_eq_one_of_ne_bot_of_forall_aeval_mem_imp_eq_zero_of_ringKrullDim_eq
    (k : Type u) [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥)
    (d : ℕ) (hd : ((d + 1 : ℕ) : WithBot ℕ∞) = ringKrullDim A)
    (f : Fin d → A) (hind : ∀ Q : MvPolynomial (Fin d) k, MvPolynomial.aeval f Q ∈ p → Q = 0) :
    p.height = 1 := by
  have : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  have hind' := algebraicIndependent_mk k p f hind
  have hle : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p) :=
    natCast_le_ringKrullDim_of_algebraicIndependent k hind'
  have hsum := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k p
  rw [← hd] at hsum
  have hne : p.height ≠ 0 := by
    intro h0
    rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]
        at h0
    exact hp h0
  exact enat_eq_one_of_add_eq_of_le hsum hle hne

end AbelianVarieties.NOSProofs.HeightOne
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ValuationSubring_le_trdeg_residueField_comap_of_le_trdeg_residueField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.ResidueTower


universe u

open Cardinal

namespace TranscendenceInequality

theorem card_book (a b c : Cardinal.{u}) (nK nL : ℕ)
    (h1 : ((nL - 1 : ℕ) : Cardinal) ≤ a + b) (h2 : b ≤ c) (h3 : (nK : Cardinal) + c ≤ nL) :
    ((nK - 1 : ℕ) : Cardinal) ≤ a := by
  rcases lt_or_ge a ℵ₀ with ha | ha
  · obtain ⟨m, rfl⟩ := Cardinal.lt_aleph0.mp ha
    have hc : c < ℵ₀ := lt_of_le_of_lt (le_trans (self_le_add_left c (nK : Cardinal)) h3)
        Cardinal.natCast_lt_aleph0
    obtain ⟨c', rfl⟩ := Cardinal.lt_aleph0.mp hc
    have hb : b < ℵ₀ := lt_of_le_of_lt h2 Cardinal.natCast_lt_aleph0
    obtain ⟨b', rfl⟩ := Cardinal.lt_aleph0.mp hb
    rw [← Nat.cast_add, Nat.cast_le] at h1 h3
    rw [Nat.cast_le] at h2 ⊢
    omega
  · exact le_trans Cardinal.natCast_lt_aleph0.le ha

end TranscendenceInequality

open TranscendenceInequality in
theorem _root_.ValuationSubring.le_trdeg_residueField_comap_of_le_trdeg_residueField
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L]
    (A : ValuationSubring L) (hk : ∀ x : k, algebraMap k L x ∈ A)
    (nK nL : ℕ) (hK : Algebra.trdeg k K = nK) (hL : Algebra.trdeg k L = nL)
    (hA : let : Algebra k (IsLocalRing.ResidueField A) :=
        ((IsLocalRing.residue A).comp ((algebraMap k L).codRestrict A.toSubring hk)).toAlgebra
      ((nL - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField A)) :
    let O : ValuationSubring K := A.comap (algebraMap K L)
    let hkO : ∀ x : k, algebraMap k K x ∈ O := fun x => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hk x
    let : Algebra k (IsLocalRing.ResidueField O) :=
      ((IsLocalRing.residue O).comp ((algebraMap k K).codRestrict O.toSubring hkO)).toAlgebra
    ((nK - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField O) := by
  intro O hkO iO
  let f : O →+* A := ((algebraMap K L).comp O.toSubring.subtype).codRestrict A.toSubring
    (fun o => ValuationSubring.mem_comap.mp o.2)
  have hf : ∀ o : O, (f o : L) = algebraMap K L (o : K) := fun o => rfl
  have : IsLocalHom f := by
    constructor
    intro o ho
    obtain ⟨u, hu⟩ := ho
    have hne : (o : K) ≠ 0 := by
      intro h0
      have : (f o : L) = 0 := by rw [hf, h0, map_zero]
      exact (u.ne_zero) (by rw [hu]; exact Subtype.ext this)
    have hinvA : algebraMap K L (o : K)⁻¹ ∈ A := by
      have h1 : ((u : A) : L) * (((u⁻¹ : Aˣ) : A) : L) = 1 := congrArg Subtype.val u.mul_inv
      have h2 : (((u⁻¹ : Aˣ) : A) : L) = ((u : A) : L)⁻¹ := (eq_inv_of_mul_eq_one_right h1)
      rw [map_inv₀, ← hf, ← hu, ← h2]
      exact ((u⁻¹ : Aˣ) : A).2
    have hinvO : (o : K)⁻¹ ∈ O := ValuationSubring.mem_comap.mpr hinvA
    exact isUnit_iff_exists_inv.mpr ⟨⟨(o : K)⁻¹, hinvO⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩
  let : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) :=
    (IsLocalRing.ResidueField.map f).toAlgebra
  have hcompat : ∀ b : O,
      algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) (IsLocalRing.residue _
          b) =
        IsLocalRing.residue A ⟨algebraMap K L (b : K), ValuationSubring.mem_comap.mp b.2⟩ := fun b
            =>
    IsLocalRing.ResidueField.map_residue f b
  have h5 := ValuationSubring.trdeg_residueField_le_trdeg A hcompat
  let iA : Algebra k (IsLocalRing.ResidueField A) :=
    ((IsLocalRing.residue A).comp ((algebraMap k L).codRestrict A.toSubring hk)).toAlgebra
  have : IsScalarTower k (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change IsLocalRing.residue A ⟨algebraMap k L x, hk x⟩ =
      IsLocalRing.ResidueField.map f (IsLocalRing.residue O ⟨algebraMap k K x, hkO x⟩)
    rw [IsLocalRing.ResidueField.map_residue]
    congr 1
    apply Subtype.ext
    change algebraMap k L x = algebraMap K L (algebraMap k K x)
    exact IsScalarTower.algebraMap_apply k K L x
  have : FaithfulSMul k (IsLocalRing.ResidueField O) :=
    (faithfulSMul_iff_algebraMap_injective k _).mpr (algebraMap k (IsLocalRing.ResidueField
        O)).injective
  have : FaithfulSMul (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A)).injective
  have : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).mpr (algebraMap k
      K).injective
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr (algebraMap K
      L).injective
  have hadd : Algebra.trdeg k (IsLocalRing.ResidueField O) +
      Algebra.trdeg (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField A) =
        Algebra.trdeg k (IsLocalRing.ResidueField A) :=
    trdeg_add_eq k (IsLocalRing.ResidueField O)
  have hKL : Algebra.trdeg k K + Algebra.trdeg K L ≤ Algebra.trdeg k L := trdeg_add_le
  rw [hK, hL] at hKL
  change ((nL - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField A) at hA
  rw [← hadd] at hA
  exact card_book _ _ _ nK nL hA h5 hKL

end AbelianVarieties.NOSProofs.ResidueTower
end
