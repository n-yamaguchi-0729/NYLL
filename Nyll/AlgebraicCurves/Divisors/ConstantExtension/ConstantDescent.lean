/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.lean
The maximal-ideal transport lemmas also use the finite-orbit descent source:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension_of_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.ValuationRings.BasicValuationSubring
import Nyll.AlgebraicCurves.Places.Orders.MemRangeAlgebraMapOrdEqZeroAlgClosed
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusRiemannIndexCurve
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Spaces.SectionBounds
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Places.Rational.RatFuncFiniteDimensionalLSpaceZero
import Nyll.AlgebraicCurves.Places.Basic
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeTranscendental
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Common constructions for constant-field descent

Principal divisors, one-dimensional Riemann--Roch spaces, and the behavior of
places above the generic point are shared by the derivation and finite-orbit proofs.
-/

noncomputable section

namespace AlgebraicCurve.ConstantDescent

open Divisor

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_lSpace_add_divOf_iff [HasPrincipalDivisors K F] {D : Divisor K F} {u : F}
    (hu : u ≠ 0) {y : F} :
    y ∈ LSpace (D + divOf u) ↔ y * u ∈ LSpace D := by
  rw [mem_lSpace_iff_ord, mem_lSpace_iff_ord]
  rcases eq_or_ne y 0 with rfl | hy
  · constructor
    · intro _
      exact Or.inl (zero_mul u)
    · intro _
      exact Or.inl rfl
  simp only [hy, mul_ne_zero hy hu, false_or, Finsupp.add_apply]
  constructor
  · intro h v
    have := h v
    rw [divOf_apply hu] at this
    rw [Place.ord_mul _ hy hu]
    linarith
  · intro h v
    have := h v
    rw [Place.ord_mul _ hy hu] at this
    rw [divOf_apply hu]
    linarith

theorem divOf_add_mem_lSpace [HasPrincipalDivisors K F] {D : Divisor K F} {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ LSpace D) : 0 ≤ D + divOf f := by
  intro v
  have := ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) v
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, divOf_apply hf0]
  linarith

theorem constantsAreBase_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ConstantsAreBase K F := by
  classical
  refine le_antisymm ?_ ?_
  · intro f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact zero_mem _
    have hord : ∀ v : Place K F, 0 ≤ v.ord f := by
      intro v
      have := ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) v
      simpa only [Finsupp.zero_apply, neg_zero] using this
    have hzero : ∀ v : Place K F, v.ord f = 0 := by
      have hdeg := degree_divOf (K := K) f
      rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at hdeg
      have hnonneg : ∀ v ∈ (divOf (K := K) f).support,
          (0 : ℤ) ≤ (AddMonoidHom.mulRight (v.deg : ℤ)) (divOf (K := K) f v) := by
        intro v _
        simp only [AddMonoidHom.coe_mulRight, IsCurveOver.deg_eq_one_of_isAlgClosed v,
          Nat.cast_one, mul_one, divOf_apply hf0]
        exact hord v
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdeg
      intro v
      by_cases hv : v ∈ (divOf (K := K) f).support
      · have := hall v hv
        simpa only [AddMonoidHom.coe_mulRight, IsCurveOver.deg_eq_one_of_isAlgClosed v,
          Nat.cast_one, mul_one, divOf_apply hf0] using this
      · have : divOf (K := K) f v = 0 := Finsupp.notMem_support_iff.mp hv
        rwa [divOf_apply hf0] at this
    obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj hzero
    exact ⟨c, hc⟩
  · rintro _ ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

theorem exists_riemann_inequality [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  have : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hj hfd
  obtain ⟨γ, hγ⟩ :=
    exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) (constantsAreBase_of_isAlgClosed j
      hj)
  refine ⟨γ, fun D => ?_⟩
  have h := (hγ D).2
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

theorem exists_reduced [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    (c : Divisor K F) (hc : Divisor.degree c = 0) (P : Place K F) :
    ∃ (r : ℕ) (f : F), f ≠ 0 ∧ f ∈ LSpace (c + (r : ℤ) • Finsupp.single P 1) ∧
      ∀ h ∈ LSpace (c + (r : ℤ) • Finsupp.single P 1), ∃ a : K, a • f = h := by
  classical
  obtain ⟨γ, hγ⟩ := exists_riemann_inequality (K := K) (F := F) j hj
  have hC := constantsAreBase_of_isAlgClosed (K := K) (F := F) j hj
  have := RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  let Dk : ℕ → Divisor K F := fun k => c + (k : ℤ) • Finsupp.single P 1
  have hdeg1 : P.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P
  have hdegk : ∀ k : ℕ, Divisor.degree (Dk k) = k := by
    intro k
    simp only [Dk, map_add, map_zsmul, hc, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one,
      smul_eq_mul, zero_add]
  have hex : ∃ k : ℕ, LSpace (Dk k) ≠ ⊥ := by
    refine ⟨γ.toNat, fun hbot => ?_⟩
    have h1 := hγ (Dk γ.toNat)
    have h2 : ell (Dk γ.toNat) = 0 := by
      rw [ell, hbot, finrank_bot]
    rw [hdegk, h2] at h1
    have := Int.self_le_toNat γ
    push_cast at h1
    linarith
  set r := Nat.find hex with hr_def
  have hr : LSpace (Dk r) ≠ ⊥ := Nat.find_spec hex
  obtain ⟨f, hfmem, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hr
  refine ⟨r, f, hf0, hfmem, ?_⟩
  have hprev : LSpace (Dk r - Finsupp.single P 1) = ⊥ := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · apply lSpace_eq_bot_of_degree_neg
      rw [map_sub, hdegk, h0, Divisor.degree_single, hdeg1]
      norm_num
    · have heq : Dk r - Finsupp.single P 1 = Dk (r - 1) := by
        simp only [Dk]
        rw [Nat.cast_sub hpos, sub_smul, Nat.cast_one, one_smul]
        abel
      rw [heq]
      by_contra hne
      exact Nat.find_min hex (Nat.sub_lt hpos one_pos) hne
  have hle : ell (Dk r) ≤ 1 := by
    have := ell_le_ell_sub_single_add_deg (Dk r) P
    have h0 : ell (Dk r - Finsupp.single P 1) = 0 := by
      rw [ell, hprev, finrank_bot]
    rw [h0, hdeg1, zero_add] at this
    exact this
  have : FiniteDimensional K (LSpace (Dk r)) := finiteDimensional_lSpace (Dk r)
  have hfne : (⟨f, hfmem⟩ : LSpace (Dk r)) ≠ 0 := by
    intro h
    apply hf0
    exact congrArg Subtype.val h
  have hone : Module.finrank K (LSpace (Dk r)) = 1 := by
    refine le_antisymm hle ?_
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨f, hfmem⟩, hfne⟩
  intro h hh
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨f, hfmem⟩ : LSpace (Dk r)) hfne).mp hone
    ⟨h, hh⟩
  exact ⟨a, congrArg Subtype.val ha⟩

end General

section Extension

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra F F']

/-- The condition that a place restricts to the specified place of the original function field. -/
def LiesOver (w' : Place K' F') (v : Place K F) : Prop :=
  w'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring

/-- The condition that the place does not lie over any place of the original function field. -/
def IsGeneric (K F : Type*) [Field K] [Field F] [Algebra K F] [Algebra F F']
    (w' : Place K' F') : Prop :=
  ∀ v : Place K F, ¬ LiesOver w' v

section Tower

variable [Algebra K K'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem IsGeneric.comap_eq_top [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') :
    w'.toValuationSubring.comap (algebraMap F F') = ⊤ := by
  by_contra hne
  obtain ⟨v, hv⟩ := Place.exists_of_valuationSubring (K := K) x
    (w'.toValuationSubring.comap (algebraMap F F')) (fun a => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply K K' F']
      exact w'.algebraMap_mem' _) hne
  exact hw v hv.symm

theorem IsGeneric.algebraMap_mem [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') (y : F) :
    algebraMap F F' y ∈ w'.toValuationSubring := by
  rw [← ValuationSubring.mem_comap, hw.comap_eq_top x]
  exact ValuationSubring.mem_top _

theorem IsGeneric.ord_algebraMap [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') (y : F) :
    w'.ord (algebraMap F F' y) = 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [map_zero, Place.ord_zero]
  have hy' : algebraMap F F' y ≠ 0 := (map_ne_zero (algebraMap F F')).mpr hy
  have hyi' : algebraMap F F' y⁻¹ ≠ 0 := (map_ne_zero (algebraMap F F')).mpr (inv_ne_zero hy)
  have h1 := (Place.mem_iff_ord_nonneg w' hy').mp (hw.algebraMap_mem x y)
  have h2 := (Place.mem_iff_ord_nonneg w' hyi').mp (hw.algebraMap_mem x y⁻¹)
  rw [map_inv₀, Place.ord_inv] at h2
  linarith

end Tower

/-- The condition that an element is zero or has strictly positive order at the place. -/
def InMax (w : Place K' F') (y : F') : Prop := y = 0 ∨ 0 < w.ord y

theorem InMax.sub {w : Place K' F'} {a b : F'} (ha : InMax w a) (hb : InMax w b) :
    InMax w (a - b) := by
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact Or.inl (sub_self 0)
    · right; rwa [zero_sub, ← neg_one_smul K' b, Place.ord_smul_of_ne_zero w (by norm_num) b]
  rcases hb with rfl | hb
  · right; rwa [sub_zero]
  by_cases hab : a - b = 0
  · exact Or.inl hab
  right
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, Place.ord_zero] at ha
    exact lt_irrefl 0 ha
  have hb0 : -b ≠ 0 := by
    apply neg_ne_zero.mpr
    intro h
    rw [h, Place.ord_zero] at hb
    exact lt_irrefl 0 hb
  have hnb : 0 < w.ord (-b) := by
    rwa [← neg_one_smul K' b, Place.ord_smul_of_ne_zero w (by norm_num) b]
  have := Place.min_ord_le_ord_add w ha0 hb0 (by rwa [← sub_eq_add_neg])
  rw [← sub_eq_add_neg] at this
  exact lt_of_lt_of_le (lt_min ha hnb) this

theorem InMax.eq_zero_of_algebraMap {w : Place K' F'} {c : K'} (h : InMax w (algebraMap K' F' c)) :
    c = 0 := by
  rcases h with h | h
  · exact (algebraMap K' F').injective (h.trans (map_zero (algebraMap K' F')).symm)
  · rw [Place.ord_algebraMap] at h
    exact absurd h (lt_irrefl 0)

theorem InMax.smul_iff (g : SemilinearAut K' F') {w : Place K' F'} {y : F'} :
    InMax (g • w) (g • y) ↔ InMax w y := by
  simp only [InMax, SemilinearAut.ord_smul, smul_eq_zero_iff_eq]

section Tower

variable [Algebra K K'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem IsGeneric.exists_inMax_sub [CharZero K] [IsAlgClosed K'] [IsCurveOver K' F'] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') :
    ∃ t : K', InMax w' (algebraMap F F' x - algebraMap K' F' t) := by
  have hsurj : Function.Surjective (algebraMap K' w'.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField w').mp
      (IsCurveOver.deg_eq_one_of_isAlgClosed w')
  have hxmem : algebraMap F F' x ∈ w'.toValuationSubring := hw.algebraMap_mem x x
  obtain ⟨t, ht⟩ := hsurj (IsLocalRing.residue _ ⟨algebraMap F F' x, hxmem⟩)
  have htmem : algebraMap K' F' t ∈ w'.toValuationSubring := w'.algebraMap_mem' t
  refine ⟨t, (Place.mk_mem_maximalIdeal_iff_eq_zero_or_ord_pos w' (sub_mem hxmem htmem)).mp ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsub : (⟨algebraMap F F' x - algebraMap K' F' t, sub_mem hxmem htmem⟩ :
      w'.toValuationSubring) =
      ⟨algebraMap F F' x, hxmem⟩ - algebraMap K' w'.toValuationSubring t := by
    apply Subtype.ext
    exact congrArg (algebraMap F F' x - ·) (Place.coe_algebraMap w' t).symm
  rw [hsub, map_sub, ← ht, sub_eq_zero, IsScalarTower.algebraMap_apply K' w'.toValuationSubring
    w'.ResidueField]
  rfl

theorem IsGeneric.not_mem_range [CharZero K] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') {t : K'}
    (ht : InMax w' (algebraMap F F' x - algebraMap K' F' t)) :
    t ∉ Set.range (algebraMap K K') := by
  rintro ⟨c, rfl⟩
  have heq : algebraMap F F' x - algebraMap K' F' (algebraMap K K' c) =
      algebraMap F F' (x - algebraMap K F c) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [heq] at ht
  have hne : x - algebraMap K F c ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hx (h ▸ isAlgebraic_algebraMap c)
  rcases ht with h | h
  · exact hne ((map_eq_zero_iff _ (algebraMap F F').injective).mp h)
  · rw [hw.ord_algebraMap x] at h
    exact lt_irrefl _ h

end Tower

theorem transcendental_of_not_mem_range [Algebra K K'] [IsAlgClosed K] {t : K'}
    (ht : t ∉ Set.range (algebraMap K K')) : Transcendental K t := by
  intro halg
  have hint : IsIntegral K t := halg.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  exact ht (minpoly.mem_range_of_degree_eq_one K t hdeg)

end Extension

end AlgebraicCurve.ConstantDescent
