/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Polynomial.IrreducibleRing
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Unramified.Dedekind
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.Invariant.Galois

/-!
# Inertia, unramifiedness and unramified extensions of discrete valuation rings
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Ideal_mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace ValuationInertia
open scoped Pointwise

theorem _root_.Ideal.mem_inertia_iff_smul_valuationSubring_eq_and_forall_smul_sub_mem_nonunits
    {B : Type*} [CommRing B] {F : Type*} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G B] [MulSemiringAction G F]
    (ρ : B →+* F) (hρ : ∀ (g : G) (b : B), g • ρ b = ρ (g • b))
    (𝔶 : Ideal B) (P : ValuationSubring F)
    (hP : ∀ b : B, ρ b ∈ P) (hPy : ∀ b : B, ρ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F,
      (∀ b : B, ρ b ∈ P') → (∀ b : B, ρ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ b : B, (e : F) - ρ b ∈ P.nonunits)
    (g : G) :
    g ∈ 𝔶.inertia G ↔ (g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits) := by
  have hnu : ∀ (h : G) (x : F), x ∈ (h • P).nonunits ↔ h⁻¹ • x ∈ P.nonunits := by
    intro h x
    simp only [ValuationSubring.mem_nonunits_iff_or,
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      smul_inv'', smul_eq_zero_iff_eq]
  have hmem : ∀ {h : G}, h ∈ 𝔶.inertia G → ∀ b : B, h • b ∈ 𝔶 ↔ b ∈ 𝔶 := by
    intro h hh b
    have hb := hh b
    constructor
    · intro h1
      simpa only [sub_sub_self] using 𝔶.sub_mem h1 hb
    · intro h1
      simpa only [sub_add_cancel] using 𝔶.add_mem hb h1
  constructor
  · intro hg
    have hstab : g • P = P := by
      apply huniq
      · intro b
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hρ]
        exact hP _
      · intro b
        rw [hnu, hρ, hPy]
        exact hmem (inv_mem hg) b
    refine ⟨hstab, fun e => ?_⟩
    obtain ⟨b, hb⟩ := hres e
    have h1 : g • ((e : F) - ρ b) ∈ P.nonunits := by
      have : g • ((e : F) - ρ b) ∈ (g • P).nonunits := by
        rw [hnu, inv_smul_smul]; exact hb
      rwa [hstab] at this
    have h2 : g • ρ b - ρ b ∈ P.nonunits := by
      rw [hρ, ← map_sub]; exact (hPy _).mpr (hg b)
    have h3 : ρ b - (e : F) ∈ P.nonunits := by
      have := P.nonunits.neg_mem hb
      rwa [neg_sub] at this
    have : g • (e : F) - e = g • ((e : F) - ρ b) + (g • ρ b - ρ b) + (ρ b - e) := by
      rw [smul_sub]; ring
    rw [this]
    exact P.nonunits.add_mem (P.nonunits.add_mem h1 h2) h3
  · rintro ⟨-, hres'⟩ b
    have h := hres' ⟨ρ b, hP b⟩
    change g • ρ b - ρ b ∈ P.nonunits at h
    rw [hρ, ← map_sub] at h
    exact (hPy _).mp h

end ValuationInertia
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace UnramifiedCriterion
open IsLocalRing

universe u v

namespace ResidueFields

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The quotient by a maximal ideal identified with its residue field. -/
noncomputable def quotEquiv (p : Ideal R) [p.IsMaximal] : (R ⧸ p) ≃+* p.ResidueField :=
  RingEquiv.ofBijective (algebraMap (R ⧸ p) p.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField p)

theorem quotEquiv_mk (p : Ideal R) [p.IsMaximal] (r : R) :
    quotEquiv p (Ideal.Quotient.mk p r) = algebraMap R p.ResidueField r := by
  change algebraMap (R ⧸ p) p.ResidueField (algebraMap R (R ⧸ p) r) = _
  rw [← IsScalarTower.algebraMap_apply]

theorem main [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥)
    (he : p.ramificationIdx' P = 1)
    [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] : Algebra.IsUnramifiedAt R P := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver p P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  let : Field (S ⧸ P) := Ideal.Quotient.field P
  rw [Algebra.isUnramifiedAt_iff_map_eq R p P]
  refine ⟨?_, (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff hP ?_).mp he⟩
  · refine Algebra.IsSeparable.of_equiv_equiv (A₁ := R ⧸ p) (B₁ := S ⧸ P) (A₂ := p.ResidueField)
      (B₂ := P.ResidueField) (quotEquiv p) (quotEquiv P) ?_
    apply Ideal.Quotient.ringHom_ext
    ext r
    simp only [RingHom.comp_apply]
    change algebraMap p.ResidueField P.ResidueField (quotEquiv p (Ideal.Quotient.mk p r)) =
      quotEquiv P (algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p r))
    rw [quotEquiv_mk]
    have h1 : algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p r) =
        Ideal.Quotient.mk P (algebraMap R S r) := rfl
    rw [h1, quotEquiv_mk, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R S]
  · rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (Ideal.LiesOver.over (p := p) (P := P))

end ResidueFields

theorem _root_.Algebra.isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsPrime] [P.LiesOver p] (hP : P ≠ ⊥)
    (he : p.ramificationIdx' P = 1) [Algebra.IsSeparable (R ⧸ p) (S ⧸ P)] :
    Algebra.IsUnramifiedAt R P :=
  ResidueFields.main p P hP he

end UnramifiedCriterion
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Ideal_inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace InertiaTriviality
open scoped Pointwise

namespace P2mInertiaTrivial

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  {p : Ideal A} (P : Ideal B)

theorem ramificationIdxIn_mul_inertiaDegIn_eq_card_stabilizer [p.IsMaximal]
    [P.IsMaximal] [P.LiesOver p] :
    p.ramificationIdxIn B * p.inertiaDegIn B = Nat.card (MulAction.stabilizer G P) := by
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G
  have h2 : (p.primesOver B).ncard * Nat.card (MulAction.stabilizer G P) = Nat.card G := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver A B G p P]
    simpa only [Nat.card_prod, Nat.card_coe_set_eq]
      using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  have hr : (p.primesOver B).ncard ≠ 0 := IsDedekindDomain.primesOver_ncard_ne_zero p B
  exact mul_left_cancel₀ hr (h1.trans h2.symm)

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B] [Module.IsTorsionFree A B] in
theorem card_stabilizer_eq_card_inertia_mul_card_aut [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (P.inertia G) * Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) := by
  have hq : Nat.card (MulAction.stabilizer G P ⧸ (P.inertia G).subgroupOf (MulAction.stabilizer G
      P))
      = Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
    Nat.card_congr (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [← hq, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv, mul_comm]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem inertia_eq_bot_iff (hpb : p ≠ ⊥) [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] :
    P.inertia G = ⊥ ↔ p.ramificationIdxIn B = 1 ∧ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Field (B ⧸ P) := Ideal.Quotient.field P
  have hef := ramificationIdxIn_mul_inertiaDegIn_eq_card_stabilizer G P (p := p)
  have hDI := card_stabilizer_eq_card_inertia_mul_card_aut G P (p := p)
  have hf : p.inertiaDegIn B = Module.finrank (A ⧸ p) (B ⧸ P) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg p P G, Ideal.inertiaDeg_eq_of_isMaximal p P]
  have he0 : p.ramificationIdxIn B ≠ 0 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
      ← Ideal.ramificationIdx'_eq_ramificationIdx p P hpb]
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P hpb
  have hfpos : 0 < Module.finrank (A ⧸ p) (B ⧸ P) := Module.finrank_pos
  have haut_le : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) ≤ Module.finrank (A ⧸ p) (B ⧸ P) := by
    have h := AlgEquiv.card_le (F := A ⧸ p) (K := B ⧸ P)
    rwa [← Nat.card_eq_fintype_card] at h
  have hnormal : Normal (A ⧸ p) (B ⧸ P) := Ideal.Quotient.normal (A := A) G p P
  constructor
  · intro hI
    have hI1 : Nat.card (P.inertia G) = 1 := by rw [hI, Subgroup.card_bot]
    rw [hI1, one_mul] at hDI
    have hle : p.ramificationIdxIn B * Module.finrank (A ⧸ p) (B ⧸ P) ≤
        1 * Module.finrank (A ⧸ p) (B ⧸ P) := by
      rw [one_mul, ← hf, hef, hDI, hf]; exact haut_le
    have he1 : p.ramificationIdxIn B ≤ 1 := Nat.le_of_mul_le_mul_right hle hfpos
    have he : p.ramificationIdxIn B = 1 := by omega
    refine ⟨he, ?_⟩
    have hcard : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) = Module.finrank (A ⧸ p) (B ⧸ P) := by
      rw [← hDI, ← hef, he, one_mul, hf]
    have : IsGalois (A ⧸ p) (B ⧸ P) := IsGalois.of_card_aut_eq_finrank _ _ hcard
    infer_instance
  · rintro ⟨he, hsep⟩
    have : IsGalois (A ⧸ p) (B ⧸ P) := ⟨⟩
    have hcard : Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) = Module.finrank (A ⧸ p) (B ⧸ P) :=
      IsGalois.card_aut_eq_finrank _ _
    have h : Nat.card (P.inertia G) * Module.finrank (A ⧸ p) (B ⧸ P) =
        1 * Module.finrank (A ⧸ p) (B ⧸ P) := by
      rw [← hcard, ← hDI, ← hef, he, hf, hcard]
    have h1 : Nat.card (P.inertia G) = 1 := Nat.eq_of_mul_eq_mul_right hfpos h
    exact Subgroup.eq_bot_of_card_eq (P.inertia G) h1

end P2mInertiaTrivial

theorem _root_.Ideal.inertia_eq_bot_iff_ramificationIdxIn_eq_one_and_isSeparable
    {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    {p : Ideal A} (hpb : p ≠ ⊥) [p.IsMaximal] (P : Ideal B) [P.IsMaximal] [P.LiesOver p] :
    P.inertia G = ⊥ ↔ p.ramificationIdxIn B = 1 ∧ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) :=
  P2mInertiaTrivial.inertia_eq_bot_iff G P hpb

end InertiaTriviality
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace UnramifiedSplitting
universe u

namespace P2mEtaleSplitting

open IntermediateField

section PiFactor

variable (K : Type*) [Field K] {I : Type u} [Finite I] (Ai : I → Type u) [∀ i, Field (Ai i)]
  [∀ i, Algebra K (Ai i)] {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- A field-valued homomorphism restricted to the unique nonzero product factor. -/
noncomputable def factorHom [DecidableEq I] (φ : (Π i, Ai i) →ₐ[K] Ω) (i : I)
    (hi : φ (Pi.single i 1) = 1) : Ai i →ₐ[K] Ω where
  toFun a := φ (Pi.single i a)
  map_one' := hi
  map_mul' a b := by rw [← map_mul, ← Pi.single_mul]
  map_zero' := by rw [Pi.single_zero, map_zero]
  map_add' a b := by rw [← map_add, ← Pi.single_add]
  commutes' k := by
    rw [Algebra.algebraMap_eq_smul_one, show (Pi.single i (k • (1 : Ai i)) : Π j, Ai j) =
        k • Pi.single i (1 : Ai i) from Pi.single_smul i k (1 : Ai i), map_smul, hi,
      Algebra.algebraMap_eq_smul_one]

omit [Finite I] in
theorem factorHom_apply [DecidableEq I] (φ : (Π i, Ai i) →ₐ[K] Ω) (i : I)
    (hi : φ (Pi.single i 1) = 1) (a : Ai i) : factorHom K Ai φ i hi a = φ (Pi.single i a) := rfl

theorem exists_eq_comp_evalAlgHom (φ : (Π i, Ai i) →ₐ[K] Ω) :
    ∃ (i : I) (ψ : Ai i →ₐ[K] Ω), ∀ x, φ x = ψ (x i) := by
  classical
  obtain ⟨_⟩ := nonempty_fintype I
  have hsum : ∑ i, φ (Pi.single i (1 : Ai i)) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ => (1 : _))]
    exact map_one φ
  have hex : ∃ i, φ (Pi.single i (1 : Ai i)) ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero (fun i _ => h i)] at hsum
    exact zero_ne_one hsum
  obtain ⟨i, hi0⟩ := hex
  have hidem : φ (Pi.single i (1 : Ai i)) * φ (Pi.single i (1 : Ai i)) =
      φ (Pi.single i (1 : Ai i)) := by
    rw [← map_mul, ← Pi.single_mul, mul_one]
  have hi : φ (Pi.single i (1 : Ai i)) = 1 := by
    have h := hidem
    rwa [mul_left_eq_self₀, or_iff_left hi0] at h
  refine ⟨i, factorHom K Ai φ i hi, fun x => ?_⟩
  rw [factorHom_apply]
  have hx : x = Pi.single i (x i) + x * (1 - Pi.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply,
        Pi.single_eq_same, sub_self, mul_zero, add_zero]
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.one_apply,
        Pi.single_eq_of_ne hj, sub_zero, mul_one, zero_add]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, map_sub, map_one, hi, sub_self, mul_zero, add_zero]

end PiFactor

theorem exists_isGalois_forall_algHom_apply_mem
    (K : Type u) [Field K] (E : Type u) [CommRing E] [Algebra K E]
    [Module.Finite K E] [Algebra.FormallyUnramified K E]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L := by
  classical
  have : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_formallyUnramified_of_field K E
  obtain ⟨I, hI, Ai, hF, hA, iso, hsep⟩ :=
    (Algebra.FormallyEtale.iff_exists_algEquiv_prod K E).mp inferInstance
  have hfin : ∀ i, FiniteDimensional K (Ai i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.proj i).comp iso.toLinearMap)
      ((Function.surjective_eval i).comp iso.surjective)
  let N : I → IntermediateField K Ω := fun i => normalClosure K (Ai i) Ω
  refine ⟨⨆ i, N i, ?_, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_iSup_of_finite
  · have : Normal K (⨆ i, N i : IntermediateField K Ω) :=
      IntermediateField.normal_iSup (F := K) (K := Ω) N
    have : ∀ i, Algebra.IsSeparable K (N i) := by
      intro i
      rw [← le_separableClosure_iff]
      refine (normalClosure_le_iff).mpr fun ψ => ?_
      rintro _ ⟨a, rfl⟩
      rw [mem_separableClosure_iff]
      change IsSeparable K (ψ a)
      rw [IsSeparable, minpoly.algHom_eq ψ ψ.injective]
      exact Algebra.IsSeparable.isSeparable K a
    have : Algebra.IsSeparable K (⨆ i, N i : IntermediateField K Ω) :=
      IntermediateField.isSeparable_iSup K Ω
    exact ⟨⟩
  · intro φ e
    obtain ⟨i, ψ, hψ⟩ := exists_eq_comp_evalAlgHom K Ai (φ.comp iso.symm.toAlgHom)
    have hφ : φ e = ψ (iso e i) := by
      have h := hψ (iso e)
      simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
        AlgEquiv.symm_apply_apply] using h
    rw [hφ]
    have hle : N i ≤ ⨆ j, N j := le_iSup N i
    apply hle
    exact AlgHom.fieldRange_le_normalClosure ψ ⟨iso e i, rfl⟩

end P2mEtaleSplitting

theorem _root_.Algebra.FormallyUnramified.exists_isGalois_forall_algHom_apply_mem
    (K : Type u) [Field K] (E : Type u) [CommRing E] [Algebra K E]
    [Module.Finite K E] [Algebra.FormallyUnramified K E]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L :=
  P2mEtaleSplitting.exists_isGalois_forall_algHom_apply_mem K E Ω

end UnramifiedSplitting
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace DVRBirationalFlatness
open IsLocalRing

theorem _root_.IsDiscreteValuationRing.bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
    {O' O F : Type*} [CommRing O'] [IsNoetherianRing O'] [IsLocalRing O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O' O] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F]
    [IsFractionRing O F] [IsFractionRing O' F]
    [IsLocalHom (algebraMap O' O)] [Module.Flat O' O]
    (hinj : Function.Injective (algebraMap O' O))
    (π : O') (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime) :
    Function.Bijective (algebraMap O' O) := by
  classical
  have : IsDomain O' := Function.Injective.isDomain (algebraMap O' O) hinj
  have : (Ideal.span {π} : Ideal O').IsPrime := hπ
  have hπu : ¬ IsUnit π := by
    intro hu
    apply hπ.ne_top
    rw [Ideal.eq_top_iff_one]
    obtain ⟨v, hv⟩ := hu.exists_left_inv
    have : v * π ∈ Ideal.span {π} := Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    rwa [hv] at this
  have hπm : π ∈ maximalIdeal O' := (mem_maximalIdeal π).mpr (mem_nonunits_iff.mpr hπu)
  have hnf : ¬ IsField O' := fun hF => by
    have h := isField_iff_maximalIdeal_eq.mp hF
    rw [h, Ideal.mem_bot] at hπm
    exact hπ0 hπm
  have hunder : (maximalIdeal O).under O' = maximalIdeal O' := by
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff,
        mem_nonunits_iff,
      isUnit_map_iff]
  have : (maximalIdeal O).LiesOver (maximalIdeal O') := ⟨hunder.symm⟩
  have hle : Ideal.span {π} ≤ maximalIdeal O' := (Ideal.span_singleton_le_iff_mem _).mpr hπm
  obtain ⟨P, hPle, hPprime, hPover⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal O) hle
  have hPne : P ≠ ⊥ := by
    intro hP
    have h1 : (P.under O') = Ideal.span {π} := hPover.over.symm
    rw [hP, Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
        hinj] at h1
    exact hπ0 (Ideal.span_singleton_eq_bot.mp h1.symm)
  have hPmax : P = maximalIdeal O := by
    have : P.IsPrime := hPprime
    exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal hPprime hPne)
  have hmax : maximalIdeal O' = Ideal.span {π} := by
    rw [← hunder, ← hPmax]; exact hPover.over.symm
  have hprinc : (maximalIdeal O').IsPrincipal := ⟨⟨π, by rw [hmax]⟩⟩
  have : ValuationRing O' := ((IsDiscreteValuationRing.TFAE O' hnf).out 5 2).mp hprinc
  refine ⟨hinj, fun x => ?_⟩
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  have hinjO : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  rcases ValuationRing.isInteger_or_isInteger O' (algebraMap O F x) with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨a, hinjO ?_⟩
    rw [← IsScalarTower.algebraMap_apply]; exact ha
  · have hx' : algebraMap O F x ≠ 0 := fun h => hx (hinjO (by rw [h, map_zero]))
    have hmul : algebraMap O' O a * x = 1 := by
      apply hinjO
      rw [map_mul, map_one, ← IsScalarTower.algebraMap_apply, ha, inv_mul_cancel₀ hx']
    have hau : IsUnit a := (isUnit_map_iff (algebraMap O' O) a).mp (IsUnit.of_mul_eq_one _ hmul)
    obtain ⟨u, rfl⟩ := hau
    refine ⟨(u⁻¹ : O'ˣ), ?_⟩
    have : algebraMap O' O (u : O') * algebraMap O' O (↑u⁻¹ : O') = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc algebraMap O' O (↑u⁻¹ : O') = algebraMap O' O (↑u⁻¹ : O') * (algebraMap O' O (u : O') * x)
        := by rw [hmul, mul_one]
      _ = (algebraMap O' O (u : O') * algebraMap O' O (↑u⁻¹ : O')) * x := by ring
      _ = x := by rw [this, one_mul]

end DVRBirationalFlatness
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace UnramifiedDVRExtension
universe u v

open Polynomial

namespace UnramifiedExtensionOfDVR

theorem key
    (R : Type u) [CommRing R] [IsLocalRing R] (F : R[X]) :
    ∀ p : R[X], AdjoinRoot.quotEquivQuotMap F (IsLocalRing.maximalIdeal R)
        (Ideal.Quotient.mk _ (AdjoinRoot.mk F p)) = AdjoinRoot.mk (F.map (IsLocalRing.residue R))
            (p.map (IsLocalRing.residue R)) :=
  fun p => AdjoinRoot.quotEquivQuotMap_apply_mk F p (IsLocalRing.maximalIdeal R)

end UnramifiedExtensionOfDVR

theorem
    _root_.IsDiscreteValuationRing.exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k' : Type v) [Field k'] [Algebra (IsLocalRing.ResidueField R) k'] [FiniteDimensional
        (IsLocalRing.ResidueField R) k']
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) k'] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ :
        Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      Nonempty (k' ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R') := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable (IsLocalRing.ResidueField R) k'
  have hint : IsIntegral (IsLocalRing.ResidueField R) pb.gen := IsIntegral.of_finite _ _
  set g : (IsLocalRing.ResidueField R)[X] := minpoly (IsLocalRing.ResidueField R) pb.gen with hg
  have hgm : g.Monic := minpoly.monic hint
  have hgi : Irreducible g := minpoly.irreducible hint
  have hgs : g.Separable := Algebra.IsSeparable.isSeparable (IsLocalRing.ResidueField R) pb.gen
  have hgdeg : 0 < g.degree := minpoly.degree_pos hint
  obtain ⟨F, hFg, hFdeg, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts g).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective g)) hgm
  have hFdeg0 : F.degree ≠ 0 := by rw [hFdeg]; exact ne_of_gt hgdeg
  have : Nontrivial (AdjoinRoot F) := AdjoinRoot.nontrivial F hFdeg0
  have : Module.Finite R (AdjoinRoot F) := Module.Finite.of_basis (AdjoinRoot.powerBasis' hFm).basis
  have : Module.Free R (AdjoinRoot F) := Module.Free.of_basis (AdjoinRoot.powerBasis' hFm).basis
  have : Module.FaithfullyFlat R (AdjoinRoot F) := inferInstance
  have hfact : Fact (Irreducible (F.map (IsLocalRing.residue R))) := ⟨by rw [hFg]; exact hgi⟩
  set 𝔪' : Ideal (AdjoinRoot F) := Ideal.map (algebraMap R (AdjoinRoot F))
      (IsLocalRing.maximalIdeal R) with h𝔪'
  have h𝔪'of : 𝔪' = Ideal.map (AdjoinRoot.of F) (IsLocalRing.maximalIdeal R) := by
    rw [h𝔪', AdjoinRoot.algebraMap_eq]
  let θ₀ : (AdjoinRoot F ⧸ 𝔪') ≃+* AdjoinRoot (F.map (IsLocalRing.residue R)) :=
    (Ideal.quotEquivOfEq h𝔪'of).trans (AdjoinRoot.quotEquivQuotMap F (IsLocalRing.maximalIdeal
        R)).toRingEquiv
  have hθ₀ : ∀ p : R[X], θ₀ (Ideal.Quotient.mk 𝔪' (AdjoinRoot.mk F p)) =
      AdjoinRoot.mk (F.map (IsLocalRing.residue R)) (p.map (IsLocalRing.residue R)) := by
    intro p
    change AdjoinRoot.quotEquivQuotMap F (IsLocalRing.maximalIdeal R)
      (Ideal.quotEquivOfEq h𝔪'of (Ideal.Quotient.mk 𝔪' (AdjoinRoot.mk F p))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact UnramifiedExtensionOfDVR.key R F p
  have hfield : IsField (AdjoinRoot F ⧸ 𝔪') :=
    MulEquiv.isField (Field.toIsField (AdjoinRoot (F.map (IsLocalRing.residue R)))) θ₀.toMulEquiv
  have hmax : 𝔪'.IsMaximal := Ideal.Quotient.maximal_of_isField _ hfield
  have : Algebra.IsIntegral R (AdjoinRoot F) := Algebra.IsIntegral.of_finite R _
  have hloc : IsLocalRing (AdjoinRoot F) := by
    refine IsLocalRing.of_unique_max_ideal ⟨𝔪', hmax, fun M hM => ?_⟩
    have : M.IsMaximal := hM
    have hc : (M.comap (algebraMap R (AdjoinRoot F))) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) M)
    have hle : 𝔪' ≤ M := by
      rw [h𝔪', ← hc]; exact Ideal.map_comap_le
    exact (hmax.eq_of_le hM.ne_top hle).symm
  have hmR' : IsLocalRing.maximalIdeal (AdjoinRoot F) = 𝔪' := (IsLocalRing.eq_maximalIdeal
      hmax).symm
  have hlh : IsLocalHom (algebraMap R (AdjoinRoot F)) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R (AdjoinRoot F))).out 1 3).mpr (by
      rw [← h𝔪', hmR'])
  have hunit : ∀ p : R[X], AdjoinRoot.mk (F.map (IsLocalRing.residue R)) (p.map
      (IsLocalRing.residue R)) ≠ 0 →
      IsUnit (AdjoinRoot.mk F p) := by
    intro p hp
    by_contra hnu
    have hmem : AdjoinRoot.mk F p ∈ IsLocalRing.maximalIdeal (AdjoinRoot F) :=
      (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
    rw [hmR'] at hmem
    have h0 : Ideal.Quotient.mk 𝔪' (AdjoinRoot.mk F p) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem
    apply hp
    rw [← hθ₀ p, h0, map_zero]
  have hderiv : IsUnit (AdjoinRoot.mk F (derivative F)) := by
    apply hunit
    rw [← Polynomial.derivative_map]
    have hfs : (F.map (IsLocalRing.residue R)).Separable := by rw [hFg]; exact hgs
    obtain ⟨a, b, hab⟩ := hfs
    intro h0
    have h1 : AdjoinRoot.mk (F.map (IsLocalRing.residue R))
        (a * F.map (IsLocalRing.residue R) + b * derivative (F.map (IsLocalRing.residue R))) = 1
            := by
      rw [hab, map_one]
    rw [map_add, map_mul, map_mul, AdjoinRoot.mk_self, mul_zero, zero_add, h0, mul_zero] at h1
    exact zero_ne_one h1
  have hFi : Irreducible F := by
    apply hFm.irreducible_of_irreducible_map (IsLocalRing.residue R) F
    rw [hFg]
    exact hgi
  have hdom : IsDomain (AdjoinRoot F) := AdjoinRoot.isDomain_of_prime hFi.prime
  have : IsNoetherianRing (AdjoinRoot F) := Algebra.FiniteType.isNoetherianRing R (AdjoinRoot F)
  obtain ⟨ϖ, hϖ⟩ := (inferInstance : (IsLocalRing.maximalIdeal R).IsPrincipal)
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field R
    rw [hϖ]
    exact Submodule.span_zero_singleton R
  have hgen : IsLocalRing.maximalIdeal (AdjoinRoot F) = Ideal.span {algebraMap R (AdjoinRoot F) ϖ}
      := by
    rw [hmR', h𝔪', hϖ]
    change Ideal.map (algebraMap R (AdjoinRoot F)) (Ideal.span {ϖ}) = _
    rw [Ideal.map_span, Set.image_singleton]
  have hnf : ¬ IsField (AdjoinRoot F) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hgen, Ideal.span_singleton_eq_bot,
        AdjoinRoot.algebraMap_eq]
    intro h
    exact hϖ0 (AdjoinRoot.of.injective_of_degree_ne_zero hFdeg0 (by rw [h, map_zero]))
  have hpr : (IsLocalRing.maximalIdeal (AdjoinRoot F)).IsPrincipal := ⟨⟨algebraMap R (AdjoinRoot F)
      ϖ, hgen⟩⟩
  have hdvr : IsDiscreteValuationRing (AdjoinRoot F) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot F) hnf).out 1 5).mpr hpr
  obtain ⟨u, hu⟩ := hderiv.exists_right_inv
  obtain ⟨p₁, rfl⟩ := AdjoinRoot.mk_surjective u
  have hdvd : F ∣ derivative F * p₁ - 1 := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, hu, map_one, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  let P : StandardEtalePair R :=
    ⟨F, hFm, 1, p₁, -q, 0, by rw [pow_zero, mul_neg, ← hq]; ring⟩
  have hP1 : Submonoid.powers (AdjoinRoot.mk P.f P.g) ≤ IsUnit.submonoid (AdjoinRoot F) := by
    refine Submonoid.powers_le.2 ?_
    change IsUnit (AdjoinRoot.mk F 1)
    rw [map_one]; exact isUnit_one
  let e₁ : P.Ring ≃ₐ[R] Localization.Away (AdjoinRoot.mk P.f P.g) := P.equivAwayAdjoinRoot
  let e₂ : AdjoinRoot F ≃ₐ[AdjoinRoot F] Localization.Away (AdjoinRoot.mk P.f P.g) :=
    IsLocalization.atUnits (AdjoinRoot F) (Submonoid.powers (AdjoinRoot.mk P.f P.g)) hP1
  let e : P.Ring ≃ₐ[R] AdjoinRoot F := e₁.trans (e₂.restrictScalars R).symm
  have : Algebra.IsStandardEtale R (AdjoinRoot F) := Algebra.IsStandardEtale.of_equiv e
  have het : Algebra.Etale R (AdjoinRoot F) := inferInstance
  have hθ : ∀ x : IsLocalRing.ResidueField R,
      ((Ideal.quotEquivOfEq hmR').trans θ₀) (algebraMap (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField (AdjoinRoot F)) x) =
        algebraMap (IsLocalRing.ResidueField R) (AdjoinRoot (F.map (IsLocalRing.residue R))) x := by
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.algebraMap_residue, AdjoinRoot.algebraMap_eq,
        AdjoinRoot.algebraMap_eq]
    change θ₀ (Ideal.quotEquivOfEq hmR' (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot
        F)) (AdjoinRoot.mk F (C r)))) =
      AdjoinRoot.mk (F.map (IsLocalRing.residue R)) (C (IsLocalRing.residue R r))
    rw [Ideal.quotEquivOfEq_mk, hθ₀, Polynomial.map_C]
  let θ : IsLocalRing.ResidueField (AdjoinRoot F) ≃ₐ[IsLocalRing.ResidueField R] AdjoinRoot (F.map
      (IsLocalRing.residue R)) :=
    AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq hmR').trans θ₀) hθ
  have h₁ : aeval (AdjoinRoot.root (F.map (IsLocalRing.residue R))) (minpoly
      (IsLocalRing.ResidueField R) pb.gen) = 0 := by
    rw [← hg, ← hFg, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h₂ : aeval pb.gen (F.map (IsLocalRing.residue R)) = 0 := by
    rw [hFg]; exact minpoly.aeval _ _
  let e₃ : AdjoinRoot (F.map (IsLocalRing.residue R)) ≃ₐ[IsLocalRing.ResidueField R] k' :=
      AdjoinRoot.equiv' _ pb h₁ h₂
  exact ⟨AdjoinRoot F, inferInstance, hdom, hdvr, inferInstance, inferInstance, het, inferInstance,
      hlh,
    by rw [← h𝔪', hmR'], ⟨(θ.trans e₃).symm⟩⟩

end UnramifiedDVRExtension
end NOSProofs
end AbelianVarieties
end
