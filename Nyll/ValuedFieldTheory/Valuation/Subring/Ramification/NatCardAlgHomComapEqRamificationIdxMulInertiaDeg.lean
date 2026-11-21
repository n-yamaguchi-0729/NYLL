/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.IsGaloisGroup.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Ring.RingNF
public import Nyll.ValuedFieldTheory.Valuation.Subring.Discrete.DVRAlgebraMapMemSeparable
public import Nyll.SchemeTheory.RingTheory.Localization.InertiaDegree

/-!
# Valuation Subring nat Card alg Hom comap eq ramification Idx mul inertia Deg
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg

open IsLocalRing IsDedekindDomain

open ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.EmbCountDvr
  (Over)

namespace KFA2a

open ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.EmbCountDvr
  (valuationSubringAtCenter_eq over_valuationSubringAtPrime overAlgebra
  algebraMap_injective algebraMap_overAlgebra_injective
  mem_of_mem_integralClosure ne_top_of_over coe_algebraMap_integralClosure
  algebraMap_integralClosure_injective isTorsionFree_integralClosure toOver coe_toOver center
  mem_center_iff
  center_isPrime center_ne_bot vOf mem_maximalIdeal_iff_inv_not_mem
  maximalIdeal_ne_bot liesOver_maximalIdeal)

section Dict

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]

theorem mem_nonunits_comap_iff {L L' : Type*} [Field L] [Field L'] (B : ValuationSubring L')
    (f : L →+* L') (x : L) : x ∈ (B.comap f).nonunits ↔ f x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

attribute [local instance] liesOver_maximalIdeal

omit K in
theorem comap_center (B : ValuationSubring F) (h : Over C B) :
    (center B h.mem).comap (algebraMap C (integralClosure C F)) = maximalIdeal C := by
  ext c
  rw [Ideal.mem_comap, mem_center_iff, coe_algebraMap_integralClosure, h.nonunit_iff]

scoped instance center_liesOver (B : ValuationSubring F) (h : Over C B) :
    (center B h.mem).LiesOver (maximalIdeal C) :=
  ⟨(comap_center B h).symm⟩

@[scoped simp] theorem vOf_asIdeal (B : ValuationSubring F) (h : Over C B) :
    (vOf K B h).asIdeal = center B h.mem := rfl

section dedekind

variable [IsDedekindDomain (integralClosure C F)] [IsFractionRing (integralClosure C F) F]

local notation "W" => HeightOneSpectrum.valuationSubringAtPrime F

omit [IsDomain C] [IsDiscreteValuationRing C] in
theorem isDiscreteValuationRing_W (v : HeightOneSpectrum (integralClosure C F)) :
    IsDiscreteValuationRing (W v) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure C F)
    v.ne_bot (W v)

include K in
theorem eq_of_center_eq (B B' : ValuationSubring F) (h : Over C B) (h' : Over C B')
    (hc : center B h.mem = center B' h'.mem) : B = B' := by
  rw [← valuationSubringAtCenter_eq K B h, ← valuationSubringAtCenter_eq K B' h']
  have : vOf K B h = vOf K B' h' := HeightOneSpectrum.ext hc
  rw [this]

/-- The product of the ramification index and residue degree above the base maximal ideal. -/
noncomputable def ef (B : ValuationSubring F) (h : ∀ c : C, algebraMap C F c ∈ B) : ℕ :=
  letI := overAlgebra B h
  (maximalIdeal C).ramificationIdx' (maximalIdeal B) * (maximalIdeal B).inertiaDeg C
include K in
theorem ef_W (v : HeightOneSpectrum (integralClosure C F)) :
    ef (W v) (over_valuationSubringAtPrime v).mem =
    (maximalIdeal C).ramificationIdx' v.asIdeal * v.asIdeal.inertiaDeg C := by
  let : Algebra C (W v) := overAlgebra (W v) (over_valuationSubringAtPrime v).mem
  have : IsScalarTower C (integralClosure C F) (W v) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  have : IsDiscreteValuationRing (W v) := isDiscreteValuationRing_W v
  have hmapS : Ideal.map (algebraMap (integralClosure C F) (W v)) v.asIdeal =
      maximalIdeal (W v) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal (W v)
  have hmW0 : maximalIdeal (W v) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have : (maximalIdeal (W v)).LiesOver v.asIdeal :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal (W v) v.asIdeal).symm⟩
  have he : (maximalIdeal C).ramificationIdx' (maximalIdeal (W v)) =
      (maximalIdeal C).ramificationIdx' v.asIdeal *
        v.asIdeal.ramificationIdx' (maximalIdeal (W v)) :=
    Ideal.ramificationIdx'_algebra_tower (by rw [hmapS]; exact hmW0)
      (by
        rw [Ne, Ideal.map_eq_bot_iff_of_injective (algebraMap_overAlgebra_injective K _ _)]
        exact IsDiscreteValuationRing.not_a_field C)
      hmapS.le
  have he1 : v.asIdeal.ramificationIdx' (maximalIdeal (W v)) = 1 := by
    rw [← hmapS]
    exact Ideal.ramificationIdx'_map_self_eq_one
      (by rw [hmapS]; exact (maximalIdeal.isMaximal _).ne_top) (by rw [hmapS]; exact hmW0)
  have hf : (maximalIdeal (W v)).inertiaDeg C =
      v.asIdeal.inertiaDeg C * (maximalIdeal (W v)).inertiaDeg (integralClosure C F) :=
    Ideal.inertiaDeg_tower _ _
  have hf1 : (maximalIdeal (W v)).inertiaDeg (integralClosure C F) = 1 :=
    _root_.IsLocalization.AtPrime.inertiaDeg_maximalIdeal_eq_one v.asIdeal (W v)
  change (maximalIdeal C).ramificationIdx' (maximalIdeal (W v)) *
      (maximalIdeal (W v)).inertiaDeg C = _
  rw [he, he1, hf, hf1, mul_one, mul_one]
include K in
theorem ef_eq (B : ValuationSubring F) (h : Over C B) :
    ef B h.mem = (maximalIdeal C).ramificationIdx' (center B h.mem) *
      (center B h.mem).inertiaDeg C := by
  have key : (⟨B, h⟩ : {B : ValuationSubring F // Over C B}) =
      ⟨W (vOf K B h), over_valuationSubringAtPrime _⟩ :=
    Subtype.ext (valuationSubringAtCenter_eq K B h).symm
  have := congrArg (fun x : {B : ValuationSubring F // Over C B} => ef x.1 x.2.mem) key
  simp only at this
  rw [this, ef_W K]
  rfl

end dedekind

end Dict

section Gal

open scoped Pointwise

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {κ : Type*} [Field κ] [Algebra K κ] [Algebra C κ] [IsScalarTower C K κ]
variable {N : Type*} [Field N] [Algebra K N] [Algebra C N] [IsScalarTower C K N]
variable [Algebra κ N] [IsScalarTower K κ N] [IsScalarTower C κ N]

/-- The map between integral closures induced by the inclusion of the intermediate field. -/
noncomputable def jS : integralClosure C κ →ₐ[C] integralClosure C N :=
  ((IsScalarTower.toAlgHom C κ N).comp (integralClosure C κ).val).codRestrict (integralClosure C N)
    (fun s => (mem_integralClosure_iff C N).mpr
      (((mem_integralClosure_iff C κ).mp s.2).map (IsScalarTower.toAlgHom C κ N)))
omit K [IsDomain C] [IsDiscreteValuationRing C] in
@[scoped simp] theorem coe_jS (s : integralClosure C κ) :
    ((jS (C := C) (κ := κ) (N := N) s : integralClosure C N) : N) = algebraMap κ N s := rfl
omit K [IsDomain C] [IsDiscreteValuationRing C] in
theorem jS_injective : Function.Injective (jS (C := C) (κ := κ) (N := N)) := by
  intro a b h
  have : algebraMap κ N a = algebraMap κ N b := congrArg (fun z : integralClosure C N => (z : N)) h
  exact Subtype.ext ((algebraMap κ N).injective this)

theorem card_smul_mem {G X : Type*} [Group G] [MulAction G X] [Finite G] (x₀ : X) (T : Set X)
    (hT : T ⊆ MulAction.orbit G x₀) (hTfin : T.Finite) :
    Nat.card {g : G // g • x₀ ∈ T} = Nat.card T * Nat.card (MulAction.stabilizer G x₀) := by
  classical
  have : Fintype T := hTfin.fintype
  let e := Equiv.sigmaSubtypeFiberEquivSubtype (fun g : G => g • x₀)
    (p := fun g => g • x₀ ∈ T) (q := fun x => x ∈ T) (fun _ => Iff.rfl)
  rw [← Nat.card_congr e, Nat.card_sigma]
  have hfib : ∀ t : T, Nat.card {g : G // g • x₀ = (t : X)} =
      Nat.card (MulAction.stabilizer G x₀) := by
    intro t
    obtain ⟨g₀, hg₀⟩ := MulAction.mem_orbit_iff.mp (hT t.2)
    refine Nat.card_congr
      { toFun := fun g => ⟨g₀⁻¹ * g.1, by
          rw [MulAction.mem_stabilizer_iff, mul_smul, g.2, ← hg₀, inv_smul_smul]⟩
        invFun := fun s => ⟨g₀ * s.1, by
          rw [mul_smul, MulAction.mem_stabilizer_iff.mp s.2, hg₀]⟩
        left_inv := fun g => Subtype.ext (mul_inv_cancel_left g₀ g.1)
        right_inv := fun s => Subtype.ext (inv_mul_cancel_left g₀ s.1) }
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
omit N [IsFractionRing C K] in
theorem over_comap {N' : Type*} [Field N'] [Algebra K N'] [Algebra C N'] [IsScalarTower C K N']
    (V : ValuationSubring N') (hV : Over C V) (τ : κ →ₐ[K] N') :
    Over C (V.comap (τ : κ →+* N')) := by
  have hτ : ∀ c : C, τ (algebraMap C κ c) = algebraMap C N' c := fun c => by
    rw [IsScalarTower.algebraMap_apply C K κ, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  refine ⟨fun c => ?_, fun c => ?_⟩
  · simp only [ValuationSubring.mem_comap, RingHom.coe_coe, hτ]
    exact hV.mem c
  · simp only [mem_nonunits_comap_iff, RingHom.coe_coe, hτ]
    exact hV.2 c

/-- The intermediate-field embedding obtained by composing inclusion with an automorphism. -/
noncomputable def twist (g : N ≃ₐ[K] N) : κ →ₐ[K] N :=
  (g : N →ₐ[K] N).comp (IsScalarTower.toAlgHom K κ N)
omit C in
@[scoped simp] theorem twist_apply (g : N ≃ₐ[K] N) (x : κ) :
    twist K (κ := κ) g x = g (algebraMap κ N x) := rfl

variable [FiniteDimensional K N] [IsGalois K N]
variable [IsDedekindDomain (integralClosure C κ)] [IsFractionRing (integralClosure C κ) κ]
variable [IsDedekindDomain (integralClosure C N)] [IsFractionRing (integralClosure C N) N]

theorem card_twist (V : ValuationSubring N) (hV : Over C V) (B : ValuationSubring κ)
    (hB : Over C B) [FiniteDimensional K κ] [Algebra.IsSeparable K κ] :
    Nat.card {g : N ≃ₐ[K] N // V.comap (twist K (κ := κ) g : κ →+* N) = B} =
      Module.finrank κ N * ef B hB.mem := by
  classical
  let algSS : Algebra (integralClosure C κ) (integralClosure C N) :=
    (jS (C := C) (κ := κ) (N := N)).toRingHom.toAlgebra
  have hSS : ∀ s : integralClosure C κ,
      algebraMap (integralClosure C κ) (integralClosure C N) s = jS s := fun s => rfl
  have : IsScalarTower (integralClosure C κ) (integralClosure C N) N :=
    ⟨fun s t n => by
      simp only [Algebra.smul_def, hSS, mul_assoc, map_mul]
      rfl⟩
  have : IsScalarTower C (integralClosure C κ) (integralClosure C N) :=
    IsScalarTower.of_algebraMap_eq (fun c => Subtype.ext (IsScalarTower.algebraMap_apply C κ N c))
  have : Module.IsTorsionFree (integralClosure C κ) (integralClosure C N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r c hrc
    rw [Algebra.smul_def] at hrc
    rcases mul_eq_zero.mp hrc with h | h
    · exact Or.inl (jS_injective (by rw [← hSS, h, map_zero]))
    · exact Or.inr h
  have : IsIntegralClosure (integralClosure C N) (integralClosure C κ) N :=
    { algebraMap_injective := Subtype.val_injective
      isIntegral_iff := fun {x} => by
        constructor
        · intro hx
          have : IsIntegral C x := isIntegral_trans (R := C) (A := integralClosure C κ) x hx
          exact ⟨⟨x, this⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact ((mem_integralClosure_iff C N).mp y.2).tower_top }
  have : Module.Finite κ N := Module.Finite.of_restrictScalars_finite K κ N
  have : Algebra.IsSeparable κ N := Algebra.isSeparable_tower_top_of_isSeparable K κ N
  have : Module.Finite (integralClosure C κ) (integralClosure C N) :=
    IsIntegralClosure.finite (integralClosure C κ) κ N (integralClosure C N)
  have : Module.Finite C (integralClosure C N) := IsIntegralClosure.finite C K N (integralClosure C
    N)
  have : Module.IsTorsionFree C (integralClosure C N) := isTorsionFree_integralClosure K
  let galAct : MulSemiringAction (N ≃ₐ[K] N) (integralClosure C N) :=
    IsIntegralClosure.MulSemiringAction C K N (integralClosure C N)
  have : IsGaloisGroup (N ≃ₐ[K] N) C (integralClosure C N) :=
    IsGaloisGroup.of_isFractionRing _ _ _ K N
  have coe_smul : ∀ (g : N ≃ₐ[K] N) (s : integralClosure C N),
      ((g • s : integralClosure C N) : N) = g (s : N) := fun g s => algebraMap_galRestrict_apply C
        g s
  set P₀ : Ideal (integralClosure C N) := center V hV.mem with hP₀
  set 𝔮 : Ideal (integralClosure C κ) := center B hB.mem with h𝔮
  have : 𝔮.IsPrime := center_isPrime B hB.mem
  have h𝔮0 : 𝔮 ≠ ⊥ := center_ne_bot K B hB
  have h𝔮max : 𝔮.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔮0 inferInstance
  have : 𝔮.LiesOver (maximalIdeal C) := center_liesOver B hB
  have : P₀.IsPrime := center_isPrime V hV.mem
  have : P₀.LiesOver (maximalIdeal C) := center_liesOver V hV
  have key : ∀ g : N ≃ₐ[K] N, ∀ s : integralClosure C κ,
      (s ∈ center (V.comap (twist K (κ := κ) g : κ →+* N)) (over_comap K V hV (twist K g)).1 ↔
        s ∈ (g⁻¹ • P₀).comap (algebraMap (integralClosure C κ) (integralClosure C N))) := by
    intro g s
    rw [mem_center_iff, mem_nonunits_comap_iff, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff,
      mem_center_iff, coe_smul, hSS, coe_jS, RingHom.coe_coe, twist_apply]
  have step1 : ∀ g : N ≃ₐ[K] N,
      V.comap (twist K (κ := κ) g : κ →+* N) = B ↔
        (g⁻¹ • P₀).comap (algebraMap (integralClosure C κ) (integralClosure C N)) = 𝔮 := by
    intro g
    constructor
    · intro h
      have hc : center (V.comap (twist K (κ := κ) g : κ →+* N))
          (over_comap K V hV (twist K g)).1 = 𝔮 := by
        rw [h𝔮]; subst h; rfl
      rw [← hc]; ext s; exact (key g s).symm
    · intro h
      refine eq_of_center_eq K _ _ (over_comap K V hV (twist K g)) hB ?_
      ext s; rw [key g s, h]
  set T : Set (Ideal (integralClosure C N)) :=
    ↑(IsDedekindDomain.primesOverFinset 𝔮 (integralClosure C N)) with hT
  have hTcoe : T = 𝔮.primesOver (integralClosure C N) := by
    rw [hT, IsDedekindDomain.coe_primesOverFinset h𝔮0 (integralClosure C N)]
  have hT_orbit : T ⊆ MulAction.orbit (N ≃ₐ[K] N) P₀ := by
    rw [Algebra.IsInvariant.orbit_eq_primesOver C (integralClosure C N) (N ≃ₐ[K] N)
      (maximalIdeal C) P₀, hTcoe]
    rintro P ⟨hP, hPover⟩
    exact ⟨hP, Ideal.LiesOver.trans P 𝔮 (maximalIdeal C)⟩
  have hmemT : ∀ g : N ≃ₐ[K] N,
      ((g⁻¹ • P₀).comap (algebraMap (integralClosure C κ) (integralClosure C N)) = 𝔮 ↔
        g⁻¹ • P₀ ∈ T) := by
    intro g
    rw [hTcoe]
    constructor
    · intro h
      exact ⟨inferInstance, ⟨by rw [Ideal.under_def, h]⟩⟩
    · rintro ⟨_, hover⟩
      rw [← Ideal.under_def]
      exact hover.over.symm
  have step2 : Nat.card {g : N ≃ₐ[K] N // V.comap (twist K (κ := κ) g : κ →+* N) = B} =
      Nat.card T * Nat.card (MulAction.stabilizer (N ≃ₐ[K] N) P₀) := by
    rw [← card_smul_mem P₀ T hT_orbit (hT ▸ Finset.finite_toSet _)]
    refine Nat.card_congr ((Equiv.subtypeEquivRight (fun g => (step1 g).trans (hmemT g))).trans ?_)
    exact (Equiv.inv (N ≃ₐ[K] N)).subtypeEquiv (fun g => Iff.rfl)
  set eN := (maximalIdeal C).ramificationIdxIn (integralClosure C N) with heN
  set fN := (maximalIdeal C).inertiaDegIn (integralClosure C N) with hfN
  have hG : ((maximalIdeal C).primesOver (integralClosure C N)).ncard * (eN * fN) =
      Nat.card (N ≃ₐ[K] N) :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal C)
      (integralClosure C N) (N ≃ₐ[K] N)
  have hidx : ((maximalIdeal C).primesOver (integralClosure C N)).ncard *
      Nat.card (MulAction.stabilizer (N ≃ₐ[K] N) P₀) = Nat.card (N ≃ₐ[K] N) := by
    rw [← Algebra.IsInvariant.orbit_eq_primesOver C (integralClosure C N) (N ≃ₐ[K] N)
      (maximalIdeal C) P₀, ← MulAction.index_stabilizer, Subgroup.index_mul_card]
  have hr0 : ((maximalIdeal C).primesOver (integralClosure C N)).ncard ≠ 0 :=
    IsDedekindDomain.primesOver_ncard_ne_zero (maximalIdeal C) (integralClosure C N)
  have step3 : Nat.card (MulAction.stabilizer (N ≃ₐ[K] N) P₀) = eN * fN :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr0) (hidx.trans hG.symm)
  have hsum :
      ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔮 (integralClosure C N),
        𝔮.ramificationIdx' P * P.inertiaDeg (integralClosure C κ) = Module.finrank κ N := by
    calc
      _ = ∑ P ∈ IsDedekindDomain.primesOverFinset 𝔮 (integralClosure C N),
            P.ramificationIdx (integralClosure C κ) *
              P.inertiaDeg (integralClosure C κ) := by
          refine Finset.sum_congr rfl ?_
          intro P hP
          obtain ⟨hPprime, hPover⟩ :=
            (IsDedekindDomain.mem_primesOverFinset_iff h𝔮0 (integralClosure C N)).mp hP
          let : P.IsPrime := hPprime
          let : P.LiesOver 𝔮 := hPover
          rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ h𝔮0]
      _ = ∑ P : (IsDedekindDomain.primesOverFinset 𝔮 (integralClosure C N)),
            P.1.ramificationIdx (integralClosure C κ) *
              P.1.inertiaDeg (integralClosure C κ) := by
          exact (Finset.sum_coe_sort
            (IsDedekindDomain.primesOverFinset 𝔮 (integralClosure C N))
            (fun P : Ideal (integralClosure C N) =>
              P.ramificationIdx (integralClosure C κ) * P.inertiaDeg (integralClosure C κ))).symm
      _ = ∑ P : 𝔮.primesOver (integralClosure C N),
            P.1.ramificationIdx (integralClosure C κ) *
              P.1.inertiaDeg (integralClosure C κ) := by
          exact Fintype.sum_equiv
            (Set.equivOfEq (IsDedekindDomain.coe_primesOverFinset h𝔮0 (integralClosure C N)))
            _ _ (by intro P; rfl)
      _ = Module.finrank (integralClosure C κ) (integralClosure C N) :=
        Ideal.sum_ramification_inertia_eq_finrank 𝔮 (integralClosure C N)
      _ = Module.finrank κ N :=
        (IsFractionRing.finrank_eq (integralClosure C κ) κ (integralClosure C N) N).symm
  have hterm : ∀ P ∈ IsDedekindDomain.primesOverFinset 𝔮 (integralClosure C N),
      eN * fN = ((maximalIdeal C).ramificationIdx' 𝔮 * 𝔮.inertiaDeg C) *
        (𝔮.ramificationIdx' P * P.inertiaDeg (integralClosure C κ)) := by
    intro P hP
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset h𝔮0 (integralClosure C N)] at hP
    obtain ⟨hPprime, hPover⟩ := hP
    have : P.LiesOver (maximalIdeal C) := Ideal.LiesOver.trans P 𝔮 (maximalIdeal C)
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔮0 P
    have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hPprime
    rw [heN, hfN, Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal C) P (N ≃ₐ[K] N),
      Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal C) P (N ≃ₐ[K] N),
      ← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal C) P
        (IsDiscreteValuationRing.not_a_field C)]
    have he : (maximalIdeal C).ramificationIdx' P =
        (maximalIdeal C).ramificationIdx' 𝔮 * 𝔮.ramificationIdx' P := by
      refine Ideal.ramificationIdx'_algebra_tower ?_ ?_ ?_
      · rw [Ne, Ideal.map_eq_bot_iff_of_injective]
        · exact h𝔮0
        · intro a b hab
          exact jS_injective (by rw [← hSS, ← hSS]; exact hab)
      · rw [Ne, Ideal.map_eq_bot_iff_of_injective (algebraMap_integralClosure_injective (F := N) K)]
        exact IsDiscreteValuationRing.not_a_field C
      · exact Ideal.map_le_iff_le_comap.mpr (le_of_eq
          (by rw [← Ideal.under_def]; exact hPover.over))
    have hf : P.inertiaDeg C = 𝔮.inertiaDeg C * P.inertiaDeg (integralClosure C κ) :=
      Ideal.inertiaDeg_tower _ _
    rw [he, hf]; ring
  have hcardT : Nat.card T = (IsDedekindDomain.primesOverFinset 𝔮 (integralClosure C N)).card := by
    rw [hT, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have step4 : Nat.card T * (eN * fN) =
      ((maximalIdeal C).ramificationIdx' 𝔮 * 𝔮.inertiaDeg C) *
        Module.finrank κ N := by
    rw [← hsum, Finset.mul_sum, hcardT, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl hterm
  rw [step2, step3, step4, ef_eq K B hB, mul_comm]

end Gal

section Emb

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]

theorem card_stabilizer_algHom {κ N : Type*} [Field κ] [Field N] [Algebra K κ] [Algebra K N]
    [Algebra κ N] [IsScalarTower K κ N] [FiniteDimensional K N] [IsGalois K N]
    (act : MulAction (N ≃ₐ[K] N) (κ →ₐ[K] N))
    (hact : ∀ (g : N ≃ₐ[K] N) (τ : κ →ₐ[K] N), g • τ = (g : N →ₐ[K] N).comp τ) :
    Nat.card (MulAction.stabilizer (N ≃ₐ[K] N) (IsScalarTower.toAlgHom K κ N)) =
      Module.finrank κ N := by
  have : IsGalois κ N := IsGalois.tower_top_of_isGalois K κ N
  have : Module.Finite κ N := Module.Finite.of_restrictScalars_finite K κ N
  rw [← IsGalois.card_aut_eq_finrank κ N]
  refine Nat.card_congr
    { toFun := fun g => AlgEquiv.ofRingEquiv (f := (g.1 : N ≃+* N)) (fun x => by
        have h := g.2
        rw [MulAction.mem_stabilizer_iff, hact] at h
        exact AlgHom.congr_fun h x)
      invFun := fun h => ⟨AlgEquiv.restrictScalars K h, by
        rw [MulAction.mem_stabilizer_iff, hact]
        ext x
        exact h.commutes x⟩
      left_inv := fun g => Subtype.ext (by ext; rfl)
      right_inv := fun h => by ext; rfl }

end Emb

end KFA2a

open KFA2a in
theorem _root_.ValuationSubring.natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {L : Type*} [Field L] [IsAlgClosed L] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
      [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hCA : ∀ c : C, algebraMap C L c ∈ A)
    (hCAmax : ∀ c : C, (⟨algebraMap C L c, hCA c⟩ : ↥A) ∈ maximalIdeal ↥A ↔ c ∈ maximalIdeal C)
    (κ : Type*) [Field κ] [Algebra K κ] [Algebra C κ] [IsScalarTower C K κ] [FiniteDimensional K κ]
      [Algebra.IsSeparable K κ]
    (B : ValuationSubring κ) (hCB : ∀ c : C, algebraMap C κ c ∈ B)
    (hCBmax : ∀ c : C, (⟨algebraMap C κ c, hCB c⟩ : ↥B) ∈ maximalIdeal ↥B ↔ c ∈ maximalIdeal C) :
    Finite {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B} ∧
    Nat.card {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B} =
      (letI : Algebra C ↥B := ((algebraMap C κ).codRestrict B hCB).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B) * (maximalIdeal ↥B).inertiaDeg C) := by
  classical
  refine ⟨inferInstance, ?_⟩
  have hB : Over C B :=
    ⟨hCB, fun c => by rw [← hCBmax c, ← ValuationSubring.coe_mem_nonunits_iff]⟩
  have hA : Over C A :=
    ⟨hCA, fun c => by rw [← hCAmax c, ← ValuationSubring.coe_mem_nonunits_iff]⟩
  have : IsAlgClosure K L := (isAlgClosure_iff K L).mpr ⟨inferInstance, inferInstance⟩
  set N : IntermediateField K L := IntermediateField.normalClosure K κ L with hN
  have : Algebra.IsSeparable K N := by
    rw [hN, normalClosure_def]
    have : ∀ f : κ →ₐ[K] L, Algebra.IsSeparable K f.fieldRange := fun f =>
      ⟨fun x => by
        obtain ⟨y, hy⟩ := (AlgHom.mem_fieldRange).mp x.2
        refine IsSeparable.of_algHom (F := K) (K := ↥f.fieldRange) (E := L)
          (f := f.fieldRange.val) ?_
        change IsSeparable K (x : L)
        rw [← hy]
        exact IsSeparable.map f f.injective (Algebra.IsSeparable.isSeparable K y)⟩
    infer_instance
  have : IsGalois K N := IsGalois.mk
  have hne : Nonempty (κ →ₐ[K] L) := ⟨IsAlgClosed.lift⟩
  let σ₀ : κ →ₐ[K] N := (normalClosure.algHomEquiv K κ L).symm hne.some
  let : Algebra κ N := σ₀.toRingHom.toAlgebra
  have : IsScalarTower K κ N := IsScalarTower.of_algebraMap_eq (fun x => (σ₀.commutes x).symm)
  have : IsScalarTower C κ N := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap C N c = σ₀ (algebraMap C κ c)
    rw [IsScalarTower.algebraMap_apply C K κ, AlgHom.commutes, ← IsScalarTower.algebraMap_apply])
  have hσ₀ : IsScalarTower.toAlgHom K κ N = σ₀ := AlgHom.ext fun x => rfl
  have : IsFractionRing (integralClosure C κ) κ :=
    integralClosure.isFractionRing_of_finite_extension K κ
  have : IsDedekindDomain (integralClosure C κ) :=
    IsIntegralClosure.isDedekindDomain C K κ (integralClosure C κ)
  have : IsFractionRing (integralClosure C N) N :=
    integralClosure.isFractionRing_of_finite_extension K N
  have : IsDedekindDomain (integralClosure C N) :=
    IsIntegralClosure.isDedekindDomain C K N (integralClosure C N)
  let ι : N →ₐ[K] L := N.val
  have hAN : Over C (A.comap (ι : N →+* L)) := KFA2a.over_comap K A hA ι
  have hcount := KFA2a.card_twist K (A.comap (ι : N →+* L)) hAN B hB
  let act : MulAction (N ≃ₐ[K] N) (κ →ₐ[K] N) :=
    { smul := fun g τ => (g : N →ₐ[K] N).comp τ
      one_smul := fun τ => by ext; rfl
      mul_smul := fun g h τ => by ext; rfl }
  have hact : ∀ (g : N ≃ₐ[K] N) (τ : κ →ₐ[K] N), g • τ = (g : N →ₐ[K] N).comp τ := fun _ _ => rfl
  have htwist : ∀ g : N ≃ₐ[K] N, KFA2a.twist K (κ := κ) g = g • IsScalarTower.toAlgHom K κ N :=
    fun g => rfl
  have horbit : ∀ τ : κ →ₐ[K] N, τ ∈ MulAction.orbit (N ≃ₐ[K] N) (IsScalarTower.toAlgHom K κ N) :=
    by
    intro τ
    let φ : N →ₐ[K] N := AlgHom.liftNormal τ N
    have hφ : ∀ x : κ, φ (algebraMap κ N x) = τ x := fun x => AlgHom.liftNormal_commutes τ N x
    refine MulAction.mem_orbit_iff.mpr ⟨AlgEquiv.ofBijective φ (AlgHom.normal_bijective K N N φ),
      ?_⟩
    rw [hact]
    exact AlgHom.ext fun x => hφ x
  set T : Set (κ →ₐ[K] N) := {τ | (A.comap (ι : N →+* L)).comap (τ : κ →+* N) = B} with hT
  have h1 : Nat.card {g : N ≃ₐ[K] N //
      (A.comap (ι : N →+* L)).comap (KFA2a.twist K (κ := κ) g : κ →+* N) = B} =
      Nat.card T * Module.finrank κ N := by
    rw [← KFA2a.card_stabilizer_algHom K act hact,
      ← KFA2a.card_smul_mem (IsScalarTower.toAlgHom K κ N) T (fun τ _ => horbit τ) (Set.toFinite T)]
    rfl
  have h2 : Nat.card T = Nat.card {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B} := by
    refine Nat.card_congr ((normalClosure.algHomEquiv K κ L).subtypeEquiv fun τ => ?_)
    change (A.comap (ι : N →+* L)).comap (τ : κ →+* N) = B ↔
      A.comap ((normalClosure.algHomEquiv K κ L τ : κ →ₐ[K] L) : κ →+* L) = B
    have : (A.comap (ι : N →+* L)).comap (τ : κ →+* N) =
        A.comap ((normalClosure.algHomEquiv K κ L τ : κ →ₐ[K] L) : κ →+* L) := by
      ext x; simp only [ValuationSubring.mem_comap, RingHom.coe_coe]; rfl
    rw [this]
  have hpos : 0 < Module.finrank κ N := by
    have : Module.Finite κ N := Module.Finite.of_restrictScalars_finite K κ N
    exact Module.finrank_pos
  have h3 : Nat.card T = KFA2a.ef B hCB := by
    have := h1.symm.trans hcount
    rw [mul_comm] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [← h2, h3]
  rfl
end ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
