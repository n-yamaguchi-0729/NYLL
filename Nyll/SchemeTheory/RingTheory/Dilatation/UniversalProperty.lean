/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.RingTheory.Dilatation.Basic

/-!
# Universal properties and localization of affine dilatations
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace DilatationSurjections
universe u

namespace DilatationQuotient

open AffineDilatation

variable {R : Type u} [CommRing R] (π : R)
  {C : Type u} (A : Type u) [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A]
      [IsScalarTower R C A]

local notation "a" => algebraMap R C π
local notation "a'" => algebraMap R A π
local notation "q" => algebraMap C A
local notation "LC" => Localization.Away (algebraMap R C π)
local notation "LA" => Localization.Away (algebraMap R A π)

theorem q_a : q a = a' := (IsScalarTower.algebraMap_apply R C A π).symm

/-- The map between localizations induced by the quotient homomorphism. -/
noncomputable def Φ : LC →ₐ[C] LA :=
  IsLocalization.liftAlgHom (M := Submonoid.powers a) (f := Algebra.ofId C LA) (fun y => by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
    change IsUnit (algebraMap C LA y)
    rw [← hn, map_pow, IsScalarTower.algebraMap_apply C A LA, q_a π A]
    exact IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (S := LA) (algebraMap R A π)))

theorem Φ_algebraMap (c : C) : Φ π A (algebraMap C LC c) = algebraMap A LA (q c) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply C A LA]

theorem Φ_mk' (c : C) (n : ℕ) :
    Φ π A (IsLocalization.mk' LC c (⟨a ^ n, pow_mem (Submonoid.mem_powers _) n⟩ : Submonoid.powers
        a)) =
      IsLocalization.mk' LA (q c) (⟨a' ^ n, pow_mem (Submonoid.mem_powers _) n⟩ : Submonoid.powers
          a') := by
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have h : IsLocalization.mk' LC c (⟨a ^ n, pow_mem (Submonoid.mem_powers _) n⟩ : Submonoid.powers
      a) * algebraMap C LC (a ^ n) =
      algebraMap C LC c := IsLocalization.mk'_spec LC c ⟨a ^ n, pow_mem (Submonoid.mem_powers _) n⟩
  have h2 := congrArg (Φ π A) h
  rw [map_mul, Φ_algebraMap, Φ_algebraMap, map_pow, q_a π A] at h2
  rw [← h2]

theorem Φ_mem_subalgebra (J : Ideal C) (x : LC) (hx : x ∈ subalgebra J a) :
    Φ π A x ∈ subalgebra (J.map q) a' := by
  have hle : (subalgebra J a).map (Φ π A) ≤ (subalgebra (J.map q) a').restrictScalars C := by
    rw [subalgebra_eq_adjoin, AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    change Φ π A _ ∈ subalgebra (J.map q) a'
    have : Φ π A (IsLocalization.mk' LC g (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) =
        IsLocalization.mk' LA (q g) (⟨a', Submonoid.mem_powers a'⟩ : Submonoid.powers a') := by
      have h := Φ_mk' π A g 1
      simp only [pow_one] at h
      exact h
    rw [this]
    exact gen_subset _ _ ⟨q g, Ideal.mem_map_of_mem _ hg, rfl⟩
  exact hle ⟨x, hx, rfl⟩

/-- The induced homomorphism of affine dilatation algebras. -/
noncomputable def θ (J : Ideal C) :
    AffineDilatation.Ring J a →ₐ[C] AffineDilatation.Ring (J.map q) a' where
  toFun x := ⟨Φ π A x.1, Φ_mem_subalgebra π A J x.1 x.2⟩
  map_one' := Subtype.ext (by change Φ π A 1 = 1; exact map_one _)
  map_mul' x y := Subtype.ext (by
    change Φ π A (x.1 * y.1) = Φ π A x.1 * Φ π A y.1
    exact map_mul _ _ _)
  map_zero' := Subtype.ext (by change Φ π A 0 = 0; exact map_zero _)
  map_add' x y := Subtype.ext (by
    change Φ π A (x.1 + y.1) = Φ π A x.1 + Φ π A y.1
    exact map_add _ _ _)
  commutes' c := Subtype.ext (by
    change Φ π A (algebraMap C LC c) = algebraMap C LA c
    exact AlgHom.commutes _ _)

theorem coe_θ (J : Ideal C) (x : AffineDilatation.Ring J a) : ((θ π A J x : AffineDilatation.Ring
    (J.map q) a') : LA) = Φ π A x.1 := rfl

theorem θ_surjective (J : Ideal C) (hsurj : Function.Surjective q) : Function.Surjective (θ π A J)
    := by
  intro y
  suffices h : ∀ z : LA, z ∈ subalgebra (J.map q) a' → ∃ x : AffineDilatation.Ring J a, Φ π A x.1 =
      z by
    obtain ⟨x, hx⟩ := h y.1 y.2
    exact ⟨x, Subtype.ext hx⟩
  intro z hz
  rw [subalgebra_eq_adjoin] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨h, hh, rfl⟩ := hz
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective q hsurj).mp hh
    refine ⟨divElem J a g hg, ?_⟩
    have h := Φ_mk' π A g 1
    simp only [pow_one] at h
    exact h
  | algebraMap r =>
    obtain ⟨c, rfl⟩ := hsurj r
    exact ⟨algebraMap C _ c, Φ_algebraMap π A c⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx; obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [← hx', ← hy']; exact map_add _ _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx'⟩ := hx; obtain ⟨y', hy'⟩ := hy
    exact ⟨x' * y', by rw [← hx', ← hy']; exact map_mul _ _ _⟩

theorem θ_eq_zero_iff (J : Ideal C) (x : AffineDilatation.Ring J a) :
    θ π A J x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
      (RingHom.ker q).map (algebraMap C (AffineDilatation.Ring J a)) := by
  constructor
  · intro h0
    have h0' : Φ π A x.1 = 0 := by
      have := congrArg Subtype.val h0
      exact this
    obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.mk'_surjective (Submonoid.powers a) x.1
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hs : s = ⟨a ^ m, pow_mem (Submonoid.mem_powers _) m⟩ := Subtype.ext hm.symm
    subst hs
    simp only at hcs
    rw [← hcs, Φ_mk', IsLocalization.mk'_eq_zero_iff] at h0'
    obtain ⟨⟨t, ht⟩, hct⟩ := h0'
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp ht
    have hker : a ^ k * c ∈ RingHom.ker q := by
      rw [RingHom.mem_ker, map_mul, map_pow, q_a π A, hk]
      exact hct
    refine ⟨m + k, ?_⟩
    have heq : (algebraMap R (AffineDilatation.Ring J a) π) ^ (m + k) * x =
        algebraMap C (AffineDilatation.Ring J a) (a ^ k * c) := by
      apply Subtype.ext
      change (algebraMap R LC π) ^ (m + k) * x.1 = algebraMap C LC (a ^ k * c)
      have hspec : algebraMap C LC (a ^ m) *
          IsLocalization.mk' LC c (⟨a ^ m, pow_mem (Submonoid.mem_powers _) m⟩ : Submonoid.powers
              a) =
          algebraMap C LC c :=
        IsLocalization.mk'_spec' LC c ⟨a ^ m, pow_mem (Submonoid.mem_powers _) m⟩
      rw [IsScalarTower.algebraMap_apply R C LC, ← map_pow, add_comm, pow_add, map_mul, mul_assoc,
          ← hcs, hspec,
        ← map_mul]
    rw [heq]
    exact Ideal.mem_map_of_mem _ hker
  · rintro ⟨ν, hν⟩
    have hkill : ∀ y ∈ (RingHom.ker q).map (algebraMap C (AffineDilatation.Ring J a)), θ π A J y =
        0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        rw [AlgHom.commutes]
        apply Subtype.ext
        change algebraMap C LA i = 0
        rw [IsScalarTower.algebraMap_apply C A LA, RingHom.mem_ker.mp hi, map_zero]
      | zero => exact map_zero _
      | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
      | smul c y _ hy => rw [smul_eq_mul, map_mul, hy, mul_zero]
    have h := hkill _ hν
    rw [map_mul, map_pow] at h
    have hunit : IsUnit ((θ π A J) (algebraMap R (AffineDilatation.Ring J a) π) :
        AffineDilatation.Ring (J.map q) a').1 := by
      rw [coe_θ]
      change IsUnit (Φ π A (algebraMap R LC π))
      rw [IsScalarTower.algebraMap_apply R C LC, Φ_algebraMap, q_a π A]
      exact IsLocalization.Away.algebraMap_isUnit (S := LA) (algebraMap R A π)
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    change (((θ π A J) (algebraMap R _ π)).1) ^ ν * (θ π A J x).1 = 0 at h'
    exact (hunit.pow ν).mul_right_eq_zero.mp h'

theorem main (hsurj : Function.Surjective q) (J : Ideal C) :
    ∃ θ' : AffineDilatation.Ring J a →ₐ[C] AffineDilatation.Ring (J.map q) a',
      Function.Surjective θ' ∧
      ∀ x : AffineDilatation.Ring J a,
        θ' x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
          (RingHom.ker q).map (algebraMap C (AffineDilatation.Ring J a)) :=
  ⟨θ π A J, θ_surjective π A J hsurj, θ_eq_zero_iff π A J⟩

end DilatationQuotient

theorem _root_.AffineDilatation.exists_algHom_surjective_ker_iff_of_surjective
    {R : Type u} [CommRing R] (π : R)
    {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A]
        [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A)) (J : Ideal C) :
    ∃ θ' : AffineDilatation.Ring J (algebraMap R C π) →ₐ[C]
        AffineDilatation.Ring (J.map (algebraMap C A)) (algebraMap R A π),
      Function.Surjective θ' ∧
      ∀ x : AffineDilatation.Ring J (algebraMap R C π),
        θ' x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
          (RingHom.ker (algebraMap C A)).map (algebraMap C (AffineDilatation.Ring J (algebraMap R C
              π))) :=
  DilatationQuotient.main π A hsurj J

end DilatationSurjections
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AffineDilatation_nonempty_algHom_and_subsingleton_of_isSMulRegular.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace DilatationUniversal
universe u v

namespace AffineDilatation
open _root_.AffineDilatation
namespace UniversalProperty
open _root_.AffineDilatation

open scoped nonZeroDivisors

variable {A : Type u} [CommRing A]
variable {C : Type v} [CommRing C] [Algebra A C]

theorem algHom_ext (I : Ideal A) (a : A) (hreg : IsSMulRegular C a)
    (φ ψ : Ring I a →ₐ[A] C) : φ = ψ := by
  apply AlgHom.ext
  rintro ⟨x, hx⟩
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      change φ (divElem I a g hg) = ψ (divElem I a g hg)
      have h := congrArg φ (algebraMap_mul_divElem I a g hg)
      have h' := congrArg ψ (algebraMap_mul_divElem I a g hg)
      rw [map_mul, φ.commutes, φ.commutes] at h
      rw [map_mul, ψ.commutes, ψ.commutes] at h'
      refine hreg (?_ : a • φ (divElem I a g hg) = a • ψ (divElem I a g hg))
      rw [Algebra.smul_def, Algebra.smul_def, h, h']
  | algebraMap r =>
      exact (φ.commutes r).trans (ψ.commutes r).symm
  | add x y hx hy ihx ihy =>
      have : (⟨x + y, Subalgebra.add_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [this, map_add, map_add, ihx, ihy]
  | mul x y hx hy ihx ihy =>
      have : (⟨x * y, Subalgebra.mul_mem _ hx hy⟩ : Ring I a) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, map_mul, ihx, ihy]

theorem subsingleton_algHom (I : Ideal A) (a : A) (hreg : IsSMulRegular C a) :
    Subsingleton (Ring I a →ₐ[A] C) :=
  ⟨algHom_ext I a hreg⟩

theorem nonempty_algHom (I : Ideal A) (a : A) (hreg : IsSMulRegular C a)
    (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
    Nonempty (Ring I a →ₐ[A] C) := by
  classical
  set b : C := algebraMap A C a with hb
  let Ca := Localization.Away b
  let j : C →+* Ca := algebraMap C Ca
  have hj : Function.Injective j := by
    refine IsLocalization.injective Ca (M := Submonoid.powers b) ?_
    rw [Submonoid.powers_le]
    rw [mem_nonZeroDivisors_iff_right]
    intro c hc
    refine hreg (?_ : a • c = a • (0 : C))
    rw [Algebra.smul_def, Algebra.smul_def, mul_zero, mul_comm]
    exact hc
  have hunit : IsUnit ((j.comp (algebraMap A C)) a) := by
    change IsUnit (j b)
    exact IsLocalization.Away.algebraMap_isUnit b
  let Φ : Localization.Away a →+* Ca := IsLocalization.Away.lift a hunit
  have hΦalg : ∀ g : A, Φ (algebraMap A (Localization.Away a) g) = j (algebraMap A C g) := by
    intro g
    exact IsLocalization.Away.lift_eq a hunit g
  have hΦmk : ∀ g : A, Φ (IsLocalization.mk' (Localization.Away a) g
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) * j b = j (algebraMap A C g) := by
    intro g
    have h := IsLocalization.mk'_spec (Localization.Away a) g
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)
    have h' := congrArg Φ h
    rw [map_mul, hΦalg, hΦalg] at h'
    exact h'
  have hrange : ∀ x ∈ subalgebra I a, Φ x ∈ j.range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
        obtain ⟨g, hg, rfl⟩ := hx
        have hgC : algebraMap A C g ∈ Ideal.span {b} := hI (Ideal.mem_map_of_mem _ hg)
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hgC
        refine ⟨c, ?_⟩
        have h1 := hΦmk g
        rw [← hc, map_mul] at h1
        exact ((IsLocalization.Away.algebraMap_isUnit b).mul_left_injective h1).symm
    | algebraMap r => exact ⟨algebraMap A C r, (hΦalg r).symm⟩
    | add x y _ _ ihx ihy => rw [map_add]; exact Subring.add_mem _ ihx ihy
    | mul x y _ _ ihx ihy => rw [map_mul]; exact Subring.mul_mem _ ihx ihy
  let e : C ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun x y h => hj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective j⟩
  let ΦD : Ring I a →+* j.range :=
    (Φ.comp (subalgebra I a).val.toRingHom).codRestrict j.range (fun x => hrange x.1 x.2)
  let φ : Ring I a →+* C := e.symm.toRingHom.comp ΦD
  have hφ : ∀ x : Ring I a, j (φ x) = Φ x := by
    intro x
    have h1 : (e (φ x) : Ca) = (ΦD x : Ca) := by
      change (e (e.symm (ΦD x)) : Ca) = _
      rw [RingEquiv.apply_symm_apply]
    exact h1
  refine ⟨{ φ with commutes' := ?_ }⟩
  intro g
  apply hj
  change j (φ (algebraMap A (Ring I a) g)) = j (algebraMap A C g)
  rw [hφ]
  exact hΦalg g

end UniversalProperty
end AffineDilatation

theorem _root_.AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular
    {A : Type u} [CommRing A] (I : Ideal A) (a : A)
    {C : Type v} [CommRing C] [Algebra A C] (hreg : IsSMulRegular C a)
    (hI : I.map (algebraMap A C) ≤ Ideal.span {algebraMap A C a}) :
    Nonempty (AffineDilatation.Ring I a →ₐ[A] C) ∧
      Subsingleton (AffineDilatation.Ring I a →ₐ[A] C) :=
  ⟨AffineDilatation.UniversalProperty.nonempty_algHom I a hreg hI,
    AffineDilatation.UniversalProperty.subsingleton_algHom I a hreg⟩

end DilatationUniversal
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AffineDilatation_exists_algHom_isLocalization_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace DilatationLocalization
universe u v

namespace AffineDilatation
open _root_.AffineDilatation
namespace LocalizationCompat
open _root_.AffineDilatation

open _root_.AffineDilatation

variable {A : Type u} [CommRing A] (I : Ideal A) (a : A)
variable (M : Submonoid A) (A' : Type v) [CommRing A'] [Algebra A A'] [IsLocalization M A']

local notation "I'" => Ideal.map (algebraMap A A') I
local notation "a'" => algebraMap A A' a
local notation "D" => AffineDilatation.Ring I a
local notation "D'" => AffineDilatation.Ring (Ideal.map (algebraMap A A') I) (algebraMap A A' a)

omit [IsLocalization M A'] in
theorem mem_map (ha : a ∈ I) : a' ∈ I' := Ideal.mem_map_of_mem _ ha

omit [IsLocalization M A'] in
theorem isSMulRegular_target (ha : a ∈ I) : IsSMulRegular D' a := by
  have h := (AffineDilatation.isSMulRegular_and_map_eq_span_singleton I' a' (mem_map I a A' ha)).1
  intro x y hxy
  apply h
  change a' • x = a' • y
  rw [algebraMap_smul, algebraMap_smul]
  exact hxy

omit [IsLocalization M A'] in
theorem algebraMap_eq_comp : algebraMap A D' = (algebraMap A' D').comp (algebraMap A A') :=
  IsScalarTower.algebraMap_eq A A' D'

omit [IsLocalization M A'] in
theorem map_le_span (ha : a ∈ I) :
    I.map (algebraMap A D') ≤ Ideal.span {algebraMap A D' a} := by
  have h := (AffineDilatation.isSMulRegular_and_map_eq_span_singleton I' a' (mem_map I a A' ha)).2
  rw [algebraMap_eq_comp, ← Ideal.map_map, h]
  rfl

omit [IsLocalization M A'] in
theorem nonempty_algHom (ha : a ∈ I) : Nonempty (D →ₐ[A] D') :=
  (AffineDilatation.nonempty_algHom_and_subsingleton_of_isSMulRegular I a
    (isSMulRegular_target I a A' ha) (map_le_span I a A' ha)).1

omit [IsLocalization M A'] in
theorem pow_smul_eq_of_coe_eq {B : Type v} [CommRing B] (J : Ideal B) (b : B) (n : ℕ) (g : B)
    (x : AffineDilatation.Ring J b)
    (hx : (x : Localization.Away b) =
      IsLocalization.mk' (Localization.Away b) g (⟨b ^ n, n, rfl⟩ : Submonoid.powers b)) :
    b ^ n • x = algebraMap B (AffineDilatation.Ring J b) g := by
  apply Subtype.ext
  change (b ^ n • x : AffineDilatation.Ring J b).1 = algebraMap B (Localization.Away b) g
  rw [Algebra.smul_def]
  change algebraMap B (Localization.Away b) (b ^ n) * (x : Localization.Away b) = _
  rw [hx, mul_comm]
  exact IsLocalization.mk'_spec (Localization.Away b) g (⟨b ^ n, n, rfl⟩ : Submonoid.powers b)

omit [IsLocalization M A'] in
theorem pow_smul_map_eq (φ : D →ₐ[A] D') (n : ℕ) (g : A) (x : D)
    (hx : (x : Localization.Away a) =
      IsLocalization.mk' (Localization.Away a) g (⟨a ^ n, n, rfl⟩ : Submonoid.powers a)) :
    a ^ n • φ x = algebraMap A D' g := by
  rw [← map_smul, pow_smul_eq_of_coe_eq I a n g x hx, φ.commutes]

omit [IsLocalization M A'] in
theorem isSMulRegular_pow (ha : a ∈ I) (n : ℕ) : IsSMulRegular D' (a ^ n) :=
  IsSMulRegular.pow n (isSMulRegular_target I a A' ha)

private theorem map_units (φ : D →ₐ[A] D') (m : M) :
    IsUnit (φ (algebraMap A D (m : A))) := by
  rw [φ.commutes, algebraMap_eq_comp, RingHom.comp_apply]
  exact (IsLocalization.map_units A' m).map (algebraMap A' D')

theorem surj (ha : a ∈ I) (φ : D →ₐ[A] D') (y : D') :
    ∃ (x : D) (m : M), y * φ (algebraMap A D (m : A)) = φ x := by
  obtain ⟨n, g', hg', hy⟩ :=
    (AffineDilatation.mem_subalgebra_iff_exists_mem_pow I' a' (mem_map I a A' ha) y.1).1 y.2
  rw [← Ideal.map_pow] at hg'
  obtain ⟨⟨⟨g₀, hg₀⟩, m⟩, hgm⟩ := (IsLocalization.mem_map_algebraMap_iff M A').1 hg'
  simp only at hgm
  have hx₀ : IsLocalization.mk' (Localization.Away a) g₀ (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) ∈
      AffineDilatation.subalgebra I a :=
    (AffineDilatation.mem_subalgebra_iff_exists_mem_pow I a ha _).2 ⟨n, g₀, hg₀, rfl⟩
  refine ⟨⟨_, hx₀⟩, m, ?_⟩
  apply isSMulRegular_pow I a A' ha n
  change a ^ n • (y * φ (algebraMap A D (m : A))) = a ^ n • φ ⟨_, hx₀⟩
  rw [pow_smul_map_eq I a A' φ n g₀ ⟨_, hx₀⟩ rfl, ← smul_mul_assoc]
  have hy' : a ^ n • y = algebraMap A' D' g' := by
    rw [← algebraMap_smul A' (a ^ n) y, map_pow]
    exact pow_smul_eq_of_coe_eq I' a' n g' y hy.symm
  rw [hy', φ.commutes, algebraMap_eq_comp, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, hgm]

theorem exists_of_eq (ha : a ∈ I) (φ : D →ₐ[A] D') (x₁ x₂ : D) (h : φ x₁ = φ x₂) :
    ∃ c : Algebra.algebraMapSubmonoid D M, (c : D) * x₁ = (c : D) * x₂ := by
  obtain ⟨n₁, g₁, hg₁, hx₁⟩ := (AffineDilatation.mem_subalgebra_iff_exists_mem_pow I a ha x₁.1).1
      x₁.2
  obtain ⟨n₂, g₂, hg₂, hx₂⟩ := (AffineDilatation.mem_subalgebra_iff_exists_mem_pow I a ha x₂.1).1
      x₂.2
  have h₁ : a ^ (n₁ + n₂) • φ x₁ = algebraMap A D' (a ^ n₂ * g₁) := by
    rw [pow_add, mul_comm, mul_smul, pow_smul_map_eq I a A' φ n₁ g₁ x₁ hx₁.symm, Algebra.smul_def,
      ← map_mul]
  have h₂ : a ^ (n₁ + n₂) • φ x₂ = algebraMap A D' (a ^ n₁ * g₂) := by
    rw [pow_add, mul_smul, pow_smul_map_eq I a A' φ n₂ g₂ x₂ hx₂.symm, Algebra.smul_def, ← map_mul]
  have h12 : algebraMap A D' (a ^ n₂ * g₁) = algebraMap A D' (a ^ n₁ * g₂) := by
    rw [← h₁, ← h₂, h]
  have h12' : algebraMap A' (Localization.Away a') (algebraMap A A' (a ^ n₂ * g₁ - a ^ n₁ * g₂)) =
      0 := by
    have := congrArg (fun z : D' => (z : Localization.Away a')) h12
    change algebraMap A (Localization.Away a') (a ^ n₂ * g₁) =
      algebraMap A (Localization.Away a') (a ^ n₁ * g₂) at this
    rw [IsScalarTower.algebraMap_apply A A' (Localization.Away a'),
      IsScalarTower.algebraMap_apply A A' (Localization.Away a') (a ^ n₁ * g₂)] at this
    rw [map_sub, map_sub, this, sub_self]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a')
    (Localization.Away a') _).1 h12'
  have hk' : algebraMap A A' (a ^ k * (a ^ n₂ * g₁ - a ^ n₁ * g₂)) = 0 := by
    rw [map_mul, map_pow]; exact hk
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff M A' _).1 hk'
  refine ⟨⟨algebraMap A D (m : A), m, m.2, rfl⟩, ?_⟩
  apply Subtype.ext
  change algebraMap A (Localization.Away a) (m : A) * (x₁ : Localization.Away a) =
    algebraMap A (Localization.Away a) (m : A) * (x₂ : Localization.Away a)
  rw [← hx₁, ← hx₂, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.eq]
  refine ⟨⟨a ^ k, k, rfl⟩, ?_⟩
  simp only
  have hm' := hm
  rw [mul_sub, mul_sub, sub_eq_zero] at hm'
  calc a ^ k * (a ^ n₂ * ((m : A) * g₁)) = (m : A) * (a ^ k * (a ^ n₂ * g₁)) := by ring
    _ = (m : A) * (a ^ k * (a ^ n₁ * g₂)) := hm'
    _ = a ^ k * (a ^ n₁ * ((m : A) * g₂)) := by ring

theorem isLocalization (ha : a ∈ I) (φ : D →ₐ[A] D') :
    @IsLocalization _ _ (Algebra.algebraMapSubmonoid D M) D' _ φ.toRingHom.toAlgebra := by
  let : Algebra D D' := φ.toRingHom.toAlgebra
  have hφ : ∀ x : D, algebraMap D D' x = φ x := fun _ => rfl
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    rw [hφ]
    exact map_units I a M A' φ ⟨m, hm⟩
  · intro y
    obtain ⟨x, m, hxm⟩ := surj I a M A' ha φ y
    exact ⟨⟨x, ⟨algebraMap A D (m : A), m, m.2, rfl⟩⟩, by rw [hφ, hφ]; exact hxm⟩
  · intro x₁ x₂ hx
    rw [hφ, hφ] at hx
    exact exists_of_eq I a M A' ha φ x₁ x₂ hx

end LocalizationCompat
end AffineDilatation

theorem _root_.AffineDilatation.exists_algHom_isLocalization_map
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I)
    (M : Submonoid A) (A' : Type v) [CommRing A'] [Algebra A A'] [IsLocalization M A'] :
    ∃ φ : AffineDilatation.Ring I a →ₐ[A]
        AffineDilatation.Ring (I.map (algebraMap A A')) (algebraMap A A' a),
      @IsLocalization _ _ (Algebra.algebraMapSubmonoid (AffineDilatation.Ring I a) M)
        (AffineDilatation.Ring (I.map (algebraMap A A')) (algebraMap A A' a)) _
        φ.toRingHom.toAlgebra := by
  obtain ⟨φ⟩ := AffineDilatation.LocalizationCompat.nonempty_algHom I a A' ha
  exact ⟨φ, AffineDilatation.LocalizationCompat.isLocalization I a M A' ha φ⟩

end DilatationLocalization
end NOSProofs
end AbelianVarieties
end
