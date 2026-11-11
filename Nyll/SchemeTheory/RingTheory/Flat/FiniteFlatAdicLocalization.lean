/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Flat.FiniteFlatAdicCriterion
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Localizing the original flat adic reductions

The standard quotient/tensor and scalar-tower equivalences transport the
original flat reductions through arbitrary base change. At a prime containing
the original ideal, the existing finite local adic criterion then supplies
freeness of the original localized module.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace Module

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (M : Type u) [AddCommGroup M] [Module R M]

/-- Flatness of the actual quotient module is preserved by arbitrary
base change of the coefficient ring. -/
theorem flat_quotient_baseChange (I : Ideal R)
    [Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Flat (S ⧸ I.map (algebraMap R S))
      ((S ⊗[R] M) ⧸
        (I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)))) := by
  let J : Ideal S := I.map (algebraMap R S)
  let R₀ := R ⧸ I
  let S₀ := S ⧸ J
  let : Algebra R₀ S₀ := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have : IsScalarTower R R₀ S₀ := IsScalarTower.of_algebraMap_eq' rfl
  have : Flat R₀ (R₀ ⊗[R] M) :=
    Flat.of_linearEquiv ((TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective (I := I)))
  have : Flat S₀ (S₀ ⊗[R₀] (R₀ ⊗[R] M)) := inferInstance
  have : Flat S₀ (S₀ ⊗[R] M) :=
    Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R R₀ S₀ S₀ M).symm
  have : Flat S₀ (S₀ ⊗[S] (S ⊗[R] M)) :=
    Flat.of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S₀ S₀ M)
  exact Flat.of_linearEquiv
    ((TensorProduct.quotTensorEquivQuotSMul (S ⊗[R] M) J).extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective (I := J))).symm

/-- All actual flat adic reductions give a free base-changed module over
any Noetherian local coefficient algebra where the extended ideal is proper. -/
theorem free_baseChange_of_flat_adic_reductions
    [IsNoetherianRing S] [IsLocalRing S] [Module.Finite R M]
    (I : Ideal R) (hI : I.map (algebraMap R S) ≠ ⊤)
    (hflat : ∀ n : ℕ, Flat (R ⧸ I ^ (n + 1))
      (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) : Free S (S ⊗[R] M) := by
  apply IsLocalRing.free_of_flat_reductions_of_ne_top (S ⊗[R] M)
    (I.map (algebraMap R S)) hI
  intro n
  rw [← Ideal.map_pow]
  have : Flat (R ⧸ I ^ (n + 1))
      (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := hflat n
  exact flat_quotient_baseChange (S := S) M (I ^ (n + 1))

/-- At every prime containing the ideal, the original finite localized
module is free when its original positive adic reductions are flat. -/
theorem free_localizedModule_of_flat_adic_reductions
    [IsNoetherianRing R] [Module.Finite R M] (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p)
    (hflat : ∀ n : ℕ, Flat (R ⧸ I ^ (n + 1))
      (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))) :
    Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) := by
  let S := Localization.AtPrime p
  have hI : I.map (algebraMap R S) ≠ ⊤ := by
    intro htop
    have hle := Ideal.map_mono (f := algebraMap R S) hIp
    rw [htop, top_le_iff, IsLocalization.AtPrime.map_eq_maximalIdeal] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top hle
  have : Free S (S ⊗[R] M) := free_baseChange_of_flat_adic_reductions
    (S := S) M I hI hflat
  exact Free.of_equiv (LocalizedModule.isBaseChange p.primeCompl M).equiv

end Module
