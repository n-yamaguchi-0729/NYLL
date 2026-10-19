/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-!
# Completion along an extended ideal

For an algebra `S/R` and an `S`-module, completion for `I` as an `R`-module
is canonically isomorphic to completion for `IS` as an `S`-module. The
quotient maps in every degree come from the actual equality of the
restricted submodules `I^n M = (IS)^n M`. They commute with transition maps,
so the comparison preserves the original maps from the module.
-/

noncomputable section

universe u v w

namespace AdicCompletion

variable {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
  [IsScalarTower R S M]

/-- The actual quotient in one degree is unchanged by extending the ideal
and regarding the module over the larger coefficient ring. -/
def mapIdealQuotientEquiv (n : ℕ) :
    (M ⧸ (I ^ n • (⊤ : Submodule R M))) ≃ₗ[R]
      M ⧸ ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)) :=
  (Submodule.quotEquivOfEq (I ^ n • (⊤ : Submodule R M))
    (((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)).restrictScalars R) (by
      rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq,
        Submodule.restrictScalars_top])).trans
    (Submodule.Quotient.restrictScalarsEquiv R
      ((I.map (algebraMap R S)) ^ n • (⊤ : Submodule S M)))

/-- The quotient comparison sends the class of an actual module element
to the class of the same element. -/
theorem mapIdealQuotientEquiv_mk (n : ℕ) (x : M) :
    mapIdealQuotientEquiv S I M n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x := by
  simp only [mapIdealQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, Submodule.Quotient.restrictScalarsEquiv_mk]

/-- The comparison of quotients commutes with the actual inverse-system
transition maps. -/
theorem mapIdealQuotientEquiv_transition {m n : ℕ} (hmn : m ≤ n)
    (x : M ⧸ (I ^ n • (⊤ : Submodule R M))) :
    transitionMap (I.map (algebraMap R S)) M hmn (mapIdealQuotientEquiv S I M n x) =
      mapIdealQuotientEquiv S I M m (transitionMap I M hmn x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule R M)) x
  rw [mapIdealQuotientEquiv_mk]
  exact (mapIdealQuotientEquiv_mk S I M m x).symm

/-- Completion over the original ring agrees with completion over the
algebra along the actual extended ideal. -/
def mapIdealEquiv :
    AdicCompletion I M ≃ₗ[R] AdicCompletion (I.map (algebraMap R S)) M where
  toFun x :=
    ⟨fun n => mapIdealQuotientEquiv S I M n (x.val n), by
      intro m n hmn
      rw [mapIdealQuotientEquiv_transition, x.property hmn]⟩
  invFun x :=
    ⟨fun n => (mapIdealQuotientEquiv S I M n).symm (x.val n), by
      intro m n hmn
      apply (mapIdealQuotientEquiv S I M m).injective
      rw [← mapIdealQuotientEquiv_transition,
        (mapIdealQuotientEquiv S I M n).apply_symm_apply,
        x.property hmn, (mapIdealQuotientEquiv S I M m).apply_symm_apply]⟩
  left_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (mapIdealQuotientEquiv S I M n).symm_apply_apply (x.val n)
  right_inv x := by
    apply AdicCompletion.ext
    intro n
    exact (mapIdealQuotientEquiv S I M n).apply_symm_apply (x.val n)
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    exact (mapIdealQuotientEquiv S I M n).map_add (x.val n) (y.val n)
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    exact (mapIdealQuotientEquiv S I M n).map_smul r (x.val n)

/-- The comparison retains the original canonical map of the module into
its completion. -/
theorem mapIdealEquiv_of (x : M) :
    mapIdealEquiv S I M (AdicCompletion.of I M x) =
      AdicCompletion.of (I.map (algebraMap R S)) M x := by
  apply AdicCompletion.ext
  intro n
  exact mapIdealQuotientEquiv_mk S I M n x

end AdicCompletion
