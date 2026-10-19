/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.FractionField
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The entire generic fibre of a finite étale domain

For a finite étale algebra of domains `T / R`, a compatible fraction field
of `T` is its whole generic fibre over a fraction field of `R`. The
comparison uses the original product of the two structural maps. In
particular, it retains the actual field extension supplied by a connected
finite étale cover when further generic base changes are performed.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uT uK uL

/-- The whole generic fibre of a finite étale domain is its specified
compatible fraction field, with the original product-map values. -/
def finiteEtaleGenericFiberFractionFieldEquiv
    (R : Type uR) (T : Type uT) (K : Type uK) (L : Type uL)
    [CommRing R] [IsDomain R] [CommRing T] [IsDomain T] [Algebra R T]
    [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra T L] [Algebra K L]
    [IsScalarTower R T L] [IsScalarTower R K L] [IsFractionRing T L] :
    let : Algebra K (T ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
    T ⊗[R] K ≃ₐ[K] L := by
  intro aKG
  let G := T ⊗[R] K
  let f : G →ₐ[R] L := finiteEtaleGenericFiberToFractionField
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hRT : Function.Injective (algebraMap R T) := by
    intro x y hxy
    apply hRL
    rw [IsScalarTower.algebraMap_apply R T L,
      IsScalarTower.algebraMap_apply R T L, hxy]
  let M := Algebra.algebraMapSubmonoid T (nonZeroDivisors R)
  have hM : M ≤ nonZeroDivisors T := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    simpa only [map_zero] using hRT.ne (nonZeroDivisors.ne_zero hr)
  have : IsDomain G := IsLocalization.isDomain_of_le_nonZeroDivisors G hM
  let eComm : K ⊗[R] T ≃ₐ[K] G := Algebra.TensorProduct.commRight R K T
  have : Module.Finite K G :=
    Module.Finite.of_surjective eComm.toLinearMap eComm.surjective
  have : IsArtinianRing G := IsArtinianRing.of_finite K G
  let : Field G := (IsArtinianRing.isField_of_isDomain G).toField
  let e : G ≃ₐ[R] L := AlgEquiv.ofBijective f
    ⟨f.toRingHom.injective,
      finiteEtaleGenericFiberToFractionField_surjective (R := R) (T := T) (K := K)⟩
  refine { e.toRingEquiv with commutes' := ?_ }
  intro k
  change f (algebraMap K G k) = algebraMap K L k
  rw [Algebra.TensorProduct.right_algebraMap_apply]
  change finiteEtaleGenericFiberToFractionField (R := R) (T := T) (K := K) (L := L)
    (1 ⊗ₜ[R] k) = algebraMap K L k
  rw [finiteEtaleGenericFiberToFractionField_tmul, map_one, one_mul]

/-- The generic-fibre equivalence keeps the two actual structural maps. -/
theorem finiteEtaleGenericFiberFractionFieldEquiv_tmul
    (R : Type uR) (T : Type uT) (K : Type uK) (L : Type uL)
    [CommRing R] [IsDomain R] [CommRing T] [IsDomain T] [Algebra R T]
    [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra T L] [Algebra K L]
    [IsScalarTower R T L] [IsScalarTower R K L] [IsFractionRing T L] :
    let : Algebra K (T ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
    ∀ (t : T) (k : K), finiteEtaleGenericFiberFractionFieldEquiv R T K L (t ⊗ₜ[R] k) =
      algebraMap T L t * algebraMap K L k := by
  intro aKG t k
  exact finiteEtaleGenericFiberToFractionField_tmul t k

end EtaleFundamentalGroups
