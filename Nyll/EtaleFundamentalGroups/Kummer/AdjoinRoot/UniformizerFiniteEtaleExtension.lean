/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerNormalizationEtale
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.SchemeTheory.RingTheory.GenericFiber.Finite
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRFiniteEtaleAlgebra
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# A finite étale normalized extension after an explicitly chosen root

For a finite separable extension `L / Frac(V)` of a DVR with residue
characteristic zero, let `d` be the field degree. Adjoining a `d!`-th root
of any specified uniformizer produces a DVR `W` such that the integral
closure of `W` in the entire original tensor product
`Frac(W) ⊗[Frac(V)] L` is finite étale. Its actual generic fibre is that
same tensor product, through an algebra equivalence over `Frac(W)`.

The exponent bound is proved from the finite flat ramification identity
and the generic fibre of the original integral closure. Neither branch
divisibility nor the existence of an étale normalization is a hypothesis.
The source DVR need not be complete or henselian.

This is the local normalized extension used in Stacks Project,
Proposition 58.30.2, https://stacks.math.columbia.edu/tag/0C0Q.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe uV uC uL

private theorem branchIndex_dvd_factorial_degree
    {V : Type uV} {C : Type uC}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing C] [IsDedekindDomain C] [Algebra V C]
    [Module.IsTorsionFree V C] [Module.Finite V C]
    {L : Type uL} [Field L] [Algebra C L] [IsFractionRing C L]
    [Algebra V L] [IsScalarTower V C L]
    [Algebra (FractionRing V) L] [IsScalarTower V (FractionRing V) L]
    (Q : (IsLocalRing.maximalIdeal V).primesOver C) :
    Q.1.ramificationIdx V ∣ (Module.finrank (FractionRing V) L).factorial := by
  classical
  let K := FractionRing V
  let p := IsLocalRing.maximalIdeal V
  let : Fintype (p.primesOver C) := Fintype.ofFinite (p.primesOver C)
  have : Module.Free V C := inferInstance
  have hdegree : Module.finrank V C = Module.finrank K L := by
    calc
      Module.finrank V C = Module.finrank K (K ⊗[V] C) :=
        (Module.finrank_baseChange (R := K) (S := V) (M' := C)).symm
      _ = Module.finrank K L :=
        (finiteGenericFiberAlgEquiv (R := V) (C := C) (K := K) (E := L)).toLinearEquiv.finrank_eq
  have hle : Q.1.ramificationIdx V ≤ Module.finrank K L := by
    calc
      Q.1.ramificationIdx V ≤ Q.1.ramificationIdx V * Q.1.inertiaDeg V :=
        Nat.le_mul_of_pos_right _ (Q.1.inertiaDeg_pos V)
      _ ≤ ∑ q : p.primesOver C, q.1.ramificationIdx V * q.1.inertiaDeg V :=
        Finset.single_le_sum
          (f := fun q : p.primesOver C ↦ q.1.ramificationIdx V * q.1.inertiaDeg V)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ Q)
      _ = Module.finrank V C := Ideal.sum_ramification_inertia_eq_finrank p C
      _ = Module.finrank K L := hdegree
  exact Nat.dvd_factorial (Q.1.ramificationIdx_pos V) hle

/-- After the factorial-degree root of a uniformizer, the normalization in
the entire generic tensor product is finite étale and recovers that tensor
product on the generic fibre. The original finite separable extension is
the only input concerning the cover. -/
theorem finiteEtale_uniformizerFactorialRoot_normalization
    (V : Type uV) (L : Type uL)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field L] [Algebra V L] [Algebra (FractionRing V) L]
    [IsScalarTower V (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] [Algebra.IsSeparable (FractionRing V) L]
    (π : V) (hπ : Prime π)
    (hCharZero : CharZero (V ⧸ IsLocalRing.maximalIdeal V)) :
    let n := (Module.finrank (FractionRing V) L).factorial
    let W := AdjoinRoot (X ^ n - Polynomial.C π)
    let : IsDomain W :=
      isDomain_adjoinRoot_X_pow_sub_C_of_prime (Nat.factorial_pos _) π hπ
    let : IsDiscreteValuationRing W :=
      isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime (Nat.factorial_pos _) π hπ
    let : Module.FaithfullyFlat V W :=
      faithfullyFlat_adjoinRoot_X_pow_sub_C (Nat.factorial_pos _) π
    let Kroot := FractionRing W
    let : Algebra (FractionRing V) Kroot := FractionRing.liftAlgebra V Kroot
    let A := Kroot ⊗[FractionRing V] L
    let : Algebra W A := genericTensorProductLeftScalarAlgebra
    Module.Finite W (integralClosure W A) ∧ Algebra.Etale W (integralClosure W A) ∧
      Nonempty (Kroot ⊗[W] integralClosure W A ≃ₐ[Kroot] A) := by
  intro n W hDomainW hDvrW hFlatW Kroot aKKroot A aWA
  let K := FractionRing V
  let C := integralClosure V L
  have : IsFractionRing C L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L C
  have : IsDedekindDomain C := IsIntegralClosure.isDedekindDomain V K L C
  have : Module.IsTorsionFree V L := Module.IsTorsionFree.trans_faithfulSMul V K L
  have : Module.IsTorsionFree V C := IsIntegralClosure.isTorsionFree V L
  have : Module.Finite V C := IsIntegralClosure.finite V K L C
  have hdiv : ∀ Q : (IsLocalRing.maximalIdeal V).primesOver C,
      Q.1.ramificationIdx V ∣ n := fun Q ↦ branchIndex_dvd_factorial_degree Q
  have hEtale : Algebra.Etale W (integralClosure W A) := by
    apply integralClosure_genericTensorProduct_etale
    intro m hm
    exact integralClosure_uniformizerRootTensorComponent_etale_of_ramification_dvd
      (V := V) (C := C) (L := L) π hπ n (Nat.factorial_pos _) hdiv hCharZero m hm
  have : Algebra.FinitePresentation W (integralClosure W A) := hEtale.finitePresentation
  have hFiniteType : Algebra.FiniteType W (integralClosure W A) :=
    Algebra.FiniteType.of_finitePresentation (R := W) (A := integralClosure W A)
  have hFinite : Module.Finite W (integralClosure W A) :=
    Algebra.IsIntegral.finite (R := W) (A := integralClosure W A) (h' := hFiniteType)
  have : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  have : Module.Finite Kroot A := Module.Finite.base_change K Kroot L
  have : Algebra.Etale Kroot A := inferInstance
  have : IsScalarTower W Kroot A :=
    TensorProduct.isScalarTower_left (R := K) (R'₂ := W) (R' := Kroot)
  exact ⟨hFinite, hEtale,
    ⟨SchemeTheory.integralClosureFiniteEtaleGenericFiberEquiv W Kroot A⟩⟩

end EtaleFundamentalGroups.Kummer
