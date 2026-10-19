/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerGenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# A uniformizer root inside the prescribed geometric generic field

Adjoin a positive root of a uniformizer of a strictly Henselian DVR.
When the exponent is prime to the residue characteristic, or that
characteristic is zero, the resulting DVR is finite and strictly
Henselian and embeds into the prescribed separably closed extension
of the original fraction field.

The residue condition first makes the exponent a unit in the DVR. The
actual fraction field of the root ring is then a finite separable
extension. Its embedding into the given separably closed field restricts
to the required integral root embedding. In particular, the geometric
generic field need not be replaced after the ramification-removing root
base change used in specialization.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- The actual uniformizer root is a finite strictly Henselian DVR and
embeds into the given separably closed generic field while fixing the
original DVR. The residue characteristic condition supplies the required
separability of its fraction field. -/
theorem exists_strictHenselianUniformizerRoot_embedding
    (C Ω : Type u) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [HenselianLocalRing C] [IsSepClosed (IsLocalRing.ResidueField C)]
    [Field Ω] [IsSepClosed Ω] [Algebra C Ω] [FaithfulSMul C Ω]
    (c n : ℕ) [CharP (IsLocalRing.ResidueField C) c]
    (hn : 0 < n) (hdegree : c = 0 ∨ Nat.Coprime n c) (π : C) (hπ : Prime π) :
    let W := AdjoinRoot (X ^ n - Polynomial.C π)
    let : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    let : IsDiscreteValuationRing W :=
      isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
    Module.Finite C W ∧ HenselianLocalRing W ∧
      IsSepClosed (IsLocalRing.ResidueField W) ∧
      ∃ j : W →ₐ[C] Ω, Function.Injective j := by
  intro W hDomainW hDVRW
  have hnResidue : (n : IsLocalRing.ResidueField C) ≠ 0 := by
    by_cases hc : c = 0
    · have hCharP : CharP (IsLocalRing.ResidueField C) 0 :=
        hc ▸ (inferInstance : CharP (IsLocalRing.ResidueField C) c)
      have : CharZero (IsLocalRing.ResidueField C) :=
        CharP.charP_to_charZero (IsLocalRing.ResidueField C)
      exact Nat.cast_ne_zero.mpr hn.ne'
    · have hcPrime : c.Prime :=
        (CharP.char_is_prime_or_zero (IsLocalRing.ResidueField C) c).resolve_right hc
      have hCoprime : Nat.Coprime n c := hdegree.resolve_left hc
      exact ((CharP.isUnit_natCast_iff (R := IsLocalRing.ResidueField C) hcPrime).mpr
        (hcPrime.coprime_iff_not_dvd.mp hCoprime.symm)).ne_zero
  have hnUnit : IsUnit (n : C) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (n : C)).mp
    simpa only [map_natCast] using hnResidue
  have hFinite : Module.Finite C W := (monic_X_pow_sub_C π hn.ne').finite_adjoinRoot
  have : Module.FaithfullyFlat C W := faithfullyFlat_adjoinRoot_X_pow_sub_C hn π
  have : IsLocalHom (algebraMap C W) := inferInstance
  have hHenselian : HenselianLocalRing W :=
    HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := C) (S := W)
  have hResidue : IsSepClosed (IsLocalRing.ResidueField W) :=
    Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField C)
      (E := IsLocalRing.ResidueField W)
  let : Algebra (FractionRing C) (FractionRing W) :=
    FractionRing.liftAlgebra C (FractionRing W)
  have : IsScalarTower C (FractionRing C) (FractionRing W) :=
    FractionRing.isScalarTower_liftAlgebra C (FractionRing W)
  let : Algebra (FractionRing C) Ω := FractionRing.liftAlgebra C Ω
  have : IsScalarTower C (FractionRing C) Ω := FractionRing.isScalarTower_liftAlgebra C Ω
  have hGeneric := uniformizerRoot_fractionField_finiteSeparable_degree hn hnUnit π hπ
  have : Algebra.IsSeparable (FractionRing C) (FractionRing W) := hGeneric.2.1
  let φ : FractionRing W →ₐ[FractionRing C] Ω :=
    IsSepClosed.lift (K := FractionRing C) (L := FractionRing W) (M := Ω)
  let j : W →ₐ[C] Ω := (φ.restrictScalars C).comp
    (IsScalarTower.toAlgHom C W (FractionRing W))
  have hj : Function.Injective j := by
    intro x y hxy
    exact (IsFractionRing.injective W (FractionRing W)) (φ.injective hxy)
  exact ⟨hFinite, hHenselian, hResidue, j, hj⟩

end EtaleFundamentalGroups.Kummer
