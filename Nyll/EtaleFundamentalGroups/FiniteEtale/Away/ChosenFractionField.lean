/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# The function field of an away cover over a chosen fraction field

A connected finite étale cover of `Spec (R[1/f])` gives a finite separable
extension of any chosen fraction field `K` of the normal domain `R`.
The scalar map is constructed from the unique `R`-algebra equivalence
between `K` and the function field of `Spec (R[1/f])`. The resulting
action is compared with the original action of `R` on the cover's
function field.

This lets the actual cover supply the field extension used by the
normalization calculation at a prime of the special fibre. No change
of the cover's function field or of its original normalization is
required.
-/

noncomputable section

open AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups

universe u

/-- The function field of an actual connected away cover, regarded as an
extension of a chosen fraction field of the original affine ring. -/
@[instance_reducible] noncomputable def finiteEtaleAwayChosenFractionFieldAlgebra
    {R K : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y] :
    let S := Localization.Away f
    let : IsDomain S := IsLocalization.Away.isDomain S hf
    let : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    Algebra K Y.left.functionField := by
  intro S hDomainS hNormalS hIntegralY
  let X := Spec (.of S)
  let : Algebra R X.functionField := localizationAwaySpecFunctionFieldAlgebra f hf
  have : IsFractionRing R X.functionField :=
    localizationAwaySpecFunctionField_isFractionRing f hf
  let : Algebra X.functionField Y.left.functionField := finiteEtaleFunctionFieldAlgebra Y
  let e : K ≃ₐ[R] X.functionField :=
    IsLocalization.algEquiv (nonZeroDivisors R) K X.functionField
  exact ((algebraMap X.functionField Y.left.functionField).comp e.toRingHom).toAlgebra

/-- The chosen fraction-field action is finite separable and restricts to
the original coefficient action of the connected finite étale cover. -/
theorem finiteEtaleAwayChosenFractionField_finite_separable
    {R K : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y] :
    let S := Localization.Away f
    let : IsDomain S := IsLocalization.Away.isDomain S hf
    let : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra K Y.left.functionField :=
      finiteEtaleAwayChosenFractionFieldAlgebra (K := K) f hf Y
    let : Algebra R Y.left.functionField := finiteEtaleAwayFunctionFieldAlgebra f hf Y
    IsScalarTower R K Y.left.functionField ∧
      Module.Finite K Y.left.functionField ∧
      Algebra.IsSeparable K Y.left.functionField := by
  intro S hDomainS hNormalS hIntegralY aKL aRL
  let X := Spec (.of S)
  let L := Y.left.functionField
  let K₀ := X.functionField
  let : Algebra R K₀ := localizationAwaySpecFunctionFieldAlgebra f hf
  have : IsFractionRing R K₀ := localizationAwaySpecFunctionField_isFractionRing f hf
  let : Algebra K₀ L := finiteEtaleFunctionFieldAlgebra Y
  have : IsScalarTower R K₀ L := finiteEtaleAway_functionField_isScalarTower f hf Y
  have : Module.Finite K₀ L := finiteDimensional_functionField_of_finiteEtale_isConnected Y
  have : Algebra.IsSeparable K₀ L := isSeparable_functionField_of_finiteEtale_isConnected Y
  let e : K ≃ₐ[R] K₀ := IsLocalization.algEquiv (nonZeroDivisors R) K K₀
  have hmap (x : K) : algebraMap K L x = algebraMap K₀ L (e x) := rfl
  have htower : IsScalarTower R K L := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    rw [hmap, e.commutes]
    exact IsScalarTower.algebraMap_apply R K₀ L r
  have hcomp : (algebraMap K L).comp e.symm.toRingHom =
      (RingHom.id L).comp (algebraMap K₀ L) := by
    apply RingHom.ext
    intro x
    change algebraMap K L (e.symm x) = algebraMap K₀ L x
    rw [hmap, e.apply_symm_apply]
  exact ⟨htower,
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) hcomp,
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) hcomp⟩

end EtaleFundamentalGroups
