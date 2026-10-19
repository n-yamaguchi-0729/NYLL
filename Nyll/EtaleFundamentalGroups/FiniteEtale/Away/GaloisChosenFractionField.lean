/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.ChosenFractionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionField
import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Localization.Basic

/-!
# The Galois degree of an actual away cover

For a finite étale Galois cover of `Spec (R[1/f])`, the action of any
chosen fraction field of `R` on the cover's function field is Galois.
Its degree equals the order of the original cover automorphism group.

Thus a prime-to-p condition on the actual geometric cover supplies the
same condition for the fraction-field extension used in the root
normalization calculation. The field, its scalar action, and the
automorphism group are those of the original cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups

universe u

/-- A Galois away cover supplies a Galois extension of a chosen fraction
field, of degree equal to the order of its actual cover automorphism
group. -/
theorem finiteEtaleAwayChosenFractionField_galois_degree
    {R K : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) :
    let S := Localization.Away f
    let : IsDomain S := IsLocalization.Away.isDomain S hf
    let : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    ∀ [PreGaloisCategory.IsGalois Y],
      let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
      let : Algebra K Y.left.functionField :=
        finiteEtaleAwayChosenFractionFieldAlgebra (K := K) f hf Y
      _root_.IsGalois K Y.left.functionField ∧
        Nat.card (Aut Y) = Module.finrank K Y.left.functionField := by
  intro S hDomainS hNormalS hGaloisY hIntegralY aKL
  let X := Spec (.of S)
  let K₀ := X.functionField
  let L := Y.left.functionField
  let : Algebra R K₀ := localizationAwaySpecFunctionFieldAlgebra f hf
  have : IsFractionRing R K₀ := localizationAwaySpecFunctionField_isFractionRing f hf
  let : Algebra K₀ L := finiteEtaleFunctionFieldAlgebra Y
  have : _root_.IsGalois K₀ L :=
    isGalois_functionField_of_isGalois_finiteEtale Y inferInstance
  let e : K ≃ₐ[R] K₀ := IsLocalization.algEquiv (nonZeroDivisors R) K K₀
  have hmap (x : K) : algebraMap K L x = algebraMap K₀ L (e x) := rfl
  have hcomp : (algebraMap K L).comp e.symm.toRingHom =
      (RingHom.id L).comp (algebraMap K₀ L) := by
    apply RingHom.ext
    intro x
    change algebraMap K L (e.symm x) = algebraMap K₀ L x
    rw [hmap, e.apply_symm_apply]
  refine ⟨_root_.IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl L) hcomp, ?_⟩
  exact (natCard_finiteEtaleAut_eq_finrank_functionField_of_isGalois Y inferInstance).trans
    (Algebra.finrank_eq_of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl L) hcomp)

end EtaleFundamentalGroups
