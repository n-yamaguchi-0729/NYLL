/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerFiniteEtaleExtension
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerGenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.SchemeTheory.Normalization.GenericFiber.IntegralClosure
import Nyll.SchemeTheory.Normalization.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The normalized generic cover after a uniformizer root

Let `V` be a DVR with residue characteristic zero, and let `L` be a finite
separable extension of `K = Frac(V)`. For `n = [L : K]!`, take the actual
root DVR `W = V[X] / (X ^ n - π)`, and put `K' = Frac(W)`.

The relative normalization of `Spec W` in `Spec (K' ⊗[K] L)` is finite
étale. Its canonical map from `Spec (K' ⊗[K] L)` is the generic-fibre
pullback square. This generic source is also identified, over `Spec K'`,
with the actual base change of `Spec L → Spec K`. The base extension
`K' / K` is finite separable of the specified degree.

Thus the DVR-local normalized cover used in Stacks Project,
Proposition 58.30.2, is constructed with both original structure maps.
Applying this calculation at the special-fibre generic points of a smooth
scheme, and applying purity on that scheme, are subsequent steps.
https://stacks.math.columbia.edu/tag/0C0Q
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

/-- The actual relative normalization after the factorial-degree
uniformizer root is finite étale. Both the canonical generic-fibre square
and the comparison to the original cover's literal base change are given
over the same root fraction field. -/
theorem uniformizerFactorialRoot_normalization_finiteEtale
    (V L : Type u)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field L] [Algebra V L] [Algebra (FractionRing V) L]
    [IsScalarTower V (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] [Algebra.IsSeparable (FractionRing V) L]
    (π : V) (hπ : Prime π)
    (hCharZero : CharZero (V ⧸ IsLocalRing.maximalIdeal V)) :
    let K := FractionRing V
    let n := (Module.finrank K L).factorial
    let W := AdjoinRoot (X ^ n - C π)
    let : IsDomain W :=
      isDomain_adjoinRoot_X_pow_sub_C_of_prime (Nat.factorial_pos _) π hπ
    let : IsDiscreteValuationRing W :=
      isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime (Nat.factorial_pos _) π hπ
    let : Module.FaithfullyFlat V W :=
      faithfullyFlat_adjoinRoot_X_pow_sub_C (Nat.factorial_pos _) π
    let Kroot := FractionRing W
    let : Algebra K Kroot := FractionRing.liftAlgebra V Kroot
    let A := Kroot ⊗[K] L
    let : Algebra W A := genericTensorProductLeftScalarAlgebra
    let f := Spec.map (CommRingCat.ofHom (algebraMap W A))
    Module.Finite K Kroot ∧ Algebra.IsSeparable K Kroot ∧
      Module.finrank K Kroot = n ∧ IsFinite f.fromNormalization ∧
      Etale f.fromNormalization ∧
      IsPullback f.toNormalization (Spec.map (CommRingCat.ofHom (algebraMap Kroot A)))
        f.fromNormalization (Spec.map (CommRingCat.ofHom (algebraMap W Kroot))) ∧
      ∃ e : Spec (.of A) ≅
          pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
            (Spec.map (CommRingCat.ofHom (algebraMap K Kroot))),
        e.hom ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom (algebraMap Kroot A)) := by
  intro K n W hDomainW hDvrW hFlatW Kroot aKKroot A aWA f
  have hnUnit : IsUnit (n : V) := by
    have : CharZero (IsLocalRing.ResidueField V) := hCharZero
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (n : V)).mp
    rw [map_natCast]
    exact Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  obtain ⟨hFiniteRoot, hSeparableRoot, hDegreeRoot⟩ :=
    uniformizerRoot_fractionField_finiteSeparable_degree
      (Nat.factorial_pos _) hnUnit π hπ
  obtain ⟨hFinite, hEtale, _hGeneric⟩ :=
    finiteEtale_uniformizerFactorialRoot_normalization V L π hπ hCharZero
  have : Module.Finite W (integralClosure W A) := hFinite
  have : Algebra.Etale W (integralClosure W A) := hEtale
  let g := Spec.map (CommRingCat.ofHom (R := W) (S := integralClosure W A)
    (algebraMap W (integralClosure W A)))
  have : IsFinite g :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hFinite)
  have : Etale g :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hEtale)
  have hbase : (specNormalizationIso W A).hom ≫ g = f.fromNormalization :=
    specNormalizationIso_hom_base W A
  have hFiniteNormalization : IsFinite f.fromNormalization := by
    rw [← hbase]
    infer_instance
  have hEtaleNormalization : Etale f.fromNormalization := by
    rw [← hbase]
    infer_instance
  have : Module.Finite Kroot A := Module.Finite.base_change K Kroot L
  have : IsScalarTower W Kroot A :=
    TensorProduct.isScalarTower_left (R := K) (R'₂ := W) (R' := Kroot)
  have hGeneric := isPullback_affineNormalization_generic W Kroot A
  refine ⟨hFiniteRoot, hSeparableRoot, hDegreeRoot, hFiniteNormalization,
    hEtaleNormalization, hGeneric, ?_⟩
  let e : Spec (.of A) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (Spec.map (CommRingCat.ofHom (algebraMap K Kroot))) :=
    (pullbackSpecIso K Kroot L).symm ≪≫ pullbackSymmetry _ _
  refine ⟨e, ?_⟩
  simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']

end EtaleFundamentalGroups.Kummer
