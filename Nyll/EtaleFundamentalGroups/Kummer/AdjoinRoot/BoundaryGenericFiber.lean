/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.UniformizerGenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain

/-!
# The actual generic fiber of a boundary Kummer cover

At a generic point of a reduced Cartier divisor, the literal localization
of the original root cover has generic fiber `Spec (Frac(B))`, where `B`
is the existing integral root algebra over the boundary DVR. The map from
`A[1/f]` and the projection of the pullback retain their coefficient maps.

The proof uses the localization pushout, cancellation of base change, and
`uniformizerRootFractionEquiv`. It requires no chosen extension field or
unproved comparison with the original cover. This is the generic-fiber
comparison for Stacks Project, Example 58.31.4 (tag `0EYF`); tameness is a
separate assertion. The comparison itself does not require the exponent
to be invertible.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

universe u

/-- The generic pullback of the original away cover is the fraction field
of the integral root algebra over the actual generic boundary local ring.
Both the generic base map and the projection to it preserve coefficients. -/
theorem standardKummerCover_boundaryGenericFiber
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    {n : ℕ} (hn : 0 < n) :
    let V := Localization.AtPrime P
    let C₀ := AdjoinRoot (X ^ n - C f)
    let B := AdjoinRoot (X ^ n - C (algebraMap A V f))
    let : IsRegularLocalRing V :=
      SchemeTheory.isRegularLocalRing_localizationAtPrime_of_reduced_quotient f hf P hP
    let : IsDomain V := IsRegularLocalRing.isDomain V
    let : IsDiscreteValuationRing V :=
      SchemeTheory.isDiscreteValuationRing_localizationAtPrime_of_reduced_quotient f hf P hP
    ∃ hdomain : IsDomain B,
      let : IsDomain B := hdomain
      let : Module.FaithfullyFlat V B :=
        faithfullyFlat_adjoinRoot_X_pow_sub_C hn (algebraMap A V f)
      let : Algebra (FractionRing V) (FractionRing B) :=
        FractionRing.liftAlgebra V (FractionRing B)
      ∃ r : Localization.Away f →+* FractionRing V,
        r.comp (algebraMap A (Localization.Away f)) =
          (algebraMap V (FractionRing V)).comp (algebraMap A V) ∧
        ∃ e : Spec (CommRingCat.of (FractionRing B)) ≅
            pullback
              (Spec.map (CommRingCat.ofHom
                (Localization.awayMap (algebraMap A C₀) f)))
              (Spec.map (CommRingCat.ofHom r)),
          e.hom ≫ pullback.snd _ _ =
            Spec.map (CommRingCat.ofHom
              (algebraMap (FractionRing V) (FractionRing B))) := by
  intro V C₀ B hregular hdomainV hdvrV
  let π : V := algebraMap A V f
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span ({π} : Set V) :=
    SchemeTheory.maximalIdeal_localizationAtPrime_eq_span_of_reduced_quotient f P hP
  have hπ : Prime π :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hmax).prime
  refine ⟨isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ, ?_⟩
  intro hdomainB hflat hfieldAlgebra
  let K := FractionRing V
  let L := FractionRing B
  let Af := Localization.Away f
  let Cf := Localization.Away (algebraMap A C₀ f)
  have hfK : IsUnit (algebraMap A K f) := by
    rw [IsScalarTower.algebraMap_apply A V K]
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (IsFractionRing.injective V K).ne hπ.ne_zero
  let r : Af →+* K := IsLocalization.Away.lift f hfK
  have hr : r.comp (algebraMap A Af) = algebraMap A K :=
    IsLocalization.Away.lift_comp f hfK
  refine ⟨r, hr.trans (IsScalarTower.algebraMap_eq A V K), ?_⟩
  let : Algebra Af K := r.toAlgebra
  have : IsScalarTower A Af K := IsScalarTower.of_algebraMap_eq' hr.symm
  let : Algebra Af Cf := (Localization.awayMap (algebraMap A C₀) f).toAlgebra
  have : IsScalarTower A Af Cf := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap C₀ Cf (algebraMap A C₀ a) =
      Localization.awayMap (algebraMap A C₀) f (algebraMap A Af a)
    change algebraMap C₀ Cf (algebraMap A C₀ a) =
      IsLocalization.map Cf (algebraMap A C₀) _ (algebraMap A Af a)
    exact (IsLocalization.map_eq _ a).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid C₀ (Submonoid.powers f)) Cf := by
    change IsLocalization ((Submonoid.powers f).map (algebraMap A C₀)) Cf
    rw [Submonoid.map_powers]
    exact Localization.isLocalization
  have : Algebra.IsPushout A Af C₀ Cf :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers f) Af C₀ Cf).symm
  let eAway : (Af ⊗[A] C₀) ≃ₐ[Af] Cf := Algebra.IsPushout.equiv A Af C₀ Cf
  let eRoot : (K ⊗[A] C₀) ≃ₐ[K]
      AdjoinRoot (X ^ n - C (algebraMap V K π)) :=
    (adjoinRootBaseChangeAlgEquiv (S := K) (X ^ n - C f)).trans
      (AdjoinRoot.algEquivOfEq K _ _ (by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
          IsScalarTower.algebraMap_apply A V K]))
  let eField : (K ⊗[A] C₀) ≃ₐ[K] L :=
    eRoot.trans (uniformizerRootFractionEquiv hn π hπ)
  let eTensor : (K ⊗[Af] Cf) ≃ₐ[K] L :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) eAway.symm).trans
      ((Algebra.TensorProduct.cancelBaseChange A Af K K C₀).trans eField)
  let eSpec : Spec (CommRingCat.of L) ≅ Spec (CommRingCat.of (K ⊗[Af] Cf)) :=
    Scheme.Spec.mapIso eTensor.toRingEquiv.toCommRingCatIso.op
  have he : eSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[Af] Cf))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    change Spec.map (CommRingCat.ofHom eTensor.toRingHom) ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext eTensor.commutes)
  refine ⟨eSpec ≪≫ (pullbackSpecIso Af K Cf).symm ≪≫ pullbackSymmetry _ _, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst']
  exact he

end EtaleFundamentalGroups.Kummer
