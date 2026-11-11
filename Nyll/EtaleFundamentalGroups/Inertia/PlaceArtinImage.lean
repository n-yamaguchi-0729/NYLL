/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.NativePlaceInertiaArtin
public import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationInertiaImage
public import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.FiniteAbelian

/-!
# Actual absolute place inertia and finite Artin unit images

The original absolute normalization prime determines the extending place
at every prescribed finite normal subextension. Its contraction is a
nonzero prime because it lies over the maximal ideal of the original
valuation ring. The finite-level inertia-image theorem and the native
place-residue comparison then identify its full restricted inertia with
the image of the original one-place units under finite global reciprocity.

The finite place and the normalization comparison are constructed here;
neither is supplied as a matching assumption.
-/

@[expose] public section

universe u v w x

noncomputable section

open AlgebraicCurve IsDedekindDomain FunctionField
open scoped AlgebraicCurve.Place Pointwise

namespace EtaleFundamentalGroups.Inertia

attribute [local instance]
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring

variable {k : Type u} {K : Type v} {L : Type w} {Ω : Type x}
  [Field k] [Field K] [Field L] [Field Ω]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [FiniteDimensional K L]
  [Algebra K Ω] [IsGalois K Ω]
  [Algebra L Ω] [IsScalarTower K L Ω]

/-- The actual contraction of an absolute place prime determines a finite
extending place, whose literal normalization inertia is the full image of
the original absolute inertia. -/
theorem exists_place_fiberCenter_inertia_eq_absolute_image
    [IsGalois K L]
    (v : Place k K)
    [Algebra v.toValuationSubring Ω] [IsScalarTower v.toValuationSubring K Ω]
    [IsScalarTower v.toValuationSubring L Ω]
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsMaximal] :
    let _ : MulSemiringAction Gal(Ω/K) (integralClosure v.toValuationSubring Ω) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring K Ω
        (integralClosure v.toValuationSubring Ω)
    let _ : MulSemiringAction Gal(L/K) (Place.integralClosureAt L v) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring K L
        (Place.integralClosureAt L v)
    ∃ (w : Place k L) (hw : w.restrict K = v),
      (Q.inertia Gal(Ω/K)).map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) =
        (Place.fiberCenter L v hw).asIdeal.inertia Gal(L/K) := by
  intro absoluteAction finiteAction
  have : Q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    ⟨(StrictHenselian.integralClosure_maximalPrime_under v.toValuationSubring Ω Q).symm⟩
  let q := absoluteNormalizationPrimeContraction
    (A := v.toValuationSubring) (L := L) (Omega := Ω) Q
  have : q.IsPrime := inferInstance
  have hqover : q.LiesOver (IsLocalRing.maximalIdeal v.toValuationSubring) :=
    inferInstance
  have hqne : q ≠ ⊥ := by
    intro hq
    apply Place.maximalIdeal_ne_bot v
    have h := hqover.over
    rw [hq, Ideal.under_def, Ideal.comap_bot_of_injective _
      (Place.algebraMap_integralClosureAt_injective v)] at h
    exact h
  let P : HeightOneSpectrum (Place.integralClosureAt L v) :=
    ⟨q, inferInstance, hqne⟩
  let w := Place.placeOfPrime P
  have hw : w.restrict K = v := Place.restrict_placeOfPrime P
  have hcenter : (Place.fiberCenter L v hw).asIdeal = q :=
    congrArg HeightOneSpectrum.asIdeal (Place.fiberCenter_placeOfPrime P)
  refine ⟨w, hw, ?_⟩
  rw [hcenter]
  exact absoluteNormalizationPrime_inertia_map_eq_contraction Q

section Reciprocity

variable [Finite k]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  [IsAbelianGalois K L] [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Every finite abelian restriction of the original absolute place
inertia is exactly the full local unit image under the actual global
Artin map and the original one-place idele inclusion. -/
theorem absolute_place_inertia_image_eq_finiteArtin_units
    (v : Place k K)
    [Algebra v.toValuationSubring Ω] [IsScalarTower v.toValuationSubring K Ω]
    [IsScalarTower v.toValuationSubring L Ω]
    (Q : Ideal (integralClosure v.toValuationSubring Ω)) [Q.IsMaximal] :
    let _ : MulSemiringAction Gal(Ω/K) (integralClosure v.toValuationSubring Ω) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring K Ω
        (integralClosure v.toValuationSubring Ω)
    ∃ w : Place k L, w.restrict K = v ∧
      (Q.inertia Gal(Ω/K)).map
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) =
        (RayClass.localHigherUnitGroup (w.restrict K) 0).map
          ((FunctionField.abelianFiniteArtin k K L).comp
            (IdeleClassGroup.mk.comp (IdeleGroup.placeIdele (w.restrict K)))) := by
  intro absoluteAction
  let : MulSemiringAction Gal(L/K) (Place.integralClosureAt L v) :=
    IsIntegralClosure.MulSemiringAction v.toValuationSubring K L
      (Place.integralClosureAt L v)
  obtain ⟨w, hw, hI⟩ :=
    exists_place_fiberCenter_inertia_eq_absolute_image (k := k) (K := K) (L := L) (Ω := Ω) v Q
  exact ⟨w, hw, hI.trans
    (FunctionField.abelianFiniteArtin_placeUnits_eq_fiberCenter_inertia v w hw).symm⟩

end Reciprocity

end EtaleFundamentalGroups.Inertia
