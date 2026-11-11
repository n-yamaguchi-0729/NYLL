/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.AbsolutePlaceArtinImage
public import Nyll.AlgebraicCurves.Places.ValuationRings.RangeStalkEq
public import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.BaseRingEquiv
public import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-!
# Original closed stalks and full place Artin images

Every original closed stalk of a smooth integral curve supplies a place
of its literal function field. The injective stalk inclusion gives the
valuation-ring equivalence, which in turn identifies the two actual
normalization rings inside the same separable closure. Contraction of the
given prime along this equivalence preserves the full original inertia.

The absolute Artin comparison consequently applies to the actual stalk
inertia, without a supplied place, normalization comparison or equality of
residue actions.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve FunctionField LocalClassFieldTheory
open scoped AlgebraicCurve.Place Pointwise

namespace EtaleFundamentalGroups.Inertia

attribute [local instance]
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring

universe u

/-- A local ring with the actual valuation-ring image defines the same
full normalization decomposition and inertia inside any algebraic extension
of its fraction field. The normalization-ring equivalence is the identity
on that extension, so it preserves both subgroups at the same prime. -/
theorem exists_placeNormalizationPrime_decomposition_inertia_eq_of_range
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (A : Type*) [CommRing A]
    [Algebra A K] [IsFractionRing A K]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra A Ω] [IsScalarTower A K Ω]
    (v : Place k K)
    (hv : (algebraMap A K).range = v.toValuationSubring.toSubring) :
    let _ : MulSemiringAction Gal(Ω/K) (integralClosure A Ω) :=
      IsIntegralClosure.MulSemiringAction A K Ω (integralClosure A Ω)
    ∀ (Q : Ideal (integralClosure A Ω)) [Q.IsMaximal],
      let _ : MulSemiringAction Gal(Ω/K) (integralClosure v.toValuationSubring Ω) :=
        IsIntegralClosure.MulSemiringAction v.toValuationSubring K Ω
          (integralClosure v.toValuationSubring Ω)
      ∃ q : Ideal (integralClosure v.toValuationSubring Ω), q.IsMaximal ∧
        MulAction.stabilizer Gal(Ω/K) Q = MulAction.stabilizer Gal(Ω/K) q ∧
        Q.inertia Gal(Ω/K) = q.inertia Gal(Ω/K) := by
  intro stalkAction Q hQ placeAction
  let f : A →+* v.toValuationSubring :=
    (algebraMap A K).codRestrict v.toValuationSubring.toSubring fun a => by
      rw [← hv]
      exact ⟨a, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact IsFractionRing.injective A K (congrArg Subtype.val hab)
    · intro b
      have hb : (b : K) ∈ (algebraMap A K).range := by
        rw [hv]
        exact b.property
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩
  let e : A ≃+* v.toValuationSubring := RingEquiv.ofBijective f hf
  have he : (algebraMap v.toValuationSubring Ω).comp e.toRingHom = algebraMap A Ω := by
    apply RingHom.ext
    intro a
    exact (IsScalarTower.algebraMap_apply A K Ω a).symm
  let : Algebra A (integralClosure v.toValuationSubring Ω) := integralClosureBaseRingAlgebra e
  let eN := (integralClosureBaseRingAlgEquiv e he).toRingEquiv
  let q := Q.comap eN.symm.toRingHom
  have hq : q.IsMaximal := Ideal.comap_isMaximal_of_surjective
    eN.symm.toRingHom eN.symm.surjective
  have haction (σ : Gal(Ω/K)) (b : integralClosure v.toValuationSubring Ω) :
      eN.symm (σ • b) = σ • eN.symm b := by
    apply Subtype.ext
    calc
      (eN.symm (σ • b) : Ω) = ((σ • b : integralClosure v.toValuationSubring Ω) : Ω) := rfl
      _ = σ (b : Ω) := algebraMap_galRestrict_apply v.toValuationSubring σ b
      _ = σ (eN.symm b : Ω) := rfl
      _ = ((σ • eN.symm b : integralClosure A Ω) : Ω) :=
        (algebraMap_galRestrict_apply A (K := K) (L := Ω)
          (B := integralClosure A Ω) σ (eN.symm b)).symm
  have hcomap (σ : Gal(Ω/K)) :
      (σ • Q).comap eN.symm.toRingHom = σ • q := by
    apply Ideal.ext
    intro b
    rw [Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
    exact (Iff.of_eq (congrArg (fun a : integralClosure A Ω => a ∈ Q)
      (haction σ⁻¹ b))).symm
  refine ⟨q, hq, ?_, ?_⟩
  · apply Subgroup.ext
    intro σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro hσ
      exact (hcomap σ).symm.trans
        (congrArg (fun I : Ideal (integralClosure A Ω) =>
          I.comap eN.symm.toRingHom) hσ)
    · intro hσ
      apply Ideal.comap_injective_of_surjective eN.symm.toRingHom eN.symm.surjective
      exact (hcomap σ).trans hσ
  · apply Subgroup.ext
    intro σ
    constructor
    · intro hσ b
      change eN.symm (σ • b - b) ∈ Q
      rw [map_sub, haction]
      exact hσ (eN.symm b)
    · intro hσ a
      obtain ⟨b, rfl⟩ := eN.symm.surjective a
      have hb := hσ b
      change eN.symm (σ • b - b) ∈ Q at hb
      rw [map_sub, haction] at hb
      exact hb

/-- The full inertia comparison is the inertia component of the
same-prime decomposition-and-inertia construction. -/
theorem exists_placeNormalizationPrime_inertia_eq_of_range
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (A : Type*) [CommRing A]
    [Algebra A K] [IsFractionRing A K]
    (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra A Ω] [IsScalarTower A K Ω]
    (v : Place k K)
    (hv : (algebraMap A K).range = v.toValuationSubring.toSubring) :
    let _ : MulSemiringAction Gal(Ω/K) (integralClosure A Ω) :=
      IsIntegralClosure.MulSemiringAction A K Ω (integralClosure A Ω)
    ∀ (Q : Ideal (integralClosure A Ω)) [Q.IsMaximal],
      let _ : MulSemiringAction Gal(Ω/K) (integralClosure v.toValuationSubring Ω) :=
        IsIntegralClosure.MulSemiringAction v.toValuationSubring K Ω
          (integralClosure v.toValuationSubring Ω)
      ∃ q : Ideal (integralClosure v.toValuationSubring Ω), q.IsMaximal ∧
        Q.inertia Gal(Ω/K) = q.inertia Gal(Ω/K) := by
  intro stalkAction Q hQ placeAction
  obtain ⟨q, hq, -, hI⟩ :=
    exists_placeNormalizationPrime_decomposition_inertia_eq_of_range A Ω v hv Q
  exact ⟨q, hq, hI⟩

/-- An original closed-point normalization inertia is literally the same
subgroup of the original absolute Galois group as the inertia of a
constructed place normalization prime. -/
theorem exists_closedStalk_place_normalization_inertia
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    let _ : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
      X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
    let _ : IsScalarTower (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : MulSemiringAction Gal(SeparableClosure X.functionField/X.functionField)
        (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField)) :=
      IsIntegralClosure.MulSemiringAction (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField)
        (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField))
    ∀ (Q : Ideal (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField)))
      [Q.IsMaximal], ∃ v : Place k X.functionField,
        (algebraMap (X.presheaf.stalk x) X.functionField).range =
          v.toValuationSubring.toSubring ∧
        let _ : MulSemiringAction Gal(SeparableClosure X.functionField/X.functionField)
            (integralClosure v.toValuationSubring (SeparableClosure X.functionField)) :=
          IsIntegralClosure.MulSemiringAction v.toValuationSubring X.functionField
            (SeparableClosure X.functionField)
            (integralClosure v.toValuationSubring (SeparableClosure X.functionField))
        ∃ q : Ideal (integralClosure v.toValuationSubring (SeparableClosure X.functionField)),
          q.IsMaximal ∧ Q.inertia Gal(SeparableClosure X.functionField/X.functionField) =
            q.inertia Gal(SeparableClosure X.functionField/X.functionField) := by
  intro baseAlgebra stalkAlgebra stalkTower stalkAction Q hQ
  obtain ⟨v, hv⟩ := exists_place_range_stalk_eq c x hx
  refine ⟨v, hv, ?_⟩
  intro placeAction
  exact exists_placeNormalizationPrime_inertia_eq_of_range
    (X.presheaf.stalk x) (SeparableClosure X.functionField) v hv Q

/-- The original closed stalk's full inertia image in absolute
abelianization is the full unit Artin image of its constructed place. -/
theorem exists_closedStalk_place_abelian_inertia_image
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [IsIntegral X]
    (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField] [FunctionField k X.functionField]
      [HasPrincipalDivisors k X.functionField],
    let _ : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
      X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
    let _ : IsScalarTower (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : MulSemiringAction Gal(SeparableClosure X.functionField/X.functionField)
        (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField)) :=
      IsIntegralClosure.MulSemiringAction (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField)
        (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField))
    ∀ (Q : Ideal (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField)))
      [Q.IsMaximal], ∃ v : Place k X.functionField,
        (algebraMap (X.presheaf.stalk x) X.functionField).range =
          v.toValuationSubring.toSubring ∧
        (Q.inertia Gal(SeparableClosure X.functionField/X.functionField)).map
            (localAbsoluteAbelianizationQuotientMap X.functionField) =
          (RayClass.localHigherUnitGroup v 0).map (placeAbsoluteArtin v).toMonoidHom := by
  intro baseAlgebra rationalAlgebra rationalTower functionField principalDivisors
    stalkAlgebra stalkTower stalkAction Q hQ
  obtain ⟨v, hv, q, hq, hI⟩ := exists_closedStalk_place_normalization_inertia c x hx Q
  have : q.IsMaximal := hq
  refine ⟨v, hv, ?_⟩
  rw [hI]
  exact absolute_place_inertia_abelian_image_eq_units v q

end EtaleFundamentalGroups.Inertia
