/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.PlaceArtinImage
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteRestriction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.CompactUnits
public import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ClosedAndCosets
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve

/-!
# Full place inertia in the actual absolute abelianization

The images of the original absolute normalization inertia and of the full
one-place units are compact. Every finite quotient of the original
absolute abelianization is the Galois group of its native finite fixed
field. The finite place-inertia comparison therefore identifies the two
compact subgroups themselves, with no choice of a reciprocity quotient or
of an inertia matching.
-/

@[expose] public section

universe u v

noncomputable section

open AlgebraicCurve FunctionField LocalClassFieldTheory
open scoped AlgebraicCurve.Place Pointwise

namespace EtaleFundamentalGroups.Inertia

private theorem closedSubgroup_le_of_finiteImages
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [TotallyDisconnectedSpace P]
    (H J : Subgroup P) (hJ : IsClosed (J : Set P))
    (hfinite : ∀ N : OpenNormalSubgroup P,
      H.map (QuotientGroup.mk' N.toSubgroup) ≤
        J.map (QuotientGroup.mk' N.toSubgroup)) : H ≤ J := by
  have hsep : J = sInf {U : Subgroup P | IsOpen (U : Set P) ∧ J ≤ U} :=
    ProCGroups.ProC.closedSubgroup_eq_sInf_open ⟨J, hJ⟩
  refine le_trans ?_ hsep.symm.le
  apply le_sInf
  intro U hU
  obtain ⟨N, hNU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := P) hU.1 U.one_mem
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hfinite N ⟨x, hx, rfl⟩
  let q : P →* P ⧸ N.toSubgroup := QuotientGroup.mk' N.toSubgroup
  have hdiff : y⁻¹ * x ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (y⁻¹ * x) = 1
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have hmem := U.mul_mem (hU.2 hy) (hNU hdiff)
  simpa only [mul_inv_cancel_left] using hmem

private theorem closedSubgroup_eq_of_finiteImages
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [TotallyDisconnectedSpace P]
    (H J : Subgroup P) (hH : IsClosed (H : Set P)) (hJ : IsClosed (J : Set P))
    (hfinite : ∀ N : OpenNormalSubgroup P,
      H.map (QuotientGroup.mk' N.toSubgroup) =
        J.map (QuotientGroup.mk' N.toSubgroup)) : H = J :=
  le_antisymm (closedSubgroup_le_of_finiteImages H J hJ fun N => (hfinite N).le)
    (closedSubgroup_le_of_finiteImages J H hH fun N => (hfinite N).symm.le)

attribute [local instance]
  AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring
  AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring

variable {k : Type u} {K : Type v} [Field k] [Finite k] [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [HasPrincipalDivisors k K]

/-- The original one-place inclusion followed by the full absolute Artin map. -/
def placeAbsoluteArtin (v : Place k K) :
    v.adicCompletionˣ →ₜ* localAbsoluteAbelianProfinite K :=
  (absoluteArtin k K).comp
    { toMonoidHom := IdeleClassGroup.mk.comp (IdeleGroup.placeIdele v)
      continuous_toFun := QuotientGroup.continuous_mk.comp
        (IdeleGroup.continuous_placeIdele v) }

/-- The full unit Artin image is compact in the original Krull quotient topology. -/
theorem placeAbsoluteArtin_units_isCompact (v : Place k K) :
    IsCompact (((RayClass.localHigherUnitGroup v 0).map
      (placeAbsoluteArtin v).toMonoidHom : Subgroup (localAbsoluteAbelianProfinite K)) :
        Set (localAbsoluteAbelianProfinite K)) := by
  rw [RayClass.localHigherUnitGroup_zero]
  exact (isCompact_localUnits v).image (placeAbsoluteArtin v).continuous_toFun

/-- The literal absolute normalization inertia, mapped to the actual
absolute abelianization, is exactly the full one-place Artin unit image. -/
theorem absolute_place_inertia_abelian_image_eq_units
    (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsMaximal] :
    let _ : MulSemiringAction Gal(SeparableClosure K/K)
        (integralClosure v.toValuationSubring (SeparableClosure K)) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring K (SeparableClosure K)
        (integralClosure v.toValuationSubring (SeparableClosure K))
    (Q.inertia Gal(SeparableClosure K/K)).map
        (localAbsoluteAbelianizationQuotientMap K) =
      (RayClass.localHigherUnitGroup v 0).map (placeAbsoluteArtin v).toMonoidHom := by
  intro absoluteAction
  let Ω := SeparableClosure K
  let : Algebra k Ω := ((algebraMap K Ω).comp (algebraMap k K)).toAlgebra
  let : Algebra (RatFunc k) Ω :=
    ((algebraMap K Ω).comp (algebraMap (RatFunc k) K)).toAlgebra
  have : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (RatFunc k) K Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k (RatFunc k) Ω :=
    IsScalarTower.of_algebraMap_eq fun x => congrArg (algebraMap K Ω)
      (IsScalarTower.algebraMap_apply k (RatFunc k) K x)
  let I := Q.inertia Gal(Ω/K)
  let q := localAbsoluteAbelianizationQuotientMap K
  let H := I.map q
  let J := (RayClass.localHigherUnitGroup v 0).map (placeAbsoluteArtin v).toMonoidHom
  have hH : IsClosed (H : Set (localAbsoluteAbelianProfinite K)) :=
    ((actualNormalizationInertia_isClosed v.toValuationSubring K Ω Q).isCompact.image
      QuotientGroup.continuous_mk).isClosed
  have hJ : IsClosed (J : Set (localAbsoluteAbelianProfinite K)) :=
    (placeAbsoluteArtin_units_isCompact v).isClosed
  apply closedSubgroup_eq_of_finiteImages H J hH hJ
  intro N
  let E := absoluteFiniteQuotientField K N
  have : HasPrincipalDivisors k E :=
    (ClassFieldTheory.FunctionField.finiteExtension_isCurveOver k K E).toHasPrincipalDivisors
  have hREΩ : IsScalarTower v.toValuationSubring E Ω :=
    IsScalarTower.to₁₃₄ v.toValuationSubring K E Ω
  obtain ⟨w, hw, hI⟩ :=
    @absolute_place_inertia_image_eq_finiteArtin_units k K E Ω
      _ _ _ _
      _ _ _ _ _
      _ _ _ _
      _ _ _ _ _ _ _ _ _ _
      v _ _ hREΩ Q _
  have hfinite : I.map (AlgEquiv.restrictNormalHom E) =
      (RayClass.localHigherUnitGroup v 0).map
        ((abelianFiniteArtin k K E).comp
          (IdeleClassGroup.mk.comp (IdeleGroup.placeIdele v))) := by
    exact hI.trans (congrArg (fun v' : Place k K =>
      (RayClass.localHigherUnitGroup v' 0).map
        ((abelianFiniteArtin k K E).comp
          (IdeleClassGroup.mk.comp (IdeleGroup.placeIdele v')))) hw)
  let e := absoluteFiniteQuotientEquiv K N
  have hleft : e.toMonoidHom.comp
      ((QuotientGroup.mk' N.toSubgroup).comp q) = AlgEquiv.restrictNormalHom E := by
    apply MonoidHom.ext
    intro σ
    exact absoluteFiniteQuotientEquiv_mk_mk K N σ
  have hright : e.toMonoidHom.comp
      ((QuotientGroup.mk' N.toSubgroup).comp (placeAbsoluteArtin v).toMonoidHom) =
        (abelianFiniteArtin k K E).comp
          (IdeleClassGroup.mk.comp (IdeleGroup.placeIdele v)) := by
    apply MonoidHom.ext
    intro x
    change e (QuotientGroup.mk (absoluteArtin k K
      (IdeleClassGroup.mk (IdeleGroup.placeIdele v x)))) = _
    rw [absoluteArtin_finiteProjection]
    exact e.apply_symm_apply _
  have hmap : (H.map (QuotientGroup.mk' N.toSubgroup)).map e.toMonoidHom =
      (J.map (QuotientGroup.mk' N.toSubgroup)).map e.toMonoidHom := by
    change ((I.map q).map (QuotientGroup.mk' N.toSubgroup)).map e.toMonoidHom =
      (((RayClass.localHigherUnitGroup v 0).map (placeAbsoluteArtin v).toMonoidHom).map
        (QuotientGroup.mk' N.toSubgroup)).map e.toMonoidHom
    simp only [Subgroup.map_map]
    rw [hleft, hright]
    exact hfinite
  apply Subgroup.ext
  intro x
  exact (Subgroup.mem_map_iff_mem e.injective).symm.trans
    ((congrArg (fun S : Subgroup Gal(E/K) => e x ∈ S) hmap).to_iff.trans
      (Subgroup.mem_map_iff_mem e.injective))

/-- Every original continuous abelian quotient retains the same native
inertia image and the same full local units. In particular this applies
to the abelianization of the original arithmetic first quotient, composed
with its prescribed field-source map. -/
theorem absolute_place_inertia_image_eq_units_of_commutative
    {P : Type*} [CommGroup P] [TopologicalSpace P] [T1Space P]
    (f : Gal(SeparableClosure K/K) →ₜ* P)
    (v : Place k K)
    (Q : Ideal (integralClosure v.toValuationSubring (SeparableClosure K)))
    [Q.IsMaximal] :
    let _ : MulSemiringAction Gal(SeparableClosure K/K)
        (integralClosure v.toValuationSubring (SeparableClosure K)) :=
      IsIntegralClosure.MulSemiringAction v.toValuationSubring K (SeparableClosure K)
        (integralClosure v.toValuationSubring (SeparableClosure K))
    (Q.inertia Gal(SeparableClosure K/K)).map f.toMonoidHom =
      (RayClass.localHigherUnitGroup v 0).map
        ((ProCGroups.Abelian.TopologicalAbelianization.lift f).comp
          (placeAbsoluteArtin v)).toMonoidHom := by
  intro absoluteAction
  let l := ProCGroups.Abelian.TopologicalAbelianization.lift f
  have h := congrArg (fun S : Subgroup (localAbsoluteAbelianProfinite K) =>
    S.map l.toMonoidHom) (absolute_place_inertia_abelian_image_eq_units v Q)
  have hcomp : l.toMonoidHom.comp (localAbsoluteAbelianizationQuotientMap K) =
      f.toMonoidHom := by
    apply MonoidHom.ext
    intro σ
    rfl
  let I := Q.inertia Gal(SeparableClosure K/K)
  have hleft : (I.map (localAbsoluteAbelianizationQuotientMap K)).map l.toMonoidHom =
      I.map f.toMonoidHom :=
    (Subgroup.map_map I l.toMonoidHom (localAbsoluteAbelianizationQuotientMap K)).trans
      (congrArg (fun m : Gal(SeparableClosure K/K) →* P => I.map m) hcomp)
  have hright :
      ((RayClass.localHigherUnitGroup v 0).map (placeAbsoluteArtin v).toMonoidHom).map
          l.toMonoidHom =
        (RayClass.localHigherUnitGroup v 0).map (l.comp (placeAbsoluteArtin v)).toMonoidHom :=
    Subgroup.map_map (RayClass.localHigherUnitGroup v 0) l.toMonoidHom
      (placeAbsoluteArtin v).toMonoidHom
  exact hleft.symm.trans (h.trans hright)

end EtaleFundamentalGroups.Inertia
