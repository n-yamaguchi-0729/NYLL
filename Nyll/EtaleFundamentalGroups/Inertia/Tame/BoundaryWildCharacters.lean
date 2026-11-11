/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.Tame.BoundaryWildQuotient
public import Nyll.EtaleFundamentalGroups.Inertia.WildPrimeToCharacters
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
public import Nyll.ProCGroups.Topologies.Conjugation
public import Mathlib.Algebra.CharP.Algebra

/-!
# Geometric characters and the original boundary-wild quotient

The native wild groups map continuously into the original fundamental group.
Their images lie in the original arithmetic kernel. For a prime different from
the characteristic, the closed normal subgroup they generate is contained in
the embedded pro-prime residual core of that geometric group. Thus characters
of the geometric group, not only characters of the arithmetic group, kill the
boundary-wild kernel.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory TopologicalSpace SchemeTheory NeronModelInfra
open ProCGroups ProCGroups.ProC

namespace EtaleFundamentalGroups.Tame

universe u v

attribute [local instance] Inertia.normalizationCommAlgGaloisAction

section NativeMap

variable (A F Ω : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Field Ω] [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω] [IsSepClosure F Ω]
  [IsSepClosed Ω] (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
  {U : Scheme.{u}} [IsIntegral U] (p : Spec (.of F) ⟶ U)

/-- The continuous map from the native principal-unit wild group uses the
literal two subgroup inclusions and the original field-source homomorphism. -/
def normalizationWildFieldSourceHom :
    (Inertia.actualNormalizationWildGroup A F Ω Q).carrier →ₜ* π₁ᵉᵗ(ξ F Ω ≫ p) :=
  (fieldSourceAbsoluteGaloisHom F Ω p).comp
    { toMonoidHom := (Inertia.actualNormalizationInertiaInclusion A F Ω Q).hom'.comp
        (Inertia.actualNormalizationWildSubgroup A F Ω Q).subtype
      continuous_toFun := continuous_subtype_val.comp continuous_subtype_val }

omit [IsIntegral U] in
/-- Its original automorphism representative is unchanged. -/
@[simp] theorem normalizationWildFieldSourceHom_apply
    (σ : (Inertia.actualNormalizationWildGroup A F Ω Q).carrier) :
    normalizationWildFieldSourceHom A F Ω Q p σ =
      fieldSourceAbsoluteGaloisHom F Ω p σ.val.val := rfl

end NativeMap

private theorem embeddedResidual_normal
    {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    (ℓ : ℕ) [Fact ℓ.Prime] (D : Subgroup P) [D.Normal] [CompactSpace D] :
    ((proCResidualCore (FiniteGroupClass.pGroup ℓ) D).map D.subtype).Normal := by
  refine ⟨?_⟩
  rintro x ⟨d, hd, rfl⟩ g
  let c : D →ₜ* D := ContinuousMonoidHom.toContinuousMonoidHom
    (Subgroup.conjNormalContinuousMulEquiv D g)
  exact ⟨c d, map_proCResidualCore_le_of_continuousMonoidHom
    (FiniteGroupClass.pGroup_fullFormation ℓ).hereditary c ⟨d, hd, rfl⟩, rfl⟩

private theorem embeddedResidual_isClosed
    {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    (ℓ : ℕ) [Fact ℓ.Prime] (D : Subgroup P) [CompactSpace D] :
    IsClosed (((proCResidualCore (FiniteGroupClass.pGroup ℓ) D).map D.subtype) : Set P) := by
  change IsClosed (D.subtype '' (proCResidualCore (FiniteGroupClass.pGroup ℓ) D : Set D))
  exact ((proCResidualCore_isClosed (FiniteGroupClass.pGroup ℓ) D).isCompact.image
    (show Continuous (D.subtype : D → P) from continuous_subtype_val)).isClosed

private theorem nativeWild_range_le_embeddedResidual
    (A F Ω : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Field Ω] [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [IsScalarTower A F Ω] [IsGalois F Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (r ℓ : ℕ) [Fact r.Prime] [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) r] (hrℓ : r ≠ ℓ)
    {P : Type v} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [T2Space P] [TotallyDisconnectedSpace P]
    (D : Subgroup P) [CompactSpace D]
    (ι : (Inertia.actualNormalizationWildGroup A F Ω Q).carrier →ₜ* P)
    (hι : ∀ σ, ι σ ∈ D) :
    ι.toMonoidHom.range ≤ (proCResidualCore (FiniteGroupClass.pGroup ℓ) D).map D.subtype := by
  let R := proCResidualCore (FiniteGroupClass.pGroup ℓ) D
  have : IsClosed (R : Set D) := proCResidualCore_isClosed (FiniteGroupClass.pGroup ℓ) D
  let ψ : (Inertia.actualNormalizationWildGroup A F Ω Q).carrier →ₜ* D :=
    { toMonoidHom := ι.toMonoidHom.codRestrict D hι
      continuous_toFun := ι.continuous_toFun.subtype_mk hι }
  let q : D →ₜ* D ⧸ R :=
    { toMonoidHom := QuotientGroup.mk' R
      continuous_toFun := QuotientGroup.continuous_mk }
  have hq : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ) (D ⧸ R) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (FiniteGroupClass.pGroup_fullFormation ℓ).melnikovFormation.formation
  rintro x ⟨σ, rfl⟩
  refine ⟨ψ σ, ?_, rfl⟩
  exact (QuotientGroup.eq_one_iff (N := R) (ψ σ)).mp
    (Inertia.normalizationWild_proPrime_character_eq_one A F Ω Q r ℓ hrℓ hq
      (q.comp ψ) σ)

attribute [local instance] integralOpenDominant

variable (k F Ω : Type u) [Field k] [Field F] [Field Ω]
  [Algebra F Ω] [IsSepClosure F Ω] [IsSepClosed Ω]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
  (j : U ⟶ X) [IsOpenImmersion j]
  (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
  (κ : Type u) [Field κ] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra κ Ω] [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsAlgClosure k κ] [IsSepClosure k κ]
  (hp : (p ≫ j) ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))
  (r ℓ : ℕ) [Fact r.Prime] [Fact ℓ.Prime] [CharP k r] (hrℓ : r ≠ ℓ)

local notation "π" => arithmeticFundamentalGroupHom k κ (j ≫ c) (ξ F Ω ≫ p)

include hp hrℓ in
private theorem normalizationWildImageAt_le_embeddedResidual
    (x : X) (hx : IsClosed ({x} : Set X)) :
    normalizationWildImageAt k F Ω c j p x hx ≤
      (proCResidualCore (FiniteGroupClass.pGroup ℓ) (π).toMonoidHom.ker).map
        (π).toMonoidHom.ker.subtype := by
  let D := (π).toMonoidHom.ker
  have : CompactSpace D := isCompact_iff_compactSpace.mp
    (ContinuousMonoidHom.isClosed_ker π).isCompact
  have hgeo := normalizationWildImageAt_le_arithmetic_ker k F Ω c j p κ hp x hx
  let A := X.presheaf.stalk x
  have : IsDiscreteValuationRing A :=
    SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c x hx
  let : Algebra A F := genericFieldSourceStalkAlgebra (p ≫ j) x
  have : IsFractionRing A F := genericFieldSourceStalk_isFractionRing (p ≫ j) x
  let : Algebra A Ω := ((algebraMap F Ω).comp (algebraMap A F)).toAlgebra
  have : IsScalarTower A F Ω := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra k A := stalkAlgebra c x
  let v : k →+* IsLocalRing.ResidueField A :=
    (IsLocalRing.residue A).comp (algebraMap k A)
  have : CharP (IsLocalRing.ResidueField A) r := charP_of_injective_ringHom v.injective r
  change (⨆ Q : MaximalSpectrum (normalizationCommAlgCat A Ω),
    let : Q.asIdeal.IsMaximal := Q.isMaximal
    (Inertia.actualNormalizationWildSubgroup A F Ω Q.asIdeal).map
      ((fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom.comp
        (Inertia.actualNormalizationInertiaInclusion A F Ω Q.asIdeal).hom')) ≤ _
  apply iSup_le
  intro Q
  have : Q.asIdeal.IsMaximal := Q.isMaximal
  let ι := normalizationWildFieldSourceHom A F Ω Q.asIdeal p
  have hι (σ : (Inertia.actualNormalizationWildGroup A F Ω Q.asIdeal).carrier) : ι σ ∈ D := by
    apply hgeo
    exact (le_iSup (fun Q : MaximalSpectrum (normalizationCommAlgCat A Ω) =>
      let : Q.asIdeal.IsMaximal := Q.isMaximal
      (Inertia.actualNormalizationWildSubgroup A F Ω Q.asIdeal).map
        ((fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom.comp
          (Inertia.actualNormalizationInertiaInclusion A F Ω Q.asIdeal).hom')) Q)
        ⟨σ.val, σ.property, rfl⟩
  have hR := nativeWild_range_le_embeddedResidual A F Ω Q.asIdeal r ℓ hrℓ D ι hι
  rintro γ ⟨σ, hσ, rfl⟩
  exact hR ⟨⟨σ, hσ⟩, rfl⟩

include hp hrℓ in
/-- The actual boundary-wild kernel is contained in the embedded pro-ell
residual core of the original geometric group. Conjugation here is by the
whole original arithmetic group. -/
theorem boundaryWildKernel_le_geometricProPrimeResidual :
    boundaryWildKernel k F Ω c j p ≤
      (proCResidualCore (FiniteGroupClass.pGroup ℓ) (π).toMonoidHom.ker).map
        (π).toMonoidHom.ker.subtype := by
  let D := (π).toMonoidHom.ker
  have : CompactSpace D := isCompact_iff_compactSpace.mp
    (ContinuousMonoidHom.isClosed_ker π).isCompact
  have : ((proCResidualCore (FiniteGroupClass.pGroup ℓ) D).map D.subtype).Normal :=
    embeddedResidual_normal ℓ D
  apply Subgroup.topologicalClosure_minimal
  · apply Subgroup.normalClosure_le_normal
    rintro γ ⟨x, hx, _hboundary, hγ⟩
    exact normalizationWildImageAt_le_embeddedResidual k F Ω c j p κ hp r ℓ hrℓ x hx hγ
  · exact embeddedResidual_isClosed ℓ D

include hp hrℓ in
/-- Every continuous pro-ell character of the original geometric group
kills the actual boundary-wild kernel inside that group. -/
theorem boundaryWild_geometric_character_eq_one
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hH : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ) H)
    (χ : (π).toMonoidHom.ker →ₜ* H) (d : (π).toMonoidHom.ker)
    (hd : d.val ∈ boundaryWildKernel k F Ω c j p) : χ d = 1 := by
  have : CompactSpace (π).toMonoidHom.ker := isCompact_iff_compactSpace.mp
    (ContinuousMonoidHom.isClosed_ker π).isCompact
  obtain ⟨e, he, hed⟩ :=
    boundaryWildKernel_le_geometricProPrimeResidual k F Ω c j p κ hp r ℓ hrℓ hd
  have heq : e = d := Subtype.ext hed
  exact proPrimeResidualCore_le_ker_acrossUniverses ℓ χ hH (heq ▸ he)

end EtaleFundamentalGroups.Tame
