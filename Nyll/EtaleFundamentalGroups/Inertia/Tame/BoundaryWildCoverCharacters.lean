/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.Tame.BoundaryWildGeometricCharacters

/-!
# Prime-to-characteristic characters on covers of the boundary-wild quotient

Every closed subgroup containing the original boundary-wild kernel has the
same continuous pro-ell characters as its image in the quotient. The argument
uses all original arithmetic conjugates of the native wild groups. It applies
to geometric subgroups of higher covers without a tame-cover-category
comparison or an assumption that the entire geometric p-primary part vanishes.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory TopologicalSpace SchemeTheory NeronModelInfra
open ProCGroups ProCGroups.ProC

namespace EtaleFundamentalGroups.Tame

universe u v

attribute [local instance] Inertia.normalizationCommAlgGaloisAction

attribute [local instance] integralOpenDominant

variable (k F Ω : Type u) [Field k] [Field F] [Field Ω]
  [Algebra F Ω] [IsSepClosure F Ω] [IsSepClosed Ω]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 c]
  (j : U ⟶ X) [IsOpenImmersion j]
  (p : Spec (.of F) ⟶ U) [IsDominant p] [IsPreimmersion p]
  (r ℓ : ℕ) [Fact r.Prime] [Fact ℓ.Prime] [CharP k r] (hrℓ : r ≠ ℓ)

local notation "Π" => π₁ᵉᵗ(ξ F Ω ≫ p)
local notation "N" => boundaryWildKernel k F Ω c j p
local notation "qt" => boundaryWildProjection k F Ω c j p

include hrℓ in
private theorem conjugateWildImageAt_le_embeddedResidual
    (B : Subgroup Π) [CompactSpace B] (hNB : N ≤ B)
    (x : X) (hx : IsClosed ({x} : Set X)) (hboundary : x ∉ Set.range j) (g : Π) :
    normalizationWildImageAt k F Ω c j p x hx ≤
      ((proCResidualCore (FiniteGroupClass.pGroup ℓ) B).map B.subtype).comap
        (MulAut.conj g).toMonoidHom := by
  let R := proCResidualCore (FiniteGroupClass.pGroup ℓ) B
  have : IsClosed (R : Set B) := proCResidualCore_isClosed (FiniteGroupClass.pGroup ℓ) B
  let q : B →ₜ* B ⧸ R :=
    { toMonoidHom := QuotientGroup.mk' R
      continuous_toFun := QuotientGroup.continuous_mk }
  have hq : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ) (B ⧸ R) :=
    proCResidualCoreQuotient_hasOpenNormalBasisInClass
      (FiniteGroupClass.pGroup_fullFormation ℓ).melnikovFormation.formation
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
  let cg : Π →ₜ* Π :=
    { toMonoidHom := (MulAut.conj g).toMonoidHom
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const }
  have hι (σ : (Inertia.actualNormalizationWildGroup A F Ω Q.asIdeal).carrier) :
      cg (ι σ) ∈ B := by
    apply hNB
    apply (boundaryWildKernel_normal k F Ω c j p).conj_mem
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    refine ⟨x, hx, hboundary, ?_⟩
    exact (le_iSup (fun Q : MaximalSpectrum (normalizationCommAlgCat A Ω) =>
      let : Q.asIdeal.IsMaximal := Q.isMaximal
      (Inertia.actualNormalizationWildSubgroup A F Ω Q.asIdeal).map
        ((fieldSourceAbsoluteGaloisHom F Ω p).toMonoidHom.comp
          (Inertia.actualNormalizationInertiaInclusion A F Ω Q.asIdeal).hom')) Q)
        ⟨σ.val, σ.property, rfl⟩
  let ψ : (Inertia.actualNormalizationWildGroup A F Ω Q.asIdeal).carrier →ₜ* B :=
    { toMonoidHom := (cg.comp ι).toMonoidHom.codRestrict B hι
      continuous_toFun := (cg.comp ι).continuous_toFun.subtype_mk hι }
  rintro γ ⟨σ, hσ, rfl⟩
  let τ : (Inertia.actualNormalizationWildGroup A F Ω Q.asIdeal).carrier := ⟨σ, hσ⟩
  refine ⟨ψ τ, ?_, rfl⟩
  exact (QuotientGroup.eq_one_iff (ψ τ)).mp
    (Inertia.normalizationWild_proPrime_character_eq_one A F Ω Q.asIdeal r ℓ hrℓ hq
      (q.comp ψ) τ)

include hrℓ in
/-- The wild kernel lies in the embedded pro-ell residual core of every
closed subgroup containing it. No normality of that subgroup is required. -/
theorem boundaryWildKernel_le_subgroupProPrimeResidual
    (B : Subgroup Π) (hB : IsClosed (B : Set Π)) (hNB : N ≤ B) :
    N ≤ (proCResidualCore (FiniteGroupClass.pGroup ℓ) B).map B.subtype := by
  have : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  apply Subgroup.topologicalClosure_minimal
  · change Subgroup.closure (Group.conjugatesOfSet
      (boundaryWildGenerators k F Ω c j p)) ≤ _
    apply (Subgroup.closure_le _).mpr
    intro γ hγ
    obtain ⟨a, ⟨x, hx, hboundary, ha⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hγ
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hmem := conjugateWildImageAt_le_embeddedResidual
      k F Ω c j p r ℓ hrℓ B hNB x hx hboundary g ha
    exact hg ▸ hmem
  · change IsClosed (B.subtype '' (proCResidualCore (FiniteGroupClass.pGroup ℓ) B : Set B))
    exact ((proCResidualCore_isClosed (FiniteGroupClass.pGroup ℓ) B).isCompact.image
      (show Continuous (B.subtype : B → Π) from continuous_subtype_val)).isClosed

include hrℓ in
/-- Every continuous pro-ell character of a closed subgroup containing the
wild kernel kills that same kernel. This includes the geometric subgroups of
the preimages of all higher tame first-layer covers. -/
theorem boundaryWild_subgroup_character_eq_one
    (B : Subgroup Π) (hB : IsClosed (B : Set Π)) (hNB : N ≤ B)
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hH : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ) H)
    (χ : B →ₜ* H) (b : B) (hb : b.val ∈ N) : χ b = 1 := by
  have : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  obtain ⟨d, hd, hdb⟩ :=
    boundaryWildKernel_le_subgroupProPrimeResidual k F Ω c j p r ℓ hrℓ B hB hNB hb
  have hdbeq : d = b := Subtype.ext hdb
  exact proPrimeResidualCore_le_ker_acrossUniverses ℓ χ hH (hdbeq ▸ hd)

include hrℓ in
/-- For any actual closed subgroup of the boundary-wild quotient, pullback
identifies its pro-ell characters with the characters of its original
preimage. The comparison is the literal restriction of the original quotient. -/
theorem boundaryWild_cover_character_pullback_bijective
    (B : Subgroup (BoundaryWildQuotient k F Ω c j p))
    (hB : IsClosed (B : Set (BoundaryWildQuotient k F Ω c j p)))
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (hH : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup ℓ) H) :
    Function.Bijective (fun χ : B →ₜ* H =>
      χ.comp (ContinuousMonoidHom.restrictPreimage (qt) B)) := by
  let B' := B.comap (qt).toMonoidHom
  have hB' : IsClosed (B' : Set Π) := hB.preimage (qt).continuous_toFun
  have : CompactSpace B' := isCompact_iff_compactSpace.mp hB'.isCompact
  have hNB : N ≤ B' := by
    intro γ hγ
    change qt γ ∈ B
    have hq : qt γ = 1 := (QuotientGroup.eq_one_iff γ).mpr hγ
    rw [hq]
    exact B.one_mem
  let q := ContinuousMonoidHom.restrictPreimage (qt) B
  have hq : Function.Surjective q := ContinuousMonoidHom.restrictPreimage_surjective
    (qt) (boundaryWildProjection_surjective k F Ω c j p) B
  constructor
  · intro χ ψ h
    apply ContinuousMonoidHom.ext
    intro b
    obtain ⟨g, rfl⟩ := hq b
    exact DFunLike.congr_fun h g
  · intro χ
    apply exists_continuous_factor_of_surjective q hq χ
    intro b hb
    apply boundaryWild_subgroup_character_eq_one k F Ω c j p r ℓ hrℓ B' hB' hNB hH χ b
    exact (QuotientGroup.eq_one_iff b.val).mp (congrArg Subtype.val hb)

end EtaleFundamentalGroups.Tame
