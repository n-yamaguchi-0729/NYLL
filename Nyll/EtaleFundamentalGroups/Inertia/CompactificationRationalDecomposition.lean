/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.CompactificationCharts
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationLocalizedArithmeticRestriction
public import Nyll.EtaleFundamentalGroups.Inertia.DecompositionImageIntersection
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.SchemeTheory.FunctionFields.OpenAffineFractionField
public import Nyll.SchemeTheory.LocalGeometry.RationalPointStalk
public import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverStabilizerPreimage
public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticNormalizer
public import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization

/-!
# Rational compactification points and the same original decomposition group

An actual rational point in a pointed connected-cover compactification,
lying under a specified absolute-normalization prime, supplies every
arithmetic automorphism in the intersection of that prime's original
decomposition image with the original pointed-cover stabilizer.

The local ring is constructed inside the literal integral-closure chart.
Its residue map comes from the given rational point, its fraction field
from the original generic source, and its normalization prime from exact
contraction and localization. No decomposition containment or arithmetic
surjectivity is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NeronModelInfra SchemeTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u v

attribute [local instance] normalizationCommAlgGaloisAction
  AlgebraicGeometry.FiniteEtale.connectedLeftIntegral

local instance compactificationFieldSourceQuasiCompact
    {Y : Scheme.{u}} {L : Type u} [Field L] (p : Spec (.of L) ⟶ Y) :
    QuasiCompact p :=
  ⟨fun V _ _ => (Set.toFinite (p ⁻¹' V)).isCompact⟩

variable {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  [IsNormalIntegral U] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
  [Algebra k U.functionField] [Algebra U.functionField Ω]
  [Algebra k κ] [Algebra k Ω] [Algebra κ Ω]
  [IsScalarTower k U.functionField Ω] [IsScalarTower k κ Ω]
  [IsAlgClosed κ] [IsAlgClosure k κ] [IsSepClosure k κ]
  [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
  (c : X ⟶ Spec (.of k))
  (hbase : U.fromSpecStalk (genericPoint U) ≫ (j ≫ c) =
    Spec.map (CommRingCat.ofHom (algebraMap k U.functionField)))
  (W : FiniteEtale U) [IsConnected W]
  (w : (fiber (U.genericExtensionMorphism Ω)).obj W)

include hbase in
/-- A rational point below the specified original normalization prime gives
every arithmetic label in its original decomposition image and in the same
pointed-cover stabilizer. All local coefficient data are constructed from
the actual chart and the actual rational-point morphism. -/
theorem exists_samePrime_decomposition_lift_of_rationalPoint
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra Γ(X, V) U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionAffine V
    let : IsFractionRing Γ(X, V) U.functionField :=
      j.functionField_isFractionRing_of_isOpenImmersionAffine V hV
    let : Algebra X.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V Ω
    let : IsScalarTower Γ(X, V) U.functionField Ω :=
      j.functionField_isScalarTower_of_isOpenImmersionAffine V Ω
    ∀ (Q : PrimeSpectrum (normalizationCommAlgCat Γ(X, V) Ω))
      (y : Spec (.of k) ⟶ (connectedCoverGenericComposite W ≫ j).normalization)
      (_hy : y ≫ ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c) = 𝟙 _)
      (_hQy : connectedCoverAbsoluteNormalizationMap Ω j W w
        (openGenericNormalizationChart j Ω V hV Q) = y (IsLocalRing.closedPoint k))
      (τ : Gal(κ/k)),
      ∃ d : normalizationDecompositionGroup Γ(X, V) U.functionField Ω Q.asIdeal,
        absoluteGenericGaloisToFundamentalGroup U Ω d.val ∈
            MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w ∧
          arithmeticFundamentalGroupHom k κ (j ≫ c) (U.genericExtensionMorphism Ω)
            (absoluteGenericGaloisToFundamentalGroup U Ω d.val) = τ := by
  intro instAF fracAF instXΩ instAΩ towerAFΩ Q y hy hQy τ
  let A := Γ(X, V)
  let F := U.functionField
  let L := W.left.functionField
  let : Algebra F L := finiteEtaleFunctionFieldAlgebra W
  let β := finiteEtaleGenericHomFunctionFieldAlgHom W
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w)
  let instLΩ : Algebra L Ω := β.toRingHom.toAlgebra
  have towerFLΩ : IsScalarTower F L Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    exact β.comp_algebraMap.symm
  have : IsSepClosure L Ω :=
    ⟨IsSepClosure.sep_closed F, Algebra.isSeparable_tower_top_of_isSeparable F L Ω⟩
  let : Algebra X.functionField L :=
    ((algebraMap F L).comp j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
  let : Algebra A L := X.affineExtensionAlgebra V L
  have : IsScalarTower A F L :=
    j.functionField_isScalarTower_of_isOpenImmersionAffine V L
  have : IsScalarTower A X.functionField L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A X.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
  let φ : L →ₐ[A] Ω :=
    (connectedCoverAmbientFieldEmbedding j W Ω w).restrictScalars A
  let B := integralClosure A L
  let instBΩ : Algebra B Ω := (φ.toRingHom.comp (algebraMap B L)).toAlgebra
  have towerABΩ : IsScalarTower A B Ω :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  have towerBLΩ : IsScalarTower B L Ω := IsScalarTower.of_algebraMap_eq' rfl
  have : FiniteDimensional F L := finiteDimensional_functionField_of_finiteEtale_isConnected W
  have : IsFractionRing B L :=
    integralClosure_isFractionRing_of_fractionField_algebraic A F L
  have : IsIntegrallyClosed B :=
    (IsIntegrallyClosed.integralClosure_eq_bot_iff L).mp integralClosure_idem
  let e := @normalizationIntegralBaseRingEquiv A B Ω _ _ _ _ _ instBΩ towerABΩ _
  let chart := connectedCoverCompactificationChart j W V hV
  let P : PrimeSpectrum B := Q.comap
    (genericNormalizationChartRingMap X (connectedCoverAmbientFieldEmbedding j W Ω w) V)
  have hP : chart P = y (IsLocalRing.closedPoint k) :=
    (connectedCoverCompactificationChart_comap j W Ω w V hV Q).trans hQy
  have hrange : Set.range y ⊆ Set.range chart := by
    rintro _ ⟨t, rfl⟩
    exact ⟨P, hP.trans (congrArg y (Subsingleton.elim _ t))⟩
  let y' := IsOpenImmersion.lift chart y hrange
  have hy'chart : y' ≫ chart = y := IsOpenImmersion.lift_fac chart y hrange
  let z := y' (IsLocalRing.closedPoint k)
  have hPz : P = z := by
    apply chart.isOpenEmbedding.injective
    have hz : chart z = y (IsLocalRing.closedPoint k) :=
      congrArg (fun f => f (IsLocalRing.closedPoint k)) hy'chart
    exact hP.trans hz.symm
  let cB : Spec (.of B) ⟶ Spec (.of k) :=
    chart ≫ ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c)
  have hy' : y' ≫ cB = 𝟙 _ := by
    change y' ≫ (chart ≫ _) = _
    rw [← Category.assoc, hy'chart]
    exact hy
  let pB : Spec (.of L) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B L))
  have : IsDominant pB :=
    ⟨Scheme.Hom.affineSpecMap_denseRange_of_injective _ Subtype.val_injective⟩
  have : IsPreimmersion pB :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors B)
  let : Algebra k L := ((algebraMap F L).comp (algebraMap k F)).toAlgebra
  have towerkLΩ : IsScalarTower k L Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (IsScalarTower.algebraMap_apply k F Ω a).trans
      (β.commutes (algebraMap k F a)).symm
  have hpB : pB ≫ cB = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    have hsource : connectedCoverGenericComposite W ≫ j =
        U.genericExtensionMorphism L ≫ j :=
      (genericExtensionMorphism_eq_connectedCoverGenericComposite_comp j W).symm.trans
        (genericExtensionMorphism_eq_comp_openImmersion j L)
    change pB ≫ (chart ≫ ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c)) = _
    rw [← Category.assoc, spec_val_connectedCoverCompactificationChart,
      ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hsource, Category.assoc]
    change (Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫
      U.fromSpecStalk (genericPoint U)) ≫ (j ≫ c) = _
    rw [Category.assoc, hbase, ← Spec.map_comp]
    rfl
  let R := (Spec (.of B)).presheaf.stalk z
  let : Algebra B R := StructureSheaf.stalkAlgebra B z
  let : Algebra k R := stalkAlgebra cB z
  let : Algebra R L := genericFieldSourceStalkAlgebra pB z
  let instRΩ : Algebra R Ω := ((algebraMap L Ω).comp (algebraMap R L)).toAlgebra
  have : IsFractionRing R L := genericFieldSourceStalk_isFractionRing pB z
  have : IsIntegrallyClosed R := IsNormalIntegral.stalk_isIntegrallyClosed z
  have towerRLΩ : IsScalarTower R L Ω := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B R L := by
    apply IsScalarTower.of_algebraMap_eq'
    have hfrom : (Spec (.of B)).fromSpecStalk z =
        Spec.map (CommRingCat.ofHom (algebraMap B R)) :=
      Spec.fromSpecStalk_eq' (.of B) z
    have h : CommRingCat.ofHom (algebraMap B L) =
        CommRingCat.ofHom (algebraMap B R) ≫ CommRingCat.ofHom (algebraMap R L) := by
      apply Spec.map_injective
      calc
        Spec.map (CommRingCat.ofHom (algebraMap B L)) =
            Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫
              (Spec (.of B)).fromSpecStalk z :=
          (genericFieldSourceStalkMap_fromSpecStalk pB z).symm
        _ = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap B R)) :=
          congrArg (fun f => Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ f) hfrom
        _ = Spec.map (CommRingCat.ofHom (algebraMap B R) ≫
            CommRingCat.ofHom (algebraMap R L)) :=
          (Spec.map_comp (CommRingCat.ofHom (algebraMap B R))
            (CommRingCat.ofHom (algebraMap R L))).symm
    exact congrArg (fun f : CommRingCat.of B ⟶ CommRingCat.of L => f.hom) h
  have towerBRΩ : IsScalarTower B R Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    exact congrArg (algebraMap L Ω) (IsScalarTower.algebraMap_apply B R L b)
  have : IsScalarTower k R L := genericFieldSourceStalk_isScalarTower pB z cB hpB
  have towerkRΩ : IsScalarTower k R Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (IsScalarTower.algebraMap_apply k L Ω a).trans
      (congrArg (algebraMap L Ω) (IsScalarTower.algebraMap_apply k R L a))
  have : z.asIdeal.IsPrime := z.isPrime
  have : IsLocalization.AtPrime R z.asIdeal := StructureSheaf.IsLocalization.to_stalk B z
  have hQover : (Q.asIdeal.comap e.toRingHom).LiesOver z.asIdeal := by
    have hcoeff : e.toRingHom.comp (algebraMap B (integralClosure B Ω)) =
        genericNormalizationChartRingMap X (connectedCoverAmbientFieldEmbedding j W Ω w) V := by
      apply RingHom.ext
      intro b
      apply Subtype.ext
      exact @normalizationIntegralBaseRingEquiv_toAmbient A B Ω _ _ _ _ _ instBΩ
        towerABΩ _ (algebraMap B (integralClosure B Ω) b)
    have h : (Q.asIdeal.comap e.toRingHom).LiesOver P.asIdeal := by
      constructor
      change Q.asIdeal.comap
          (genericNormalizationChartRingMap X (connectedCoverAmbientFieldEmbedding j W Ω w) V) =
        (Q.asIdeal.comap e.toRingHom).comap (algebraMap B (integralClosure B Ω))
      exact congrArg (fun f : B →+* normalizationCommAlgCat A Ω => Q.asIdeal.comap f)
        hcoeff.symm
    exact hPz ▸ h
  let r : R →ₐ[k] k := Scheme.rationalPointStalkAlgHom cB y' hy'
  have hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal R :=
    Scheme.rationalPointStalkAlgHom_ker cB y' hy'
  have hΩbase : (ξ F Ω ≫ U.fromSpecStalk (genericPoint U)) ≫ (j ≫ c) = ξ k Ω := by
    rw [Category.assoc, hbase, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom ((algebraMap F Ω).comp (algebraMap k F))) = _
    rw [← IsScalarTower.algebraMap_eq k F Ω]
  obtain ⟨α, hα⟩ := exists_fieldSource_arithmetic_restriction_label k F κ Ω
    (j ≫ c) (U.fromSpecStalk (genericPoint U)) hΩbase
  obtain ⟨d, hfield, hd⟩ := @exists_normalizationLocalizedDecomposition_lift_constants
    k A B R F L κ Ω
    _ _ _ _ _ _ _ _ _ _ _ _ instAΩ instBΩ towerABΩ _ instRΩ towerBRΩ _ _ _ _
    instLΩ towerBLΩ towerRLΩ _ instAF fracAF _ _ towerFLΩ towerAFΩ _
    _ _ _ _ _ _ towerkRΩ _ towerkLΩ _ _ _
    z.asIdeal _ _ Q.asIdeal _ hQover r hr (α⁻¹ * τ * α)
  refine ⟨d, ?_, ?_⟩
  · change d.val ∈ (MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w).comap
      (absoluteGenericGaloisToFundamentalGroup U Ω)
    rw [pointedCoverStabilizer_comap_absoluteGenericGalois Ω W w]
    exact hfield
  · have hconst : α * (d.val.restrictScalars k).restrictNormal κ * α⁻¹ = τ := by
      rw [hd]
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
    have hmap := DFunLike.congr_fun
      (absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom U Ω) d.val
    exact (congrArg
      (arithmeticFundamentalGroupHom k κ (j ≫ c) (U.genericExtensionMorphism Ω)) hmap).trans
        ((hα d.val).trans hconst)

include hbase in
/-- A rational point below the specified normalization prime supplies every
arithmetic label in its original quotient decomposition image, intersected
with any subgroup containing the actual pointed-cover stabilizer image.
The covering object and its point are abstract throughout this comparison. -/
theorem exists_samePrime_decomposition_image_inf_of_rationalPoint
    {P : Type v} [Group P] [TopologicalSpace P]
    (ρ : π₁ᵉᵗ(U.genericExtensionMorphism Ω) →ₜ* P) (π : P →ₜ* Gal(κ/k))
    (hπ : ∀ γ, π (ρ γ) = arithmeticFundamentalGroupHom k κ (j ≫ c)
      (U.genericExtensionMorphism Ω) γ)
    (H : Subgroup P)
    (hH : MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w ≤
      H.comap ρ.toMonoidHom)
    (V : X.Opens) (hV : IsAffineOpen V) [Nonempty V] :
    let : Algebra Γ(X, V) U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionAffine V
    let : IsFractionRing Γ(X, V) U.functionField :=
      j.functionField_isFractionRing_of_isOpenImmersionAffine V hV
    let : Algebra X.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let := X.affineExtensionAlgebra V Ω
    let : IsScalarTower Γ(X, V) U.functionField Ω :=
      j.functionField_isScalarTower_of_isOpenImmersionAffine V Ω
    ∀ (Q : PrimeSpectrum (normalizationCommAlgCat Γ(X, V) Ω))
      (y : Spec (.of k) ⟶ (connectedCoverGenericComposite W ≫ j).normalization)
      (_hy : y ≫ ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c) = 𝟙 _)
      (_hQy : connectedCoverAbsoluteNormalizationMap Ω j W w
        (openGenericNormalizationChart j Ω V hV Q) = y (IsLocalRing.closedPoint k))
      (g : Gal(κ/k)),
      ∃ x : P,
        x ∈ ((ρ.comp (fieldSourceAbsoluteGaloisHom U.functionField Ω
          (U.fromSpecStalk (genericPoint U)))).toMonoidHom.comp
            (normalizationDecompositionInclusion Γ(X, V) U.functionField Ω
              Q.asIdeal)).range ⊓ H ∧ π x = g := by
  intro instAF fracAF instXΩ instAΩ towerAFΩ Q y hy hQy g
  have hlift := exists_samePrime_decomposition_lift_of_rationalPoint
    j k κ Ω c hbase W w V hV Q y hy hQy g
  exact @exists_normalizationDecomposition_image_inf_of_generic_lift
    U _ Ω _ _ _ _ Γ(X, V) _ instAF fracAF instAΩ towerAFΩ Q.asIdeal
    P Gal(κ/k) _ _ _ ρ π.toMonoidHom
    (arithmeticFundamentalGroupHom k κ (j ≫ c) (U.genericExtensionMorphism Ω))
    hπ (MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w) H hH g hlift

end EtaleFundamentalGroups.Inertia
