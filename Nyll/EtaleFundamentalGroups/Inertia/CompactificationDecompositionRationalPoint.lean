/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.CompactificationCharts
public import Nyll.EtaleFundamentalGroups.Inertia.ConstantResidueRationality
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationIntegralBaseDecomposition
public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationLocalizedArithmeticRestriction
public import Nyll.SchemeTheory.FunctionFields.OpenAffineFractionField
public import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverStabilizerPreimage
public import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Actual rational compactification points from the same decomposition action

At a specified maximal absolute-normalization prime, constant automorphisms
whose original decomposition lifts fix the pointed cover give a rational
point of its actual compactification. The residue map is constructed on
the literal finite integral-closure chart and its kernel is the exact
contraction of the original prime.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace SchemeTheory
open AlgebraicGeometry.FiniteEtale CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationCommAlgGaloisAction

private local instance connectedLeftIntegral
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (W : FiniteEtale U) [IsConnected W] : IsIntegral W.left :=
  isIntegral_left_of_isConnected_finiteEtale W

variable {X U : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
  [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
  (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
  [Algebra k U.functionField] [Algebra U.functionField Ω]
  [Algebra k κ] [Algebra k Ω] [Algebra κ Ω]
  [IsScalarTower k U.functionField Ω] [IsScalarTower k κ Ω]
  [IsAlgClosed κ] [IsAlgClosure k κ] [IsSepClosure k κ]
  [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
  (c : X ⟶ Spec (.of k)) [IsProper c]
  (hbase : U.fromSpecStalk (genericPoint U) ≫ (j ≫ c) =
    Spec.map (CommRingCat.ofHom (algebraMap k U.functionField)))
  (W : FiniteEtale U) [IsConnected W]
  (w : (fiber (U.genericExtensionMorphism Ω)).obj W)

include hbase in
/-- Original decomposition lifts fixing the actual pointed cover construct
a rational compactification point with the exact original prime image. -/
theorem exists_rationalPoint_of_samePrime_decomposition_constants
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
      (_hQmax : Q.asIdeal.IsMaximal)
      (_h : ∀ σ : Gal(κ/k),
        ∃ d : normalizationDecompositionGroup Γ(X, V) U.functionField Ω Q.asIdeal,
          absoluteGenericGaloisToFundamentalGroup U Ω d.val ∈
              MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w ∧
            (d.val.restrictScalars k).restrictNormal κ = σ),
      ∃ y : Spec (.of k) ⟶ (connectedCoverGenericComposite W ≫ j).normalization,
        y ≫ ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c) = 𝟙 _ ∧
          y (IsLocalRing.closedPoint k) = connectedCoverAbsoluteNormalizationMap Ω j W w
            (openGenericNormalizationChart j Ω V hV Q) := by
  intro _ _ _ _ _ Q hQmax h
  let A := Γ(X, V)
  let F := U.functionField
  let L := W.left.functionField
  let : Algebra F L := finiteEtaleFunctionFieldAlgebra W
  let β := finiteEtaleGenericHomFunctionFieldAlgHom W
    (fiberObjEquivHom (U.genericExtensionMorphism Ω) W w)
  let instLΩ : Algebra L Ω := β.toRingHom.toAlgebra
  have : IsScalarTower F L Ω := IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
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
  let chart := connectedCoverCompactificationChart j W V hV
  let cB : Spec (.of B) ⟶ Spec (.of k) :=
    chart ≫ ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c)
  let : Algebra k B := (Spec.homEquiv cB).hom.toAlgebra
  have hcB : Spec.map (CommRingCat.ofHom (algebraMap k B)) = cB :=
    Spec.homEquiv.symm_apply_apply cB
  have : IsProper ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c) :=
    connectedCoverCompactification_isProper j W c
  have : LocallyOfFiniteType cB := inferInstance
  have hfinite : (algebraMap k B).FiniteType := by
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k B))) := by
      rw [hcB]
      infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  have : Algebra.FiniteType k B := (RingHom.finiteType_algebraMap).mp hfinite
  let : Algebra k L := ((algebraMap F L).comp (algebraMap k F)).toAlgebra
  have : IsScalarTower k L Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (IsScalarTower.algebraMap_apply k F Ω a).trans
      (β.commutes (algebraMap k F a)).symm
  have hpB : Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ cB =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    have hsource : connectedCoverGenericComposite W ≫ j =
        U.genericExtensionMorphism L ≫ j :=
      (genericExtensionMorphism_eq_connectedCoverGenericComposite_comp j W).symm.trans
        (genericExtensionMorphism_eq_comp_openImmersion j L)
    change _ ≫ (chart ≫ ((connectedCoverGenericComposite W ≫ j).fromNormalization ≫ c)) = _
    rw [← Category.assoc, spec_val_connectedCoverCompactificationChart,
      ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hsource, Category.assoc]
    change (Spec.map (CommRingCat.ofHom (algebraMap F L)) ≫
      U.fromSpecStalk (genericPoint U)) ≫ (j ≫ c) = _
    rw [Category.assoc, hbase, ← Spec.map_comp]
    rfl
  have : IsScalarTower k B L := by
    apply IsScalarTower.of_algebraMap_eq'
    have he : CommRingCat.ofHom (algebraMap k L) =
        CommRingCat.ofHom (algebraMap k B) ≫ CommRingCat.ofHom (algebraMap B L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hcB, hpB]
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of L => f.hom) he
  have towerkBΩ : IsScalarTower k B Ω := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (IsScalarTower.algebraMap_apply k L Ω a).trans
      (congrArg (algebraMap L Ω) (IsScalarTower.algebraMap_apply k B L a))
  let e := @normalizationIntegralBaseRingEquiv A B Ω _ _ _ _ _ instBΩ towerABΩ _
  let QB := Q.asIdeal.comap e.toRingHom
  have : Q.asIdeal.IsMaximal := hQmax
  have hQBmax : QB.IsMaximal := hQmax.comap_bijective e.toRingHom e.bijective
  have hB : ∀ σ : Gal(κ/k),
      ∃ d : @normalizationDecompositionGroup B L Ω _ _ _ _ _ instLΩ instBΩ towerBLΩ _ QB,
      (d.val.restrictScalars k).restrictNormal κ = σ := by
    intro σ
    obtain ⟨d, hfix, hd⟩ := h σ
    have hfield : d.val ∈ (AlgEquiv.restrictScalarsHom F : Gal(Ω/L) →* Gal(Ω/F)).range := by
      rw [← pointedCoverStabilizer_comap_absoluteGenericGalois Ω W w]
      exact hfix
    obtain ⟨δ, hδ⟩ := hfield
    have hD := hδ.symm ▸ d.property
    let dB := @normalizationIntegralBaseDecompositionOfRestriction A B Ω
      _ _ _ _ _ _ instBΩ towerABΩ F L _ _ _ _ _ _ _ _ instLΩ _ _ towerBLΩ _ _
      Q.asIdeal δ hD
    refine ⟨dB, ?_⟩
    change (δ.restrictScalars k).restrictNormal κ = σ
    have heq : δ.restrictScalars k = d.val.restrictScalars k := by
      have heq' := congrArg (fun γ : Gal(Ω/F) => γ.restrictScalars k) hδ
      exact heq'
    rw [heq]
    exact hd
  obtain ⟨r, hr, -⟩ := @exists_rationalResidueMap_of_decomposition_constants k B κ Ω
    _ _ _ _ _ _ _ instBΩ _ towerkBΩ _ _ _ _ _ L _ _ _ _ instLΩ towerBLΩ _ _ QB hQBmax hB
  let y : Spec (.of k) ⟶ (connectedCoverGenericComposite W ≫ j).normalization :=
    Spec.map (CommRingCat.ofHom r.toRingHom) ≫ chart
  refine ⟨y, ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom r.toRingHom) ≫ chart) ≫ _ = _
    rw [Category.assoc]
    change Spec.map (CommRingCat.ofHom r.toRingHom) ≫ cB = _
    rw [← hcB, ← Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap k B) ≫ CommRingCat.ofHom r.toRingHom = 𝟙 _ :=
      CommRingCat.hom_ext r.comp_algebraMap
    rw [he, Spec.map_id]
  · let P : PrimeSpectrum B := Q.comap
      (genericNormalizationChartRingMap X (connectedCoverAmbientFieldEmbedding j W Ω w) V)
    have hQover : QB.LiesOver P.asIdeal := by
      have hcoeff : e.toRingHom.comp (algebraMap B (integralClosure B Ω)) =
          genericNormalizationChartRingMap X (connectedCoverAmbientFieldEmbedding j W Ω w) V := by
        apply RingHom.ext
        intro b
        apply Subtype.ext
        exact @normalizationIntegralBaseRingEquiv_toAmbient A B Ω _ _ _ _ _ instBΩ
          towerABΩ _ (algebraMap B (integralClosure B Ω) b)
      constructor
      change Q.asIdeal.comap
          (genericNormalizationChartRingMap X (connectedCoverAmbientFieldEmbedding j W Ω w) V) =
        QB.comap (algebraMap B (integralClosure B Ω))
      exact congrArg (fun f : B →+* normalizationCommAlgCat A Ω => Q.asIdeal.comap f)
        hcoeff.symm
    have hp : (Spec.map (CommRingCat.ofHom r.toRingHom)) (IsLocalRing.closedPoint k) = P := by
      apply PrimeSpectrum.ext
      change Ideal.comap r.toRingHom (IsLocalRing.maximalIdeal k) = P.asIdeal
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact hr.trans (QB.over_def P.asIdeal).symm
    change chart ((Spec.map (CommRingCat.ofHom r.toRingHom)) (IsLocalRing.closedPoint k)) = _
    rw [hp]
    exact connectedCoverCompactificationChart_comap j W Ω w V hV Q

end EtaleFundamentalGroups.Inertia
