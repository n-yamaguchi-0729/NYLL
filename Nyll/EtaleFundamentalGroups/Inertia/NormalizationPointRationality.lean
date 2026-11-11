/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationPointAction
public import Nyll.EtaleFundamentalGroups.Inertia.ConstantResidueRationality
public import Nyll.SchemeTheory.Normalization.OpenGenericExtension
public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspArithmeticNormalizer
public import Nyll.EtaleFundamentalGroups.Inertia.GenericGaloisMapComparison
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Rationality from the actual normalization decomposition action

Full arithmetic image of the stabilizer of an actual closed normalization
point supplies every constant automorphism through its original generic
source. On an original affine chart, the native residue calculation then
constructs a rational point with exactly the original base point. This is
applicable after restricting to a finite constant field and choosing one
compatible closure embedding; the point is not assumed rational in advance.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale
open TopologicalSpace SchemeTheory NeronModelInfra EtaleFundamentalGroups

namespace EtaleFundamentalGroups.Inertia

universe u

variable (k κ Ω : Type u) [Field k] [Field κ] [Field Ω]
  {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
  (c : X ⟶ Spec (.of k)) [IsProper c]
  (j : U ⟶ X) [IsOpenImmersion j]
  [Algebra k U.functionField] [Algebra U.functionField Ω]
  [Algebra k κ] [Algebra k Ω] [Algebra κ Ω]
  [IsScalarTower k U.functionField Ω] [IsScalarTower k κ Ω]
  [IsAlgClosed κ] [IsAlgClosure k κ] [IsSepClosure k κ]
  [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
  (hbase : U.fromSpecStalk (genericPoint U) ≫ (j ≫ c) =
    Spec.algebraMap k U.functionField)

include hbase in
/-- The full arithmetic image of the actual absolute-normalization
stabilizer constructs a rational point with its exact original base point. -/
theorem exists_rationalPoint_of_normalization_arithmetic_lifts
    (z : (U.genericExtensionMorphism Ω ≫ j).normalization)
    (hclosed : IsClosed {(U.genericExtensionMorphism Ω ≫ j).fromNormalization z})
    (h : let _ := openGenericNormalizationPointAction j Ω
      ∀ σ : Gal(κ/k), ∃ τ : Gal(Ω/U.functionField),
        τ ∈ MulAction.stabilizer Gal(Ω/U.functionField) z ∧
          arithmeticFundamentalGroupHom k κ (j ≫ c) (U.genericExtensionMorphism Ω)
            (absoluteGenericGaloisToFundamentalGroup U Ω τ) = σ) :
    ∃ y : SchemeHomOver (𝟙 (Spec (.of k))) c,
      y.val (IsLocalRing.closedPoint k) =
        (U.genericExtensionMorphism Ω ≫ j).fromNormalization z := by
  let _ := openGenericNormalizationPointAction j Ω
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤)
    (x := (U.genericExtensionMorphism Ω ≫ j).fromNormalization z) (by trivial)
  let : Nonempty V := ⟨⟨(U.genericExtensionMorphism Ω ≫ j).fromNormalization z, hzV⟩⟩
  let A := Γ(X, V)
  let F := U.functionField
  let : Algebra A F := j.functionFieldAlgebraOfIsOpenImmersionAffine V
  have : IsFractionRing A F := j.functionField_isFractionRing_of_isOpenImmersionAffine V hV
  let : Algebra X.functionField Ω :=
    ((algebraMap F Ω).comp j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
  let := X.affineExtensionAlgebra V Ω
  have : IsScalarTower A F Ω := j.functionField_isScalarTower_of_isOpenImmersionAffine V Ω
  obtain ⟨Q, hQ, -, hQmax⟩ :=
    exists_openGenericNormalizationChart_maximalPoint j Ω V hV z hzV hclosed
  have : Q.asIdeal.IsMaximal := hQmax
  let cA := hV.fromSpec ≫ c
  let : Algebra k A := (Spec.homEquiv cA).hom.toAlgebra
  have hcA : Spec.algebraMap k A = cA := Spec.homEquiv.symm_apply_apply cA
  have hfinite : (algebraMap k A).FiniteType := by
    have : LocallyOfFiniteType (Spec.algebraMap k A) := by
      rw [hcA]
      infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  have : Algebra.FiniteType k A := (RingHom.finiteType_algebraMap).mp hfinite
  have hΩbase : U.genericExtensionMorphism Ω ≫ (j ≫ c) = Spec.algebraMap k Ω := by
    change (Spec.algebraMap F Ω ≫ U.fromSpecStalk (genericPoint U)) ≫ (j ≫ c) = _
    rw [Category.assoc, hbase, ← Spec.map_comp]
    congr 1
    ext a
    exact (IsScalarTower.algebraMap_apply k F Ω a).symm
  have hgeneric : Spec.algebraMap A Ω ≫ hV.fromSpec = U.genericExtensionMorphism Ω ≫ j :=
    spec_algebraMap_openGenericNormalizationChart_fromSpec j Ω V hV
  have : IsScalarTower k A Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    have he : CommRingCat.ofHom (algebraMap k Ω) =
        CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom (algebraMap A Ω) := by
      apply Spec.map_injective
      have hsquare : Spec.algebraMap k Ω = Spec.algebraMap A Ω ≫ Spec.algebraMap k A :=
        hΩbase.symm.trans
        ((congrArg (· ≫ c) hgeneric.symm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (Spec.algebraMap A Ω ≫ ·) hcA.symm)))
      exact hsquare.trans (Spec.map_comp _ _).symm
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of Ω => f.hom) he
  obtain ⟨α, hα⟩ := exists_fieldSource_arithmetic_restriction_label
    k F κ Ω (j ≫ c) (U.fromSpecStalk (genericPoint U)) hΩbase
  have hlifts : ∀ σ : Gal(κ/k), ∃ d : normalizationDecompositionGroup A F Ω Q.asIdeal,
      (d.val.restrictScalars k).restrictNormal κ = σ := by
    intro σ
    obtain ⟨τ, hτ, hlabel⟩ := h (α * σ * α⁻¹)
    have hτQ : τ ∈ MulAction.stabilizer Gal(Ω/F)
        (openGenericNormalizationChart j Ω V hV Q) :=
      Eq.mp (congrArg (fun z' => τ ∈ MulAction.stabilizer Gal(Ω/F) z') hQ.symm) hτ
    have hτrange : τ ∈ (normalizationDecompositionInclusion A F Ω Q.asIdeal).range :=
      Eq.mp (congrArg (fun H : Subgroup Gal(Ω/F) => τ ∈ H)
        (openGenericNormalizationPointAction_stabilizer j Ω V hV Q)) hτQ
    obtain ⟨d, hd⟩ := hτrange
    refine ⟨d, ?_⟩
    have hres : α * (τ.restrictScalars k).restrictNormal κ * α⁻¹ = α * σ * α⁻¹ := by
      calc
        α * (τ.restrictScalars k).restrictNormal κ * α⁻¹ =
            arithmeticFundamentalGroupHom k κ (j ≫ c) (U.genericExtensionMorphism Ω)
              (fieldSourceAbsoluteGaloisHom F Ω (U.fromSpecStalk (genericPoint U)) τ) :=
          (hα τ).symm
        _ = α * σ * α⁻¹ := by
          have hq := DFunLike.congr_fun
            (absoluteGenericGaloisToFundamentalGroup_eq_fieldSourceAbsoluteGaloisHom U Ω) τ
          exact (congrArg (arithmeticFundamentalGroupHom k κ (j ≫ c)
            (U.genericExtensionMorphism Ω)) hq).symm.trans hlabel
    have hτres := mul_left_cancel (mul_right_cancel hres)
    exact (congrArg (fun δ : Gal(Ω/F) => (δ.restrictScalars k).restrictNormal κ) hd).trans hτres
  have : (show Ideal (normalizationCommAlgCat A Ω) from Q.asIdeal).IsMaximal := hQmax
  obtain ⟨r, hr, -⟩ := exists_rationalResidueMap_of_decomposition_constants
    k A κ Ω F Q.asIdeal hlifts
  let y : Spec (.of k) ⟶ X := Spec.map (CommRingCat.ofHom r.toRingHom) ≫ hV.fromSpec
  have hy : y ≫ c = 𝟙 _ := by
    have he : CommRingCat.ofHom (algebraMap k A) ≫ CommRingCat.ofHom r.toRingHom = 𝟙 _ :=
      CommRingCat.hom_ext r.comp_algebraMap
    have hy' : Spec.map (CommRingCat.ofHom r.toRingHom) ≫ Spec.algebraMap k A = 𝟙 _ := by
      rw [← Spec.map_comp, he, Spec.map_id]
    exact (Category.assoc _ _ _).trans
      ((congrArg (Spec.map (CommRingCat.ofHom r.toRingHom) ≫ ·) hcA.symm).trans hy')
  refine ⟨⟨y, hy⟩, ?_⟩
  have hp : (Spec.map (CommRingCat.ofHom r.toRingHom)) (IsLocalRing.closedPoint k) =
      Q.comap (algebraMap A (normalizationCommAlgCat A Ω)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap r.toRingHom (IsLocalRing.maximalIdeal k) = Q.asIdeal.under A
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact hr
  change hV.fromSpec ((Spec.map (CommRingCat.ofHom r.toRingHom)) (IsLocalRing.closedPoint k)) = _
  rw [hp]
  have hchart := congrArg (fun f => f Q) (openGenericNormalizationChart_base j Ω V hV)
  exact hchart.symm.trans (congrArg (U.genericExtensionMorphism Ω ≫ j).fromNormalization hQ)

end EtaleFundamentalGroups.Inertia
