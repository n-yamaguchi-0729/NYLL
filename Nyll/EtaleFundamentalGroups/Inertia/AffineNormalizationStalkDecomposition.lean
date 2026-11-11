/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationDecompositionBaseLocalization
public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceStalk
public import Nyll.SchemeTheory.FunctionFields.OpenAffineFractionField
public import Nyll.SchemeTheory.Normalization.OpenGenericExtension
public import Nyll.SchemeTheory.Affine.StalkLocalization
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective

/-!
# Original decomposition groups in the actual stalk of an intermediate open

Let `U → X → C` be the original open immersions. An affine normalization
prime of `C` above a point of `X` localizes to a maximal prime in the
literal stalk of `X`. The coefficient map into the original function field
of `U` is the one constructed from its original generic field source.
The full original absolute-Galois decomposition and inertia subgroups are unchanged.

The germ, the stalk isomorphism and the generic-source factorization prove
all scalar-tower comparisons. In particular an intermediate one-point
filling can use this theorem without replacing the original normalization
point or assuming a decomposition comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace SchemeTheory
open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationCommAlgGaloisAction
  AlgebraicGeometry.FiniteEtale.genericPoint_isDominant

local instance affineNormalizationStalkOpenDominant
    {X U : Scheme.{u}} [IsIntegral X] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j⟩

/-- The original affine normalization prime localizes in the actual stalk
of any intermediate open containing its base point. The local coefficient
map is the original generic-field-source map. Both the full decomposition
and full inertia subgroups are preserved at this same stalk prime in the
same absolute Galois group. -/
theorem exists_openAffineNormalizationStalkPrime_and_inertia
    {C X U : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsIntegral U]
    (i : X ⟶ C) [IsOpenImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsGalois U.functionField Ω]
    (V : C.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (x : X) (hx : i x ∈ V) :
    let R := Γ(C, V)
    let A := X.presheaf.stalk x
    let : Algebra R U.functionField :=
      (j ≫ i).functionFieldAlgebraOfIsOpenImmersionAffine V
    let : IsFractionRing R U.functionField :=
      (j ≫ i).functionField_isFractionRing_of_isOpenImmersionAffine V hV
    let : Algebra C.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        (j ≫ i).functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let : Algebra R Ω := C.affineExtensionAlgebra V Ω
    let : IsScalarTower R U.functionField Ω :=
      (j ≫ i).functionField_isScalarTower_of_isOpenImmersionAffine V Ω
    let : Algebra A U.functionField :=
      genericFieldSourceStalkAlgebra (U.fromSpecStalk (genericPoint U) ≫ j) x
    let : IsFractionRing A U.functionField :=
      genericFieldSourceStalk_isFractionRing (U.fromSpecStalk (genericPoint U) ≫ j) x
    let : Algebra A Ω := ((algebraMap U.functionField Ω).comp
      (algebraMap A U.functionField)).toAlgebra
    let : IsScalarTower A U.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra R A :=
      ((i.stalkMap x).hom.comp (C.presheaf.germ V (i x) hx).hom).toAlgebra
    ∀ (Q : Ideal (normalizationCommAlgCat R Ω)) [Q.IsPrime]
      [Q.LiesOver (hV.primeIdealOf ⟨i x, hx⟩).asIdeal],
      ∃ q : Ideal (normalizationCommAlgCat A Ω), q.IsMaximal ∧
        MulAction.stabilizer Gal(Ω/U.functionField) Q =
          MulAction.stabilizer Gal(Ω/U.functionField) q ∧
        Q.inertia Gal(Ω/U.functionField) = q.inertia Gal(Ω/U.functionField) := by
  intro R A instRF fractionR instCΩ instRΩ towerR instAF fractionA instAΩ towerA
    instRA Q hQ hOver
  let B := C.presheaf.stalk (i x)
  let P := (hV.primeIdealOf ⟨i x, hx⟩).asIdeal
  let : Algebra R B := (C.presheaf.germ V (i x) hx).hom.toAlgebra
  let e : B ≃ₐ[R] A :=
    { (asIso (i.stalkMap x)).commRingCatIsoToRingEquiv with
      commutes' := fun _ => rfl }
  have : IsLocalization.AtPrime B P := hV.isLocalization_stalk ⟨i x, hx⟩
  have : IsLocalization.AtPrime A P :=
    (IsLocalization.isLocalization_iff_of_algEquiv P.primeCompl e).mp inferInstance
  have hRA : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ hV.fromSpec =
      X.fromSpecStalk x ≫ i := by
    have hfrom : Spec.map (C.presheaf.germ V (i x) hx) ≫ hV.fromSpec =
        C.fromSpecStalk (i x) := hV.fromSpecStalk_eq_fromSpecStalk hx
    change Spec.map (C.presheaf.germ V (i x) hx ≫ i.stalkMap x) ≫ hV.fromSpec = _
    rw [Spec.map_comp, Category.assoc, hfrom]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk i (x := x)
  have hRK : Spec.map (CommRingCat.ofHom (algebraMap R U.functionField)) ≫
      hV.fromSpec = U.fromSpecStalk (genericPoint U) ≫ (j ≫ i) := by
    have h := spec_algebraMap_openGenericNormalizationChart_fromSpec
      (j ≫ i) U.functionField V hV
    have hgeneric : U.genericExtensionMorphism U.functionField =
        U.fromSpecStalk (genericPoint U) := by
      change Spec.map (𝟙 U.functionField) ≫ U.fromSpecStalk (genericPoint U) = _
      rw [Spec.map_id, Category.id_comp]
    rw [hgeneric] at h
    exact h
  have hcoeff : CommRingCat.ofHom (algebraMap R U.functionField) =
      CommRingCat.ofHom (algebraMap R A) ≫
        CommRingCat.ofHom (algebraMap A U.functionField) := by
    apply Spec.map_injective
    apply (cancel_mono hV.fromSpec).mp
    rw [Spec.map_comp, Category.assoc, hRA, ← Category.assoc,
      genericFieldSourceStalkMap_fromSpecStalk
        (U.fromSpecStalk (genericPoint U) ≫ j) x, Category.assoc, hRK]
  have : IsScalarTower R A U.functionField :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hcoeff)
  have : IsScalarTower R A Ω := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [IsScalarTower.algebraMap_eq R U.functionField Ω,
      IsScalarTower.algebraMap_eq R A U.functionField, ← RingHom.comp_assoc]
    rfl
  let q := Q.map (normalizationBaseLocalizationRingMap R A Ω)
  have hD := normalizationDecomposition_eq_of_primeLocalization R A U.functionField Ω P Q
  have : (show Ideal (integralClosure R Ω) from Q).IsPrime := hQ
  have : (show Ideal (integralClosure R Ω) from Q).LiesOver P := hOver
  have hI := originalNormalizationInertia_eq_of_primeLocalization R A U.functionField Ω P Q
  refine ⟨q, hD.1, hD.2.trans ?_, hI.2⟩
  apply Subgroup.ext
  intro σ
  change (σ • (show Ideal (integralClosure A Ω) from q) = q) ↔
    σ • (show Ideal (normalizationCommAlgCat A Ω) from q) = q
  have hsmul : (show Ideal (normalizationCommAlgCat A Ω) from
      σ • (show Ideal (integralClosure A Ω) from q)) =
      σ • (show Ideal (normalizationCommAlgCat A Ω) from q) := by
    apply Ideal.ext
    intro b
    have hraw := Ideal.mem_pointwise_smul_iff_inv_smul_mem (a := σ)
      (S := (show Ideal (integralClosure A Ω) from q))
      (x := (show integralClosure A Ω from b))
    have hnative := Ideal.mem_pointwise_smul_iff_inv_smul_mem (a := σ)
      (S := (show Ideal (normalizationCommAlgCat A Ω) from q))
      (x := (show normalizationCommAlgCat A Ω from b))
    have hb : (show normalizationCommAlgCat A Ω from
        σ⁻¹ • (show integralClosure A Ω from b)) =
        σ⁻¹ • (show normalizationCommAlgCat A Ω from b) := by
      apply Subtype.ext
      exact congrArg (fun f : normalizationCommAlgCat A Ω →+* Ω => f b)
        (normalizationCommAlg_action_comp_inclusion A U.functionField Ω σ⁻¹)
    exact hraw.trans ((Iff.of_eq (congrArg
      (fun a : normalizationCommAlgCat A Ω =>
        a ∈ (show Ideal (normalizationCommAlgCat A Ω) from q)) hb)).trans hnative.symm)
  exact Iff.of_eq (congrArg (fun I : Ideal (normalizationCommAlgCat A Ω) => I = q) hsmul)

/-- The original affine normalization prime localizes in the actual stalk
with its full decomposition subgroup unchanged. This is the decomposition
part of the same-prime decomposition-and-inertia comparison. -/
theorem exists_openAffineNormalizationStalkPrime
    {C X U : Scheme.{u}} [IsIntegral C] [IsIntegral X] [IsIntegral U]
    (i : X ⟶ C) [IsOpenImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsGalois U.functionField Ω]
    (V : C.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (x : X) (hx : i x ∈ V) :
    let R := Γ(C, V)
    let A := X.presheaf.stalk x
    let : Algebra R U.functionField :=
      (j ≫ i).functionFieldAlgebraOfIsOpenImmersionAffine V
    let : IsFractionRing R U.functionField :=
      (j ≫ i).functionField_isFractionRing_of_isOpenImmersionAffine V hV
    let : Algebra C.functionField Ω :=
      ((algebraMap U.functionField Ω).comp
        (j ≫ i).functionFieldRingEquivOfIsOpenImmersion.toRingHom).toAlgebra
    let : Algebra R Ω := C.affineExtensionAlgebra V Ω
    let : IsScalarTower R U.functionField Ω :=
      (j ≫ i).functionField_isScalarTower_of_isOpenImmersionAffine V Ω
    let : Algebra A U.functionField :=
      genericFieldSourceStalkAlgebra (U.fromSpecStalk (genericPoint U) ≫ j) x
    let : IsFractionRing A U.functionField :=
      genericFieldSourceStalk_isFractionRing (U.fromSpecStalk (genericPoint U) ≫ j) x
    let : Algebra A Ω := ((algebraMap U.functionField Ω).comp
      (algebraMap A U.functionField)).toAlgebra
    let : IsScalarTower A U.functionField Ω := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra R A :=
      ((i.stalkMap x).hom.comp (C.presheaf.germ V (i x) hx).hom).toAlgebra
    ∀ (Q : Ideal (normalizationCommAlgCat R Ω)) [Q.IsPrime]
      [Q.LiesOver (hV.primeIdealOf ⟨i x, hx⟩).asIdeal],
      ∃ q : Ideal (normalizationCommAlgCat A Ω), q.IsMaximal ∧
        MulAction.stabilizer Gal(Ω/U.functionField) Q =
          MulAction.stabilizer Gal(Ω/U.functionField) q := by
  intro R A instRF fractionR instCΩ instRΩ towerR instAF fractionA instAΩ towerA
    instRA Q hQ hOver
  obtain ⟨q, hq, hD, -⟩ :=
    exists_openAffineNormalizationStalkPrime_and_inertia i j Ω V hV x hx Q
  exact ⟨q, hq, hD⟩

end EtaleFundamentalGroups.Inertia
