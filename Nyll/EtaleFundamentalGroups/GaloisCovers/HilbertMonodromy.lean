/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Normalization.HilbertClassField
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.GenericPointSurjective
public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.SchemeTheory.Normalization.GenericFiber.GenericExtension
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Separation.Hausdorff
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.HilbertClassFieldConstruction

/-!
# Native monodromy of the actual Hilbert normalization

The generic fibre of the Hilbert normalization is the original intermediate
field. Consequently the kernel of the original generic Galois map fixes that
field. Literal Galois restriction therefore descends continuously and
surjectively to the original fundamental group. Its coefficient formula is
proved from that restriction, without choosing a deck-group comparison.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve TopologicalSpace
open scoped CategoryTheory.PreGaloisCategory FintypeCatDiscrete

namespace EtaleFundamentalGroups

attribute [local instance] AlgebraicGeometry.FiniteEtale.genericPoint_isDominant

section Normalization

variable (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω] [IsSepClosed Ω]
    (L : Type u) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]
    (i : L →ₐ[X.functionField] Ω)

/-- The original generic kernel fixes every finite subfield whose actual
normalization is finite étale. The generic-fibre comparison is supplied by
the canonical normalization square. -/
theorem genericKernel_le_fixingSubgroup_of_finiteEtale_normalization
    [IsFiniteEtale (X.genericExtensionMorphism L).fromNormalization] :
    (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω
      (X.fromSpecStalk (genericPoint X))).toMonoidHom.ker ≤ i.fieldRange.fixingSubgroup := by
  have hfinite : FiniteDimensional X.functionField i.fieldRange :=
    FiniteDimensional.of_surjective i.equivFieldRange.toLinearMap i.equivFieldRange.surjective
  apply (FiniteEtale.fieldSourceKernel_le_fixingSubgroup_iff_exists_finiteEtale_genericFiber
    X.functionField Ω (X.fromSpecStalk (genericPoint X)) i.fieldRange).mpr
  let f := (X.genericExtensionMorphism L).fromNormalization
  let e := (isPullback_genericExtensionNormalization X L).isoPullback
  let efield := Scheme.Spec.mapIso i.equivFieldRange.symm.toRingEquiv.toCommRingCatIso.op
  refine ⟨(X.genericExtensionMorphism L).normalization, f,
    inferInstance, inferInstance, e.symm.trans efield, ?_⟩
  change (e.inv ≫ Spec.map (CommRingCat.ofHom i.equivFieldRange.symm.toRingHom)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap X.functionField i.fieldRange)) = _
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcoeff : i.equivFieldRange.symm.toRingHom.comp
      (algebraMap X.functionField i.fieldRange) = algebraMap X.functionField L := by
    ext a
    exact i.equivFieldRange.symm.commutes a
  rw [hcoeff]
  have he : e.hom ≫ pullback.snd f (X.fromSpecStalk (genericPoint X)) =
      Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) :=
    (isPullback_genericExtensionNormalization X L).isoPullback_hom_snd
  rw [← he, Iso.inv_hom_id_assoc]

variable [IsGalois X.functionField L]

/-- Literal finite Galois restriction descends through the original
generic-point map when the corresponding normalization is finite étale.
The descended homomorphism is continuous and surjective. -/
theorem exists_normalizationGaloisMonodromy
    [IsFiniteEtale (X.genericExtensionMorphism L).fromNormalization] :
    ∃ χ : Aut (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom
        (algebraMap X.functionField Ω)) ≫
        X.fromSpecStalk (genericPoint X))) →ₜ* Gal(L/X.functionField),
      Function.Surjective χ ∧
        ∀ (σ : Gal(Ω/X.functionField)) (a : L),
          i (χ (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω
            (X.fromSpecStalk (genericPoint X)) σ) a) = σ (i a) := by
  let aLΩ : Algebra L Ω := i.toRingHom.toAlgebra
  have hKLΩ : IsScalarTower X.functionField L Ω :=
    IsScalarTower.of_algebraMap_eq (fun a => (i.commutes a).symm)
  have hfinite : FiniteDimensional X.functionField i.fieldRange :=
    FiniteDimensional.of_surjective i.equivFieldRange.toLinearMap i.equivFieldRange.surjective
  let q := FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField Ω
    (X.fromSpecStalk (genericPoint X))
  let r : Gal(Ω/X.functionField) →* Gal(L/X.functionField) := AlgEquiv.restrictNormalHom L
  have hrker : r.ker = i.fieldRange.fixingSubgroup :=
    AlgEquiv.ker_restrictNormalHom L
  have hker : q.toMonoidHom.ker ≤ r.ker := by
    rw [hrker]
    exact genericKernel_le_fixingSubgroup_of_finiteEtale_normalization X Ω L i
  have hq : Function.Surjective q := FiniteEtale.fieldSourceAbsoluteGaloisHom_surjective
    X.functionField Ω (X.fromSpecStalk (genericPoint X))
  let χ := q.toMonoidHom.liftOfSurjective hq ⟨r, hker⟩
  have hχ (σ : Gal(Ω/X.functionField)) : χ (q σ) = r σ :=
    q.toMonoidHom.liftOfRightInverse_comp_apply
      (Function.surjInv hq) (Function.rightInverse_surjInv hq) ⟨r, hker⟩ σ
  have hr : Continuous r := by
    apply ProCGroups.MonoidHom.continuous_of_isOpen_ker_to_discrete
    rw [hrker]
    exact i.fieldRange.fixingSubgroup_isOpen
  have hχcontinuous : Continuous χ := by
    have hquotient : Topology.IsQuotientMap q :=
      Topology.IsQuotientMap.of_surjective_continuous hq q.continuous
    rw [hquotient.continuous_iff]
    have hcomp : χ ∘ q = r := funext hχ
    rw [hcomp]
    exact hr
  refine ⟨⟨χ, hχcontinuous⟩, ?_, ?_⟩
  · intro τ
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective Ω τ
    exact ⟨q σ, (hχ σ).trans hσ⟩
  · intro σ a
    change i (χ (q σ) a) = σ (i a)
    rw [hχ]
    exact AlgEquiv.restrictNormal_commutes σ L a

end Normalization

/-- The original pointed Hilbert field supplies its native finite
fundamental-group quotient. The field, the normalization and the generic
Galois map are the original ones for the specified proper curve. -/
theorem exists_hilbertClassFieldMonodromy
    (k : Type u) [Field k] [Finite k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    (c : X ⟶ Spec (.of k)) [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let _ : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
    ∀ [Algebra (RatFunc k) X.functionField]
      [IsScalarTower k (RatFunc k) X.functionField]
      [FunctionField k X.functionField] [HasPrincipalDivisors k X.functionField]
      (S : Finset (Place k X.functionField)) (hS : S.Nonempty),
      let H := FunctionField.hilbertClassField k X.functionField S hS
      ∀ (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
        [IsSepClosure X.functionField Ω] [IsSepClosed Ω]
        (i : H.val →ₐ[X.functionField] Ω),
      ∃ χ : Aut (FiniteEtale.fiber (Spec.map (CommRingCat.ofHom
          (algebraMap X.functionField Ω)) ≫
          X.fromSpecStalk (genericPoint X))) →ₜ* Gal(H.val/X.functionField),
        Function.Surjective χ ∧
          ∀ (σ : Gal(Ω/X.functionField)) (a : H.val),
            i (χ (FiniteEtale.fieldSourceAbsoluteGaloisHom X.functionField
              Ω (X.fromSpecStalk (genericPoint X)) σ) a) = σ (i a) := by
  intro akK aRK hkRK hfunction hprincipal S hS H Ω hΩ aKΩ hsepΩ hclosedΩ i
  have hnormalization := hilbertClassField_normalization_finiteEtale
    k X.functionField (CurveModel.ofSmoothProperCurve c) S hS
  change let _ : Algebra X.functionField H.val :=
      (algebraMap X.functionField H.val).toAlgebra
    IsIntegral (X.genericExtensionMorphism H.val).normalization ∧
      IsFiniteEtale (X.genericExtensionMorphism H.val).fromNormalization at hnormalization
  rw [toAlgebra_algebraMap] at hnormalization
  have hfiniteEtale : IsFiniteEtale (X.genericExtensionMorphism H.val).fromNormalization :=
    hnormalization.2
  exact exists_normalizationGaloisMonodromy X Ω H.val i

end EtaleFundamentalGroups
