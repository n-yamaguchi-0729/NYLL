/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.EmbeddedArtinTransfer
public import Nyll.EtaleFundamentalGroups.GaloisCovers.CoverSourceKernel
public import Nyll.EtaleFundamentalGroups.GeometricFiber.NativeSourceAbelianComparison
public import Nyll.ProCGroups.Abelian.TransferThroughCoverEquiv
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisNaturality
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.AbsoluteArtin
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange

/-!
# Original native reciprocity and transfer into an actual finite cover

The actual covering source embeds in the original native separable
closure through the supplied ambient comparison. Its original finite
fixing subgroup contains the original generic kernel because that
kernel fixes the actual covering fiber. Naturality of the literal
Galois action supplies the covering-group square.

Original transfer naturality consequently compares the native transfer
with transfer into the actual covering group. The proved native Artin
inclusion theorem then gives the actual reciprocity square. None of
the kernel, transfer, or Artin squares is assumed.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry ProCGroups.Abelian
open ClassFormation LocalClassFieldTheory FunctionField
open ProCGroups.FiniteStepSolvableQuotients

namespace AlgebraicGeometry.FiniteEtale

/-- Equality transport of an actual pointed group map is conjugation by
its equality-induced fiber isomorphism. -/
private theorem coverSourcePointedHom_eq_conjAut
    {X Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    (f : X ⟶ Y) (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h : x ≫ f = y) (a : π₁ᵉᵗ(x)) :
    pointedFundamentalGroupHom f x y h a =
      CategoryTheory.PreGaloisCategory.continuousConjAut
        (eqToIso (congrArg fiber h)) (fundamentalGroupHom f x a) := by
  subst y
  rfl

variable (K L Ω : Type u) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
  [FiniteDimensional K L] [IsGalois K L]
  [IsSepClosure K Ω] [IsSepClosure L Ω] [IsSepClosed Ω]
  (eK : SeparableClosure K ≃ₐ[K] Ω)

/-- The actual upper-field embedding into the lower native separable
closure, through the original common ambient field. -/
def coverSourceNativeEmbedding : L →ₐ[K] SeparableClosure K :=
  eK.symm.toAlgHom.comp (IsScalarTower.toAlgHom K L Ω)

omit [FiniteDimensional K L] [IsGalois K L]
  [IsSepClosure K Ω] [IsSepClosure L Ω] [IsSepClosed Ω] in
/-- The embedding retains exactly the original ambient coefficients. -/
theorem coverSourceNativeEmbedding_apply (a : L) :
    eK (coverSourceNativeEmbedding K L Ω eK a) = algebraMap L Ω a :=
  eK.apply_symm_apply _

variable {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
  (W : FiniteEtale X) [IsIntegral W.left] [IsNormalIntegral W.left]
  (p : Spec (.of K) ⟶ X) [IsDominant p] [IsPreimmersion p]
  (q : Spec (.of L) ⟶ W.left) [IsDominant q] [IsPreimmersion q]
  (hpoint : (ξ L Ω ≫ q) ≫ W.hom = ξ K Ω ≫ p)
  (M : OpenNormalSubgroup π₁ᵉᵗ(ξ K Ω ≫ p))
  (eW : π₁ᵉᵗ(ξ L Ω ≫ q) ≃ₜ* M.toSubgroup)
  (heW : ∀ g : π₁ᵉᵗ(ξ L Ω ≫ q),
    (eW g).val = pointedFundamentalGroupHom W.hom
      (ξ L Ω ≫ q) (ξ K Ω ≫ p) hpoint g)
  (eL : SeparableClosure L ≃ₐ[L] Ω)

include heW in
/-- Native original transfer agrees with original transfer into the actual
covering group. The actual source fields and literal pointed-cover map
prove the required kernel containment and quotient square. -/
theorem nativeAbsoluteTransfer_coverSource
    (a : localAbsoluteAbelianProfinite K) :
    have _ : Finite (π₁ᵉᵗ(ξ K Ω ≫ p) ⧸ M.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen M.toSubgroup M.isOpen'
    nativeSourceAbelianHomOfClosure q eL
        (nativeAbsoluteTransferOfEmbedding K L (coverSourceNativeEmbedding K L Ω eK) a) =
      (TopologicalAbelianization.congr eW).symm
        (openNormalTransferTopologicalAbelianization M
          (nativeSourceAbelianHomOfClosure p eK a)) := by
  intro hMfinite
  let i := coverSourceNativeEmbedding K L Ω eK
  let H := embeddedTransferAbstractField K L i
  have hHnormal : H.field.toSubgroup.Normal := by
    change (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup.Normal
    infer_instance
  have hHfinite : Finite (Gal(SeparableClosure K/K) ⧸ H.field.toSubgroup) :=
    ambientQuotientFiniteOfAbstractFinite K (SeparableClosure K) H.field H.finite
  let N := finiteAbstractOpenNormal K (SeparableClosure K) H
  let f := nativeSourceGaloisHomOfClosure p eK
  have hf : Function.Surjective f := nativeSourceGaloisHomOfClosure_surjective p eK
  have hker : f.toMonoidHom.ker ≤ N.toSubgroup := by
    intro σ hσ
    change σ ∈ (finiteGaloisFieldRangeOfEmbedding K L i).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨b, rfl⟩
    have hfix := fieldSourceKernel_fixes_coverSource K L Ω W p q hpoint
      (AlgEquiv.autCongr eK σ) hσ b
    apply eK.injective
    calc
      eK (σ (i b)) = AlgEquiv.autCongr eK σ (algebraMap L Ω b) := rfl
      _ = algebraMap L Ω b := hfix
      _ = eK (i b) := (coverSourceNativeEmbedding_apply K L Ω eK b).symm
  let aLNative : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
  let eKL : SeparableClosure K ≃ₐ[L] Ω :=
    { eK.toRingEquiv with commutes' := coverSourceNativeEmbedding_apply K L Ω eK }
  let eBridge : SeparableClosure L ≃ₐ[L] Ω :=
    (embeddedTransferClosureEquiv K L i).trans eKL
  let g := nativeSourceGaloisHomOfClosure q eBridge
  have hg : Function.Surjective g := nativeSourceGaloisHomOfClosure_surjective q eBridge
  let eG := embeddedTransferAbsoluteGaloisEquiv K L i
  have hsquare (σ : Gal(SeparableClosure L/L)) :
      (eW (g σ)).val = f (eG σ).val := by
    rw [heW, coverSourcePointedHom_eq_conjAut]
    have hgal : (AlgEquiv.autCongr eBridge σ).restrictScalars K =
        AlgEquiv.autCongr eK (eG σ).val := by
      apply AlgEquiv.ext
      intro x
      change eK (embeddedTransferClosureEquiv K L i
          (σ ((embeddedTransferClosureEquiv K L i).symm (eK.symm x)))) =
        eK ((eG σ).val (eK.symm x))
      rw [embeddedTransferAbsoluteGaloisEquiv_apply]
    exact (fieldSourceAbsoluteGaloisHom_naturality K L Ω
      (X := X) (Y := W.left) W.hom q p hpoint
      (AlgEquiv.autCongr eBridge σ)).trans
        (congrArg (fieldSourceAbsoluteGaloisHom K Ω p) hgal)
  have htransfer := openNormalTransfer_through_cover_equivalences f hf N M hker
    eG eW g hg hsquare a
  have hnative :
      TopologicalAbelianization.congr eG
          (nativeAbsoluteTransferOfEmbedding K L i a) =
        openNormalTransferTopologicalAbelianization N a :=
    nativeAbsoluteTransferOfEmbedding_comparison K L i a
  have hcancel : (TopologicalAbelianization.congr eG).symm
      (openNormalTransferTopologicalAbelianization N a) =
        nativeAbsoluteTransferOfEmbedding K L i a :=
    (congrArg (TopologicalAbelianization.congr eG).symm hnative.symm).trans
      ((TopologicalAbelianization.congr eG).symm_apply_apply _)
  rw [hcancel] at htransfer
  change nativeSourceAbelianHomOfClosure q eBridge
      (nativeAbsoluteTransferOfEmbedding K L i a) = _ at htransfer
  rw [nativeSourceAbelianHomOfClosure_eq q eBridge eL] at htransfer
  exact htransfer

section Artin

variable (k : Type v) [Field k] [Finite k]
  [Algebra k K] [Algebra k L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]

include heW in
/-- Original native Artin reciprocity of actual finite-field inclusion
commutes with original transfer into the actual pointed cover. -/
theorem absoluteArtin_baseChange_coverSource (c : FunctionField.IdeleClassGroup k K) :
    have _ : Finite (π₁ᵉᵗ(ξ K Ω ≫ p) ⧸ M.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen M.toSubgroup M.isOpen'
    nativeSourceAbelianHomOfClosure q eL
        (FunctionField.absoluteArtin k L
          (FunctionField.IdeleClassGroup.baseChange (k := k) (K := K) (L := L) c)) =
      (TopologicalAbelianization.congr eW).symm
        (openNormalTransferTopologicalAbelianization M
          (nativeSourceAbelianHomOfClosure p eK (FunctionField.absoluteArtin k K c))) := by
  intro hMfinite
  rw [FunctionField.absoluteArtin_baseChange_transferOfEmbedding K L
    (coverSourceNativeEmbedding K L Ω eK) k]
  exact nativeAbsoluteTransfer_coverSource K L Ω eK W p q hpoint M eW heW eL
    (FunctionField.absoluteArtin k K c)

end Artin

end AlgebraicGeometry.FiniteEtale
