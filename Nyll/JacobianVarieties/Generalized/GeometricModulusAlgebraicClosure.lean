/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusUniversalProperty
import Nyll.JacobianVarieties.Generalized.GeometricModulusScalarExtension
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionTorsor
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.ScalarExtensionTowerComparisons
import Nyll.SchemeTheory.GroupSchemes.BaseChangeTowerComparison
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # One algebraic closure tests a fixed geometric modulus

An actual equivariant Abel factor on an iterated scalar extension is
transported backwards through the existing group, Picard-one, and
complement isomorphisms. Thus a fixed ground divisor which has the full
condition over an algebraic closure has that condition after every closed
extension. Neither the divisor nor its regular map is replaced.
-/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem equivariant_factor_transport_inverse
    {A : Type u} [Category.{v} A] [CartesianMonoidalCategory A] [BraidedCategory A]
    {J₁ J₂ H₁ H₂ : CommGrp A} {P₁ P₂ : A}
    [ModObj J₁.X P₁] [ModObj J₂.X P₂]
    (eJ : J₁ ≅ J₂) (eP : P₁ ≅ P₂) (eH : H₁ ≅ H₂)
    (he : ∀ (T : A) (a : T ⟶ J₁.X) (x : T ⟶ P₁),
      (a • x) ≫ eP.hom = (a ≫ eJ.hom.hom.hom.hom) • (x ≫ eP.hom))
    (φ : J₁ ⟶ H₁) (f : P₁ ⟶ H₁.X)
    (hf : ∀ (T : A) (a : T ⟶ J₁.X) (x : T ⟶ P₁),
      (a • x) ≫ f = (a ≫ φ.hom.hom.hom) * (x ≫ f)) :
    ∀ (T : A) (a : T ⟶ J₂.X) (x : T ⟶ P₂),
      (a • x) ≫ (eP.inv ≫ f ≫ eH.hom.hom.hom.hom) =
        (a ≫ (eJ.inv ≫ φ ≫ eH.hom).hom.hom.hom) *
          (x ≫ (eP.inv ≫ f ≫ eH.hom.hom.hom.hom)) := by
  intro T a x
  have hJ : eJ.inv.hom.hom.hom ≫ eJ.hom.hom.hom.hom = 𝟙 J₂.X :=
    congrArg (fun z => z.hom.hom.hom) eJ.inv_hom_id
  have hback : (a • x) ≫ eP.inv =
      (a ≫ eJ.inv.hom.hom.hom) • (x ≫ eP.inv) := by
    apply (cancel_mono eP.hom).mp
    rw [Category.assoc, eP.inv_hom_id, Category.comp_id, he]
    simp only [Category.assoc, hJ, eP.inv_hom_id, Category.comp_id]
  calc
    _ = (((a ≫ eJ.inv.hom.hom.hom) • (x ≫ eP.inv)) ≫ f) ≫
        eH.hom.hom.hom.hom := by rw [← Category.assoc, ← Category.assoc, hback]
    _ = (((a ≫ eJ.inv.hom.hom.hom) ≫ φ.hom.hom.hom) *
        ((x ≫ eP.inv) ≫ f)) ≫ eH.hom.hom.hom.hom := by rw [hf]
    _ = _ := by simp only [MonObj.mul_comp, Category.assoc]; rfl

private theorem factorization_transport_inverse
    {A : Type u} [Category.{v} A] {U₁ U₂ P₁ P₂ Q₁ Q₂ : A}
    (eU : U₁ ≅ U₂) (eP : P₁ ≅ P₂)
    (a₁ : U₁ ⟶ P₁) (a₂ : U₂ ⟶ P₂)
    (q₁ : U₁ ⟶ Q₁) (q₂ : U₂ ⟶ Q₂) (t : Q₁ ⟶ Q₂) (f : P₁ ⟶ Q₁)
    (ha : eU.hom ≫ a₂ = a₁ ≫ eP.hom)
    (hq : eU.hom ≫ q₂ = q₁ ≫ t) (hf : a₁ ≫ f = q₁) :
    a₂ ≫ (eP.inv ≫ f ≫ t) = q₂ := by
  apply (cancel_epi eU.hom).mp
  rw [← Category.assoc, ha]
  simp only [Category.assoc, eP.hom_inv_id_assoc]
  rw [← Category.assoc, hf, hq]

private theorem geometricModulus_transport_inverse
    {K : Type u} [Field K] {C₁ C₂ : Scheme.{u}}
    (c₁ : C₁ ⟶ Spec (.of K))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    (c₂ : C₂ ⟶ Spec (.of K))
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    {d₁ d₂ : ℕ}
    (D₁ : RelEffCartierDiv c₁ d₁ (𝟙 (Spec (.of K))))
    (D₂ : RelEffCartierDiv c₂ d₂ (𝟙 (Spec (.of K))))
    (H₁ H₂ : CommGrp (Over (Spec (.of K))))
    [IsSeparated H₁.X.hom] [IsSeparated H₂.X.hom]
    (q₁ : Over.mk ((modulusComplement (modulusCurveMap D₁)).ι ≫ c₁) ⟶ H₁.X)
    (q₂ : Over.mk ((modulusComplement (modulusCurveMap D₂)).ι ≫ c₂) ⟶ H₂.X)
    (eJ : groupScheme c₁ D₁ ≅ groupScheme c₂ D₂)
    (eP : picardOne c₁ D₁ ≅ picardOne c₂ D₂)
    (eU : Over.mk ((modulusComplement (modulusCurveMap D₁)).ι ≫ c₁) ≅
      Over.mk ((modulusComplement (modulusCurveMap D₂)).ι ≫ c₂))
    (eH : H₁ ≅ H₂)
    (he : ∀ (T : Over (Spec (.of K)))
      (a : T ⟶ (groupScheme c₁ D₁).X) (x : T ⟶ picardOne c₁ D₁),
      (a • x) ≫ eP.hom = (a ≫ eJ.hom.hom.hom.hom) • (x ≫ eP.hom))
    (ha : eU.hom ≫ abelOneMap c₂ D₂ = abelOneMap c₁ D₁ ≫ eP.hom)
    (hq : eU.hom ≫ q₂ = q₁ ≫ eH.hom.hom.hom.hom)
    (hmod : geometricRegularMapHasModulus c₁ D₁ H₁ q₁) :
    geometricRegularMapHasModulus c₂ D₂ H₂ q₂ := by
  let _ : ModObj H₁.X H₁.X := ModObj.regular H₁.X
  have : IsIso (ModObj.leftSMul H₁.X H₁.X) :=
    SchemeTheory.PointedTorsor.isIso_leftSMul_regular H₁.X
  have hcoord₁ : q₁ ≫ SchemeTheory.PointedTorsor.coordinate (G := H₁.X) η[H₁.X] =
      q₁ :=
    (congrArg (fun a : H₁.X ⟶ H₁.X => q₁ ≫ a)
      (SchemeTheory.PointedTorsor.coordinate_regular_unit H₁.X)).trans
        (Category.comp_id q₁)
  have ht₁ : geometricTorsorMapHasModulus c₁ D₁ H₁ H₁.X q₁ :=
    (geometricTorsorMapHasModulus_iff_coordinate c₁ D₁ H₁ H₁.X q₁ η[H₁.X]).mpr
      (Eq.mpr (congrArg (geometricRegularMapHasModulus c₁ D₁ H₁) hcoord₁) hmod)
  obtain ⟨fg, hfg, _⟩ := existsUnique_picardOneMapFromGeometricModulus_unpointed
    c₁ D₁ H₁ H₁.X q₁ ht₁
  let φ : groupScheme c₂ D₂ ⟶ H₂ := eJ.inv ≫ fg.1 ≫ eH.hom
  let f : picardOne c₂ D₂ ⟶ H₂.X := eP.inv ≫ fg.2 ≫ eH.hom.hom.hom.hom
  have hf : ∀ (T : Over (Spec (.of K)))
      (a : T ⟶ (groupScheme c₂ D₂).X) (x : T ⟶ picardOne c₂ D₂),
      (a • x) ≫ f = (a ≫ φ.hom.hom.hom) * (x ≫ f) :=
    equivariant_factor_transport_inverse eJ eP eH he fg.1 fg.2 hfg.2
  have hfac : abelOneMap c₂ D₂ ≫ f = q₂ :=
    factorization_transport_inverse eU eP (abelOneMap c₁ D₁)
      (abelOneMap c₂ D₂) q₁ q₂ eH.hom.hom.hom.hom fg.2 ha hq hfg.1
  let _ : ModObj H₂.X H₂.X := ModObj.regular H₂.X
  have : IsIso (ModObj.leftSMul H₂.X H₂.X) :=
    SchemeTheory.PointedTorsor.isIso_leftSMul_regular H₂.X
  have ht₂ : geometricTorsorMapHasModulus c₂ D₂ H₂ H₂.X q₂ :=
    Eq.mp (congrArg (geometricTorsorMapHasModulus c₂ D₂ H₂ H₂.X) hfac)
      (geometricTorsorMapHasModulus_comp c₂ D₂ (groupScheme c₂ D₂) H₂
        (picardOne c₂ D₂) H₂.X (abelOneMap c₂ D₂)
        (geometricTorsorMapHasModulus_abelOne c₂ D₂) φ f hf)
  have hgroup := (geometricTorsorMapHasModulus_iff_coordinate c₂ D₂ H₂ H₂.X
    q₂ η[H₂.X]).mp ht₂
  have hcoord₂ : q₂ ≫ SchemeTheory.PointedTorsor.coordinate (G := H₂.X) η[H₂.X] = q₂ :=
    (congrArg (fun a : H₂.X ⟶ H₂.X => q₂ ≫ a)
      (SchemeTheory.PointedTorsor.coordinate_regular_unit H₂.X)).trans
        (Category.comp_id q₂)
  exact Eq.mp (congrArg (geometricRegularMapHasModulus c₂ D₂ H₂) hcoord₂) hgroup



private theorem geometricModulus_iterated_native_transport
    {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
    (H : CommGrp (Over (Spec (.of K)))) [IsSeparated H.X.hom]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let qL := modulusGroupMapScalarExtension c D L H q
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let HM := (GroupSchemes.baseChange (specMap K M)).obj H
    let HLM := (GroupSchemes.baseChange (specMap L M)).obj HL
    let qM : Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM) ⟶ HM.X :=
      modulusGroupMapScalarExtension c D M H q
    let qLM : Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM) ⟶ HLM.X :=
      modulusGroupMapScalarExtension cL DL M HL qL
    ∀ (eJ : groupScheme cLM DLM ≅ groupScheme cM DM)
      (eP : picardOne cLM DLM ≅ picardOne cM DM)
      (eU : Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM) ≅
        Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM))
      (eH : HLM ≅ HM),
      (∀ (T : Over (Spec (.of M)))
        (a : T ⟶ (groupScheme cLM DLM).X) (x : T ⟶ picardOne cLM DLM),
        (a • x) ≫ eP.hom = (a ≫ eJ.hom.hom.hom.hom) • (x ≫ eP.hom)) →
      (eU.hom ≫ abelOneMap cM DM = abelOneMap cLM DLM ≫ eP.hom) →
      (eU.hom ≫ qM = qLM ≫ eH.hom.hom.hom.hom) →
      geometricRegularMapHasModulus cLM DLM HLM qLM →
      geometricRegularMapHasModulus cM DM HM qM := by
  intro cL DL HL qL cM DM cLM DLM HM HLM qM qLM eJ eP eU eH he ha hq hLM
  have : IsSeparated HL.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K L))
    infer_instance
  have : IsSeparated HM.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K M))
    infer_instance
  have : IsSeparated HLM.X.hom := by
    change IsSeparated (Limits.pullback.snd HL.X.hom (specMap L M))
    infer_instance
  exact geometricModulus_transport_inverse cLM cM DLM DM HLM HM qLM qM
    eJ eP eU eH he ha hq hLM

private theorem geometricModulus_of_iterated_factor_of_iso
    {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
    (H : CommGrp (Over (Spec (.of K)))) [IsSeparated H.X.hom]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X)
    (e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M)) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let qL := modulusGroupMapScalarExtension c D L H q
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let HM := (GroupSchemes.baseChange (specMap K M)).obj H
    let HLM := (GroupSchemes.baseChange (specMap L M)).obj HL
    let qM : Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM) ⟶ HM.X :=
      modulusGroupMapScalarExtension c D M H q
    let _qLM : Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM) ⟶ HLM.X :=
      modulusGroupMapScalarExtension cL DL M HL qL
    geometricRegularMapHasModulus cL DL HL qL →
      geometricRegularMapHasModulus cM DM HM qM := by
  intro cL DL HL qL cM DM cLM DLM HM HLM qM qLM hL
  have : IsSeparated HL.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K L))
    infer_instance
  have hLM : geometricRegularMapHasModulus cLM DLM HLM qLM :=
    geometricRegularMapHasModulus_scalarExtension_unpointed cL DL HL qL hL M
  obtain ⟨eJ, eP, eU, he, ha, hq⟩ :=
    exists_scalarExtensionTowerComparisons c D L M H.X q e
  obtain ⟨eH, hqH⟩ := GroupSchemes.exists_baseChangeTowerIso_square
    (specMap K L) (specMap L M) (specMap K M) e H
    (U₁ := Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM))
    (U₂ := Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM))
    eU.hom
    (modulusMapScalarExtension cL DL M ((Over.pullback (specMap K L)).obj H.X)
      (modulusMapScalarExtension c D L H.X q))
    (modulusMapScalarExtension c D M H.X q) hq
  have hqM : qM = modulusMapScalarExtension c D M H.X q := rfl
  have hqLM : qLM =
      modulusMapScalarExtension cL DL M ((Over.pullback (specMap K L)).obj H.X)
        (modulusMapScalarExtension c D L H.X q) := rfl
  have hqNative : eU.hom ≫ qM = qLM ≫ eH.hom.hom.hom.hom :=
    (congrArg
      (fun m : Over.mk ((modulusComplement (modulusCurveMap (c := cM) DM)).ι ≫ cM) ⟶
          HM.X => eU.hom ≫ m) hqM).trans
      (hqH.trans (congrArg
        (fun m : Over.mk ((modulusComplement (modulusCurveMap (c := cLM) DLM)).ι ≫ cLM) ⟶
            HLM.X => m ≫ eH.hom.hom.hom.hom) hqLM.symm))
  exact geometricModulus_iterated_native_transport (L := L) (M := M) c D H q
    eJ eP eU eH he ha hqNative hLM

private theorem geometricModulus_of_iterated_factor
    {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
    (H : CommGrp (Over (Spec (.of K)))) [IsSeparated H.X.hom]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X) :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let qL := modulusGroupMapScalarExtension c D L H q
    geometricRegularMapHasModulus cL DL HL qL →
    geometricRegularMapHasModulus (baseChange K c M)
      (D.changeBaseOfIdentity (specMap K M))
      ((GroupSchemes.baseChange (specMap K M)).obj H)
      (modulusGroupMapScalarExtension c D M H q) := by
  intro cL DL HL qL hL
  let w : specMap L M ≫ specMap K L = specMap K M := specMap_scalarTower_comp K L M
  let e : Over.pullback (specMap K M) ≅
      Over.pullback (specMap K L) ⋙ Over.pullback (specMap L M) :=
    (eqToIso (congrArg (fun a : Spec (.of M) ⟶ Spec (.of K) => Over.pullback a) w)).symm ≪≫
      Over.pullbackComp (specMap L M) (specMap K L)
  exact geometricModulus_of_iterated_factor_of_iso c D H q e hL

/-- A fixed ground divisor has its full geometric condition as soon as
the actual scalar-extended map has its principal-divisor condition over
one algebraic closure. The proof constructs the embedding into every
closed extension and transports an actual equivariant Abel factor. -/
theorem geometricRegularMapHasModulus_of_algebraicClosure
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X) :
    let L := AlgebraicClosure K
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let G_L := (GroupSchemes.baseChange (specMap K L)).obj G
    let _ : Algebra L (Limits.pullback c (specMap K L)).functionField :=
      (AlgebraicCurve.baseToFunctionField cL).toAlgebra
    let ML := AlgebraicCurve.CurveModel.ofSmoothProperCurve cL
    let qL := modulusGroupMapScalarExtension c D L G q
    ML.regularMapHasModulus DL G_L ⟨qL.left, Over.w qL⟩ →
      geometricRegularMapHasModulus c D G q := by
  intro L cL DL G_L algL ML qL hL
  have : IsSeparated G_L.X.hom := by
    change IsSeparated (Limits.pullback.snd G.X.hom (specMap K L))
    infer_instance
  have : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cL
    infer_instance
  have hgeoL := ML.regularMapHasModulus_geometric DL G_L ⟨qL.left, Over.w qL⟩ hL
  intro M fieldM algKM closedM cM DM algM MM qM
  let j : L →ₐ[K] M := IsAlgClosed.lift
  let algLM : Algebra L M := j.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  have hgeoM := geometricModulus_of_iterated_factor (K := K) (L := L) (M := M)
    c D G q hgeoL
  have : GeometricallyIntegral MM.toBase := by
    change GeometricallyIntegral cM
    infer_instance
  have : IsSeparated ((GroupSchemes.baseChange (specMap K M)).obj G).X.hom := by
    change IsSeparated (Limits.pullback.snd G.X.hom (specMap K M))
    infer_instance
  exact (MM.geometricRegularMapHasModulus_iff DM
    ((GroupSchemes.baseChange (specMap K M)).obj G) ⟨qM.left, Over.w qM⟩).mp hgeoM

end AlgebraicGeometry.GeneralizedJacobian
