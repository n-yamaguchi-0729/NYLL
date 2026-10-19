/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.GeometricModulusRegularMap
import Nyll.JacobianVarieties.Generalized.GeometricModulusMapCondition
import Nyll.JacobianVarieties.Generalized.PicardOneAbelEquivariantUniqueness
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates
import Nyll.SchemeTheory.CategoryTheory.EquivariantScalarTowerComparison
import Nyll.SchemeTheory.Morphisms.SeparatedQuasiCompactDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Nyll.JacobianVarieties.Generalized.ModulusTorsorRegularMap
import Nyll.JacobianVarieties.Generalized.GeometricModulusScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusComplementFiniteExtension
import Nyll.JacobianVarieties.Generalized.PicardOneScalarExtensionTorsor
import Nyll.JacobianVarieties.Generalized.ScalarExtensionGroupScheme
import Nyll.SchemeTheory.Morphisms.OverPullbackDescent
import Nyll.JacobianVarieties.Generalized.PicardOneUnpointedConstruction
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Monoidal.CommGrp_

/-! # Positive geometric modulus and regular torsor factorization

Over any field, an actual point outside a positive modulus gives a unique
regular equivariant factor through the intrinsic Picard-one torsor. The
geometric principal-divisor condition supplies the group factor; no group
or torsor factor is part of the hypotheses. Existence of a complement point
and descent without one are separate tasks.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

/-- Faithful monoidal transport reflects the unit and multiplication laws of
an underlying map once its transported map is a group homomorphism. -/
private theorem isMonHom_of_mapCommGrp
    {A B : Type u}
    [Category A] [CartesianMonoidalCategory A] [BraidedCategory A]
    [Category B] [CartesianMonoidalCategory B] [BraidedCategory B]
    (F : A ⥤ B) [F.Braided] [F.Faithful]
    (G H : CommGrp A) (g : G.X ⟶ H.X)
    (m : F.mapCommGrp.obj G ⟶ F.mapCommGrp.obj H)
    (hg : F.map g = m.hom.hom.hom) : IsMonHom g := by
  constructor
  · apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
    have h : (Functor.LaxMonoidal.ε F ≫ F.map η[G.X]) ≫ m.hom.hom.hom =
        Functor.LaxMonoidal.ε F ≫ F.map η[H.X] :=
      IsMonHom.one_hom m.hom.hom.hom
    rw [← hg] at h
    exact (congrArg (fun t => Functor.LaxMonoidal.ε F ≫ t)
      (F.map_comp η[G.X] g)).trans
        ((Category.assoc (Functor.LaxMonoidal.ε F) (F.map η[G.X]) (F.map g)).symm.trans h)
  · apply F.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ F G.X G.X)).mp
    have h : (Functor.LaxMonoidal.μ F G.X G.X ≫ F.map μ[G.X]) ≫ m.hom.hom.hom =
        (m.hom.hom.hom ⊗ₘ m.hom.hom.hom) ≫
          Functor.LaxMonoidal.μ F H.X H.X ≫ F.map μ[H.X] :=
      IsMonHom.mul_hom m.hom.hom.hom
    rw [← hg] at h
    exact (congrArg (fun t => Functor.LaxMonoidal.μ F G.X G.X ≫ t)
      (F.map_comp μ[G.X] g)).trans
        ((Category.assoc (Functor.LaxMonoidal.μ F G.X G.X)
          (F.map μ[G.X]) (F.map g)).symm.trans
          (h.trans ((Functor.LaxMonoidal.μ_natural_assoc F g g (F.map μ[H.X])).trans
            (congrArg (fun t => Functor.LaxMonoidal.μ F G.X G.X ≫ t)
              (F.map_comp (g ⊗ₘ g) μ[H.X]).symm))))

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
  (Q : Over (Spec (CommRingCat.of K))) [ModObj H.X Q]
  [IsIso (ModObj.leftSMul H.X Q)]
  (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q)

include H q in
/-- A curve map supplies a geometric point of the target torsor. Its actual
torsor coordinates identify that scalar-extended target with the separated
group, so fpqc descent proves separatedness over the original field. This
needs neither a rational ground-field point nor a modulus assumption. -/
theorem isSeparated_target_of_modulusMap : IsSeparated Q.hom := by
  let L := AlgebraicClosure K
  let s := specMap K L
  let F := Over.pullback s
  let HL := (GroupSchemes.baseChange s).obj H
  let _ : ModObj HL.X (F.obj Q) := F.modObjObj H.X Q
  have : IsIso (ModObj.leftSMul HL.X (F.obj Q)) := F.isIso_leftSMul_modObjObj H.X Q
  have : IsSeparated HL.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom s)
    infer_instance
  obtain ⟨εL⟩ := modulusComplement_point (baseChange K c L) (D.changeBaseOfIdentity s)
  let p : 𝟙_ (Over (Spec (CommRingCat.of L))) ⟶ F.obj Q :=
    εL ≫ modulusMapScalarExtension c D L Q q
  let e : F.obj Q ≅ HL.X := SchemeTheory.PointedTorsor.trivialization (G := HL.X) p
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hsep : IsSeparated (F.obj Q).hom := by
    have h : IsSeparated (e.hom.left ≫ HL.X.hom) := inferInstance
    simpa only [Over.w e.hom] using h
  have : Flat s :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective s :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2
  have : MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := IsSeparated.descendsAlong_fpqc
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsSeparated) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (IsPullback.of_hasPullback Q.hom s).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsep

include ε in
/-- Positive full geometric modulus constructs both the group morphism and
the regular equivariant torsor morphism over the original field. -/
theorem existsUnique_picardOneMapFromGeometricModulus (hd : 0 < d)
    (hmod : geometricTorsorMapHasModulus c D H Q q) :
    ∃! fg : (groupScheme c D ⟶ H) × (picardOne c D ⟶ Q),
      abelOneMap c D ≫ fg.2 = q ∧
        ∀ (T : Over (Spec (CommRingCat.of K)))
          (a : T ⟶ (groupScheme c D).X) (x : T ⟶ picardOne c D),
          (a • x) ≫ fg.2 = (a ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  have hcoord := (geometricTorsorMapHasModulus_iff_coordinate c D H Q q (ε ≫ q)).mp hmod
  let qOver := q ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) (ε ≫ q)
  let q₀ : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ c) H.X.hom :=
    ⟨qOver.left, Over.w qOver⟩
  let ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap D)).ι ≫ c) := ⟨ε.left, Over.w ε⟩
  have hε : ε ≫ qOver = 1 := by
    change ε ≫ (q ≫ SchemeTheory.PointedTorsor.coordinate (G := H.X) (ε ≫ q)) = 1
    rw [← Category.assoc]
    simpa only [toUnit_unit, Category.id_comp] using
      SchemeTheory.PointedTorsor.coordinate_basepoint (G := H.X) (ε ≫ q)
        (𝟙_ (Over (Spec (CommRingCat.of K))))
  let φ := geometricGroupHomFromModulus c D ε₀ H q₀ hcoord hd
  have hφ : modulusAbelMap c D ε ≫ φ.hom.hom.hom = qOver := by
    have h := geometricGroupHomFromModulus_abel_translation_over c D H ε qOver hcoord hd
    change modulusAbelMap c D ε ≫ φ.hom.hom.hom =
      qOver / ((Over.homMk _ (Category.comp_id _) :
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
          Over.mk (𝟙 (Spec (CommRingCat.of K)))) ≫ ε ≫ qOver) at h
    rw [hε, MonObj.comp_one, div_one] at h
    exact h
  exact picardOneEquivariantMap_factors_uniquely c D ε q φ hφ


/-- The geometric full modulus supplies an actual equivariant Abel factor
over every algebraically closed extension, in every modulus degree. The
complement point and target coordinates are constructed internally. -/
theorem existsUnique_picardOneMap_geometricExtension
    (hmod : geometricTorsorMapHasModulus c D H Q q)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L] :
    let F := Over.pullback (specMap K L)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let _ : ModObj HL.X (F.obj Q) := F.modObjObj H.X Q
    let _ : IsIso (ModObj.leftSMul HL.X (F.obj Q)) := F.isIso_leftSMul_modObjObj H.X Q
    ∃! fg : (groupScheme cL DL ⟶ HL) × (picardOne cL DL ⟶ F.obj Q),
      abelOneMap cL DL ≫ fg.2 = modulusMapScalarExtension c D L Q q ∧
        ∀ (T : Over (Spec (CommRingCat.of L)))
          (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
          (a • x) ≫ fg.2 = (a ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  intro F cL DL HL actionL torsorL
  have : IsSeparated HL.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K L))
    infer_instance
  let _ : Algebra L (Limits.pullback c (specMap K L)).functionField :=
    (AlgebraicCurve.baseToFunctionField cL).toAlgebra
  let ML := AlgebraicCurve.CurveModel.ofSmoothProperCurve cL
  have : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cL
    infer_instance
  let qL := modulusMapScalarExtension c D L Q q
  obtain ⟨εL⟩ := modulusComplement_point cL DL
  exact ML.existsUnique_picardOneMapFromModulus DL εL HL (F.obj Q) qL (hmod L (εL ≫ qL))

omit [IsSeparated H.X.hom] [IsIso (ModObj.leftSMul H.X Q)] in
/-- The actual scalar-extension comparisons transport equivariance through
an arbitrary pullback tower. All composite maps retain their defining comparisons. -/
private theorem picardOne_tower_factor_equivariant
    (L : Type u) [Field L] [Algebra K L]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M] :
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let HM := (GroupSchemes.baseChange (specMap K M)).obj H
    let HLM := (GroupSchemes.baseChange (specMap L M)).obj HL
    let _ : ModObj HL.X (FKL.obj Q) := FKL.modObjObj H.X Q
    let _ : ModObj HM.X (FKM.obj Q) := FKM.modObjObj H.X Q
    let _ : ModObj HLM.X (FLM.obj (FKL.obj Q)) :=
      FLM.modObjObj HL.X (FKL.obj Q)
    ∀ (e : FKM ≅ FKL ⋙ FLM)
      (φM : groupScheme cM DM ⟶ HM) (fM : picardOne cM DM ⟶ FKM.obj Q),
      (∀ (T : Over (Spec (CommRingCat.of M)))
        (g : T ⟶ (groupScheme cM DM).X) (x : T ⟶ picardOne cM DM),
          (g • x) ≫ fM = (g ≫ φM.hom.hom.hom) • (x ≫ fM)) →
      let eB := Functor.mapCommGrpNatIso e ≪≫ Functor.mapCommGrpCompIso
      let eG : groupScheme cLM DLM ≅ groupScheme cM DM :=
        (groupActualScalarExtensionIso cL DL M).symm ≪≫
        FLM.mapCommGrp.mapIso (groupActualScalarExtensionIso c D L).symm ≪≫
          (eB.app (groupScheme c D)).symm ≪≫ groupActualScalarExtensionIso c D M
      let eP : picardOne cLM DLM ≅ picardOne cM DM :=
        (picardOneScalarExtensionIso cL DL M).symm ≪≫
        FLM.mapIso (picardOneScalarExtensionIso c D L).symm ≪≫
          (e.app (picardOne c D)).symm ≪≫ picardOneScalarExtensionIso c D M
      let t : HM ⟶ HLM := (eB.app H).hom
      let p : FKM.obj Q ⟶ FLM.obj (FKL.obj Q) := e.hom.app Q
      let ψ : groupScheme cLM DLM ⟶ HLM := eG.hom ≫ φM ≫ t
      let f : picardOne cLM DLM ⟶ FLM.obj (FKL.obj Q) :=
        eP.hom ≫ fM ≫ p
      ∀ (T : Over (Spec (CommRingCat.of M)))
        (g : T ⟶ (groupScheme cLM DLM).X) (x : T ⟶ picardOne cLM DLM),
        (g • x) ≫ f = (g ≫ ψ.hom.hom.hom) • (x ≫ f) := by
  intro FKL FLM FKM cL DL cLM DLM cM DM HL HM HLM
    actionL actionM actionLM e φM fM hfM eB eG eP t p ψ f
  have heB : t.hom.hom.hom = e.hom.app H.X := by
    change e.hom.app H.X ≫ 𝟙 _ = e.hom.app H.X
    exact Category.comp_id _
  have ht : ∀ (T : Over (Spec (CommRingCat.of M)))
      (g : T ⟶ HM.X) (x : T ⟶ FKM.obj Q),
      (g • x) ≫ p = (g ≫ t.hom.hom.hom) • (x ≫ p) := by
    intro T g x
    rw [heB]
    exact FKM.natTrans_comp_modObj_smul H.X Q FKL FLM e.hom g x
  exact equivariant_commGrp_tower_comp_apply FKM FKL FLM e
    (groupScheme c D) (picardOne c D) (groupScheme cL DL) (picardOne cL DL)
    (groupScheme cLM DLM) (groupScheme cM DM) HM HLM
    (picardOne cLM DLM) (picardOne cM DM) (FKM.obj Q) (FLM.obj (FKL.obj Q))
    (groupActualScalarExtensionIso c D L).symm (picardOneScalarExtensionIso c D L).symm
    (groupActualScalarExtensionIso cL DL M).symm (picardOneScalarExtensionIso cL DL M).symm
    (groupActualScalarExtensionIso c D M) (picardOneScalarExtensionIso c D M)
    φM t fM p hfM ht
    (fun _ g x => picardOneScalarExtensionIso_inv_smul c D L g x)
    (fun _ g x => picardOneScalarExtensionIso_inv_smul cL DL M g x)
    (fun _ g x => picardOneScalarExtensionIso_smul c D M g x)


omit [IsSeparated H.X.hom] in
/-- Compose an equivariant map and its factorization identity while the source
and target torsors are abstract. -/
private theorem geometricTorsorMapHasModulus_of_equivariant_factor
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (P : Over (Spec (CommRingCat.of K))) [ModObj G.X P]
    [IsIso (ModObj.leftSMul G.X P)]
    (r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ P)
    (hr : geometricTorsorMapHasModulus c D G P r)
    (φ : G ⟶ H) (f : P ⟶ Q)
    (hf : ∀ (T : Over (Spec (CommRingCat.of K))) (g : T ⟶ G.X) (x : T ⟶ P),
      (g • x) ≫ f = (g ≫ φ.hom.hom.hom) • (x ≫ f))
    (hfac : r ≫ f = q) : geometricTorsorMapHasModulus c D H Q q :=
  Eq.mp (congrArg (geometricTorsorMapHasModulus c D H Q) hfac)
    (geometricTorsorMapHasModulus_comp c D G H P Q r hr φ f hf)

omit [IsSeparated H.X.hom] in
/-- An actual equivariant Abel factor transports the full torsor modulus
through any pullback comparison of a field tower. The factor and comparison
are retained while the group, action, and Abel squares are composed. -/
private theorem geometricTorsorMapHasModulus_tower_factor
    (L : Type u) [Field L] [Algebra K L]
    (M : Type u) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    let FKL := Over.pullback (specMap K L)
    let FLM := Over.pullback (specMap L M)
    let FKM := Over.pullback (specMap K M)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let cLM := baseChange L cL M
    let DLM := DL.changeBaseOfIdentity (f := cL) (specMap L M)
    let cM := baseChange K c M
    let DM := D.changeBaseOfIdentity (specMap K M)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let HM := (GroupSchemes.baseChange (specMap K M)).obj H
    let HLM := (GroupSchemes.baseChange (specMap L M)).obj HL
    let _ : ModObj HL.X (FKL.obj Q) := FKL.modObjObj H.X Q
    let _ : IsIso (ModObj.leftSMul HL.X (FKL.obj Q)) :=
      FKL.isIso_leftSMul_modObjObj H.X Q
    let _ : ModObj HM.X (FKM.obj Q) := FKM.modObjObj H.X Q
    let _ : ModObj HLM.X (FLM.obj (FKL.obj Q)) :=
      FLM.modObjObj HL.X (FKL.obj Q)
    let _ : IsIso (ModObj.leftSMul HLM.X (FLM.obj (FKL.obj Q))) :=
      FLM.isIso_leftSMul_modObjObj HL.X (FKL.obj Q)
    let qLM := modulusMapScalarExtension cL DL M (FKL.obj Q)
      (modulusMapScalarExtension c D L Q q)
    ∀ (_ : FKM ≅ FKL ⋙ FLM)
      (φM : groupScheme cM DM ⟶ HM) (fM : picardOne cM DM ⟶ FKM.obj Q),
      abelOneMap cM DM ≫ fM = modulusMapScalarExtension c D M Q q →
      (∀ (T : Over (Spec (CommRingCat.of M)))
        (g : T ⟶ (groupScheme cM DM).X) (x : T ⟶ picardOne cM DM),
          (g • x) ≫ fM = (g ≫ φM.hom.hom.hom) • (x ≫ fM)) →
      geometricTorsorMapHasModulus cLM DLM HLM (FLM.obj (FKL.obj Q)) qLM := by
  intro FKL FLM FKM cL DL cLM DLM cM DM HL HM HLM
    actionL torsorL actionM actionLM torsorLM qLM e φM fM hAbelM hfM
  exact geometricTorsorMapHasModulus_of_equivariant_factor
    cLM DLM HLM (FLM.obj (FKL.obj Q)) qLM
    (groupScheme cLM DLM) (picardOne cLM DLM) (abelOneMap cLM DLM)
    (geometricTorsorMapHasModulus_abelOne cLM DLM) _ _
    (picardOne_tower_factor_equivariant c D H Q L M e φM fM hfM)
    (abelOneMap_scalarExtension_tower_factorization c D L M Q q e fM hAbelM)


/-- The intrinsic geometric torsor modulus survives every field extension,
including empty modulus and curves without a rational point. Over a closed
extension, the already constructed closed-field factor is transported through
the actual group, Picard-one, complement, and pullback tower comparisons. -/
theorem geometricTorsorMapHasModulus_scalarExtension
    (hmod : geometricTorsorMapHasModulus c D H Q q)
    (L : Type u) [Field L] [Algebra K L] :
    let FKL := Over.pullback (specMap K L)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let _ : ModObj HL.X (FKL.obj Q) := FKL.modObjObj H.X Q
    let _ : IsIso (ModObj.leftSMul HL.X (FKL.obj Q)) :=
      FKL.isIso_leftSMul_modObjObj H.X Q
    let qL := modulusMapScalarExtension c D L Q q
    geometricTorsorMapHasModulus cL DL HL (FKL.obj Q) qL := by
  intro FKL cL DL HL actionL torsorL qL
    M fieldM algebraLM closedM FLM cLM DLM HLM actionLM torsorLM algLM ML qLM p
  have : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cLM
    infer_instance
  let _ : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let FKM := Over.pullback (specMap K M)
  have : IsSeparated HL.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K L))
    infer_instance
  have : IsSeparated HLM.X.hom := by
    change IsSeparated (Limits.pullback.snd HL.X.hom (specMap L M))
    infer_instance
  obtain ⟨fg, hfg, _⟩ :=
    existsUnique_picardOneMap_geometricExtension c D H Q q hmod M
  let w : specMap L M ≫ specMap K L = specMap K M := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq K L M]
  let e : FKM ≅ FKL ⋙ FLM :=
    (eqToIso (congrArg
      (fun a : Spec (CommRingCat.of M) ⟶ Spec (CommRingCat.of K) => Over.pullback a) w)).symm ≪≫
        Over.pullbackComp (specMap L M) (specMap K L)
  have htransport :
      geometricTorsorMapHasModulus cLM DLM HLM (FLM.obj (FKL.obj Q)) qLM :=
    geometricTorsorMapHasModulus_tower_factor c D H Q q L M e
      fg.1 fg.2 hfg.1 hfg.2
  let q₀ : SchemeHomOver
      ((modulusComplement (modulusCurveMap (c := ML.toBase) DLM)).ι ≫ ML.toBase)
      HLM.X.hom :=
    (commGroupPointEquiv HLM
      ((modulusComplement (modulusCurveMap (c := ML.toBase) DLM)).ι ≫ ML.toBase)).symm
      (qLM ≫ SchemeTheory.PointedTorsor.coordinate (G := HLM.X) p)
  have hcoord :
      geometricRegularMapHasModulus ML.toBase DLM HLM (Over.homMk q₀.1 q₀.2) :=
    (geometricTorsorMapHasModulus_iff_coordinate ML.toBase DLM HLM
      (FLM.obj (FKL.obj Q)) qLM p).mp htransport
  exact (ML.geometricRegularMapHasModulus_iff DLM HLM q₀).mp hcoord


/-- The full geometric group modulus is preserved by every field extension,
in all degrees and without a rational point on the source curve. The regular
group torsor reduces this to the intrinsic torsor result, using its identity
coordinate rather than introducing a second action on the extended group. -/
theorem geometricRegularMapHasModulus_scalarExtension_unpointed
    (r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X)
    (hmod : geometricRegularMapHasModulus c D H r)
    (L : Type u) [Field L] [Algebra K L] :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    geometricRegularMapHasModulus cL DL HL (modulusGroupMapScalarExtension c D L H r) := by
  intro cL DL HL
  let _ : ModObj H.X H.X := ModObj.regular H.X
  have : IsIso (ModObj.leftSMul H.X H.X) :=
    SchemeTheory.PointedTorsor.isIso_leftSMul_regular H.X
  have hunit : SchemeTheory.PointedTorsor.coordinate (G := H.X) η[H.X] = 𝟙 H.X :=
    SchemeTheory.PointedTorsor.coordinate_regular_unit H.X
  have ht : geometricTorsorMapHasModulus c D H H.X r := by
    apply (geometricTorsorMapHasModulus_iff_coordinate c D H H.X r η[H.X]).mpr
    simpa only [hunit, Category.comp_id] using hmod
  let F := Over.pullback (specMap K L)
  let _ : ModObj HL.X (F.obj H.X) := F.modObjObj H.X H.X
  have : IsIso (ModObj.leftSMul HL.X (F.obj H.X)) := F.isIso_leftSMul_modObjObj H.X H.X
  let rL := modulusMapScalarExtension c D L H.X r
  have htL : geometricTorsorMapHasModulus cL DL HL (F.obj H.X) rL :=
    geometricTorsorMapHasModulus_scalarExtension c D H H.X r ht L
  let pL := Functor.LaxMonoidal.ε F ≫ F.map η[H.X]
  have hunitL : SchemeTheory.PointedTorsor.coordinate (G := HL.X) pL = 𝟙 (F.obj H.X) := by
    have h := F.map_torsor_coordinate H.X H.X η[H.X]
    rw [hunit, F.map_id] at h
    exact h.symm
  have hL := (geometricTorsorMapHasModulus_iff_coordinate cL DL HL (F.obj H.X) rL pL).mp htL
  have hr : rL ≫ SchemeTheory.PointedTorsor.coordinate (G := HL.X) pL =
      modulusGroupMapScalarExtension c D L H r :=
    (congrArg (fun f : F.obj H.X ⟶ F.obj H.X => rL ≫ f) hunitL).trans
      (Category.comp_id rL)
  exact Eq.mp (congrArg (geometricRegularMapHasModulus cL DL HL) hr) hL


/-- For positive modulus, an actual finite separable intermediate field
supports the unique equivariant Abel factor. Both the extension and the
complement point are constructed; neither a rational point over the ground
field nor a factorization is included in the hypotheses. -/
theorem exists_finiteSeparableExtension_picardOneMap
    (hd : 0 < d) (hmod : geometricTorsorMapHasModulus c D H Q q)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    ∃ E : IntermediateField K Ω, Module.Finite K E ∧ Algebra.IsSeparable K E ∧
      let cE := baseChange K c E
      let DE := D.changeBaseOfIdentity (specMap K E)
      let F := Over.pullback (specMap K E)
      let HE := (GroupSchemes.baseChange (specMap K E)).obj H
      let _ : ModObj HE.X (F.obj Q) := F.modObjObj H.X Q
      let _ : IsIso (ModObj.leftSMul HE.X (F.obj Q)) := F.isIso_leftSMul_modObjObj H.X Q
      ∃! fg : (groupScheme cE DE ⟶ HE) × (picardOne cE DE ⟶ F.obj Q),
        abelOneMap cE DE ≫ fg.2 = modulusMapScalarExtension c D E Q q ∧
          ∀ (T : Over (Spec (CommRingCat.of E)))
            (g : T ⟶ (groupScheme cE DE).X) (x : T ⟶ picardOne cE DE),
            (g • x) ≫ fg.2 = (g ≫ fg.1.hom.hom.hom) • (x ≫ fg.2) := by
  obtain ⟨E, hE, hsep, ⟨εE⟩⟩ := modulusComplement_finiteSeparableExtension_point c D Ω
  refine ⟨E, hE, hsep, ?_⟩
  intro cE DE F HE targetAction targetTorsor
  have : IsSeparated HE.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K E))
    infer_instance
  exact existsUnique_picardOneMapFromGeometricModulus cE DE εE HE (F.obj Q)
    (modulusMapScalarExtension c D E Q q) hd
    (geometricTorsorMapHasModulus_scalarExtension c D H Q q hmod E)


/-- An equivariant Abel factor over a finite separable extension descends
as an actual torsor-scheme morphism. The kernel-pair equality is proved on
geometric points using the factor supplied there by the full modulus
condition; it is not included among the hypotheses. -/
theorem existsUnique_picardOneMap_descends_finiteSeparable
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] (hmod : geometricTorsorMapHasModulus c D H Q q) :
    let F := Over.pullback (specMap K L)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let _ : ModObj HL.X (F.obj Q) := F.modObjObj H.X Q
    ∀ (φL : groupScheme cL DL ⟶ HL) (fL : picardOne cL DL ⟶ F.obj Q),
      abelOneMap cL DL ≫ fL = modulusMapScalarExtension c D L Q q →
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
          (a • x) ≫ fL = (a ≫ φL.hom.hom.hom) • (x ≫ fL)) →
      ∃! f : picardOne c D ⟶ Q,
        F.map f = (picardOneScalarExtensionIso c D L).hom ≫ fL := by
  intro F cL DL HL actionL φL fL hAbelL hfL
  have : Smooth (picardOne c D).hom := (picardOne_geometry c D).1
  have : IsSeparated Q.hom := isSeparated_target_of_modulusMap c D H Q q
  apply existsUnique_overPullback_map_of_geometricPoints
    (K := K) (L := L) (X := picardOne c D) (Y := Q)
    ((picardOneScalarExtensionIso c D L).hom ≫ fL)
  intro Ω fieldΩ algebraΩ closedΩ x₁ x₂ hx hxy
  let FΩ := Over.pullback (specMap K Ω)
  let HΩ := (GroupSchemes.baseChange (specMap K Ω)).obj H
  let _ : ModObj HΩ.X (FΩ.obj Q) := FΩ.modObjObj H.X Q
  have : IsIso (ModObj.leftSMul HΩ.X (FΩ.obj Q)) :=
    FΩ.isIso_leftSMul_modObjObj H.X Q
  have : IsSeparated HΩ.X.hom := by
    change IsSeparated (Limits.pullback.snd H.X.hom (specMap K Ω))
    infer_instance
  obtain ⟨fg, hfg, _⟩ :=
    existsUnique_picardOneMap_geometricExtension c D H Q q hmod Ω
  let y : Spec (CommRingCat.of Ω) ⟶
      Limits.pullback (picardOne c D).hom (specMap K Ω) :=
    Limits.pullback.lift
      (x₁ ≫ Limits.pullback.fst (picardOne c D).hom (specMap K L)) (𝟙 _)
      (hx.trans (Category.id_comp (specMap K Ω)).symm)
  have hy : y ≫ Limits.pullback.snd (picardOne c D).hom (specMap K Ω) = 𝟙 _ :=
    Limits.pullback.lift_snd _ _ _
  have hxy₁ : x₁ ≫ Limits.pullback.fst (picardOne c D).hom (specMap K L) =
      y ≫ Limits.pullback.fst (picardOne c D).hom (specMap K Ω) :=
    (Limits.pullback.lift_fst _ _ _).symm
  have hxy₂ : x₂ ≫ Limits.pullback.fst (picardOne c D).hom (specMap K L) =
      y ≫ Limits.pullback.fst (picardOne c D).hom (specMap K Ω) :=
    hxy.symm.trans hxy₁
  have h₁ := abelOneMap_equivariantPair_torsor_value c D L Ω q
    φL fL fg.1 fg.2 hAbelL hfL hfg.1 hfg.2 x₁ y hy hxy₁
  have h₂ := abelOneMap_equivariantPair_torsor_value c D L Ω q
    φL fL fg.1 fg.2 hAbelL hfL hfg.1 hfg.2 x₂ y hy hxy₂
  exact h₁.trans h₂.symm


/-- The group component of a finite-separable equivariant Abel factor
descends as an actual group-scheme homomorphism. Geometric-point uniqueness
supplies descent of its underlying map; faithful pullback reflects the
unit and multiplication identities on the original group structures. -/
theorem existsUnique_groupHom_descends_finiteSeparable
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] (hmod : geometricTorsorMapHasModulus c D H Q q) :
    let F := Over.pullback (specMap K L)
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let HL := (GroupSchemes.baseChange (specMap K L)).obj H
    let _ : ModObj HL.X (F.obj Q) := F.modObjObj H.X Q
    ∀ (φL : groupScheme cL DL ⟶ HL) (fL : picardOne cL DL ⟶ F.obj Q),
      abelOneMap cL DL ≫ fL = modulusMapScalarExtension c D L Q q →
      (∀ (T : Over (Spec (CommRingCat.of L)))
        (a : T ⟶ (groupScheme cL DL).X) (x : T ⟶ picardOne cL DL),
          (a • x) ≫ fL = (a ≫ φL.hom.hom.hom) • (x ≫ fL)) →
      ∃! φ : groupScheme c D ⟶ H,
        (GroupSchemes.baseChange (specMap K L)).map φ =
          (groupActualScalarExtensionIso c D L).hom ≫ φL := by
  intro F cL DL HL actionL φL fL hAbelL hfL
  let B := GroupSchemes.baseChange (specMap K L)
  let mL : B.obj (groupScheme c D) ⟶ HL :=
    (groupActualScalarExtensionIso c D L).hom ≫ φL
  let nL : F.obj (groupScheme c D).X ⟶ F.obj H.X :=
    groupActualScalarExtensionMap c D L ≫ φL.hom.hom.hom
  have hm : mL.hom.hom.hom = nL :=
    groupActualScalarExtensionMap_comp c D L φL
  have : SmoothOfRelativeDimension (geometricGenus K c + (d - 1))
      (groupScheme c D).X.hom := (geometry c D).1
  have : Smooth (groupScheme c D).X.hom :=
    SmoothOfRelativeDimension.smooth (geometricGenus K c + (d - 1)) _
  have hraw : ∃! g : (groupScheme c D).X ⟶ H.X, F.map g = mL.hom.hom.hom := by
    apply existsUnique_overPullback_map_of_geometricPoints
      (K := K) (L := L) (X := (groupScheme c D).X) (Y := H.X) mL.hom.hom.hom
    intro Ω fieldΩ algebraΩ closedΩ x₁ x₂ hx hxy
    let FΩ := Over.pullback (specMap K Ω)
    let HΩ := (GroupSchemes.baseChange (specMap K Ω)).obj H
    let _ : ModObj HΩ.X (FΩ.obj Q) := FΩ.modObjObj H.X Q
    have : IsIso (ModObj.leftSMul HΩ.X (FΩ.obj Q)) :=
      FΩ.isIso_leftSMul_modObjObj H.X Q
    have : IsSeparated HΩ.X.hom := by
      change IsSeparated (Limits.pullback.snd H.X.hom (specMap K Ω))
      infer_instance
    obtain ⟨fg, hfg, _⟩ :=
      existsUnique_picardOneMap_geometricExtension c D H Q q hmod Ω
    let y : Spec (CommRingCat.of Ω) ⟶
        Limits.pullback (groupScheme c D).X.hom (specMap K Ω) :=
      Limits.pullback.lift
        (x₁ ≫ Limits.pullback.fst (groupScheme c D).X.hom (specMap K L)) (𝟙 _)
        (hx.trans (Category.id_comp (specMap K Ω)).symm)
    have hy : y ≫ Limits.pullback.snd (groupScheme c D).X.hom (specMap K Ω) = 𝟙 _ :=
      Limits.pullback.lift_snd _ _ _
    have hxy₁ : x₁ ≫ Limits.pullback.fst (groupScheme c D).X.hom (specMap K L) =
        y ≫ Limits.pullback.fst (groupScheme c D).X.hom (specMap K Ω) :=
      (Limits.pullback.lift_fst _ _ _).symm
    have hxy₂ : x₂ ≫ Limits.pullback.fst (groupScheme c D).X.hom (specMap K L) =
        y ≫ Limits.pullback.fst (groupScheme c D).X.hom (specMap K Ω) :=
      hxy.symm.trans hxy₁
    have h₁ := abelOneMap_equivariantPair_group_value c D L Ω q
      φL fL fg.1 fg.2 hAbelL hfL hfg.1 hfg.2 x₁ y hy hxy₁
    have h₂ := abelOneMap_equivariantPair_group_value c D L Ω q
      φL fL fg.1 fg.2 hAbelL hfL hfg.1 hfg.2 x₂ y hy hxy₂
    exact (congrArg
      (fun m : F.obj (groupScheme c D).X ⟶ F.obj H.X =>
        x₁ ≫ m.left ≫ Limits.pullback.fst H.X.hom (specMap K L)) hm).trans
      ((h₁.trans h₂.symm).trans (congrArg
        (fun m : F.obj (groupScheme c D).X ⟶ F.obj H.X =>
          x₂ ≫ m.left ≫ Limits.pullback.fst H.X.hom (specMap K L)) hm).symm)
  obtain ⟨g, hg, _⟩ := hraw
  have : Flat (specMap K L) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (specMap K L) :=
    ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap K L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (inferInstanceAs (Module.FaithfullyFlat K L)))).2
  have : IsMonHom g := isMonHom_of_mapCommGrp F (groupScheme c D) H g mL hg
  let φ : groupScheme c D ⟶ H := InducedCategory.homMk (Grp.homMk g)
  have hφ : B.map φ = mL := by
    apply CommGrp.hom_ext
    exact hg
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply CommGrp.hom_ext
  apply F.map_injective
  exact congrArg (fun t => t.hom.hom.hom) (hψ.trans hφ.symm)

end AlgebraicGeometry.GeneralizedJacobian
