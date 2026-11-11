/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.JacobianVarieties.Picard.AbelJacobi.UnpointedAbelJacobi
public import Nyll.JacobianVarieties.Albanese.AbelJacobiFiniteSums
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Pic0EquivPointsPicardRepresentability
public import Nyll.AlgebraicCurves.Models.Construction.LiteralArithmeticCurveModel
public import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.GenusEqZeroPrincipalSingleSubSingle
public import Nyll.AlgebraicCurves.Differentials.Regular.MemSpanImagePolarDifferentials
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveSeparatingTranscendental
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Positive-genus separation by the actual Abel–Jacobi map

A principal difference of two distinct geometric points forces genus zero.
The proved Picard comparison applies this to the actual unpointed Jacobian
and its constructed Abel–Jacobi map, in every characteristic.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard

namespace AlgebraicCurve

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

/-- Distinct geometric points cannot differ by a principal divisor in positive genus. -/
theorem eq_of_single_sub_single_principal_of_genus_pos
    (hg : 0 < genusFF K F) (p q : Place K F)
    (h : Divisor.IsPrincipal (Finsupp.single p 1 - Finsupp.single q 1)) : p = q := by
  have : HasCanonicalDivisor (K := K) (F := F) := hasCanonicalDivisor_of_isCurveOver
  have : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨t, ht, hfin, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have hRR : FunctionFieldRiemannRoch K F :=
    functionFieldRiemannRoch_of_isAlgClosed_of_transcendental ht hfin
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have hSG : StichtenothGenusExists K F := stichtenothGenusExists_of_isCurveOver hC
  have hWDA : WeilDualityAdelic K F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hRR hSG
  have hgenus : genus K F = genusFF K F :=
    genus_eq_genusFF hRR hWDA hC
  by_contra hpq
  have hzero := genus_eq_zero_of_isPrincipal_single_sub_single hRR hC hpq
    (IsCurveOver.deg_eq_one_of_isAlgClosed q) h
  exact (Nat.ne_of_gt hg) (hgenus.symm.trans hzero)

/-- Subtracting one basepoint gives an injection from actual geometric curve
points into Pic⁰ when the genus is positive. -/
theorem CurveModel.pointDifference_class_injective_of_genus_pos
    (M : CurveModel K F) (hg : 0 < genusFF K F)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    Function.Injective (fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase =>
      Pic0.mk (M.pointDifference s x)) := by
  intro x y hxy
  have hclass : Pic0.mk (M.pointDifference s x - M.pointDifference s y) = 0 := by
    change Pic0.mk (M.pointDifference s x) - Pic0.mk (M.pointDifference s y) = 0
    exact sub_eq_zero.mpr hxy
  have hp := (Pic0.mk_eq_zero_iff _).mp hclass
  change Divisor.IsPrincipal
    ((Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1) -
      (Finsupp.single (M.pointEquivPlace y) 1 - Finsupp.single (M.pointEquivPlace s) 1)) at hp
  rw [sub_sub_sub_cancel_right] at hp
  exact M.pointEquivPlace.injective
    (eq_of_single_sub_single_principal_of_genus_pos hg _ _ hp)

end AlgebraicCurve

namespace JacobianVarieties.Picard.Unpointed

variable {k : Type u} [Field k] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)

/-- The original constructed Abel–Jacobi map separates geometric points in
positive genus. All Picard and curve-model comparisons are supplied internally. -/
theorem abelJacobi_geometricPoint_injective_of_genus_pos
    (hg : 0 < geometricGenus k c) :
    Function.Injective (fun y : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) c =>
      NeronModelInfra.schemeHomOverComp y (abelJacobi c x)) := by
  let Ω := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  let Y := pullback c b
  let d : Y ⟶ Spec (CommRingCat.of Ω) := pullback.snd c b
  have : IsIntegral Y := isIntegral_pullback_Spec_field k c b
  let F := Y.functionField
  let : Algebra Ω F := (baseToFunctionField d).toAlgebra
  obtain ⟨hcurve, hft⟩ := literalCurveModel_functionField_properties d
  have : IsCurveOver Ω F := hcurve
  have : Algebra.EssFiniteType Ω F := hft
  let M : CurveModel Ω F := literalCurveModel d
  have hgF : 0 < genusFF Ω F := hg
  let P := pointedAbelJacobiData c x
  let e : Jacobian k c ≅ P.designation.P := abelJacobiComparison c x
  have he : e.hom ≫ P.designation.toBase = toBase k c :=
    pointedComparison_over c x P.representation
  have hres (Q : MorphismProperty Scheme.{u}) (hbc : Q.IsStableUnderBaseChange) :
      Q.RespectsIso := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g j
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk j.inv.w))
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    hres (@Smooth) smooth_isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
    hres (@GeometricallyConnected) (GeometricallyConnected.eq_geometrically ▸ inferInstance)
  have hs : Smooth P.designation.toBase := by
    apply (MorphismProperty.cancel_left_of_respectsIso @Smooth e.hom P.designation.toBase).mp
    rw [he]
    exact smooth k c
  have hp : IsProper P.designation.toBase := by
    apply (MorphismProperty.cancel_left_of_respectsIso @IsProper e.hom
      P.designation.toBase).mp
    rw [he]
    exact proper k c
  have hgc : GeometricallyConnected P.designation.toBase := by
    apply (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected e.hom
      P.designation.toBase).mp
    rw [he]
    exact geometricallyConnected k c
  let eC : M.C ≅ pullback c b := Iso.refl Y
  have heC : eC.hom ≫ pullback.snd c b = M.toBase := Category.id_comp d
  obtain ⟨pts, -, hpoint⟩ :=
    (exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi k c x
      P.designation P.representation hs hp hgc P.map P.pointClass).2
      Ω (algebraMap k Ω) F M eC.hom heC
  let liftPoint : SchemeHomOver b c → SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) M.toBase :=
    fun y => ⟨pullback.lift y.val (𝟙 _) (by rw [Category.id_comp]; exact y.property),
      pullback.lift_snd _ _ _⟩
  have hlift (y : SchemeHomOver b c) :
      (liftPoint y).val ≫ pullback.fst c b = y.val :=
    pullback.lift_fst y.val (𝟙 (Spec (CommRingCat.of Ω)))
      (y.property.trans (Category.id_comp b).symm)
  let s : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) M.toBase :=
    ⟨(sectionBaseChange Ω x).val, (sectionBaseChange Ω x).property⟩
  have hbase : s.val ≫ eC.hom ≫ pullback.fst c b = b ≫ x.val := by
    exact (congrArg (fun t : Y ⟶ C => (sectionBaseChange Ω x).val ≫ t)
      (Category.id_comp (pullback.fst c b))).trans
        (sectionBaseChange_coe_fst (R := k) Ω x)
  have hvalue (y : SchemeHomOver b c) :
      (pts (Pic0.mk (M.pointDifference s (liftPoint y)))).val = y.val ≫ P.map.val := by
    obtain ⟨D, hD, hval⟩ := hpoint (liftPoint y) s hbase
    have hD' : D = M.pointDifference s (liftPoint y) := Subtype.ext hD
    rw [hD'] at hval
    have hpost : (liftPoint y).val ≫ eC.hom ≫ pullback.fst c b ≫ P.map.val =
        y.val ≫ P.map.val :=
      (congrArg (fun t : Y ⟶ P.designation.P =>
        ((liftPoint y).val : Spec (CommRingCat.of Ω) ⟶ Y) ≫ t)
        (Category.id_comp (pullback.fst c b ≫ P.map.val))).trans
          ((Category.assoc ((liftPoint y).val : Spec (CommRingCat.of Ω) ⟶ Y)
            (pullback.fst c b) P.map.val).symm.trans
              (congrArg (· ≫ P.map.val) (hlift y)))
    exact hval.trans hpost
  intro y z hyz
  have hpointed : y.val ≫ P.map.val = z.val ≫ P.map.val := by
    have h := congrArg (fun t : SchemeHomOver b (toBase k c) => t.val ≫ e.hom) hyz
    simpa only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, e,
      abelJacobi_comp_comparison] using h
  have hclasses : Pic0.mk (M.pointDifference s (liftPoint y)) =
      Pic0.mk (M.pointDifference s (liftPoint z)) := by
    apply pts.injective
    apply Subtype.ext
    exact (hvalue y).trans (hpointed.trans (hvalue z).symm)
  have hpoints := M.pointDifference_class_injective_of_genus_pos hgF s hclasses
  apply Subtype.ext
  have h := congrArg (fun q : SchemeHomOver (𝟙 (Spec (CommRingCat.of Ω))) M.toBase =>
    q.val ≫ pullback.fst c b) hpoints
  exact (hlift y).symm.trans (h.trans (hlift z))

/-- The same geometric injectivity holds in any prescribed algebraic
constant closure. Transport changes only the coefficient-field presentation
and retains the original curve and its original Abel--Jacobi morphism. -/
theorem abelJacobi_constantClosurePoint_injective_of_genus_pos
    (κ : Type u) [Field κ] [Algebra k κ] [IsAlgClosure k κ]
    (hg : 0 < geometricGenus k c) :
    Function.Injective (fun y : SchemeHomOver (Spec.algebraMap k κ) c =>
      NeronModelInfra.schemeHomOverComp y (abelJacobi c x)) := by
  let e : κ ≃ₐ[k] AlgebraicClosure k := IsAlgClosure.equiv k κ (AlgebraicClosure k)
  let η := Spec.map (CommRingCat.ofHom e.toRingHom)
  let η' := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hbase : η ≫ Spec.algebraMap k κ = Spec.algebraMap k (AlgebraicClosure k) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext r
    exact e.commutes r
  have hinv : η' ≫ η = 𝟙 (Spec (.of κ)) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext r
    exact e.symm_apply_apply r
  let send (y : SchemeHomOver (Spec.algebraMap k κ) c) :
      SchemeHomOver (Spec.algebraMap k (AlgebraicClosure k)) c :=
    ⟨η ≫ y.val, by rw [Category.assoc, y.property]; exact hbase⟩
  intro y z hyz
  have htransport : NeronModelInfra.schemeHomOverComp (send y) (abelJacobi c x) =
      NeronModelInfra.schemeHomOverComp (send z) (abelJacobi c x) := by
    apply Subtype.ext
    change (η ≫ y.val) ≫ (abelJacobi c x).val = (η ≫ z.val) ≫ (abelJacobi c x).val
    have h := congrArg Subtype.val hyz
    rw [Category.assoc, Category.assoc]
    exact congrArg (η ≫ ·) h
  have hpoints := abelJacobi_geometricPoint_injective_of_genus_pos c x hg htransport
  apply Subtype.ext
  have h := congrArg (fun p : SchemeHomOver (Spec.algebraMap k (AlgebraicClosure k)) c =>
    η' ≫ p.val) hpoints
  change η' ≫ (η ≫ y.val) = η' ≫ (η ≫ z.val) at h
  simpa only [← Category.assoc, hinv, Category.id_comp] using h

end JacobianVarieties.Picard.Unpointed
