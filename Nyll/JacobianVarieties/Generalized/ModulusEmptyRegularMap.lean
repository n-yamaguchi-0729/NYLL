/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelChangeBasepoint
import Nyll.JacobianVarieties.Generalized.ModulusAbelTransition
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniquenessGeometric
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.JacobianVarieties.Generalized.ModulusDegreeOneComparison
import Nyll.JacobianVarieties.Generalized.ModulusMapRestriction
import Nyll.JacobianVarieties.Generalized.ModulusRegularMap
import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw

/-! # Universal group factorization for degree-zero modulus

A rational reduced point supplies a positive modulus. Its actual transition to
the empty modulus is an isomorphism. The positive-modulus factor therefore gives
a group morphism on the degree-zero Jacobian, and density of the open complement
extends its Abel identity to the original curve. Basepoint change supplies the
identity at the prescribed basepoint.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]

section EmptyModulus

variable (D : RelEffCartierDiv M.toBase 0 (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) H.X.hom)

omit [IsAlgClosed K] in
/-- An actual Abel factor for a rational degree-one enlargement extends to
the empty modulus through its canonical group isomorphism. Density supplies
the Abel identity on the whole original curve. -/
theorem existsUnique_groupHom_zeroModulus_of_degreeOneFactor
    (E : RelEffCartierDiv M.toBase 1 (𝟙 (Spec (CommRingCat.of K))))
    (hED : E.I ≤ D.I)
    (εE : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase))
    (φE : groupScheme M.toBase E ⟶ H)
    (hφE :
      let r := modulusComplementRestriction M.toBase (Scheme.IdealSheafData.inclusion hED)
        (modulusIdealInclusion_curve M.toBase E D hED)
      let bE : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) ⟶
          Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk _ (Category.comp_id _)
      modulusAbelMap M.toBase E εE ≫ φE.hom.hom.hom =
        (r ≫ Over.homMk q.1 q.2) / (bE ≫ εE ≫ r ≫ Over.homMk q.1 q.2)) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) := Over.homMk _ (Category.comp_id _)
    ∃! φ : groupScheme M.toBase D ⟶ H,
      modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom =
        Over.homMk q.1 q.2 / (b ≫ ε ≫ Over.homMk q.1 q.2) := by
  intro b
  let r := modulusComplementRestriction M.toBase (Scheme.IdealSheafData.inclusion hED)
    (modulusIdealInclusion_curve M.toBase E D hED)
  let εD := εE ≫ r
  let qOver : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ H.X :=
    Over.homMk q.1 q.2
  let e : groupScheme M.toBase E ≅ groupScheme M.toBase D :=
    degreeOneGroupIso E ≪≫ (emptyModulusGroupIso M.toBase D).symm
  let φ : groupScheme M.toBase D ⟶ H := e.inv ≫ φE
  have hcomp : e.hom ≫ φ = φE := by
    change e.hom ≫ (e.inv ≫ φE) = φE
    rw [Iso.hom_inv_id_assoc]
  have hcomp' : e.hom.hom.hom.hom ≫ φ.hom.hom.hom = φE.hom.hom.hom :=
    congrArg (fun f => f.hom.hom.hom) hcomp
  have hAbel :
      r ≫ modulusAbelMap M.toBase D εD =
        modulusAbelMap M.toBase E εE ≫ e.hom.hom.hom.hom := by
    have h := modulusAbelMap_transitionAlong M.toBase E D
      (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve M.toBase E D hED) εE
    rw [transitionAlong_degreeOne_zero_eq] at h
    exact h.symm
  let bE : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk _ (Category.comp_id _)
  have hb : r ≫ b = bE := by
    apply Over.OverMorphism.ext
    exact Over.w r
  have hfacD : modulusAbelMap M.toBase D εD ≫ φ.hom.hom.hom =
      qOver / (b ≫ εD ≫ qOver) := by
    apply M.modulusComplementRestriction_hom_ext D E hED
    change r ≫ (modulusAbelMap M.toBase D εD ≫ φ.hom.hom.hom) =
      r ≫ (qOver / (b ≫ εD ≫ qOver))
    calc
      _ = (r ≫ modulusAbelMap M.toBase D εD) ≫ φ.hom.hom.hom :=
        (Category.assoc _ _ _).symm
      _ = (modulusAbelMap M.toBase E εE ≫ e.hom.hom.hom.hom) ≫
          φ.hom.hom.hom := by rw [hAbel]
      _ = modulusAbelMap M.toBase E εE ≫ φE.hom.hom.hom := by
        rw [Category.assoc, hcomp']
      _ = (r ≫ qOver) / (bE ≫ εE ≫ r ≫ qOver) :=
        hφE
      _ = r ≫ (qOver / (b ≫ εD ≫ qOver)) := by
        rw [GrpObj.comp_div]
        change (r ≫ qOver) / (bE ≫ εE ≫ r ≫ qOver) =
          (r ≫ qOver) / (r ≫ b ≫ (εE ≫ r) ≫ qOver)
        rw [← Category.assoc r b, hb, Category.assoc]
  have hfac : modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom =
      qOver / (b ≫ ε ≫ qOver) :=
    modulusAbelMap_factor_changeBasepoint M.toBase D εD ε H φ qOver hfacD
  refine ⟨φ, hfac, ?_⟩
  intro ψ hψ
  exact AlgebraicGeometry.GeneralizedJacobian.modulusAbel_groupHom_ext
    M.toBase D ε H ψ φ (hψ.trans hfac.symm)

/-- The full degree-zero modulus condition constructs a unique group morphism.
The auxiliary degree-one divisor and its complement point are supplied internally. -/
theorem existsUnique_groupHom_zeroModulus_translation
    (hmod : M.regularMapHasModulus D H q) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    ∃! φ : groupScheme M.toBase D ⟶ H,
      modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom =
        Over.homMk q.1 q.2 / (b ≫ ε ≫ Over.homMk q.1 q.2) := by
  intro b
  obtain ⟨E, hED, ⟨εE⟩⟩ := exists_degreeOneModulus_with_point M.toBase D
  let r := modulusComplementRestriction M.toBase (Scheme.IdealSheafData.inclusion hED)
    (modulusIdealInclusion_curve M.toBase E D hED)
  let εData : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) :=
    ⟨εE.left, Over.w εE⟩
  let qOver : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ H.X :=
    Over.homMk q.1 q.2
  let qE : SchemeHomOver ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) H.X.hom :=
    (commGroupPointEquiv H
      ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase)).symm (r ≫ qOver)
  have hmodE : M.regularMapHasModulus E H qE :=
    M.regularMapHasModulus_restrict D E hED H q hmod
  let φE := M.groupHomFromModulus E εData H qE hmodE Nat.zero_lt_one
  exact M.existsUnique_groupHom_zeroModulus_of_degreeOneFactor D ε H q E hED εE φE
    (M.groupHomFromModulus_abel_translation E εData H qE hmodE Nat.zero_lt_one)

end EmptyModulus

section AllModuli

variable {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated H.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) H.X.hom)

/-- The full modulus condition gives the unique translated Abel factor in every
degree, including the empty modulus. -/
theorem existsUnique_groupHom_fullModulus_translation
    (hmod : M.regularMapHasModulus D H q) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    ∃! φ : groupScheme M.toBase D ⟶ H,
      modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom =
        Over.homMk q.1 q.2 / (b ≫ ε ≫ Over.homMk q.1 q.2) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact M.existsUnique_groupHom_zeroModulus_translation D ε H q hmod
  · exact M.existsUnique_groupHomFromModulus_translation D
      ⟨ε.left, Over.w ε⟩ H q hmod hd

/-- The actual universal group morphism for every effective modulus. -/
def groupHomOfFullModulus (hmod : M.regularMapHasModulus D H q) :
    groupScheme M.toBase D ⟶ H :=
  (M.existsUnique_groupHom_fullModulus_translation D ε H q hmod).exists.choose

/-- The all-degree group morphism has the prescribed translated Abel composite. -/
theorem groupHomOfFullModulus_abel_translation
    (hmod : M.regularMapHasModulus D H q) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    modulusAbelMap M.toBase D ε ≫
        (M.groupHomOfFullModulus D ε H q hmod).hom.hom.hom =
      Over.homMk q.1 q.2 / (b ≫ ε ≫ Over.homMk q.1 q.2) :=
  (M.existsUnique_groupHom_fullModulus_translation D ε H q hmod).exists.choose_spec

/-- In positive degree the all-degree construction is the existing atlas map. -/
theorem groupHomOfFullModulus_eq_positive
    (hmod : M.regularMapHasModulus D H q) (hd : 0 < d) :
    M.groupHomOfFullModulus D ε H q hmod =
      M.groupHomFromModulus D ⟨ε.left, Over.w ε⟩ H q hmod hd := by
  apply M.modulusAbel_groupHom_ext D ε H
  exact (M.groupHomOfFullModulus_abel_translation D ε H q hmod).trans
    (M.groupHomFromModulus_abel_translation D ⟨ε.left, Over.w ε⟩ H q hmod hd).symm

/-- The actual all-degree group morphism is independent of the auxiliary
basepoint, including for the degree-zero construction. -/
theorem groupHomOfFullModulus_changeBasepoint
    (ε' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
    (hmod : M.regularMapHasModulus D H q) :
    M.groupHomOfFullModulus D ε H q hmod =
      M.groupHomOfFullModulus D ε' H q hmod := by
  apply M.modulusAbel_groupHom_ext D ε' H
  exact (modulusAbelMap_factor_changeBasepoint M.toBase D ε ε' H
    (M.groupHomOfFullModulus D ε H q hmod) (Over.homMk q.1 q.2)
    (M.groupHomOfFullModulus_abel_translation D ε H q hmod)).trans
      (M.groupHomOfFullModulus_abel_translation D ε' H q hmod).symm

/-- A normalized regular map with full modulus has a unique group factor, with
no positivity assumption on the modulus degree. -/
theorem existsUnique_groupHom_fullModulus
    (hmod : M.regularMapHasModulus D H q)
    (hε : ε ≫ Over.homMk q.1 q.2 = 1) :
    ∃! φ : groupScheme M.toBase D ⟶ H,
      modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom = Over.homMk q.1 q.2 := by
  obtain ⟨φ, hφ, _⟩ := M.existsUnique_groupHom_fullModulus_translation D ε H q hmod
  have hfac : modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom =
      Over.homMk q.1 q.2 := by
    rw [hε, MonObj.comp_one, div_one] at hφ
    exact hφ
  refine ⟨φ, hfac, ?_⟩
  intro ψ hψ
  exact M.modulusAbel_groupHom_ext D ε H ψ φ (hψ.trans hfac.symm)


/-- The constructed full-modulus factor commutes with a homomorphism of
separated target groups, including for the empty modulus. -/
theorem groupHomOfFullModulus_comp
    (hmod : M.regularMapHasModulus D H q)
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
    (φ : H ⟶ G) :
    let qG : SchemeHomOver
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom :=
      (commGroupPointEquiv G
        ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
          (Over.homMk q.1 q.2 ≫ φ.hom.hom.hom)
    M.groupHomOfFullModulus D ε G qG
        (M.regularMapHasModulus_comp D H q hmod G φ) =
      M.groupHomOfFullModulus D ε H q hmod ≫ φ := by
  intro qG
  let qOver : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶ H.X :=
    Over.homMk q.1 q.2
  let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk _ (Category.comp_id _)
  apply M.modulusAbel_groupHom_ext D ε G
  change modulusAbelMap M.toBase D ε ≫
      (M.groupHomOfFullModulus D ε G qG
        (M.regularMapHasModulus_comp D H q hmod G φ)).hom.hom.hom =
    modulusAbelMap M.toBase D ε ≫
      ((M.groupHomOfFullModulus D ε H q hmod).hom.hom.hom ≫ φ.hom.hom.hom)
  calc
    _ = (qOver ≫ φ.hom.hom.hom) / (b ≫ ε ≫ qOver ≫ φ.hom.hom.hom) :=
      M.groupHomOfFullModulus_abel_translation D ε G qG
        (M.regularMapHasModulus_comp D H q hmod G φ)
    _ = (qOver / (b ≫ ε ≫ qOver)) ≫ φ.hom.hom.hom := by
      rw [GrpObj.div_comp]
      simp only [Category.assoc]
    _ = modulusAbelMap M.toBase D ε ≫
        ((M.groupHomOfFullModulus D ε H q hmod).hom.hom.hom ≫ φ.hom.hom.hom) := by
      exact (congrArg (fun z => z ≫ φ.hom.hom.hom)
        (M.groupHomOfFullModulus_abel_translation D ε H q hmod).symm).trans
          (Category.assoc _ _ _)


/-- Enlarging the full modulus and restricting the original map commutes with
the constructed group factor in every degree, including degree zero. -/
theorem groupHomOfFullModulus_restrict
    {e : ℕ} (E : RelEffCartierDiv M.toBase e (𝟙 (Spec (CommRingCat.of K))))
    (hED : E.I ≤ D.I)
    (εE : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase))
    (hmod : M.regularMapHasModulus D H q) :
    let r := modulusComplementRestriction M.toBase (Scheme.IdealSheafData.inclusion hED)
      (modulusIdealInclusion_curve M.toBase E D hED)
    let qE := (commGroupPointEquiv H
      ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase)).symm
        (r ≫ Over.homMk q.1 q.2)
    M.groupHomOfFullModulus E εE H qE
        (M.regularMapHasModulus_restrict D E hED H q hmod) =
      transition M.toBase E D hED ≫
        M.groupHomOfFullModulus D (εE ≫ r) H q hmod := by
  intro r qE
  apply M.modulusAbel_groupHom_ext E εE H
  have hE := M.groupHomOfFullModulus_abel_translation E εE H qE
    (M.regularMapHasModulus_restrict D E hED H q hmod)
  have hD := M.groupHomOfFullModulus_abel_translation D (εE ≫ r) H q hmod
  have hAbel := modulusAbelMap_transitionAlong M.toBase E D
    (Scheme.IdealSheafData.inclusion hED)
    (modulusIdealInclusion_curve M.toBase E D hED) εE
  let bE : Over.mk ((modulusComplement (modulusCurveMap E)).ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk _ (Category.comp_id _)
  let bD : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk _ (Category.comp_id _)
  have hb : r ≫ bD = bE := by
    apply Over.OverMorphism.ext
    exact Over.w r
  change modulusAbelMap M.toBase E εE ≫
      (M.groupHomOfFullModulus E εE H qE
        (M.regularMapHasModulus_restrict D E hED H q hmod)).hom.hom.hom =
    modulusAbelMap M.toBase E εE ≫
      ((transition M.toBase E D hED).hom.hom.hom ≫
        (M.groupHomOfFullModulus D (εE ≫ r) H q hmod).hom.hom.hom)
  change modulusAbelMap M.toBase E εE ≫ (transition M.toBase E D hED).hom.hom.hom =
    r ≫ modulusAbelMap M.toBase D (εE ≫ r) at hAbel
  rw [← Category.assoc, hAbel, Category.assoc, hD, hE, GrpObj.comp_div]
  change (r ≫ Over.homMk q.1 q.2) / (bE ≫ εE ≫ r ≫ Over.homMk q.1 q.2) =
    (r ≫ Over.homMk q.1 q.2) / (r ≫ bD ≫ (εE ≫ r) ≫ Over.homMk q.1 q.2)
  rw [← Category.assoc r bD, hb, Category.assoc]

end AllModuli

end AlgebraicCurve.CurveModel
