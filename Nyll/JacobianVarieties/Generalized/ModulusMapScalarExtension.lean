/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.JacobianVarieties.Generalized.ModulusAbelMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusAbelGroupScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusMapTranslation
import Nyll.SchemeTheory.CategoryTheory.AdjunctionGroupPoints
import Nyll.SchemeTheory.CategoryTheory.PointedTorsorCoordinates

/-! # Scalar extension of regular maps with full modulus

The extended map is the actual pullback morphism on the complement of the
extended divisor. The constructed all-degree Abel factor and actual basepoint translation
prove the principal-divisor modulus condition after an algebraically closed
extension, and the constructed universal group morphism commutes with it.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (L : Type u) [Field L] [Algebra K L]

/-- Pull the actual group-valued map back to the complement of the full
extended divisor, using the native pullback group scheme. -/
def modulusGroupMapScalarExtension (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X) :
    Over.mk
        ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
          baseChange K c L) ⟶
      (Over.pullback (specMap K L)).obj G.X :=
  modulusMapScalarExtension c D L G.X q

/-- Scalar extension of an actual regular map commutes with composition by
an actual group-scheme morphism. -/
theorem modulusGroupMapScalarExtension_comp
    (G H : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (φ : G ⟶ H) :
    modulusGroupMapScalarExtension c D L H (q ≫ φ.hom.hom.hom) =
      modulusGroupMapScalarExtension c D L G q ≫
        ((GroupSchemes.baseChange (specMap K L)).map φ).hom.hom.hom :=
  modulusMapScalarExtension_comp c D L G.X H.X q φ.hom.hom.hom

/-- Evaluation of the extended regular map is the adjoint of the original
map evaluated at the projected point, on every parameter scheme. -/
theorem modulusGroupMapScalarExtension_point
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    {T : Over (Spec (CommRingCat.of L))}
    (x : T ⟶ Over.mk
      ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
        baseChange K c L)) :
    x ≫ modulusGroupMapScalarExtension c D L G q =
      (Over.mapPullbackAdj (specMap K L)).homEquiv T G.X
        (divisorScalarExtensionPoint c D L x ≫ q) :=
  modulusMapScalarExtension_point c D L G.X q x


/-- Scalar extension preserves the actual action on regular maps to a torsor. -/
theorem modulusMapScalarExtension_smul
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (Q : Over (Spec (CommRingCat.of K))) [ModObj G.X Q]
    (g : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let _ : ModObj ((Over.pullback (specMap K L)).obj G.X)
        ((Over.pullback (specMap K L)).obj Q) :=
      (Over.pullback (specMap K L)).modObjObj G.X Q
    modulusMapScalarExtension c D L Q (g • q) =
      modulusGroupMapScalarExtension c D L G g • modulusMapScalarExtension c D L Q q := by
  intro transportedAction
  unfold modulusGroupMapScalarExtension modulusMapScalarExtension
  rw [ModObj.comp_smul]
  exact (Over.mapPullbackAdj (specMap K L)).homEquiv_modObj_smul _ G.X Q _ _

/-- The difference of two actual torsor-valued maps commutes with scalar extension. -/
theorem modulusMapScalarExtension_difference
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (Q : Over (Spec (CommRingCat.of K))) [ModObj G.X Q]
    [IsIso (ModObj.leftSMul G.X Q)]
    (q r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let _ : ModObj ((Over.pullback (specMap K L)).obj G.X)
        ((Over.pullback (specMap K L)).obj Q) :=
      (Over.pullback (specMap K L)).modObjObj G.X Q
    let _ : IsIso (ModObj.leftSMul ((Over.pullback (specMap K L)).obj G.X)
        ((Over.pullback (specMap K L)).obj Q)) :=
      (Over.pullback (specMap K L)).isIso_leftSMul_modObjObj G.X Q
    modulusGroupMapScalarExtension c D L G
        (SchemeTheory.PointedTorsor.difference (G := G.X) q r) =
      SchemeTheory.PointedTorsor.difference
        (G := (Over.pullback (specMap K L)).obj G.X)
        (modulusMapScalarExtension c D L Q q) (modulusMapScalarExtension c D L Q r) := by
  intro transportedAction transportedTorsor
  unfold modulusGroupMapScalarExtension modulusMapScalarExtension
  rw [SchemeTheory.PointedTorsor.difference_naturality]
  exact (Over.mapPullbackAdj (specMap K L)).homEquiv_torsor_difference _ G.X Q _ _

/-- Choosing a torsor origin before scalar extension gives the same coordinate
map as choosing its image under the monoidal unit comparison afterwards. -/
theorem modulusMapScalarExtension_coordinate
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (Q : Over (Spec (CommRingCat.of K))) [ModObj G.X Q]
    [IsIso (ModObj.leftSMul G.X Q)]
    (p : MonoidalCategory.tensorUnit (Over (Spec (CommRingCat.of K))) ⟶ Q)
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Q) :
    let _ : ModObj ((Over.pullback (specMap K L)).obj G.X)
        ((Over.pullback (specMap K L)).obj Q) :=
      (Over.pullback (specMap K L)).modObjObj G.X Q
    let _ : IsIso (ModObj.leftSMul ((Over.pullback (specMap K L)).obj G.X)
        ((Over.pullback (specMap K L)).obj Q)) :=
      (Over.pullback (specMap K L)).isIso_leftSMul_modObjObj G.X Q
    modulusGroupMapScalarExtension c D L G
        (q ≫ SchemeTheory.PointedTorsor.coordinate (G := G.X) p) =
      modulusMapScalarExtension c D L Q q ≫
        SchemeTheory.PointedTorsor.coordinate
          (G := (Over.pullback (specMap K L)).obj G.X)
          (Functor.LaxMonoidal.ε (Over.pullback (specMap K L)) ≫
            (Over.pullback (specMap K L)).map p) := by
  intro transportedAction transportedTorsor
  rw [modulusGroupMapScalarExtension, modulusMapScalarExtension_comp,
    (Over.pullback (specMap K L)).map_torsor_coordinate]

/-- Pulling back a translated regular map gives the translate by the
actual scalar extension of the original group point. -/
theorem modulusGroupMapScalarExtension_translation
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (z : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    let bL : Over.mk
        ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
          baseChange K c L) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of L))) :=
      Over.homMk _ (Category.comp_id _)
    let zL := (Over.mapPullbackAdj (specMap K L)).homEquiv
      (Over.mk (𝟙 (Spec (CommRingCat.of L)))) G.X
        ((Over.homMk (𝟙 (Spec (CommRingCat.of L)) ≫ specMap K L)
          (Category.comp_id _)) ≫ z)
    modulusGroupMapScalarExtension c D L G (q / (b ≫ z)) =
      modulusGroupMapScalarExtension c D L G q / (bL ≫ zL) := by
  intro b bL zL
  let T := Over.mk
    ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
      baseChange K c L)
  let δ := divisorScalarExtensionPoint c D L (𝟙 T)
  let adj := Over.mapPullbackAdj (specMap K L)
  let z₀ : (Over.map (specMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶ G.X :=
    Over.homMk (𝟙 (Spec (CommRingCat.of L)) ≫ specMap K L) (Category.comp_id _) ≫ z
  have hconstant : δ ≫ b ≫ z = (Over.map (specMap K L)).map bL ≫ z₀ := by
    apply Over.OverMorphism.ext
    change δ.left ≫ (((modulusComplement (modulusCurveMap D)).ι ≫ c) ≫ z.left) =
      T.hom ≫ ((𝟙 (Spec (CommRingCat.of L)) ≫ specMap K L) ≫ z.left)
    simp only [Category.id_comp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ z.left) (Over.w δ)).trans (Category.assoc _ _ _))
  change adj.homEquiv T G.X (δ ≫ (q / (b ≫ z))) =
    adj.homEquiv T G.X (δ ≫ q) / (bL ≫ adj.homEquiv _ G.X z₀)
  rw [GrpObj.comp_div]
  change (adj.homMulEquiv T G.X) ((δ ≫ q) / (δ ≫ b ≫ z)) = _
  rw [map_div, hconstant]
  change adj.homEquiv T G.X (δ ≫ q) /
      adj.homEquiv T G.X ((Over.map (specMap K L)).map bL ≫ z₀) = _
  exact congrArg (fun t => adj.homEquiv T G.X (δ ≫ q) / t)
    (adj.homEquiv_naturality_left bL z₀)

/-- Scalar extension respects subtraction of the actual basepoint value.
The proof uses the multiplicative adjunction and projection of the same
extended complement point. -/
theorem modulusGroupMapScalarExtension_normalization
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ G.X)
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶
        Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
      Over.homMk _ (Category.comp_id _)
    let bL : Over.mk
        ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
          baseChange K c L) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of L))) :=
      Over.homMk _ (Category.comp_id _)
    modulusGroupMapScalarExtension c D L G (q / (b ≫ ε ≫ q)) =
      modulusGroupMapScalarExtension c D L G q /
        (bL ≫ modulusBasepointScalarExtension c D L ε ≫
          modulusGroupMapScalarExtension c D L G q) := by
  intro b bL
  let T := Over.mk
    ((modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L)))).ι ≫
      baseChange K c L)
  let δ := divisorScalarExtensionPoint c D L (𝟙 T)
  let adj := Over.mapPullbackAdj (specMap K L)
  have hb : δ ≫ b =
      (Over.homMk (T.hom ≫ specMap K L) (Category.comp_id _) :
        (Over.map (specMap K L)).obj T ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K)))) := by
    apply Over.OverMorphism.ext
    exact Over.w δ
  have hpoint :
      (Over.map (specMap K L)).map (bL ≫ modulusBasepointScalarExtension c D L ε) ≫ δ =
        δ ≫ b ≫ ε := by
    rw [← divisorScalarExtensionPoint_naturality, Category.comp_id]
    rw [modulusBasepointScalarExtension_project, ← Category.assoc, hb]
  change adj.homEquiv T G.X (δ ≫ (q / (b ≫ ε ≫ q))) =
    adj.homEquiv T G.X (δ ≫ q) /
      (bL ≫ modulusBasepointScalarExtension c D L ε ≫ adj.homEquiv T G.X (δ ≫ q))
  rw [GrpObj.comp_div]
  change (adj.homMulEquiv T G.X) ((δ ≫ q) / (δ ≫ b ≫ ε ≫ q)) = _
  rw [map_div]
  congr 1
  change adj.homEquiv T G.X (δ ≫ b ≫ ε ≫ q) =
    bL ≫ modulusBasepointScalarExtension c D L ε ≫ adj.homEquiv T G.X (δ ≫ q)
  rw [← Category.assoc bL (modulusBasepointScalarExtension c D L ε),
    ← adj.homEquiv_naturality_left (bL ≫ modulusBasepointScalarExtension c D L ε) (δ ≫ q)]
  congr 1
  simpa only [Category.assoc] using congrArg (fun t => t ≫ q) hpoint.symm

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

/-- An Abel composite extends to the corresponding composite of actual
group-scheme morphisms over the larger field. -/
theorem modulusGroupMapScalarExtension_abel_comp
    (G : CommGrp (Over (Spec (CommRingCat.of K)))) (φ : groupScheme c D ⟶ G)
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    modulusAbelMap (baseChange K c L) (D.changeBaseOfIdentity (specMap K L))
        (modulusBasepointScalarExtension c D L ε) ≫
      ((groupActualScalarExtensionIso c D L).inv ≫
        (GroupSchemes.baseChange (specMap K L)).map φ).hom.hom.hom =
      modulusGroupMapScalarExtension c D L G
        (modulusAbelMap c D ε ≫ φ.hom.hom.hom) := by
  simpa only [Category.id_comp, Category.assoc, modulusGroupMapScalarExtension,
    modulusMapScalarExtension] using
    groupActualScalarExtensionIso_modulusAbelMap_comp c D L G φ ε (𝟙 _)

end AlgebraicGeometry.GeneralizedJacobian

open AlgebraicGeometry GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsSeparated G.X.hom]
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)

/-- The principal-divisor modulus condition of a normalized regular map
survives every algebraically closed extension. The group factor used in the
proof is supplied by the constructed full-modulus universality theorem. -/
theorem regularMapHasModulus_scalarExtension_of_normalized
    (hmod : M.regularMapHasModulus D G q)
    (hε : ε ≫ Over.homMk q.1 q.2 = 1)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L] :
    let cL := baseChange K M.toBase L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let _ : Algebra L (CategoryTheory.Limits.pullback M.toBase (specMap K L)).functionField :=
      (baseToFunctionField cL).toAlgebra
    let ML := ofSmoothProperCurve cL
    let qL := modulusGroupMapScalarExtension M.toBase D L G (Over.homMk q.1 q.2)
    ML.regularMapHasModulus DL ((GroupSchemes.baseChange (specMap K L)).obj G)
      ⟨qL.left, Over.w qL⟩ := by
  intro cL DL algL ML qL
  let : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cL
    infer_instance
  let εL := modulusBasepointScalarExtension M.toBase D L ε
  let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
  obtain ⟨φ, hφ, -⟩ := M.existsUnique_groupHom_fullModulus D ε G q hmod hε
  let φL : groupScheme cL DL ⟶ extendedGroup :=
    (groupActualScalarExtensionIso M.toBase D L).inv ≫
      (GroupSchemes.baseChange (specMap K L)).map φ
  have hfac : modulusAbelMap cL DL εL ≫ φL.hom.hom.hom = qL := by
    change modulusAbelMap cL DL εL ≫ φL.hom.hom.hom =
      modulusGroupMapScalarExtension M.toBase D L G (Over.homMk q.1 q.2)
    rw [← hφ]
    exact modulusGroupMapScalarExtension_abel_comp M.toBase D L G φ ε
  let a : SchemeHomOver ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)
      (groupScheme cL DL).X.hom :=
    ⟨(modulusAbelMap cL DL εL).left, Over.w (modulusAbelMap cL DL εL)⟩
  have h := ML.regularMapHasModulus_comp DL (groupScheme cL DL) a
    (ML.regularMapHasModulus_abel DL εL) extendedGroup φL
  have heq :
      (commGroupPointEquiv extendedGroup
        ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase)).symm
        ((commGroupPointEquiv (groupScheme cL DL)
          ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase) a) ≫ φL.hom.hom.hom) =
      (⟨qL.left, Over.w qL⟩ :
        SchemeHomOver ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase)
          extendedGroup.X.hom) := by
    apply Subtype.ext
    exact congrArg Over.Hom.left hfac
  exact (congrArg (ML.regularMapHasModulus DL extendedGroup) heq).mp h


include ε in
/-- Every regular map with full modulus over an algebraically closed field
retains that condition after an algebraically closed extension. Translation
by the basepoint value is handled by the actual point-group operations. -/
theorem regularMapHasModulus_scalarExtension
    (hmod : M.regularMapHasModulus D G q)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L] :
    let cL := baseChange K M.toBase L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let _ : Algebra L (CategoryTheory.Limits.pullback M.toBase (specMap K L)).functionField :=
      (baseToFunctionField cL).toAlgebra
    let ML := ofSmoothProperCurve cL
    let qL := modulusGroupMapScalarExtension M.toBase D L G (Over.homMk q.1 q.2)
    ML.regularMapHasModulus DL ((GroupSchemes.baseChange (specMap K L)).obj G)
      ⟨qL.left, Over.w qL⟩ := by
  intro cL DL algL ML qL
  let b : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk _ (Category.comp_id _)
  let q₀ := (commGroupPointEquiv G
    ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase)).symm
      (Over.homMk q.1 q.2 / (b ≫ ε ≫ Over.homMk q.1 q.2))
  have h₀ : M.regularMapHasModulus D G q₀ :=
    M.regularMapHasModulus_translate D G q hmod (ε ≫ Over.homMk q.1 q.2)
  have hb : ε ≫ b = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact Over.w ε
  have hε₀ : ε ≫ Over.homMk q₀.1 q₀.2 = 1 := by
    change ε ≫ (Over.homMk q.1 q.2 / (b ≫ ε ≫ Over.homMk q.1 q.2)) = 1
    rw [GrpObj.comp_div, ← Category.assoc ε b, hb, Category.id_comp]
    exact div_self' _
  have h := M.regularMapHasModulus_scalarExtension_of_normalized D ε G q₀ h₀ hε₀ L
  let : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cL
    infer_instance
  let εL := modulusBasepointScalarExtension M.toBase D L ε
  let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
  let bL : Over.mk ((modulusComplement (modulusCurveMap DL)).ι ≫ cL) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of L))) :=
    Over.homMk _ (Category.comp_id _)
  have hn :
      modulusGroupMapScalarExtension M.toBase D L G (Over.homMk q₀.1 q₀.2) =
        qL / (bL ≫ εL ≫ qL) :=
    modulusGroupMapScalarExtension_normalization M.toBase D L G (Over.homMk q.1 q.2) ε
  change ML.regularMapHasModulus DL extendedGroup
    ((commGroupPointEquiv extendedGroup ((modulusComplement (modulusCurveMap DL)).ι ≫ cL)).symm
      (modulusGroupMapScalarExtension M.toBase D L G (Over.homMk q₀.1 q₀.2))) at h
  rw [hn] at h
  exact (ML.regularMapHasModulus_translate_iff DL extendedGroup ⟨qL.left, Over.w qL⟩
    (εL ≫ qL)).mpr h

/-- The all-degree universal group morphism commutes with actual scalar
extension, including the translation term of an unnormalized regular map. -/
theorem groupHomOfFullModulus_scalarExtension
    (hmod : M.regularMapHasModulus D G q)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L] :
    let cL := baseChange K M.toBase L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let _ : Algebra L (CategoryTheory.Limits.pullback M.toBase (specMap K L)).functionField :=
      (baseToFunctionField cL).toAlgebra
    let ML := ofSmoothProperCurve cL
    let _ : GeometricallyIntegral ML.toBase := by
      change GeometricallyIntegral cL
      infer_instance
    let εL := modulusBasepointScalarExtension M.toBase D L ε
    let extendedGroup := (GroupSchemes.baseChange (specMap K L)).obj G
    let _ : IsSeparated extendedGroup.X.hom := by
      change IsSeparated (CategoryTheory.Limits.pullback.snd G.X.hom (specMap K L))
      infer_instance
    let qL := modulusGroupMapScalarExtension M.toBase D L G (Over.homMk q.1 q.2)
    let hmodL : ML.regularMapHasModulus DL extendedGroup ⟨qL.left, Over.w qL⟩ :=
      M.regularMapHasModulus_scalarExtension D ε G q hmod L
    ML.groupHomOfFullModulus DL εL extendedGroup ⟨qL.left, Over.w qL⟩ hmodL =
      (groupActualScalarExtensionIso M.toBase D L).inv ≫
        (GroupSchemes.baseChange (specMap K L)).map
          (M.groupHomOfFullModulus D ε G q hmod) := by
  intro cL DL algL ML integralML εL extendedGroup separatedGL qL hmodL
  let φ := M.groupHomOfFullModulus D ε G q hmod
  have hfac := modulusGroupMapScalarExtension_abel_comp M.toBase D L G φ ε
  rw [M.groupHomOfFullModulus_abel_translation D ε G q hmod,
    modulusGroupMapScalarExtension_normalization] at hfac
  apply ML.modulusAbel_groupHom_ext DL εL extendedGroup
  exact (ML.groupHomOfFullModulus_abel_translation DL εL extendedGroup
    ⟨qL.left, Over.w qL⟩ hmodL).trans hfac.symm

end AlgebraicCurve.CurveModel
