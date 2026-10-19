/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Albanese.AlbaneseFactorization
import Nyll.JacobianVarieties.Albanese.AbelJacobiPointClassUnique
import Nyll.JacobianVarieties.Albanese.AbelJacobiFiniteSums
import Nyll.JacobianVarieties.Picard.GroupLaw.RelativeGroupLawAbelJacobi
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Existence
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.AbelianSchemeSchemeHomOverCompMulEqMul
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyIntegralSmooth
import Nyll.SchemeTheory.Morphisms.ReducedSmooth
import Nyll.SchemeTheory.GroupSchemes.AbelianScheme
import Nyll.JacobianVarieties.Generalized.GeometricModulusPointedUniversalProperty
import Nyll.JacobianVarieties.Generalized.ModulusComplementNonempty
import Nyll.JacobianVarieties.Generalized.ModulusClassAbel
import Nyll.JacobianVarieties.Generalized.DivisorClasses
import Nyll.JacobianVarieties.Generalized.ModulusMapCondition
import Nyll.JacobianVarieties.Generalized.ModulusMapScalarExtension
import Nyll.AlgebraicCurves.Models.Charts.OpenPointValues
import Nyll.JacobianVarieties.Generalized.ModulusAbelUniqueness
import Nyll.JacobianVarieties.Generalized.ModulusDivisorScalarPoints
import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusFunctoriality
import Nyll.AlgebraicCurves.Divisors.Modulus.LocalSymbolConductor
import Nyll.AlgebraicCurves.Models.FunctionFields.CurveRingEquivFunctionField

/-! # The empty modulus for a regular map to an abelian variety

The actual Albanese factorization and rigidity make the normalized point
map an additive map out of Pic⁰. Principal divisors therefore evaluate to
zero. Restriction and scalar extension give the full geometric modulus
condition, and the constructed generalized Jacobian supplies the unique
group factor. The map is required to extend over the whole curve.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NeronModelInfra GoodReductionJacobian AlgebraicCurve
open AlgebraicGeometry.RelPicard AlgebraicGeometry.GeneralizedJacobian
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]

private theorem exists_pic0_point_factor [IsCurveOver K F]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme H]
    (q : Over.mk M.toBase ⟶ H.X)
    (hq : (Over.homMk ε.1 ε.2 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk M.toBase) ≫ q = 1) :
    ∃ f : Pic0 K F →+ Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X),
      ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase,
        f (Pic0.mk (M.pointDifference ε x)) =
          Additive.ofMul ((Over.homMk x.1 x.2 :
            Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk M.toBase) ≫ q) := by
  obtain ⟨J, ⟨hJ⟩, hsm, hpr, hgc⟩ :=
    exists_representsRelSubPic_of_field K M.toBase ε
  have : Smooth J.toBase := hsm
  have : IsProper J.toBase := hpr
  have : IsReduced J.P := isReduced_of_smooth_of_field J.toBase
  obtain ⟨L, aj, hA, _, hone, haj, hclass, hpoints⟩ :=
    exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic
      K M.toBase ε J hJ hsm hpr hgc
  obtain ⟨aj', _, hclass', hfactor⟩ :=
    JacobianVarieties.Albanese.exists_abelJacobi_factorization_of_isAlgClosed
      M.toBase ε J hJ
  have heq : aj' = aj :=
    abelJacobi_eq_of_geometric_point_class K M.toBase ε J hJ K aj' aj
      (hclass' K _) (hclass K _)
  subst aj'
  have : GeometricallyIntegral H.X.hom :=
    geometricallyIntegral_of_smooth_of_geometricallyConnected H.X.hom
  let q' : SchemeHomOver M.toBase H.X.hom := ⟨q.left, Over.w q⟩
  have hq' : NeronModelInfra.schemeHomOverComp ε q' =
      (commGroupRelativeLaw H).one (𝟙 _) := by
    apply (commGroupPointEquiv H (𝟙 _)).injective
    exact hq
  obtain ⟨ψ, hψ⟩ := hfactor H.X.left H.X.hom (commGroupRelativeLaw H) q' hq'
  have hψone : NeronModelInfra.schemeHomOverComp (L.one (𝟙 _)) ψ =
      (commGroupRelativeLaw H).one (𝟙 _) := by
    apply Subtype.ext
    change (L.one (𝟙 _)).1 ≫ ψ.1 = _
    rw [hone, ← haj, Category.assoc, hψ]
    exact congrArg Subtype.val hq'
  let hB : AbelianSchemePropertyBundle K H.X.hom :=
    ⟨inferInstance, inferInstance, H.X.hom.isConnected_preimage_singleton,
      ⟨commGroupRelativeLaw H⟩⟩
  let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (RingHom.id K))
  have ht : t = 𝟙 _ := Spec.map_id (CommRingCat.of K)
  have : IsIso t := by
    rw [ht]
    infer_instance
  have hψmul :=
    AbelianSchemePropertyBundle.schemeHomOverComp_mul_eq_mul_of_schemeHomOverComp_one_eq_one
      hA hB L (commGroupRelativeLaw H) ψ hψone t
  let e : M.C ⟶ pullback M.toBase t := inv (pullback.fst M.toBase t)
  have he : e ≫ pullback.snd M.toBase t = M.toBase := by
    have hc : pullback.fst M.toBase t ≫ M.toBase = pullback.snd M.toBase t :=
      (pullback.condition (f := M.toBase) (g := t)).trans
        ((congrArg (pullback.snd M.toBase t ≫ ·) ht).trans (Category.comp_id _))
    change inv (pullback.fst M.toBase t) ≫ pullback.snd M.toBase t = _
    rw [← hc, IsIso.inv_hom_id_assoc]
  obtain ⟨pts, hadd, hpoint⟩ := hpoints K (RingHom.id K) F M e he
  let base : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk t :=
    Over.homMk (𝟙 _) ((Category.id_comp t).trans ht)
  let f : Pic0 K F →+ Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X) :=
    AddMonoidHom.mk'
      (fun z => Additive.ofMul (base ≫ commGroupPointEquiv H t
        (NeronModelInfra.schemeHomOverComp (pts z) ψ))) (by
          intro x y
          rw [hadd, hψmul]
          exact congrArg Additive.ofMul (MonObj.comp_mul base
            (commGroupPointEquiv H t (NeronModelInfra.schemeHomOverComp (pts x) ψ))
            (commGroupPointEquiv H t (NeronModelInfra.schemeHomOverComp (pts y) ψ))))
  refine ⟨f, ?_⟩
  intro x
  have hε : ε.1 ≫ e ≫ pullback.fst M.toBase t = t ≫ ε.1 := by
    dsimp only [e]
    rw [IsIso.inv_hom_id, Category.comp_id]
    exact ((congrArg (· ≫ ε.1) ht).trans (Category.id_comp ε.1)).symm
  obtain ⟨Dv, hDv, hval⟩ := hpoint x ε hε
  have hD : Dv = M.pointDifference ε x := Subtype.ext hDv
  rw [hD] at hval
  apply congrArg Additive.ofMul
  apply Over.OverMorphism.ext
  change 𝟙 (Spec (CommRingCat.of K)) ≫
    ((pts (Pic0.mk (M.pointDifference ε x))).1 ≫ ψ.1) = x.1 ≫ q.left
  rw [Category.id_comp, hval]
  dsimp only [e]
  rw [IsIso.inv_hom_id_assoc, Category.assoc, hψ]

private theorem zero_hasModulus_normalized [IsCurveOver K F]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme H]
    (q : Over.mk M.toBase ⟶ H.X)
    (hq : (Over.homMk ε.1 ε.2 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk M.toBase) ≫ q = 1) :
    (0 : Modulus K F).HasModulus (fun w =>
      Additive.ofMul ((Over.homMk (M.pointEquivPlace.symm w).1
        (M.pointEquivPlace.symm w).2 :
          Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk M.toBase) ≫ q)) := by
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨f, hf⟩ := M.exists_pic0_point_factor ε H q hq
  have hdeg : (M.pointEquivPlace ε).deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed _
  have h := ((0 : Modulus K F).hasModulus_classAbel
    (M.pointEquivPlace ε) rfl hdeg).map (f.comp (0 : Modulus K F).toPic0)
  apply h.congr
  intro w _
  change f ((0 : Modulus K F).toPic0
    ((0 : Modulus K F).classAbel (M.pointEquivPlace ε) rfl hdeg w)) = _
  rw [Modulus.classAbel_of_away _ _ _ _ _ rfl, Modulus.toPic0_mkZero]
  have hD : (0 : Modulus K F).toDegreeZero
      ((0 : Modulus K F).normalizeAway (M.pointEquivPlace ε) rfl hdeg
        ((0 : Modulus K F).awayPoint w rfl)) =
        M.pointDifference ε (M.pointEquivPlace.symm w) := by
    apply Subtype.ext
    change Finsupp.single w (1 : ℤ) -
      Divisor.degree (Finsupp.single w 1) • Finsupp.single (M.pointEquivPlace ε) 1 = _
    rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed,
      Nat.cast_one, one_mul, one_zsmul]
    change _ = Finsupp.single (M.pointEquivPlace (M.pointEquivPlace.symm w)) 1 - _
    rw [Equiv.apply_symm_apply]
  rw [hD]
  exact hf (M.pointEquivPlace.symm w)

/-- A map from the complete curve to an actual abelian variety has empty
modulus: every principal divisor has zero sum in the original target group. -/
theorem zero_hasModulus_of_isAbelianScheme
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase)
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme H]
    (q : Over.mk M.toBase ⟶ H.X) :
    (0 : Modulus K F).HasModulus (fun w =>
      Additive.ofMul ((Over.homMk (M.pointEquivPlace.symm w).1
        (M.pointEquivPlace.symm w).2 :
          Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk M.toBase) ≫ q)) := by
  have hcurve : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  let b : Over.mk M.toBase ⟶ Over.mk (𝟙 (Spec (CommRingCat.of K))) :=
    Over.homMk M.toBase (Category.comp_id _)
  let ε' : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk M.toBase :=
    Over.homMk ε.1 ε.2
  let q₀ := q / (b ≫ ε' ≫ q)
  have hb : ε' ≫ b = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact ε.2
  have hq₀ : ε' ≫ q₀ = 1 := by
    change ε' ≫ (q / (b ≫ ε' ≫ q)) = 1
    rw [GrpObj.comp_div, ← Category.assoc ε' b, hb, Category.id_comp]
    exact div_self' (ε' ≫ q)
  have hzero := M.zero_hasModulus_normalized ε H q₀ hq₀
  apply (Modulus.hasModulus_sub_const_iff (D := (0 : Modulus K F))
    (Additive.ofMul (ε' ≫ q))).mp
  apply hzero.congr
  intro w _
  let x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk M.toBase :=
    Over.homMk (M.pointEquivPlace.symm w).1 (M.pointEquivPlace.symm w).2
  have hx : x ≫ b = 𝟙 _ := by
    apply Over.OverMorphism.ext
    exact (M.pointEquivPlace.symm w).2
  change Additive.ofMul (x ≫ (q / (b ≫ ε' ≫ q))) =
    Additive.ofMul (x ≫ q) - Additive.ofMul (ε' ≫ q)
  rw [GrpObj.comp_div, ← Category.assoc x b, hx, Category.id_comp]
  rfl

/-- Restricting a map defined on the complete curve to an abelian variety
satisfies the full principal condition for every effective modulus. -/
theorem regularMapHasModulus_restriction_of_isAbelianScheme
    {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
    (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme H]
    (q : Over.mk M.toBase ⟶ H.X) :
    M.regularMapHasModulus D H
      ⟨(modulusComplement (modulusCurveMap D)).ι ≫ q.left,
        by rw [Category.assoc, Over.w q]; rfl⟩ := by
  obtain ⟨ε⟩ := modulusComplement_point M.toBase D
  let U := modulusComplement (modulusCurveMap D)
  let ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase :=
    ⟨ε.left ≫ U.ι, (Category.assoc _ _ _).trans (Over.w ε)⟩
  have hzero := M.zero_hasModulus_of_isAbelianScheme ε' H q
  have hmod := hzero.mono (show (0 : Modulus K F) ≤ M.functionFieldModulus D from bot_le)
  apply hmod.congr
  intro w hw
  obtain ⟨x, rfl⟩ := M.exists_modulusPlace_eq D w hw
  have hx : M.pointEquivPlace.symm (M.modulusPlace D x) =
      (⟨x.left ≫ U.ι, (Category.assoc _ _ _).trans (Over.w x)⟩ :
        SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :=
    M.pointEquivPlace.symm_apply_apply _
  rw [hx]
  change _ = M.regularMapValues U H _ (M.openPointPlace U ⟨x.left, Over.w x⟩)
  rw [M.regularMapValues_apply]
  change Additive.ofMul _ = Additive.ofMul _
  congr 1

end AlgebraicCurve.CurveModel

namespace AlgebraicGeometry.GeneralizedJacobian

private theorem pullback_adjoint_eq_of_left
    {S T : Scheme.{u}} (s : T ⟶ S)
    {P : Over T} {Q : Over S}
    (p : (Over.map s).obj P ⟶ Q) (r : P ⟶ (Over.pullback s).obj Q)
    (h : p.left = r.left ≫ pullback.fst Q.hom s) :
    (Over.mapPullbackAdj s).homEquiv P Q p = r := by
  apply ((Over.mapPullbackAdj s).homEquiv P Q).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  exact h

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (H : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme H]
  (q : Over.mk c ⟶ H.X)

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  [IsAbelianScheme H] in
/-- Restriction of a whole-curve map commutes with the actual scalar extension. -/
theorem modulusMapScalarExtension_wholeCurveRestriction
    (Q : Over (Spec (CommRingCat.of K))) (r : Over.mk c ⟶ Q)
    (L : Type u) [Field L] [Algebra K L] :
    modulusMapScalarExtension c D L Q
        ((Over.homMk (modulusComplement (modulusCurveMap D)).ι rfl :
          Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Over.mk c) ≫ r) =
      (Over.homMk
        (modulusComplement (modulusCurveMap (c := SmoothProperCurve.baseChange K c L)
          (D.changeBaseOfIdentity (SmoothProperCurve.specMap K L)))).ι rfl :
        Over.mk ((modulusComplement (modulusCurveMap (c := SmoothProperCurve.baseChange K c L)
          (D.changeBaseOfIdentity (SmoothProperCurve.specMap K L)))).ι ≫
          SmoothProperCurve.baseChange K c L) ⟶
            Over.mk (SmoothProperCurve.baseChange K c L)) ≫
              (Over.pullback (SmoothProperCurve.specMap K L)).map r := by
  let s := SmoothProperCurve.specMap K L
  let cL := SmoothProperCurve.baseChange K c L
  let DL := D.changeBaseOfIdentity s
  let U := modulusComplement (modulusCurveMap D)
  let UL := modulusComplement (modulusCurveMap (c := cL) DL)
  let j : Over.mk (U.ι ≫ c) ⟶ Over.mk c := Over.homMk U.ι rfl
  let jL : Over.mk (UL.ι ≫ cL) ⟶ (Over.pullback s).obj (Over.mk c) :=
    Over.homMk UL.ι rfl
  have hj : modulusMapScalarExtension c D L (Over.mk c) j = jL := by
    apply pullback_adjoint_eq_of_left s
    change (divisorScalarExtensionPoint c D L (𝟙 _)).left ≫ U.ι =
      UL.ι ≫ pullback.fst c s
    exact (divisorScalarExtensionPoint_inclusion c D L (𝟙 _)).trans
      (congrArg (fun f => f ≫ pullback.fst c s) (Category.id_comp UL.ι))
  change modulusMapScalarExtension c D L Q (j ≫ r) =
    jL ≫ (Over.pullback s).map r
  rw [modulusMapScalarExtension_comp, hj]

/-- Every whole-curve map to an abelian variety has the full geometric
modulus on restriction. In particular its empty modulus works over any field. -/
theorem geometricRegularMapHasModulus_restriction_of_isAbelianScheme :
    geometricRegularMapHasModulus c D H
      ((Over.homMk (modulusComplement (modulusCurveMap D)).ι rfl :
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Over.mk c) ≫ q) := by
  intro L fieldL algebraL closedL cL DL algL ML qL
  have : GeometricallyIntegral ML.toBase := by
    change GeometricallyIntegral cL
    infer_instance
  let H_L := (GroupSchemes.baseChange (SmoothProperCurve.specMap K L)).obj H
  let r : Over.mk cL ⟶ H_L.X := (Over.pullback (SmoothProperCurve.specMap K L)).map q
  have he := modulusMapScalarExtension_wholeCurveRestriction c D H.X q L
  change qL = _ at he
  let qr : SchemeHomOver
      ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase) H_L.X.hom :=
    ⟨(modulusComplement (modulusCurveMap DL)).ι ≫ r.left,
      by rw [Category.assoc, Over.w r]; rfl⟩
  have hqr : (⟨qL.left, Over.w qL⟩ : SchemeHomOver
      ((modulusComplement (modulusCurveMap DL)).ι ≫ ML.toBase) H_L.X.hom) = qr := by
    apply Subtype.ext
    exact congrArg Over.Hom.left he
  exact (congrArg (ML.regularMapHasModulus DL H_L) hqr).mpr
    (ML.regularMapHasModulus_restriction_of_isAbelianScheme DL H_L r)

/-- The actual generalized Jacobian gives the unique translated group
factor of a whole-curve map to an abelian variety, also for empty modulus. -/
theorem existsUnique_groupHom_restriction_of_isAbelianScheme
    (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
      Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) :
    let r : Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ H.X :=
      (Over.homMk (modulusComplement (modulusCurveMap D)).ι rfl :
        Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c) ⟶ Over.mk c) ≫ q
    ∃! φ : groupScheme c D ⟶ H,
      modulusAbelMap c D ε ≫ φ.hom.hom.hom =
        r / (toUnit (Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ c)) ≫ ε ≫ r) := by
  intro r
  exact existsUnique_groupHom_geometricModulus_translation c D ε H r
    (geometricRegularMapHasModulus_restriction_of_isAbelianScheme c D H q)

end AlgebraicGeometry.GeneralizedJacobian
