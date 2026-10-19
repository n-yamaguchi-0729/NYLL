/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RationalFunctionTraceAffineLine
import Nyll.JacobianVarieties.Generalized.GenericTracePoint
import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
import Nyll.SchemeTheory.GroupSchemes.AffineLineGroupFormalDifference

/-! # The affine trace difference is the original generic trace difference

The literal projective-line polynomial chart gives its actual generic-point
identity. A deformation of the native function field which translates the
specified rational coordinate therefore restricts to the ordinary polynomial
shift, by polynomial algebra extensionality. Applying the actual group law
identifies the original generic trace quotient with the full formal difference
of the already constructed affine-line trace. No comparison of formal trace
coordinates or completed-field maps is assumed.
-/

noncomputable section

universe u

open AlgebraicGeometry AlgebraicCurve CategoryTheory TopologicalSpace
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.ProjSpace

local instance chartFunctionFieldAlgebra (R : Type u) [CommRing R] [IsDomain R] :
    Algebra R (Spec (CommRingCat.of R)).functionField :=
  ((StructureSheaf.toStalk R
    (show PrimeSpectrum.Top R from genericPoint (Spec (CommRingCat.of R)))) :
      CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).functionField).hom.toAlgebra

/-- The polynomial restriction of the specified rational coordinate is
exactly the original generic-point map into the literal projective line. -/
theorem projectiveLinePolynomialChart_generic
    (K : Type u) [Field K] :
    let P := projectiveLineRatFuncModel K
    Spec.map (CommRingCat.ofHom
      (P.ffEquiv.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)))) ≫
        projectiveLinePolynomialChart K = P.C.fromSpecStalk (genericPoint P.C) := by
  intro P
  let A : Scheme.{u} := Spec (CommRingCat.of (Polynomial K))
  let j : A ⟶ P.C := projectiveLinePolynomialChart K
  have : IsOpenImmersion j := projectiveLinePolynomialChart_isOpenImmersion K
  let e := j.functionFieldRingEquivOfIsOpenImmersion
  have hd : DenseRange j :=
    j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
  have hg : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      P.C.fromSpecStalk (genericPoint P.C) = A.fromSpecStalk (genericPoint A) ≫ j :=
    EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk j hd
  have hcoord : P.ffEquiv.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)) =
      e.symm.toRingHom.comp (algebraMap (Polynomial K) A.functionField) := by
    apply RingHom.ext
    intro f
    change e.symm (polynomialFunctionFieldEquiv K
      (algebraMap (Polynomial K) (RatFunc K) f)) =
        e.symm (algebraMap (Polynomial K) A.functionField f)
    rw [AlgEquiv.commutes]
    rfl
  have hA : Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) A.functionField)) =
      A.fromSpecStalk (genericPoint A) := by
    rw [Spec.fromSpecStalk_eq']
    rfl
  have hcancel : e.symm.toRingHom.comp e.toRingHom = RingHom.id P.C.functionField := by
    ext a
    exact e.symm_apply_apply a
  change Spec.map (CommRingCat.ofHom
    (P.ffEquiv.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K)))) ≫ j =
      P.C.fromSpecStalk (genericPoint P.C)
  rw [hcoord, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hA, ← hg,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcancel,
    CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.GeneralizedJacobian

private def affineComparisonConstant (K : Type u) [CommRing K] :
    Polynomial K →ₐ[K] PowerSeries (Polynomial K) where
  toRingHom := PowerSeries.C
  commutes' a := (PowerSeries.algebraMap_apply (r := a)).symm

/-- The actual generic difference of the original trace equals the full
formal difference of its literal affine-line restriction. The original
generic-open point is constructed by its canonical owner;
the actual chart and the coordinate-shift equation prove the comparison.
In particular the original finiteCurveTrace and the affine trace returned
by exists_rationalFunctionTrace_affineLine may be used directly. -/
theorem rationalFunctionTrace_affineLine_genericOpenPoint_difference
    {K L : Type u} [Field K] [Field L] [Algebra K L] :
    let P := ProjSpace.projectiveLineRatFuncModel K
    let _ : Algebra K P.C.functionField := P.functionFieldAlgebra
    ∀ (V : P.C.Opens) (hV : (V : Set P.C).Nonempty)
      (l : Spec (.of (Polynomial K)) ⟶ V)
      (_ : l ≫ V.ι = ProjSpace.projectiveLinePolynomialChart K)
      (G : CommGrp (Over (Spec (.of K))))
      (trace : SchemeHomOver (V.ι ≫ P.toBase) G.X.hom)
      (τAffine : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) G.X.hom),
      τAffine.val = l ≫ trace.val →
    ∀ (α : P.C.functionField →ₐ[K] L) (θ : P.C.functionField →ₐ[K] PowerSeries L),
      θ (P.ffAlgEquiv RatFunc.X) =
        PowerSeries.C (α (P.ffAlgEquiv RatFunc.X)) + PowerSeries.X →
    let embeddings : RatFunc K →ₐ[K] L := α.comp P.ffAlgEquiv.toAlgHom
    let ιPoly := embeddings.comp (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
    let x := genericOpenPoint P.toBase V hV ≫
      commGroupPointEquiv G (V.ι ≫ P.toBase) trace
    ((traceScalarPointMap θ ≫ x) *
      (traceScalarPointMap
        ((IsScalarTower.toAlgHom K L (PowerSeries L)).comp α) ≫ x)⁻¹).left =
      Spec.map (CommRingCat.ofHom (PowerSeries.map ιPoly.toRingHom)) ≫
        AffineLineGroupFormalDifference.difference
          (commGroupPointEquiv G
            (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) τAffine) := by
  intro P algB V hV l hl G trace τAffine hτAffine α θ hθz embeddings ιPoly x
  let genericMap := genericOpenPoint P.toBase V hV
  have hη : genericMap.left ≫ V.ι = P.C.fromSpecStalk (genericPoint P.C) :=
    genericOpenPoint_comp P.toBase V hV
  let jPoly : Polynomial K →ₐ[K] P.C.functionField :=
    P.ffAlgEquiv.toAlgHom.comp (IsScalarTower.toAlgHom K (Polynomial K) (RatFunc K))
  let mapPS := PowerSeries.mapAlgHom ιPoly
  let θ₀ := (IsScalarTower.toAlgHom K L (PowerSeries L)).comp α
  have hiX : ιPoly Polynomial.X = α (P.ffAlgEquiv RatFunc.X) := by
    change α (P.ffAlgEquiv (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) = _
    rw [RatFunc.algebraMap_X]
  have hshift : θ.comp jPoly = mapPS.comp (AffineLineGroupFormalDifference.shift (K := K)) := by
    apply Polynomial.algHom_ext
    change θ (P.ffAlgEquiv (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)) =
      PowerSeries.map ιPoly.toRingHom
        (Polynomial.aeval (PowerSeries.C Polynomial.X + PowerSeries.X) Polynomial.X)
    rw [RatFunc.algebraMap_X, Polynomial.aeval_X, map_add, PowerSeries.map_C,
      PowerSeries.map_X]
    change θ (P.ffAlgEquiv RatFunc.X) = PowerSeries.C (ιPoly Polynomial.X) + PowerSeries.X
    rw [hiX]
    exact hθz
  have hconstant : θ₀.comp jPoly = mapPS.comp (affineComparisonConstant K) := by
    apply AlgHom.ext
    intro f
    change PowerSeries.C (α (jPoly f)) = PowerSeries.map ιPoly.toRingHom (PowerSeries.C f)
    rw [PowerSeries.map_C]
    rfl
  let chart : Spec (.of (Polynomial K)) ⟶ P.C := ProjSpace.projectiveLinePolynomialChart K
  have hlchart : l ≫ V.ι = chart := hl
  have hchart : Spec.map (CommRingCat.ofHom jPoly.toRingHom) ≫
      chart = P.C.fromSpecStalk (genericPoint P.C) :=
    ProjSpace.projectiveLinePolynomialChart_generic K
  let lOver : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶
      Over.mk (V.ι ≫ P.toBase) :=
    Over.homMk l (by
      change l ≫ V.ι ≫ P.toBase = Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))
      rw [← Category.assoc, hl]
      exact ProjSpace.projectiveLinePolynomialChart_comp_π K)
  let fPS := traceScalarPointMap mapPS
  let fShift := traceScalarPointMap (AffineLineGroupFormalDifference.shift (K := K))
  let fConst := traceScalarPointMap (affineComparisonConstant K)
  have hθpoint : traceScalarPointMap θ ≫ genericMap = fPS ≫ fShift ≫ lOver := by
    apply Over.OverMorphism.ext
    apply (cancel_mono V.ι).mp
    change (Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ genericMap.left) ≫ V.ι =
      (Spec.map (CommRingCat.ofHom mapPS.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (AffineLineGroupFormalDifference.shift (K := K)).toRingHom) ≫ l) ≫ V.ι
    simp only [Category.assoc, hη, hlchart]
    rw [← hchart]
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (θ.comp jPoly).toRingHom) ≫ _ =
      Spec.map (CommRingCat.ofHom
        (mapPS.comp (AffineLineGroupFormalDifference.shift (K := K))).toRingHom) ≫ _
    rw [hshift]
  have hθ₀point : traceScalarPointMap θ₀ ≫ genericMap = fPS ≫ fConst ≫ lOver := by
    apply Over.OverMorphism.ext
    apply (cancel_mono V.ι).mp
    change (Spec.map (CommRingCat.ofHom θ₀.toRingHom) ≫ genericMap.left) ≫ V.ι =
      (Spec.map (CommRingCat.ofHom mapPS.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (affineComparisonConstant K).toRingHom) ≫ l) ≫ V.ι
    simp only [Category.assoc, hη, hlchart]
    rw [← hchart]
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom (θ₀.comp jPoly).toRingHom) ≫ _ =
      Spec.map (CommRingCat.ofHom (mapPS.comp (affineComparisonConstant K)).toRingHom) ≫ _
    rw [hconstant]
  let tracePoint := commGroupPointEquiv G (V.ι ≫ P.toBase) trace
  let affinePoint := commGroupPointEquiv G
    (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) τAffine
  have hAffine : affinePoint = lOver ≫ tracePoint := by
    apply Over.OverMorphism.ext
    exact hτAffine
  change ((traceScalarPointMap θ ≫ genericMap ≫ tracePoint) *
      (traceScalarPointMap θ₀ ≫ genericMap ≫ tracePoint)⁻¹).left =
    (fPS ≫ ((fShift ≫ affinePoint) * (fConst ≫ affinePoint)⁻¹)).left
  apply congrArg (fun f : Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap K (PowerSeries L)))) ⟶ G.X => f.left)
  rw [MonObj.comp_mul, GrpObj.comp_inv, hAffine]
  exact congrArg₂ (fun a b => a * b⁻¹)
    (by simpa only [Category.assoc] using congrArg (fun f : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries L)))) ⟶ Over.mk (V.ι ≫ P.toBase) => f ≫ tracePoint) hθpoint)
    (by simpa only [Category.assoc] using congrArg (fun f : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries L)))) ⟶ Over.mk (V.ι ≫ P.toBase) => f ≫ tracePoint) hθ₀point)

end AlgebraicGeometry.GeneralizedJacobian
