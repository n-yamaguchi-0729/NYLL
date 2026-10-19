/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RationalFunctionTrace
import Nyll.AlgebraicCurves.Models.Rational.ProjectiveLineRatFuncModel
import Nyll.SchemeTheory.FunctionFields.OpenImmersionSections

/-! # The actual affine-line domain of a rational-function trace

The target of the finite curve map is the literal projective-line model,
with its actual polynomial chart. On this chart its rational coordinate
belongs to every closed-point valuation ring. The finite-map comparison
therefore excludes every source boundary point where the given function
has negative order. The entire affine chart lies in the trace domain,
giving an actual group-valued affine-line morphism and retaining both its
finite-trace definition and the specified generic function-field map.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian TopologicalSpace
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

local instance polynomialChart_functionFieldAlgebra
    (R : Type u) [CommRing R] [IsDomain R] :
    Algebra R (Spec (CommRingCat.of R)).functionField :=
  RingHom.toAlgebra
    ((StructureSheaf.toStalk R
      (show PrimeSpectrum.Top R from genericPoint (Spec (CommRingCat.of R)))) :
        CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).functionField).hom

variable {K : Type u} [Field K]

/-- At every closed point of the actual polynomial chart, the rational
coordinate is in the original model's valuation ring. This uses the chart
field comparison and the actual range of its stalk, without identifying
points by an auxiliary rational model. -/
theorem projectiveLinePolynomialChart_X_mem
    (y : Spec (CommRingCat.of (Polynomial K)))
    (hy : projectiveLinePolynomialChart K y ∈
      closedPoints (projectiveLineRatFuncModel K).C) :
    RatFunc.X ∈ ((projectiveLineRatFuncModel K).placeOfPoint
      ⟨projectiveLinePolynomialChart K y, hy⟩).toValuationSubring := by
  let P := projectiveLineRatFuncModel K
  let j : Spec (CommRingCat.of (Polynomial K)) ⟶ P.C := projectiveLinePolynomialChart K
  have : IsOpenImmersion j := projectiveLinePolynomialChart_isOpenImmersion (k := K)
  let U : P.C.Opens := j ''ᵁ ⊤
  have hU : Nonempty U := ⟨⟨j y, y, trivial, rfl⟩⟩
  let s : Γ(P.C, U) :=
    (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv Polynomial.X)
  have hs : P.ffEquiv.symm (P.C.germToFunctionField U s) = RatFunc.X := by
    change (polynomialFunctionFieldEquiv K).symm
      (j.functionFieldRingEquivOfIsOpenImmersion (P.C.germToFunctionField U s)) = RatFunc.X
    apply (polynomialFunctionFieldEquiv K).injective
    rw [AlgEquiv.apply_symm_apply, ← RatFunc.algebraMap_X, AlgEquiv.commutes]
    have hd : DenseRange j :=
      j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j
    exact Scheme.Hom.functionFieldMap_germToFunctionField_appIso_inv j hd
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv Polynomial.X)
  let x : closedPoints P.C := ⟨j y, hy⟩
  have hxU : x.1 ∈ U := ⟨y, trivial, rfl⟩
  let a := P.C.presheaf.germ U x.1 hxU s
  have ha : P.ffEquiv.symm
      (algebraMap (P.C.presheaf.stalk x.1) P.C.functionField a) ∈
        (P.placeOfPoint x).toValuationSubring := by
    rw [← ValuationSubring.mem_toSubring, ← P.range_stalk_eq x]
    exact ⟨a, rfl⟩
  have hasec : algebraMap (P.C.presheaf.stalk x.1) P.C.functionField a =
      P.C.germToFunctionField U s := by
    rw [RingHom.algebraMap_toAlgebra]
    exact TopCat.Presheaf.germ_stalkSpecializes_apply _ _ _ _
  rw [hasec, hs] at ha
  exact ha

end AlgebraicGeometry.ProjSpace

namespace AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

local instance affineTrace_geometricallyIntegral : GeometricallyIntegral M.toBase :=
  geometricallyIntegral_of_isAlgClosed M.toBase

omit [IsAlgClosed K] in
private theorem polynomialChart_preimage_traceLocus_eq_top
    (z : F) (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hboundary : ∀ x : closedPoints M.C, x.1 ∉ U → (M.placeOfPoint x).ord z < 0)
    (φ : RatFunc K →ₐ[K] F) (hφX : φ RatFunc.X = z)
    (hφ : φ.toRingHom.IsIntegral)
    (π : M.C ⟶ (ProjSpace.projectiveLineRatFuncModel K).C)
    (hπ : π ≫ (ProjSpace.projectiveLineRatFuncModel K).toBase = M.toBase)
    [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (n : ℕ) (hn : ∀ y, π.finrank y = n)
    (hclosed : ∀ x : closedPoints M.C,
      ∃ hx : π x.1 ∈ closedPoints (ProjSpace.projectiveLineRatFuncModel K).C,
        (ProjSpace.projectiveLineRatFuncModel K).placeOfPoint ⟨π x.1, hx⟩ =
          (M.placeOfPoint x).restrictAlong φ hφ) :
    let P := ProjSpace.projectiveLineRatFuncModel K
    let j : Spec (CommRingCat.of (Polynomial K)) ⟶ P.C :=
      ProjSpace.projectiveLinePolynomialChart K
    j ⁻¹ᵁ finiteMapTraceLocus M.toBase P.toBase π hπ n hn U = ⊤ := by
  intro P j
  have hη : genericPoint M.C ∈ U :=
    ((genericPoint_spec M.C).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  apply top_unique
  intro y _
  apply (mem_finiteMapTraceLocus_iff M.toBase P.toBase π hπ n hn U (j y)).mpr
  intro x hx
  by_contra hxU
  have hxclosed : IsClosed ({x} : Set M.C) :=
    isClosed_singleton_of_ne_genericPoint M.toBase x (by
      intro h
      exact hxU (h.symm ▸ hη))
  let x₀ : closedPoints M.C := ⟨x, hxclosed⟩
  obtain ⟨hπx, hplace⟩ := hclosed x₀
  have hyclosed : j y ∈ closedPoints P.C := hx ▸ hπx
  have hmem := ProjSpace.projectiveLinePolynomialChart_X_mem y hyclosed
  have hpoint : (⟨π x, hπx⟩ : closedPoints P.C) = ⟨j y, hyclosed⟩ :=
    Subtype.ext hx
  change RatFunc.X ∈ (P.placeOfPoint ⟨j y, hyclosed⟩).toValuationSubring at hmem
  rw [← hpoint] at hmem
  change RatFunc.X ∈ (P.placeOfPoint ⟨π x₀.1, hπx⟩).toValuationSubring at hmem
  rw [hplace] at hmem
  have hzmem : z ∈ (M.placeOfPoint x₀).toValuationSubring := by
    have hmap : φ RatFunc.X ∈ (M.placeOfPoint x₀).toValuationSubring := hmem
    rwa [hφX] at hmap
  exact (not_le_of_gt (hboundary x₀ hxU)) ((M.placeOfPoint x₀).ord_nonneg_of_mem hzmem)

/-- Negative order on the whole source boundary constructs a regular
trace on the actual affine line. The finite map has the prescribed generic
map, and the affine trace is explicitly the pullback of its actual finite
Cartier-family trace, with no supplied boundary-image condition. -/
theorem exists_rationalFunctionTrace_affineLine
    (z : F) (hz : z ∉ Set.range (algebraMap K F))
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hboundary : ∀ x : closedPoints M.C, x.1 ∉ U → (M.placeOfPoint x).ord z < 0)
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom) :
    let P := ProjSpace.projectiveLineRatFuncModel K
    ∃ φ : RatFunc K →ₐ[K] F,
      φ RatFunc.X = z ∧ φ.toRingHom.IsIntegral ∧ FiniteAlong K φ ∧
      ∃ (π : M.C ⟶ P.C) (hπ : π ≫ P.toBase = M.toBase)
        (_ : IsFinite π) (_ : Flat π) (_ : LocallyOfFinitePresentation π)
        (hn : ∀ y : P.C, π.finrank y = finrankAlong K φ),
        M.C.fromSpecStalk (genericPoint M.C) ≫ π =
          Spec.map (CommRingCat.ofHom
            (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp P.ffEquiv.symm.toRingHom))) ≫
              P.C.fromSpecStalk (genericPoint P.C) ∧
        let V := finiteMapTraceLocus M.toBase P.toBase π hπ (finrankAlong K φ) hn U
        ProjSpace.projectiveLinePolynomialChart K ⁻¹ᵁ V = ⊤ ∧
        ∃ (ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ M.toBase))
          (l : Spec (CommRingCat.of (Polynomial K)) ⟶ V),
          l ≫ V.ι = ProjSpace.projectiveLinePolynomialChart K ∧
          ∃ τ : SchemeHomOver
            (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) G.X.hom,
            τ.1 = l ≫
              (finiteCurveTrace M.toBase P.toBase π hπ (finrankAlong K φ) hn U ε G q).1 := by
  intro P
  obtain ⟨φ, hφX⟩ := FunctionField.exists_ratFuncAlgHom_apply_X_eq hz
  obtain ⟨hfinite, hφ⟩ := finiteAlong_ratFunc_of_curveModel M φ
  obtain ⟨π, hπ, hfin, hflat, hlfp, hn, hgeneric, hclosed, _huniq⟩ :=
    P.exists_finite_flat_hom_of_algHom M φ hφ hfinite
  have : IsFinite π := hfin
  have : Flat π := hflat
  have : LocallyOfFinitePresentation π := hlfp
  let V := finiteMapTraceLocus M.toBase P.toBase π hπ (finrankAlong K φ) hn U
  have hchart : ProjSpace.projectiveLinePolynomialChart K ⁻¹ᵁ V = ⊤ :=
    polynomialChart_preimage_traceLocus_eq_top M z U hU hboundary
      φ hφX hφ π hπ (finrankAlong K φ) hn hclosed
  let j : Spec (CommRingCat.of (Polynomial K)) ⟶ P.C :=
    ProjSpace.projectiveLinePolynomialChart K
  let l : Spec (CommRingCat.of (Polynomial K)) ⟶ V :=
    IsOpenImmersion.lift V.ι j (by
      rintro _ ⟨y, rfl⟩
      have hy : j y ∈ V := by
        change y ∈ ProjSpace.projectiveLinePolynomialChart K ⁻¹ᵁ V
        rw [hchart]
        trivial
      exact ⟨⟨j y, hy⟩, rfl⟩)
  have hl : l ≫ V.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : Nonempty U := ⟨⟨hU.choose, hU.choose_spec⟩⟩
  have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace (U.ι ≫ M.toBase)
  obtain ⟨x, _, hx⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set U).Nonempty) isClosed_univ.isLocallyClosed
  let ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ M.toBase) :=
    ⟨pointOfClosedPoint (U.ι ≫ M.toBase) x hx,
      pointOfClosedPoint_comp (U.ι ≫ M.toBase) x hx⟩
  let trace := finiteCurveTrace M.toBase P.toBase π hπ (finrankAlong K φ) hn U ε G q
  let τ : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) G.X.hom :=
    ⟨l ≫ trace.1, by
      rw [Category.assoc, trace.2, ← Category.assoc, hl]
      exact ProjSpace.projectiveLinePolynomialChart_comp_π K⟩
  exact ⟨φ, hφX, hφ, hfinite, π, hπ, hfin, hflat, hlfp, hn,
    hgeneric, hchart, ε, l, hl, τ, rfl⟩

end AlgebraicGeometry.GeneralizedJacobian
