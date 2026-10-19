/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RationalFunctionTraceFiniteFibre
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic

/-! # Finite trace points with a polar boundary

A coordinate with negative orders at all omitted source points has every
finite rational parameter in its actual trace domain. The lifts preserve the
original point morphisms, so they can be used in full Cartier-fibre evaluation.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open NeronModelInfra GoodReductionJacobian
open scoped BigOperators CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (P : CurveModel K (RatFunc K)) (M : CurveModel K F)
  (φ : RatFunc K →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (hfinite : FiniteAlong K φ)
  (π : M.C ⟶ P.C) (hπ : π ≫ P.toBase = M.toBase)
  [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  (n : ℕ) (hn : ∀ y : P.C, π.finrank y = n)
  (hgeneric : M.C.fromSpecStalk (genericPoint M.C) ≫ π =
    Spec.map (CommRingCat.ofHom
      (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp P.ffEquiv.symm.toRingHom))) ≫
        P.C.fromSpecStalk (genericPoint P.C))

include hφ hfinite hgeneric in
/-- If the trace coordinate has poles on the whole boundary, every rational
target point where it is integral lifts to the actual trace domain. -/
theorem rationalFunctionTrace_lift_of_boundary_poles
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hboundary : ∀ w : Place K F, (M.placeEquiv.symm w).1 ∉ U → w.ord (φ RatFunc.X) < 0)
    (p : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase)
    (hp : 0 ≤ (P.pointEquivPlace p).ord RatFunc.X) :
    let V := finiteMapTraceLocus M.toBase P.toBase π hπ n hn U
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase),
      x.1 ≫ V.ι = p.1 := by
  intro V
  classical
  let _ : Algebra (RatFunc K) F := algebraAlong φ
  have : IsScalarTower K (RatFunc K) F := isScalarTower_along φ
  have : Algebra.IsIntegral (RatFunc K) F := isIntegral_along φ hφ
  have hmem : p.1 (IsLocalRing.closedPoint K) ∈ V := by
    apply (mem_finiteMapTraceLocus_iff M.toBase P.toBase π hπ n hn U _).mpr
    intro z hz
    by_contra hzU
    have hη : genericPoint M.C ∈ U :=
      ((genericPoint_spec M.C).mem_open_set_iff U.isOpen).mpr
        ⟨hU.choose, trivial, hU.choose_spec⟩
    have hzc : IsClosed ({z} : Set M.C) :=
      isClosed_singleton_of_ne_genericPoint M.toBase z (fun h => hzU (h ▸ hη))
    let y := (pointEquivClosedPoint M.toBase).symm ⟨z, hzc⟩
    have hy : pointEquivClosedPoint M.toBase y = ⟨z, hzc⟩ :=
      (pointEquivClosedPoint M.toBase).apply_symm_apply _
    let yp : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) P.toBase :=
      ⟨y.1 ≫ π, by rw [Category.assoc, hπ]; exact y.2⟩
    have hyp : yp = p := by
      apply (pointEquivClosedPoint P.toBase).injective
      apply Subtype.ext
      change π (y.1 (IsLocalRing.closedPoint K)) = p.1 (IsLocalRing.closedPoint K)
      rw [show y.1 (IsLocalRing.closedPoint K) = z from congrArg Subtype.val hy]
      exact hz
    have hr := CurveModel.pointEquivPlace_comp_of_generic P M φ hφ hfinite
      π hgeneric y p (congrArg Subtype.val hyp)
    have hpoint : (M.placeEquiv.symm (M.pointEquivPlace y)).1 = z := by
      change (M.placeEquiv.symm (M.placeEquiv (pointEquivClosedPoint M.toBase y))).1 = z
      rw [M.placeEquiv.symm_apply_apply, hy]
    have hzord := hboundary (M.pointEquivPlace y) (by rw [hpoint]; exact hzU)
    have hord := Place.ord_restrictAlong φ hφ (M.pointEquivPlace y) RatFunc.X
    rw [hr] at hord
    have hnonneg : 0 ≤ (M.pointEquivPlace y).ord (φ RatFunc.X) := by
      rw [hord]
      exact mul_nonneg (Int.natCast_nonneg _) hp
    exact (not_le_of_gt hzord) hnonneg
  have hrange : Set.range p.1 ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hz]
    exact hmem
  let x := IsOpenImmersion.lift V.ι p.1 hrange
  have hx : x ≫ V.ι = p.1 := IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨x, ?_⟩, hx⟩
  rw [← Category.assoc, hx, p.2]


include hφ hfinite hgeneric in
/-- Every finite rational parameter belongs to the actual trace domain when
the coordinate is polar at the entire source boundary. -/
theorem rationalFunctionTrace_lift_finite_parameter
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hboundary : ∀ w : Place K F, (M.placeEquiv.symm w).1 ∉ U →
      w.ord (φ RatFunc.X) < 0) (a : K) :
    let V := finiteMapTraceLocus M.toBase P.toBase π hπ n hn U
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (V.ι ≫ P.toBase),
      x.1 ≫ V.ι = (P.pointEquivPlace.symm (RationalFunctionField.placeOfPoint K a)).1 := by
  classical
  apply rationalFunctionTrace_lift_of_boundary_poles P M φ hφ hfinite π hπ n hn hgeneric
    U hU hboundary
  rw [P.pointEquivPlace.apply_symm_apply]
  exact RationalFunctionField.ord_X_nonneg_of_ne_placeInfty K
    (RationalFunctionField.placeOfPoint_ne_placeInfty K a)

variable [GeometricallyIntegral M.toBase]

open Classical in
include hφ hfinite hgeneric in
/-- A constant actual reciprocal trace annihilates the full principal
evaluation. The two finite trace points are constructed from the polar boundary. -/
theorem rationalFunctionTrace_reciprocal_evaluation_eq_zero_of_constant
    (U : M.C.Opens) (hU : (U : Set M.C).Nonempty)
    (hboundary : ∀ w : Place K F, (M.placeEquiv.symm w).1 ∉ U →
      w.ord (φ RatFunc.X) < 0)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) (U.ι ≫ M.toBase))
    (G : CommGrp (Over (Spec (.of K)))) [IsSeparated G.X.hom]
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom)
    (g : Fˣ) (hg : (g : F) ≠ 1) (hcoordinate : φ RatFunc.X = ((g : F) - 1)⁻¹)
    (a : SchemeHomOver (𝟙 (Spec (.of K))) G.X.hom)
    (hconst : (finiteCurveTrace M.toBase P.toBase π hπ n hn U ε G q).1 =
      ((finiteMapTraceLocus M.toBase P.toBase π hπ n hn U).ι ≫ P.toBase) ≫ a.1) :
    ∑ᶠ w : Place K F, w.ord (g : F) • M.regularMapValues U G q w = 0 := by
  let V := finiteMapTraceLocus M.toBase P.toBase π hπ n hn U
  let τ := finiteCurveTrace M.toBase P.toBase π hπ n hn U ε G q
  obtain ⟨xm, hxm⟩ := rationalFunctionTrace_lift_finite_parameter P M φ hφ hfinite
    π hπ n hn hgeneric U hU hboundary (-1)
  obtain ⟨x₀, hx₀⟩ := rationalFunctionTrace_lift_finite_parameter P M φ hφ hfinite
    π hπ n hn hgeneric U hU hboundary 0
  have hpoint (x : SchemeHomOver (𝟙 (Spec (.of K))) (V.ι ≫ P.toBase)) :
      NeronModelInfra.schemeHomOverComp x τ = a := by
    apply Subtype.ext
    change x.1 ≫ τ.1 = a.1
    rw [hconst, ← Category.assoc, x.2, Category.id_comp]
  have h := rationalFunctionTrace_reciprocal_principalEvaluation P M φ hφ hfinite
    π hπ n hn hgeneric U ε G q g hg hcoordinate xm x₀ hxm hx₀
  rw [hpoint, hpoint, sub_self] at h
  exact h.symm

end AlgebraicGeometry.GeneralizedJacobian
