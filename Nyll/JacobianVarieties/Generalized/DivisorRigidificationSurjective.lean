/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.EffectiveDivisorRigidification
import Nyll.JacobianVarieties.Generalized.EventuallyNormalizedSection
import Nyll.JacobianVarieties.Generalized.NormalizedSectionNonzero
import Nyll.JacobianVarieties.Generalized.NonzeroPointTwistSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.NonzeroSectionCartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.SectionVanishingClosedSubscheme
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveTwoAffineCover
import Nyll.SchemeTheory.Divisors.StalkIdealExt
import Mathlib.Topology.JacobsonSpace

/-!
# Surjectivity of the concrete divisor map for every Cartier modulus

A point outside the actual Cartier support and the required two-chart cover
are supplied by the curve geometry. A normalized section of a sufficiently
large point twist gives a Cartier numerator. The full point-ideal decomposition
then supplies an actual function-field divisor representative.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.GeneralizedJacobian
open AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) [GeometricallyIntegral M.toBase]
  (I : M.C.IdealSheafData) (hI : I.IsInvertible)

omit [GeometricallyIntegral M.toBase] in
include hI in
private theorem exists_point_away_modulus :
    ∃ ε : Spec (CommRingCat.of K) ⟶ M.C, ε ≫ M.toBase = 𝟙 _ ∧
      ∀ z : I.subscheme, I.subschemeι.base z ∉ ε.ker.support := by
  have hη : genericPoint M.C ∉ I.support := by
    have htop : I.stalkIdeal (genericPoint M.C) = ⊤ := by
      let J : Ideal M.C.functionField := I.stalkIdeal (genericPoint M.C)
      exact (Ideal.eq_bot_or_top J).resolve_left (hI.stalkIdeal_ne_bot (genericPoint M.C))
    exact (I.stalkIdeal_eq_top_iff_notMem_support (genericPoint M.C)).mp htop
  have : JacobsonSpace M.C := LocallyOfFiniteType.jacobsonSpace M.toBase
  obtain ⟨x, hxI, hxc⟩ := nonempty_inter_closedPoints
    (Z := (I.support.compl : Set M.C)) ⟨genericPoint M.C, hη⟩
      I.support.compl.isOpen.isLocallyClosed
  let w := M.placeEquiv ⟨x, hxc⟩
  have hw : M.cartierModulus I hI w = 0 := by
    apply (M.cartierModulus_eq_zero_iff I hI w).mpr
    change (M.placeEquiv.symm (M.placeEquiv ⟨x, hxc⟩)).1 ∉ I.support
    rw [M.placeEquiv.symm_apply_apply]
    exact hxI
  exact ⟨pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2,
    pointOfClosedPoint_comp M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2,
    M.pointIdeal_avoids_modulus I hI w hw⟩

omit [GeometricallyIntegral M.toBase] in
include hI in
private theorem exists_nonzero_normalized_pointTwist
    (𝒱 : M.C.TwoAffineOpenCover)
    (ε : Spec (CommRingCat.of K) ⟶ M.C) (hε : ε ≫ M.toBase = 𝟙 _)
    (hεI : ∀ z : I.subscheme, I.subschemeι.base z ∉ ε.ker.support)
    (L : RigidifiedLineBundle I.subschemeι) :
    ∃ n : ℕ, ∃ ha : ∀ y : I.subscheme,
        I.subschemeι y ∉ (ε.ker ^ (n + 1)).support,
      ∃ s : 𝟙_ M.C.Modules ⟶ L.L ⊗ (ε.ker ^ (n + 1)).invModule,
        s ≠ 0 ∧ pullbackSection I.subschemeι s ≫
          (L.tensor (ofInvertibleIdeal I.subschemeι (ε.ker ^ (n + 1))
            ((Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow (n + 1))
            ha)).trivialization.hom = 𝟙 (𝟙_ I.subscheme.Modules) := by
  rcases isEmpty_or_nonempty I.subscheme with hempty | hnonempty
  · have : IsEmpty I.subscheme := hempty
    obtain ⟨n, s, hs⟩ := L.isInvertible.exists_nonzero_pointTwistSection M.toBase 𝒱 ε hε
    have ha : ∀ y : I.subscheme, I.subschemeι y ∉ (ε.ker ^ (n + 1)).support :=
      fun y => isEmptyElim y
    refine ⟨n, ha, s, hs, ?_⟩
    apply sub_eq_zero.mp
    apply ((Scheme.Modules.isInvertible_unit I.subscheme).zeroSchemeIdeal_eq_bot_iff _).mp
    exact Scheme.IdealSheafData.ext_of_stalkIdeal_eq (fun y => isEmptyElim y)
  · have : Nonempty I.subscheme := hnonempty
    obtain ⟨n, hn⟩ := eventually_exists_normalizedSection M.toBase 𝒱 I hI ε hε hεI L
    obtain ⟨ha, s, hs⟩ := hn n le_rfl
    let P := ofInvertibleIdeal I.subschemeι (ε.ker ^ (n + 1))
      ((Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow (n + 1)) ha
    exact ⟨n, ha, s, normalizedSection_ne_zero (L.tensor P) s hs, hs⟩

private theorem exists_divisor_class_preimage
    (L : RigidifiedLineBundle I.subschemeι) :
    ∃ E : (M.cartierModulus I hI).divAway,
      M.rigidifiedDivisorAwayHom I hI E = Additive.ofMul (classOf L) := by
  obtain ⟨ε, hε, hεI⟩ := exists_point_away_modulus M I hI
  obtain ⟨𝒱, _hV0, _hV1⟩ :=
    SmoothProperCurve.exists_twoAffineOpenCover_of_section K M.toBase ⟨ε, hε⟩
  obtain ⟨N, haQ, s, hs0, hs⟩ :=
    exists_nonzero_normalized_pointTwist M I hI 𝒱 ε hε hεI L
  let Q := ε.ker ^ (N + 1)
  have hQ : Q.IsInvertible := (Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow (N + 1)
  let P := ofInvertibleIdeal I.subschemeι Q hQ haQ
  let J := zeroSchemeIdeal s
  have hJ : J.IsInvertible :=
    (L.tensor P).isInvertible.isInvertible_zeroSchemeIdeal_of_ne_zero s hs0
  have haJ : ∀ y : I.subscheme, I.subschemeι.base y ∉ J.support :=
    normalizedSection_avoids (L.tensor P) s hs
  have hclass : classOf L = classOf (ofInvertibleIdeal I.subschemeι J hJ haJ) / classOf P := by
    apply eq_div_iff_mul_eq'.mpr
    exact (classOf_eq_iff (L.tensor P) (ofInvertibleIdeal I.subschemeι J hJ haJ)).mpr
      ⟨zeroDivisorIso (L.tensor P) s hs J hJ rfl haJ⟩
  let E : Divisor K F := (M.cartierModulus J hJ).toDivisor - (M.cartierModulus Q hQ).toDivisor
  have hEa : E ∈ (M.cartierModulus I hI).divAway :=
    (M.cartierModulus I hI).divAway.sub_mem
      (M.cartierModulus_toDivisor_mem_divAway I hI J hJ haJ)
      (M.cartierModulus_toDivisor_mem_divAway I hI Q hQ haQ)
  refine ⟨⟨E, hEa⟩, ?_⟩
  change M.rigidifiedDivisorHom I hI
    ((M.cartierModulus J hJ).toDivisor - (M.cartierModulus Q hQ).toDivisor) = _
  rw [map_sub, M.rigidifiedDivisorHom_cartierModulus I hI J hJ haJ,
    M.rigidifiedDivisorHom_cartierModulus I hI Q hQ haQ]
  exact congrArg Additive.ofMul hclass.symm

/-- Every actual compatible-isomorphism class is represented by a function-field
divisor away from the whole Cartier modulus, including the empty modulus.
No divisor representative, point outside the modulus, or chart cover is assumed. -/
theorem rigidifiedDivisorAwayHom_surjective :
    Function.Surjective (M.rigidifiedDivisorAwayHom I hI) := by
  intro z
  obtain ⟨L, hLz⟩ := Quotient.exists_rep (Additive.toMul z)
  obtain ⟨E, hE⟩ := exists_divisor_class_preimage M I hI L
  exact ⟨E, hE.trans (congrArg Additive.ofMul hLz)⟩

end AlgebraicCurve.CurveModel
