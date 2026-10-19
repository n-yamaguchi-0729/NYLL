/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Sections.RationalSectionRatio
import Nyll.AlgebraicCurves.Models.Divisors.CartierGeneratorOrder
import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.NonzeroSectionCartier

/-!
# The divisor of the actual ratio of two line-bundle sections

Every local frame computes the global rational ratio constructed from the
meromorphic presentation. Its order is the difference of the two actual
Cartier multiplicities, including all nonreduced multiplicities. The formula
is available for any function with these local ratios, so a separately proved
modulus congruence applies to the very same function.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) {L : M.C.Modules} (hL : Scheme.Modules.IsInvertible L)
  (s t : 𝟙_ M.C.Modules ⟶ L) (hs : s ≠ 0) (ht : t ≠ 0)

/-- The local ratios determine the divisor of the given rational function.
The proof uses actual zero-scheme ideals and their full stalk multiplicities. -/
theorem rationalSectionRatio_divisor (f : F)
    (hratio : ∀ (U : M.C.affineOpens) [Nonempty U.1]
      (τ : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
      f = M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff s U.1 τ.hom)) /
        M.ffEquiv.symm (M.C.germToFunctionField U.1 (coeff t U.1 τ.hom)))
    (w : Place K F) :
    ((M.cartierModulus (zeroSchemeIdeal s)
        (hL.isInvertible_zeroSchemeIdeal_of_ne_zero s hs)).toDivisor -
      (M.cartierModulus (zeroSchemeIdeal t)
        (hL.isInvertible_zeroSchemeIdeal_of_ne_zero t ht)).toDivisor) w = w.ord f := by
  let x := M.placeEquiv.symm w
  let I := zeroSchemeIdeal s
  let J := zeroSchemeIdeal t
  have hI : I.IsInvertible := hL.isInvertible_zeroSchemeIdeal_of_ne_zero s hs
  have hJ : J.IsInvertible := hL.isInvertible_zeroSchemeIdeal_of_ne_zero t ht
  obtain ⟨U, hxU, _hUtop, ⟨τ⟩⟩ := hL.exists_restrict_iso (V := ⊤) (x := x.1) trivial
  have : Nonempty U.1 := ⟨⟨x.1, hxU⟩⟩
  have hIs : I.stalkIdeal x.1 =
      Ideal.span {(M.C.presheaf.germ U.1 x.1 hxU).hom (coeff s U.1 τ.hom)} := by
    rw [I.stalkIdeal_eq_map_ideal x.1 U hxU,
      ((hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U τ).1,
      Ideal.map_span, Set.image_singleton]
  have hJt : J.stalkIdeal x.1 =
      Ideal.span {(M.C.presheaf.germ U.1 x.1 hxU).hom (coeff t U.1 τ.hom)} := by
    rw [J.stalkIdeal_eq_map_ideal x.1 U hxU,
      ((hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq t).2 U τ).1,
      Ideal.map_span, Set.image_singleton]
  have ho := M.ord_stalkGenerator_ratio I hI J hJ x _ _ hIs hJt
  simp only [M.C.algebraMap_germ_eq_germToFunctionField hxU] at ho
  rw [← hratio U τ] at ho
  have hwx : M.placeOfPoint x = w := M.placeEquiv.apply_symm_apply w
  rw [hwx] at ho
  change (M.cartierMultiplicity I hI x : ℤ) -
    (M.cartierMultiplicity J hJ x : ℤ) = w.ord f
  exact ho.symm

/-- The constructed global rational function has exactly the difference of
the two actual effective Cartier divisors as its principal divisor. -/
theorem exists_rationalSectionRatio_divisor :
    ∃ f : F, f ≠ 0 ∧ ∀ w : Place K F,
      ((M.cartierModulus (zeroSchemeIdeal s)
          (hL.isInvertible_zeroSchemeIdeal_of_ne_zero s hs)).toDivisor -
        (M.cartierModulus (zeroSchemeIdeal t)
          (hL.isInvertible_zeroSchemeIdeal_of_ne_zero t ht)).toDivisor) w = w.ord f := by
  obtain ⟨f, hf, hratio⟩ := M.exists_rationalSectionRatio hL s t hs ht
  exact ⟨f, hf, M.rationalSectionRatio_divisor hL s t hs ht f hratio⟩

end AlgebraicCurve.CurveModel
