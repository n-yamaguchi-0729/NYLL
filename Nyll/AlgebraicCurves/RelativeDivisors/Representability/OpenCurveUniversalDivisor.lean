/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Charts.IsAffineOpenMemFinsetField
import Nyll.AlgebraicCurves.Geometry.Schemes.Affine.IsAffineOpenOpensLePreimageMem
import Nyll.AlgebraicCurves.RelativeDivisors.Representability.IsUniversal
import Nyll.AlgebraicCurves.RelativeDivisors.Representability.SupportedInUniversal
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # Actual universal effective divisors on an open smooth proper curve -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.RelEffCartierDiv

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

private theorem open_affine_cover (U : C.Opens)
    (V : (Spec (CommRingCat.of K)).affineOpens) (F : Finset U)
    (hF : ∀ x ∈ F, (U.ι ≫ c) x ∈ V.1) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧
      W ≤ (U.ι ≫ c) ⁻¹ᵁ V.1 ∧ ∀ x ∈ F, x ∈ W := by
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  exact exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
    (AlgebraicCurve.exists_isAffineOpen_forall_mem_of_finset_of_field c)
    U (c ⁻¹ᵁ V.1) F hF

/-- The actual divisor functor of every open subscheme is represented.
The affine-cover prerequisite is supplied by the proper curve. -/
theorem exists_isUniversal_on_open (U : C.Opens) (n : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of K))
      (E : RelEffCartierDiv (U.ι ≫ c) n y), E.IsUniversal := by
  have : SmoothOfRelativeDimension 1 (U.ι ≫ c) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ c))
  exact exists_isUniversal (U.ι ≫ c) (open_affine_cover c U) n

/-- The actual degree-`n` divisor family supported away from a closed modulus
is represented on the original proper curve, with no affine-cover hypothesis. -/
theorem exists_supportedIn_universal_on_open (U : C.Opens) (n : ℕ) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of K))
      (E : RelEffCartierDiv c n y), E.SupportedIn U ∧
      ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of K))
        (A : RelEffCartierDiv c n t), A.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = t}, PullsBackOver E φ.1 φ.2 A := by
  have : SmoothOfRelativeDimension 1 (U.ι ≫ c) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ c))
  exact exists_supportedIn_universal_of_smooth_opens c U (open_affine_cover c U) n

end AlgebraicGeometry.RelEffCartierDiv
