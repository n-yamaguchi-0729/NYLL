/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.ModulusIdeal

/-!
# Order comparison for the actual ideal sheaves of moduli

Increasing the multiplicities decreases the ideal sheaf, and inclusion of the
actual ideal sheaves recovers the reverse coefficientwise order. The latter
implication follows from the lengths of the local quotients, so it detects all
multiplicities, including those at non-rational closed points.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve.Modulus

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K))
  [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- Increasing a modulus decreases its actual defining ideal sheaf. -/
theorem curveIdeal_antitone :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    Antitone (curveIdeal c) := by
  intro _functionFieldAlgebra E D hED
  obtain ⟨F, rfl⟩ := exists_add_of_le hED
  rw [curveIdeal_add c E F]
  intro U
  exact Ideal.mul_le_left

/-- Inclusion of the actual modulus ideals is exactly the reverse order on
the original multiplicities. -/
theorem curveIdeal_le_iff :
    let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
    ∀ D E : Modulus K C.functionField,
      curveIdeal c D ≤ curveIdeal c E ↔ E ≤ D := by
  intro _functionFieldAlgebra D E
  constructor
  · intro hDE v
    apply ENat.natCast_le_natCast.mp
    rw [← curveIdeal_local_length c E v, ← curveIdeal_local_length c D v,
      Module.length_quotient, Module.length_quotient]
    exact Order.coheight_anti
      (Scheme.IdealSheafData.stalkIdeal_mono hDE (pointOfPlace c v))
  · intro hED
    exact curveIdeal_antitone c hED

end AlgebraicCurve.Modulus
