/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.SectionDifferenceIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.InvertibleEqPullbackSectionEq
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
import Mathlib.AlgebraicGeometry.Properties

/-! # Full closed-subscheme vanishing detected by coefficient ideals -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq.AlgebraicGeometry.R4bAux

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} {L : X.Modules}

/-- The zero ideal detects the zero section of an invertible module on an
arbitrary scheme, including schemes with nilpotents. -/
theorem IsInvertible.zeroSchemeIdeal_eq_bot_iff
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) :
    zeroSchemeIdeal s = ⊥ ↔ s = 0 := by
  constructor
  · exact eq_zero_of_zeroSchemeIdeal_eq_bot hL s
  · rintro rfl
    exact zeroSchemeIdeal_zero

/-- Containment in the original kernel ideal is equivalent to vanishing
after pullback; no reducedness assumption is used. -/
theorem IsInvertible.zeroSchemeIdeal_le_ker_iff_pullback_eq_zero
    (hL : Scheme.Modules.IsInvertible L) (i : Y ⟶ X) (s : 𝟙_ X.Modules ⟶ L) :
    zeroSchemeIdeal s ≤ i.ker ↔ pullbackSection i s = 0 := by
  rw [← Scheme.IdealSheafData.map_bot i,
    Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff,
    hL.comap_zeroSchemeIdeal i s]
  exact (hL.pullback i).zeroSchemeIdeal_eq_bot_iff (pullbackSection i s)

/-- Equal restrictions are detected by containment of the coefficient
difference ideal in the full defining ideal of a closed subscheme. -/
theorem IsInvertible.pullbackSection_eq_iff_zeroSchemeIdeal_sub_le
    (hL : Scheme.Modules.IsInvertible L) (I : X.IdealSheafData)
    (s t : 𝟙_ X.Modules ⟶ L) :
    pullbackSection I.subschemeι s = pullbackSection I.subschemeι t ↔
      zeroSchemeIdeal (s - t) ≤ I := by
  have h := hL.zeroSchemeIdeal_le_ker_iff_pullback_eq_zero I.subschemeι (s - t)
  rw [I.ker_subschemeι, pullbackSection_sub, sub_eq_zero] at h
  exact h.symm

/-- A Cartier zero ideal on an integral nonempty scheme cannot come from
the zero section. -/
theorem ne_zero_of_zeroSchemeIdeal_isInvertible [IsIntegral X]
    (s : 𝟙_ X.Modules ⟶ L) (h : (zeroSchemeIdeal s).IsInvertible) : s ≠ 0 := by
  intro hs
  obtain ⟨U, f, hη, g, hg, hideal⟩ := h (genericPoint X)
  have : Nonempty (X.affineBasicOpen f).1 := ⟨⟨genericPoint X, hη⟩⟩
  have hz : (zeroSchemeIdeal s).ideal (X.affineBasicOpen f) = ⊥ := by
    rw [hs, zeroSchemeIdeal_zero]
    rfl
  exact (nonZeroDivisors.ne_zero hg)
    (Ideal.span_singleton_eq_bot.mp (hideal.symm.trans hz))

end AlgebraicGeometry.Scheme.Modules
