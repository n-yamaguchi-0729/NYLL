/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleGenericPointNotMemSupportZeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleCoeffIdealLeIdealZeroSchemeIdealEq
import Mathlib.AlgebraicGeometry.Properties

/-! # A nonzero section of a line bundle on an integral scheme is Cartier -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- Local coefficients of a nonzero line-bundle section are nonzero in the
integral coordinate rings, hence give an actual invertible zero-scheme ideal. -/
theorem isInvertible_zeroSchemeIdeal_of_ne_zero
    {X : Scheme.{u}} [IsIntegral X] {L : X.Modules}
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L) (hs : s ≠ 0) :
    (Scheme.Modules.zeroSchemeIdeal s).IsInvertible := by
  let I := Scheme.Modules.zeroSchemeIdeal s
  have hη : genericPoint X ∉ I.support := hL.genericPoint_notMem_support_zeroSchemeIdeal s hs
  intro x
  obtain ⟨U, hxU, _hUtop, ⟨τ⟩⟩ := hL.exists_restrict_iso (V := ⊤) (x := x) trivial
  let V := X.affineBasicOpen (1 : Γ(X, U.1))
  have hxV : x ∈ V.1 := by
    change x ∈ X.basicOpen (1 : Γ(X, U.1))
    simpa only [Scheme.basicOpen_one] using hxU
  have hVU : V.1 ≤ U.1 := X.basicOpen_le _
  let g : Γ(X, V.1) := X.presheaf.map (homOfLE hVU).op
    (Scheme.Modules.coeff s U.1 τ.hom)
  have hspan : I.ideal V = Ideal.span {g} := by
    rw [← I.map_ideal hVU,
      ((hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U τ).1,
      Ideal.map_span, Set.image_singleton]
    rfl
  have : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  have hg : g ≠ 0 := by
    intro hg0
    have hηV : genericPoint X ∈ V.1 :=
      ((genericPoint_spec X).mem_open_set_iff V.1.isOpen).mpr ⟨x, Set.mem_univ x, hxV⟩
    apply hη
    apply (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := V) hηV).mpr
    rw [hspan, hg0, Ideal.span_singleton_zero, Scheme.mem_zeroLocus_iff]
    intro f hf
    have hf0 : f = 0 := hf
    rw [hf0, Scheme.basicOpen_zero]
    exact fun h => h
  exact ⟨U, 1, hxV, g, mem_nonZeroDivisors_iff_ne_zero.mpr hg, hspan⟩

end AlgebraicGeometry.Scheme.Modules.IsInvertible
