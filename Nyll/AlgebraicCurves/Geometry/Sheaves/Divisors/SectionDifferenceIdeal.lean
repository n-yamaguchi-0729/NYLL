/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.SectionZeroScheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleComapZeroSchemeIdeal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleCoeffIdealLeIdealZeroSchemeIdealEq
import Nyll.SchemeTheory.Divisors.StalkIdealSupport

/-! # Equality of sections on a closed subscheme retains its full ideal -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} {L : X.Modules}

/-- Local coefficients commute with subtraction of global sections. -/
theorem coeff_sub (s t : 𝟙_ X.Modules ⟶ L) (U : X.Opens)
    (φ : L.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff (s - t) U φ = coeff s U φ - coeff t U φ := by
  have hc : ofUnitSection ⊤ (φ.app ⊤ (restrictSection (s - t) U)) =
      ofUnitSection ⊤ (φ.app ⊤ (restrictSection s U)) -
        ofUnitSection ⊤ (φ.app ⊤ (restrictSection t U)) :=
    (φ.app ⊤).hom.map_sub (restrictSection s U) (restrictSection t U)
  exact (congrArg U.topIso.hom.hom hc).trans (map_sub U.topIso.hom.hom _ _)

/-- The zero section has the zero ideal, including on nonreduced schemes. -/
theorem zeroSchemeIdeal_zero : zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ L) = ⊥ := by
  apply le_antisymm _ bot_le
  apply zeroSchemeIdeal_le
  intro U
  rw [coeffIdeal, Ideal.span_le]
  rintro _ ⟨φ, rfl⟩
  change coeff (0 : 𝟙_ X.Modules ⟶ L) U.1 φ = 0
  have hc : ofUnitSection ⊤ (φ.app ⊤ (restrictSection (0 : 𝟙_ X.Modules ⟶ L) U.1)) = 0 :=
    (φ.app ⊤).hom.map_zero
  exact (congrArg U.1.topIso.hom.hom hc).trans (map_zero U.1.topIso.hom.hom)

/-- Pullback preserves subtraction of global line-bundle sections. -/
theorem pullbackSection_sub (i : Y ⟶ X) (s t : 𝟙_ X.Modules ⟶ L) :
    pullbackSection i (s - t) = pullbackSection i s - pullbackSection i t := by
  have hmap : (Scheme.Modules.pullback i).map (s - t) =
      (Scheme.Modules.pullback i).map s - (Scheme.Modules.pullback i).map t :=
    Functor.map_sub (Scheme.Modules.pullback i) (f := s) (g := t)
  exact (congrArg ((pullbackUnitIso i).inv ≫ ·) hmap).trans
    (Preadditive.comp_sub (pullbackUnitIso i).inv
      ((Scheme.Modules.pullback i).map s) ((Scheme.Modules.pullback i).map t))

/-- A section vanishing after pullback has its full zero ideal inside the
kernel of the morphism. -/
theorem IsInvertible.zeroSchemeIdeal_le_ker_of_pullback_zero
    (hL : Scheme.Modules.IsInvertible L) (i : Y ⟶ X)
    (s : 𝟙_ X.Modules ⟶ L) (hs : pullbackSection i s = 0) :
    zeroSchemeIdeal s ≤ i.ker := by
  rw [← Scheme.IdealSheafData.map_bot i,
    Scheme.IdealSheafData.le_map_iff_comap_le,
    hL.comap_zeroSchemeIdeal i s, hs, zeroSchemeIdeal_zero]

/-- Equal restrictions of sections give containment in the original closed
subscheme ideal, with no replacement by its radical. -/
theorem IsInvertible.zeroSchemeIdeal_sub_le_of_pullback_eq
    (hL : Scheme.Modules.IsInvertible L) (I : X.IdealSheafData)
    (s t : 𝟙_ X.Modules ⟶ L)
    (hst : pullbackSection I.subschemeι s = pullbackSection I.subschemeι t) :
    zeroSchemeIdeal (s - t) ≤ I := by
  rw [← I.ker_subschemeι]
  apply hL.zeroSchemeIdeal_le_ker_of_pullback_zero I.subschemeι (s - t)
  rw [pullbackSection_sub, hst, sub_self]

/-- In every local trivialization, equal restricted sections have coefficient
difference in the full ideal of the original closed subscheme. -/
theorem IsInvertible.coeff_sub_mem_ideal_of_pullback_eq
    (hL : Scheme.Modules.IsInvertible L) (I : X.IdealSheafData)
    (s t : 𝟙_ X.Modules ⟶ L)
    (hst : pullbackSection I.subschemeι s = pullbackSection I.subschemeι t)
    (U : X.affineOpens) (φ : L.restrict U.1.ι ⟶ 𝟙_ (U.1 : Scheme.{u}).Modules) :
    coeff s U.1 φ - coeff t U.1 φ ∈ I.ideal U := by
  have hle := hL.zeroSchemeIdeal_sub_le_of_pullback_eq I s t hst
  apply hle U
  rw [← coeff_sub]
  exact (hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq (s - t)).1 U
    (coeff_mem_coeffIdeal (s - t) U.1 φ)

/-- The same full-ideal containment holds in every actual scheme stalk. -/
theorem IsInvertible.coeff_germ_sub_mem_stalkIdeal_of_pullback_eq
    (hL : Scheme.Modules.IsInvertible L) (I : X.IdealSheafData)
    (s t : 𝟙_ X.Modules ⟶ L)
    (hst : pullbackSection I.subschemeι s = pullbackSection I.subschemeι t)
    (U : X.affineOpens) (φ : L.restrict U.1.ι ⟶ 𝟙_ (U.1 : Scheme.{u}).Modules)
    (x : X) (hx : x ∈ U.1) :
    X.presheaf.germ U.1 x hx (coeff s U.1 φ) -
      X.presheaf.germ U.1 x hx (coeff t U.1 φ) ∈ I.stalkIdeal x := by
  rw [← map_sub]
  exact I.map_ideal_le_stalkIdeal x U hx
    (Ideal.mem_map_of_mem (X.presheaf.germ U.1 x hx).hom
      (hL.coeff_sub_mem_ideal_of_pullback_eq I s t hst U φ))

/-- The germ of the coefficient in an actual frame is a unit wherever the
section has no zero. -/
theorem IsInvertible.isUnit_coeff_germ_of_notMem_support
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ X.Modules ⟶ L)
    (U : X.affineOpens) (τ : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
    (x : X) (hx : x ∈ U.1) (hs : x ∉ (zeroSchemeIdeal s).support) :
    IsUnit (X.presheaf.germ U.1 x hx (coeff s U.1 τ.hom)) := by
  apply Ideal.span_singleton_eq_top.mp
  rw [← Set.image_singleton, ← Ideal.map_span,
    ← ((hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U τ).1,
    ← (zeroSchemeIdeal s).stalkIdeal_eq_map_ideal x U hx]
  exact ((zeroSchemeIdeal s).stalkIdeal_eq_top_iff_notMem_support x).mpr hs

end AlgebraicGeometry.Scheme.Modules
