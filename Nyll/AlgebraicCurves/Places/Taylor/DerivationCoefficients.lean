/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_D_ne_zero_of_ord_ne_zero.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_eq_smul_D_of_ord_ne_zero.lean
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).

Source-file correspondence is unconfirmed for:
Place_D_ne_zero_of_ord_eq_one
Place_diffCoeff_smul_D_of_ord_eq_one
Place_derivation_apply_eq_diffCoeff_D_mul
Place_kaehlerD_ne_zero_of_ord_eq_one
-/

import Nyll.AlgebraicCurves.Places.Orders.SeparableAdjoinOrdEqOne
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialDNeZero
import Nyll.AlgebraicCurves.Places.Orders.TranscendentalOrdNeZero
import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferentialSpanDEqTop
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.IsAlgebraicAdjoinTranscendental
import Nyll.AlgebraicCurves.Places.Basic
import Mathlib.FieldTheory.Perfect

/-!
# Local differential coefficients

Nonvanishing and generation of differentials come from the same separable simple extension.
The characteristic-zero statements share that construction; order-one statements use the
existing separability theorem over a perfect base field.
-/

noncomputable section

open AlgebraicCurve KaehlerDifferential

private theorem separable_adjoin_of_place_order_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F := by
  have : Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental x (v.transcendental_of_ord_ne_zero ht)
  have : CharZero (IntermediateField.adjoin K ({t} : Set F)) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  infer_instance

theorem _root_.AlgebraicCurve.Place.D_ne_zero_of_ord_eq_one {K F : Type*} [Field K] [Field F]
  [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) :
    KaehlerDifferential.D K F t ≠ 0 := by
  have : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v ht
  exact KaehlerDifferential.D_ne_zero_of_transcendental K t
    (v.transcendental_of_ord_ne_zero (ht ▸ one_ne_zero))

theorem _root_.AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero {K F : Type*} [Field K] [Field F]
  [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {t : F} (ht : v.ord t ≠ 0) :
    KaehlerDifferential.D K F t ≠ 0 := by
  have : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
    separable_adjoin_of_place_order_ne_zero x v ht
  exact KaehlerDifferential.D_ne_zero_of_transcendental K t
    (v.transcendental_of_ord_ne_zero ht)

theorem _root_.AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero {K F : Type*} [Field K] [Field
  F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    ∃ g : F, ω = g • KaehlerDifferential.D K F t := by
  have : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
    separable_adjoin_of_place_order_ne_zero x v ht
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K t
    (v.transcendental_of_ord_ne_zero ht)
  have hω : ω ∈ Submodule.span F {D K F t} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hω
  exact ⟨g, hg.symm⟩

theorem _root_.AlgebraicCurve.Place.diffCoeff_smul_D_eq {K F : Type*} [Field K] [Field F] [Algebra
  K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {t : F} (ht : v.ord t ≠ 0) (g : F) :
    AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t) = g :=
  smul_left_injective F (AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero x v ht)
    (AlgebraicCurve.Place.diffCoeff_smul_D ⟨g, rfl⟩)

theorem _root_.AlgebraicCurve.Place.diffCoeff_smul_D_eq_of_ord_eq_one {K F : Type*} [Field K]
  [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (g : F) :
    AlgebraicCurve.Place.diffCoeff t (g • KaehlerDifferential.D K F t) = g :=
  smul_left_injective F (AlgebraicCurve.Place.D_ne_zero_of_ord_eq_one x v ht)
    (AlgebraicCurve.Place.diffCoeff_smul_D ⟨g, rfl⟩)

theorem _root_.AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_ne_zero {K F : Type*} [Field K] [Field
  F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {t : F} (ht : v.ord t ≠ 0) (ω : Ω[F⁄K]) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω :=
  AlgebraicCurve.Place.diffCoeff_smul_D
    (AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero x v ht ω)

theorem _root_.AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_eq_one {K F : Type*} [Field K] [Field
  F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t = 1) (ω : Ω[F⁄K]) :
    AlgebraicCurve.Place.diffCoeff t ω • KaehlerDifferential.D K F t = ω := by
  have : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v ht
  have hspan := KaehlerDifferential.span_D_eq_top_of_transcendental K t
    (v.transcendental_of_ord_ne_zero (ht ▸ one_ne_zero))
  have hω : ω ∈ Submodule.span F {D K F t} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hω
  exact AlgebraicCurve.Place.diffCoeff_smul_D ⟨g, hg.symm⟩

theorem _root_.AlgebraicCurve.Place.derivation_apply_eq_diffCoeff_D_mul
    {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {t : F} (ht : v.ord t = 1) (δ : Derivation K F F) (f : F) :
    δ f = Place.diffCoeff t (KaehlerDifferential.D K F f) * δ t :=
  calc δ f = δ.liftKaehlerDifferential (KaehlerDifferential.D K F f) :=
        (Derivation.liftKaehlerDifferential_comp_D δ f).symm
    _ = δ.liftKaehlerDifferential
          (Place.diffCoeff t (KaehlerDifferential.D K F f) • KaehlerDifferential.D K F t) := by
        rw [Place.diffCoeff_smul_D_of_ord_eq_one x v ht]
    _ = Place.diffCoeff t (KaehlerDifferential.D K F f) * δ t := by
        rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul]

theorem _root_.AlgebraicCurve.Place.kaehlerD_ne_zero_of_ord_eq_one {K F : Type*} [Field K] [Field
  F] [Algebra K F] [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K
      F) {t : F} (ht : v.ord t = 1) :
    KaehlerDifferential.D K F t ≠ 0 := AlgebraicCurve.Place.D_ne_zero_of_ord_eq_one x v ht

end
