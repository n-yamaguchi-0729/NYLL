/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Models.Sections.RationalSectionRatio

/-! # An actual meromorphic presentation computes every local section ratio -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite
open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq

namespace AlgebraicGeometry.Scheme.Modules

private theorem topValue_res {X : Scheme.{u}} {L : X.Modules}
    (s : 𝟙_ X.Modules ⟶ L) (U : X.Opens) :
    L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s.app ⊤ (toUnitSection ⊤ 1)) =
      s.app U (toUnitSection U 1) := by
  have hn := ConcreteCategory.congr_hom
    (s.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    (toUnitSection ⊤ 1)
  change s.app U (toUnitSection U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1)) =
    L.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (s.app ⊤ (toUnitSection ⊤ 1)) at hn
  rw [map_one] at hn
  exact hn.symm

private theorem germToFunctionField_topIso {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (a : Γ((U : Scheme.{u}), ⊤)) :
    let _ : Nonempty (U.ι ''ᵁ ⊤) :=
      (Scheme.Opens.ι_image_top U).symm ▸ (inferInstance : Nonempty U)
    X.germToFunctionField U (U.topIso.hom a) = X.germToFunctionField (U.ι ''ᵁ ⊤) a := by
  let : Nonempty (U.ι ''ᵁ ⊤) :=
    (Scheme.Opens.ι_image_top U).symm ▸ (inferInstance : Nonempty U)
  rw [Scheme.Opens.topIso_hom]
  exact X.presheaf.germ_res_apply' _ _ _ a

/-- The ratio in any injective meromorphic presentation equals the ratio of the
actual local coefficients, so prescribing the presentation value prescribes the same function. -/
theorem presentation_ratio_eq_coeff_ratio {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V → ∀ m : Γ(L, U),
      φ V (L.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (s t : 𝟙_ X.Modules ⟶ L) (U : X.affineOpens) [Nonempty U.1]
    (τ : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules) :
    φ ⊤ (s.app ⊤ (toUnitSection ⊤ 1)) / φ ⊤ (t.app ⊤ (toUnitSection ⊤ 1)) =
      X.germToFunctionField U.1 (coeff s U.1 τ.hom) /
        X.germToFunctionField U.1 (coeff t U.1 τ.hom) := by
  let V : X.Opens := U.1.ι ''ᵁ ⊤
  have : Nonempty V := by
    change Nonempty (U.1.ι ''ᵁ ⊤)
    rw [Scheme.Opens.ι_image_top]
    infer_instance
  let e : Γ(L, V) := τ.inv.app ⊤ (toUnitSection ⊤ 1)
  have he : e ≠ 0 := by
    intro hz
    have hz' : toUnitSection (X := (U.1 : Scheme.{u})) ⊤ 1 = 0 :=
      (ConcreteCategory.bijective_of_isIso (τ.inv.app ⊤)).1
        (hz.trans (τ.inv.app ⊤).hom.map_zero.symm)
    exact (one_ne_zero : (1 : Γ(X, V)) ≠ 0) hz'
  have heφ : φ V e ≠ 0 := fun hz => he ((hinj V inferInstance)
    (hz.trans (map_zero (φ V)).symm))
  have hcoord (q : 𝟙_ X.Modules ⟶ L) :
      φ ⊤ (q.app ⊤ (toUnitSection ⊤ 1)) =
        X.germToFunctionField U.1 (coeff q U.1 τ.hom) * φ V e := by
    let a : Γ(X, V) := ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection q U.1))
    have hqa : a • e = restrictSection q U.1 :=
      ZeroSchemeLoc.coord_smul_gen τ ⊤ (restrictSection q U.1)
    calc
      φ ⊤ (q.app ⊤ (toUnitSection ⊤ 1)) = φ V (restrictSection q U.1) :=
        (hnat ⊤ V le_top inferInstance _).symm.trans
          (congrArg (φ V) (topValue_res q V))
      _ = φ V (a • e) := congrArg (φ V) hqa.symm
      _ = X.germToFunctionField V a * φ V e := hsmul V a e
      _ = X.germToFunctionField U.1 (coeff q U.1 τ.hom) * φ V e :=
        congrArg (· * φ V e) (germToFunctionField_topIso U.1 a).symm
  rw [hcoord s, hcoord t, mul_div_mul_right _ _ heφ]

end AlgebraicGeometry.Scheme.Modules
