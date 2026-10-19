/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionCounit
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Iso

/-!
# The original quotient unit on modules supported on a closed subscheme

The right triangle identity and the actual closed-immersion counit
show that the unit on a quasicoherent direct image is invertible.
Naturality transports this statement along a given module isomorphism.
For a morphism that is invertible after pullback, the same naturality
constructs a comparison from its original pullback quotient to its
target, retaining the original morphism after composition with the unit.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The original quotient unit on the direct image of a
quasicoherent module from a closed subscheme is invertible. -/
theorem isIso_pullbackUnit_pushforward_of_isClosedImmersion [IsClosedImmersion f]
    (N : X.Modules) [N.IsQuasicoherent] :
    IsIso ((pullbackPushforwardAdjunction f).unit.app ((pushforward f).obj N)) := by
  let adj : pullback f ⊣ pushforward f := pullbackPushforwardAdjunction f
  let ε : (pullback f).obj ((pushforward f).obj N) ⟶ N := adj.counit.app N
  have : IsIso ε := isIso_pullbackCounit_of_isClosedImmersion f N
  have h : adj.unit.app ((pushforward f).obj N) ≫ (pushforward f).map ε =
      𝟙 ((pushforward f).obj N) := adj.right_triangle_components N
  exact IsIso.of_isIso_fac_right h

/-- The original quotient unit is invertible for any module
identified with an actual quasicoherent direct image from the closed subscheme. -/
theorem isIso_pullbackUnit_of_iso_pushforward [IsClosedImmersion f]
    (P : Y.Modules) (N : X.Modules) [N.IsQuasicoherent]
    (e : P ≅ (pushforward f).obj N) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app P) := by
  let adj : pullback f ⊣ pushforward f := pullbackPushforwardAdjunction f
  let F : Y.Modules ⥤ Y.Modules := pullback f ⋙ pushforward f
  have : IsIso (adj.unit.app ((pushforward f).obj N)) :=
    isIso_pullbackUnit_pushforward_of_isClosedImmersion f N
  have h : adj.unit.app P ≫ F.map e.hom =
      e.hom ≫ adj.unit.app ((pushforward f).obj N) := (adj.unit.naturality e.hom).symm
  exact IsIso.of_isIso_fac_right h

variable {P Q : Y.Modules} (σ : P ⟶ Q)
  [IsIso ((pullbackPushforwardAdjunction f).unit.app Q)]
  [IsIso ((pullback f).map σ)]

/-- The actual pullback of a morphism and the inverse original
target unit identify its pullback quotient with its target. -/
def pullbackQuotientComparisonIso :
    (pushforward f).obj ((pullback f).obj P) ≅ Q :=
  (pushforward f).mapIso (asIso ((pullback f).map σ)) ≪≫
    (asIso ((pullbackPushforwardAdjunction f).unit.app Q)).symm

/-- The constructed quotient comparison uses the original
pullback of the supplied morphism and the original target unit. -/
theorem pullbackQuotientComparisonIso_hom :
    (pullbackQuotientComparisonIso f σ).hom =
      (pushforward f).map ((pullback f).map σ) ≫
        inv ((pullbackPushforwardAdjunction f).unit.app Q) := rfl

/-- Composing the constructed comparison with the original source
unit recovers the original morphism. -/
theorem unit_pullbackQuotientComparisonIso_hom :
    (pullbackPushforwardAdjunction f).unit.app P ≫
      (pullbackQuotientComparisonIso f σ).hom = σ := by
  let adj : pullback f ⊣ pushforward f := pullbackPushforwardAdjunction f
  let ηP : P ⟶ (pushforward f).obj ((pullback f).obj P) := adj.unit.app P
  let ηQ : Q ⟶ (pushforward f).obj ((pullback f).obj Q) := adj.unit.app Q
  let β : (pushforward f).obj ((pullback f).obj P) ⟶
      (pushforward f).obj ((pullback f).obj Q) := (pushforward f).map ((pullback f).map σ)
  have h : ηP ≫ β = σ ≫ ηQ := (adj.unit.naturality σ).symm
  calc
    ηP ≫ (β ≫ inv ηQ) = (ηP ≫ β) ≫ inv ηQ := (Category.assoc ηP β (inv ηQ)).symm
    _ = (σ ≫ ηQ) ≫ inv ηQ := congrArg (fun k => k ≫ inv ηQ) h
    _ = σ := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
