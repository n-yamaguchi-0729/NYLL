/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelFamily
import Nyll.JacobianVarieties.Generalized.ModulusScalarExtension
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The actual open complement under base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)

/-- The inclusion of the full base-changed modulus is the actual pullback of its inclusion. -/
theorem isPullback_modulusBaseChange {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (modulusBaseChange c i t) (pullback.fst (i ≫ c) t)
      (pullback.fst c t) i := by
  refine IsPullback.of_right (h₁₂ := pullback.snd c t)
    (v₁₃ := t) (h₂₂ := c) ?_ (modulusBaseChange_fst c i t)
      (IsPullback.of_hasPullback c t).flip
  rw [modulusBaseChange_snd]
  exact (IsPullback.of_hasPullback (i ≫ c) t).flip

instance {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i] :
    IsClosedImmersion (modulusBaseChange c i t) :=
  MorphismProperty.of_isPullback (isPullback_modulusBaseChange c i t).flip inferInstance

/-- Scheme-theoretic support, including multiplicities, has the expected open complement. -/
theorem modulusComplement_baseChange {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i] :
    modulusComplement (modulusBaseChange c i t) =
      pullback.fst c t ⁻¹ᵁ modulusComplement i := by
  have h := isPullback_modulusBaseChange c i t
  have hker : (modulusBaseChange c i t).ker = i.ker.comap (pullback.fst c t) := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  unfold modulusComplement
  rw [hker, Scheme.IdealSheafData.support_comap]
  rfl

/-- The actual extended open curve maps to the original open curve. -/
def modulusComplementBaseChangeMap {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i] :
    (modulusComplement (modulusBaseChange c i t)).toScheme ⟶
      (modulusComplement i).toScheme :=
  (pullback.fst c t).resLE (modulusComplement i)
    (modulusComplement (modulusBaseChange c i t))
    (le_of_eq (modulusComplement_baseChange c i t))

@[reassoc] theorem modulusComplementBaseChangeMap_ι {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i] :
    modulusComplementBaseChangeMap c i t ≫ (modulusComplement i).ι =
      (modulusComplement (modulusBaseChange c i t)).ι ≫ pullback.fst c t :=
  Scheme.Hom.resLE_comp_ι _ _

end AlgebraicGeometry.GeneralizedJacobian
