/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPullbackInvModuleIso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPow
import Nyll.SchemeTheory.Sheaves.IdealSheafComap
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The actual point-power twist under arbitrary base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {X S T : Scheme.{u}} (c : X ⟶ S) (ε : S ⟶ X) (hε : ε ≫ c = 𝟙 S)
  (t : T ⟶ S)

/-- The specified section on the actual pulled-back curve. -/
def sectionBaseChange : T ⟶ pullback c t :=
  pullback.lift (t ≫ ε) (𝟙 T) (by rw [Category.assoc, hε, Category.comp_id, Category.id_comp])

@[reassoc] theorem sectionBaseChange_snd : sectionBaseChange c ε hε t ≫ pullback.snd c t =
    𝟙 T := pullback.lift_snd _ _ _

/-- A section square is cartesian, with the same specified base-changed section. -/
theorem sectionBaseChange_isPullback :
    IsPullback (sectionBaseChange c ε hε t) t (pullback.fst c t) ε := by
  refine IsPullback.of_right (h₁₂ := pullback.snd c t) (v₁₃ := t) (h₂₂ := c)
    ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback c t).flip
  rw [sectionBaseChange_snd, hε]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

/-- Pullback retains the full graph ideal of the section. -/
theorem sectionBaseChange_ker [IsSeparated c] :
    ε.ker.comap (pullback.fst c t) = (sectionBaseChange c ε hε t).ker := by
  have : IsClosedImmersion (ε ≫ c) := hε ▸ inferInstance
  have : IsClosedImmersion ε := IsClosedImmersion.of_comp ε c
  have h := sectionBaseChange_isPullback c ε hε t
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

private theorem comap_ideal_pow (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.one_eq_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

/-- The inverse ideal of every power is transported by the actual fibre pullback. -/
def sectionPowerBaseChangeIso [IsSeparated c] [SmoothOfRelativeDimension 1 c] (n : ℕ) :
    (Scheme.Modules.pullback (pullback.fst c t)).obj (ε.ker ^ n).invModule ≅
      ((sectionBaseChange c ε hε t).ker ^ n).invModule := by
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {Y Z : Scheme.{u}} (g : Y ⟶ Z) => SmoothOfRelativeDimension 1 g) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {Y Z : Scheme.{u}} (g : Y ⟶ Z) => SmoothOfRelativeDimension 1 g)
      (IsPullback.of_hasPullback c t) inferInstance
  have hp := (Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow n
  have hp' := (Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (sectionBaseChange c ε hε t) (sectionBaseChange_snd c ε hε t)).pow n
  have he : (ε.ker ^ n).comap (pullback.fst c t) =
      (sectionBaseChange c ε hε t).ker ^ n := by
    rw [comap_ideal_pow, sectionBaseChange_ker]
  have hi : ((ε.ker ^ n).comap (pullback.fst c t)).IsInvertible := by
    rw [he]
    exact hp'
  exact Classical.choice (hp.nonempty_pullback_invModule_iso (pullback.fst c t) hi) ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.invModule he)

end AlgebraicGeometry.GeneralizedJacobian
