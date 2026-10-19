/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.ChangeBase

/-! # Geometric fibres retain the full modulus degree -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {C S T T' : Scheme.{u}} {c : C ⟶ S} {t : T ⟶ S} {d : ℕ}
  (D : RelEffCartierDiv c d t) (x : T' ⟶ T)

/-- The actual divisor on the iterated fibre has the directly pulled-back full ideal. -/
theorem relativeDivisor_fibre_ideal :
    ((RelEffCartierDiv.changeBaseEquiv c t x d).symm (D.pullbackAlong x rfl)).I =
      D.I.comap (pullback.fst (pullback.snd c t) x) := by
  change (D.I.comap (mapOnProdOver c x rfl)).comap
      (pullbackLeftPullbackSndIso c t x).hom = _
  rw [← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, mapOnProdOver_fst,
      pullbackLeftPullbackSndIso_hom_fst]
  · rw [Category.assoc, mapOnProdOver_snd, ← Category.assoc,
      pullbackLeftPullbackSndIso_hom_snd, pullback.condition]

/-- Base change retains Cartier invertibility and the degree of every full finite modulus. -/
theorem relativeDivisor_fibre_degree [IsProper c] [SmoothOfRelativeDimension 1 c] :
    let J := D.I.comap (pullback.fst (pullback.snd c t) x)
    J.IsInvertible ∧ IsFinite (J.subschemeι ≫ pullback.snd (pullback.snd c t) x) ∧
      ∀ z : T', (J.subschemeι ≫ pullback.snd (pullback.snd c t) x).finrank z = d := by
  let E := (RelEffCartierDiv.changeBaseEquiv c t x d).symm (D.pullbackAlong x rfl)
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {Y Z : Scheme.{u}} (a : Y ⟶ Z) => SmoothOfRelativeDimension 1 a) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {Y Z : Scheme.{u}} (a : Y ⟶ Z) => SmoothOfRelativeDimension 1 a)
      (IsPullback.of_hasPullback c t) inferInstance
  change (D.I.comap _).IsInvertible ∧ _
  rw [← relativeDivisor_fibre_ideal D x]
  exact ⟨RelEffCartierDiv.isInvertible_I E, E.isFinite, E.finrank_eq⟩

end AlgebraicGeometry.GeneralizedJacobian
