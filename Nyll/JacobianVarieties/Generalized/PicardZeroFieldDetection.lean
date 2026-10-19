/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroGroupFunctor
import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.AbelJacobiFamily

/-! # Detecting the modulus zero condition after geometric-point restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D T : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)
  (t : T ⟶ Spec (CommRingCat.of R))

/-- Restriction to all algebraically closed field-valued tests detects the actual zero condition. -/
theorem modulusPicardZero_of_fieldRestrictions
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t))
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      (modulusPicardGroupPresheaf c i).map
        (Over.homMk s rfl : Over.mk (s ≫ t) ⟶ Over.mk t).op x ∈
          modulusPicardZeroSubgroup c i (Over.mk (s ≫ t))) :
    x ∈ modulusPicardZeroSubgroup c i (Over.mk t) := by
  induction x using Quotient.ind with
  | _ M =>
    intro k _ _ s
    let ψ : SchemeHomOver (s ≫ t) t := ⟨s, rfl⟩
    let f := baseChangeSnd c ψ
    have hz := h k s
    have hfield := hz k (𝟙 (Spec (CommRingCat.of k)))
    let a := pullback.snd c (s ≫ t)
    let κ := pullbackLeftPullbackSndIso c t s
    let e := κ.hom ≫ toProdSpec a
    have hκ : κ.hom ≫ f = pullback.fst (pullback.snd c t) s := by
      apply pullback.hom_ext
      · simp only [f, baseChangeSnd, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, pullbackLeftPullbackSndIso_hom_fst, Category.comp_id]
      · rw [Category.assoc, baseChangeSnd_snd, ← Category.assoc,
          pullbackLeftPullbackSndIso_hom_snd, pullback.condition]
    have he : e ≫ fibreAt c (s ≫ t) (𝟙 (Spec (CommRingCat.of k))) =
        fibreAt c t s := by
      change (κ.hom ≫ toProdSpec a) ≫ pullback.snd a (𝟙 _) = _
      rw [Category.assoc]
      change κ.hom ≫ (pullback.lift (𝟙 _) a _ ≫ pullback.snd a (𝟙 _)) = _
      rw [pullback.lift_snd]
      exact pullbackLeftPullbackSndIso_hom_snd c t s
    have hf : (e ≫ pullback.fst a (𝟙 _)) ≫ f =
        pullback.fst (pullback.snd c t) s := by
      rw [show e ≫ pullback.fst a (𝟙 _) = κ.hom from by
        simp only [e, Category.assoc, toProdSpec_fst, Category.comp_id]]
      exact hκ
    have eM : (Scheme.Modules.pullback e).obj
        ((Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj
          ((Scheme.Modules.pullback f).obj M.L)) ≅
        (Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj M.L :=
      (Scheme.Modules.pullbackComp e (pullback.fst a (𝟙 _))).app
          ((Scheme.Modules.pullback f).obj M.L) ≪≫
        (Scheme.Modules.pullbackComp (e ≫ pullback.fst a (𝟙 _)) f).app M.L ≪≫
        (Scheme.Modules.pullbackCongr hf).app M.L
    exact (hfield.pullback e he).of_iso eM

end AlgebraicGeometry.GeneralizedJacobian
