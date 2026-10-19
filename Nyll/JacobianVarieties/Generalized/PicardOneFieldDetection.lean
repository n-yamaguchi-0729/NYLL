/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardOneLocalTranslation

/-! # Degree-one testing by geometric points of the parameter scheme -/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D T : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (t : T ⟶ Spec (CommRingCat.of R))

omit [GeometricallyIntegral c] in
/-- The intrinsic degree-one test can use the actual composite structure map of each point. -/
theorem modulusPicardOne_iff_fieldRestrictions
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t)) :
    x ∈ (modulusPicardOneSubfunctor c i).obj (op (Over.mk t)) ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        ∃ P : Over.mk (s ≫ t) ⟶ Over.mk ((modulusComplement i).ι ≫ c),
        let m : RigidifiedLineBundle.Classes (modulusBaseChange c i t) →*
            RigidifiedLineBundle.Classes (modulusBaseChange c i (s ≫ t)) :=
          ((modulusPicardGroupPresheaf c i).map
            (Over.homMk s rfl : Over.mk (s ≫ t) ⟶ Over.mk t).op).hom
        let b : RigidifiedLineBundle.Classes (modulusBaseChange c i (s ≫ t)) :=
          modulusAbelPointClass c i (T := Over.mk (s ≫ t)) P
        m x / b ∈ modulusPicardZeroSubgroup c i (Over.mk (s ≫ t)) := by
  constructor
  · intro hx k _ _ s
    exact hx k (s ≫ t) (Over.homMk s rfl)
  · intro hx k _ _ t' f
    obtain ⟨s, hs, rfl⟩ := Over.homMk_surjective f
    change Spec (CommRingCat.of k) ⟶ T at s
    change s ≫ t = t' at hs
    subst t'
    exact hx k s

/-- On a geometric field, one actual point difference already detects the degree-one condition. -/
theorem modulusPicardOne_iff_exists_point
    (k : Type u) [Field k] [IsAlgClosed k]
    (t₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t₀)) :
    x ∈ (modulusPicardOneSubfunctor c i).obj (op (Over.mk t₀)) ↔
      ∃ P : Over.mk t₀ ⟶ Over.mk ((modulusComplement i).ι ≫ c),
        let b : RigidifiedLineBundle.Classes (modulusBaseChange c i t₀) :=
          modulusAbelPointClass c i (T := Over.mk t₀) P
        x / b ∈ modulusPicardZeroSubgroup c i (Over.mk t₀) := by
  constructor
  · intro hx
    obtain ⟨P, hP⟩ := hx k t₀ (𝟙 (Over.mk t₀))
    refine ⟨P, ?_⟩
    let b : RigidifiedLineBundle.Classes (modulusBaseChange c i t₀) :=
      modulusAbelPointClass c i (T := Over.mk t₀) P
    let m : RigidifiedLineBundle.Classes (modulusBaseChange c i t₀) →*
        RigidifiedLineBundle.Classes (modulusBaseChange c i t₀) :=
      ((modulusPicardGroupPresheaf c i).map (𝟙 (Over.mk t₀)).op).hom
    have hm : m x = x :=
      ConcreteCategory.congr_hom ((modulusPicardGroupPresheaf c i).map_id (op (Over.mk t₀))) x
    change m x / b ∈ _ at hP
    rw [hm] at hP
    exact hP
  · rintro ⟨P, hP⟩
    exact (modulusPicardOne_iff_translatePoint c i P x).mpr hP

/-- Degree-one membership is detected by its restrictions to geometric points of the parameter. -/
theorem modulusPicardOne_of_fieldRestrictions
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t))
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
      (modulusPicardGroupPresheaf c i).map
        (Over.homMk s rfl : Over.mk (s ≫ t) ⟶ Over.mk t).op x ∈
          (modulusPicardOneSubfunctor c i).obj (op (Over.mk (s ≫ t)))) :
    x ∈ (modulusPicardOneSubfunctor c i).obj (op (Over.mk t)) := by
  apply (modulusPicardOne_iff_fieldRestrictions c i t x).mpr
  intro k _ _ s
  exact (modulusPicardOne_iff_exists_point c i k (s ≫ t) _).mp (h k s)

end AlgebraicGeometry.GeneralizedJacobian
