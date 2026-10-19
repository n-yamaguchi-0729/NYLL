/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUniformVanishing
import Nyll.AlgebraicCurves.Geometry.Picard.Cohomology.PullbackSectionTwistIso
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedAlgEquivZero
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! # The actual fibre degree of point twists of Picard-zero families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RelPicard
open AlgebraicCurves.Cohomology.Sheaves.Proofs
open Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq.Ws31ChiA

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C T : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
  (t : T ⟶ Spec (CommRingCat.of R)) (L : (pullback c t).Modules) (hL : IsInvertible L)

include hL in
/-- Point twisting adds its exponent to the degree on every actual geometric fibre. -/
theorem eulerChar_fibre_zero_pointTwist
    (hzero : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T),
      IsAlgEquivZero (fibreAt c t x)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) x)).obj L))
    (n : ℕ) (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
    (𝒱 : (pullback c (x ≫ t)).TwoAffineOpenCover) :
    let f := mapOnProdOver c x rfl
    let π := pullback.snd c (x ≫ t)
    let F := (Scheme.Modules.pullback f).obj (L ⊗ sectionTwist c ε t n)
    (Module.finrank k (𝒱.sectionsOf π F).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf π F).H1 =
      (Module.finrank k (𝒱.sectionsOf π (𝟙_ _)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf π (𝟙_ _)).H1 + n := by
  let σ := x ≫ t
  let ψ : SchemeHomOver σ t := ⟨x, rfl⟩
  let f := baseChangeSnd c ψ
  let π := pullback.snd c σ
  let κ := pullbackLeftPullbackSndIso c t x
  have hκsnd : κ.inv ≫ fibreAt c t x = π := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd c t x).symm
  have hκf : κ.inv ≫ pullback.fst (pullback.snd c t) x = f := by
    rw [Iso.inv_comp_eq]
    apply pullback.hom_ext
    · dsimp only [f, baseChangeSnd, pullback.map, ψ]
      rw [Category.assoc, pullback.lift_fst, Category.comp_id]
      exact (pullbackLeftPullbackSndIso_hom_fst c t x).symm
    · dsimp only [f, baseChangeSnd, pullback.map, ψ]
      rw [Category.assoc, pullback.lift_snd, pullback.condition,
        ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
  let eL := (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hκf).app L
  have h0 : IsAlgEquivZero π ((Scheme.Modules.pullback f).obj L) :=
    ((hzero k x).pullback κ.inv hκsnd).of_iso eL
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (a : X ⟶ Y) => SmoothOfRelativeDimension 1 a) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (a : X ⟶ Y) => SmoothOfRelativeDimension 1 a)
      (IsPullback.of_hasPullback c σ) inferInstance
  obtain ⟨et⟩ := nonempty_pullback_sectionTwist_iso R c ε ψ n
  let e := Scheme.Modules.pullbackTensorObjIso f L (sectionTwist c ε t n) ≪≫
    whiskerLeftIso ((Scheme.Modules.pullback f).obj L) et
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso π 𝒱 e
  change (Module.finrank k (𝒱.sectionsOf π ((Scheme.Modules.pullback f).obj
      (L ⊗ sectionTwist c ε t n))).H0 : ℤ) -
      Module.finrank k (𝒱.sectionsOf π ((Scheme.Modules.pullback f).obj
        (L ⊗ sectionTwist c ε t n))).H1 = _
  rw [e0.finrank_eq, e1.finrank_eq]
  exact eulerChar_zero_pointTwist π 𝒱 (rigSection c σ ε) (pullback.lift_snd _ _ _)
    ((Scheme.Modules.pullback f).obj L) (hL.pullback f) h0 n

end AlgebraicGeometry.GeneralizedJacobian
