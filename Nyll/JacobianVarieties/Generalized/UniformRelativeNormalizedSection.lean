/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RelativeNormalizedSection
import Nyll.JacobianVarieties.Generalized.ModulusUniformVanishing
import Nyll.JacobianVarieties.Generalized.SectionPowerBaseChange
import Nyll.JacobianVarieties.Generalized.GeometricCohomologyBound

/-!
# A uniform normalized section for an actual family

The input conditions are the geometric degree of the full Cartier modulus,
geometric Picard-zero for the bundle, and a uniform genus bound. The point
powers and all fibre module comparisons are constructed explicitly. Relative
cohomology then lifts the given modulus frame over the whole affine base.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RelPicard
open AlgebraicCurves.Cohomology.Sheaves.Proofs
open Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq.Ws31ChiA

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (𝒱 : X.TwoAffineOpenCover) (I : X.IdealSheafData) (hI : I.IsInvertible)
  (ε : Spec (CommRingCat.of R) ⟶ X) (hε : ε ≫ c = 𝟙 _)
  (havoid : ∀ y : I.subscheme, I.subschemeι.base y ∉ ε.ker.support)
  (M : RigidifiedLineBundle I.subschemeι)

include hI hε havoid in
/-- The same large-degree bound works for every geometric Picard-zero family. -/
theorem exists_normalizedSection_of_uniform_pointTwist
    {d g : ℕ}
    (hmod : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      let σ := Scheme.TwoAffineOpenCover.specMap R k
      let J := I.comap (pullback.fst c σ)
      J.IsInvertible ∧ IsFinite (J.subschemeι ≫ pullback.snd c σ) ∧
        ∀ z : Spec (CommRingCat.of k), (J.subschemeι ≫ pullback.snd c σ).finrank z = d)
    (hzero : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      IsAlgEquivZero (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))
        ((Scheme.Modules.pullback
          (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R k))).obj M.L))
    (hgenus : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      Module.finrank k ((𝒱.pullback c k).sectionsOf
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))
          (𝟙_ (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R k)).Modules)).H1 ≤ g)
    (n : ℕ) (hn : 2 * g + d ≤ n + 1) :
    ∃ ha : ∀ y : I.subscheme, I.subschemeι.base y ∉ (ε.ker ^ n).support,
      ∃ s : 𝟙_ X.Modules ⟶ M.L ⊗ (ε.ker ^ n).invModule,
        pullbackSection I.subschemeι s ≫
            (M.tensor (ofInvertibleIdeal I.subschemeι (ε.ker ^ n)
              ((Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow n) ha)).trivialization.hom =
          𝟙 (𝟙_ I.subscheme.Modules) := by
  have hp := (Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow n
  have ha : ∀ y : I.subscheme, I.subschemeι.base y ∉ (ε.ker ^ n).support := by
    cases n with
    | zero =>
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.support_top]
      exact fun _ hy => hy
    | succ n =>
      rw [Scheme.IdealSheafData.support_pow_succ]
      exact havoid
  let N := M.tensor (ofInvertibleIdeal I.subschemeι (ε.ker ^ n) hp ha)
  suffices ∃ s : 𝟙_ X.Modules ⟶ N.L,
      pullbackSection I.subschemeι s ≫ N.trivialization.hom = 𝟙 _ by
    exact ⟨ha, this⟩
  apply exists_normalizedSection_of_geometric_H1 c 𝒱 I hI N
  intro k _ _ _
  let σ := Scheme.TwoAffineOpenCover.specMap R k
  let f := pullback.fst c σ
  let π := pullback.snd c σ
  let 𝒲 := 𝒱.pullback c k
  let J := I.comap f
  let p := sectionBaseChange c ε hε σ
  let L := (Scheme.Modules.pullback f).obj M.L
  have hJ : J.IsInvertible := (hmod k).1
  have hfin : IsFinite (J.subschemeι ≫ π) := (hmod k).2.1
  have hdeg : ∀ z : Spec (CommRingCat.of k), (J.subschemeι ≫ π).finrank z = d :=
    (hmod k).2.2
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {Y Z : Scheme.{u}} (a : Y ⟶ Z) => SmoothOfRelativeDimension 1 a) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {Y Z : Scheme.{u}} (a : Y ⟶ Z) => SmoothOfRelativeDimension 1 a)
      (IsPullback.of_hasPullback c σ) inferInstance
  have : IsIntegral (Limits.pullback c σ) :=
    GeometricallyIntegral.geometrically_isIntegral σ f π (IsPullback.of_hasPullback c σ)
  have hbound : 2 * Module.finrank k (𝒲.sectionsOf π (𝟙_ _)).H1 + d ≤ n + 1 := by
    have hg := hgenus k
    dsimp only [𝒲, π, σ]
    omega
  have hv : Subsingleton (𝒲.sectionsOf π ((L ⊗ (p.ker ^ n).invModule) ⊗ J.module)).H1 :=
    subsingleton_H1_zero_pointTwist_modulus π 𝒲 p (sectionBaseChange_snd c ε hε σ)
      L (M.isInvertible.pullback f) (hzero k) J hJ hfin hdeg n hbound
  have : IsIso (I.pullbackModuleComparison f) :=
    hI.isIso_pullbackModuleComparison f hJ
  let e : (Scheme.Modules.pullback f).obj (N.L ⊗ I.module) ≅
      (L ⊗ (p.ker ^ n).invModule) ⊗ J.module :=
    Scheme.Modules.pullbackTensorObjIso f N.L I.module ≪≫
      ((Scheme.Modules.pullbackTensorObjIso f M.L (ε.ker ^ n).invModule ≪≫
        whiskerLeftIso L (sectionPowerBaseChangeIso c ε hε σ n)) ⊗ᵢ
          asIso (I.pullbackModuleComparison f))
  obtain ⟨_, ⟨e1⟩⟩ := nonempty_linearEquiv_of_iso π 𝒲 e
  exact e1.toEquiv.subsingleton

include 𝒱 hI hε havoid in
/-- The normalized section exists eventually over the whole affine parameter scheme. -/
theorem eventually_exists_normalizedSection_of_geometric_zero
    {d : ℕ}
    (hmod : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      let σ := Scheme.TwoAffineOpenCover.specMap R k
      let J := I.comap (pullback.fst c σ)
      J.IsInvertible ∧ IsFinite (J.subschemeι ≫ pullback.snd c σ) ∧
        ∀ z : Spec (CommRingCat.of k), (J.subschemeι ≫ pullback.snd c σ).finrank z = d)
    (hzero : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k],
      IsAlgEquivZero (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))
        ((Scheme.Modules.pullback
          (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R k))).obj M.L)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ ha : ∀ y : I.subscheme, I.subschemeι.base y ∉ (ε.ker ^ n).support,
        ∃ s : 𝟙_ X.Modules ⟶ M.L ⊗ (ε.ker ^ n).invModule,
          pullbackSection I.subschemeι s ≫
              (M.tensor (ofInvertibleIdeal I.subschemeι (ε.ker ^ n)
                ((Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε).pow n) ha)).trivialization.hom =
            𝟙 (𝟙_ I.subscheme.Modules) := by
  obtain ⟨g, hg⟩ := exists_uniform_geometric_H1_bound c 𝒱
  refine ⟨2 * g + d, ?_⟩
  intro n hn
  exact exists_normalizedSection_of_uniform_pointTwist c 𝒱 I hI ε hε havoid M
    hmod hzero (fun k _ _ _ => hg k) n (by omega)

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
