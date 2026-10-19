/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.WholeNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.AffineFunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The original affine cover after normal base change

The normalization of a normal affine base in the entire base-changed
generic algebra of a connected finite étale cover is the original
scheme-theoretic base change of that cover.

The coordinate algebra, its fraction maps, the normalization comparison,
and the pullback square are all constructed from the original cover.
The resulting isomorphism is over the new base. This comparison applies
on the boundary complement of a normalized root extension, without
requiring a chosen abstract component or a supplied comparison to the
original cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- Normalizing the new normal affine base in the whole generic tensor
recovers the actual pullback of the original finite étale cover. -/
theorem exists_finiteEtaleAffineBaseChangeNormalizationIso
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (Y : FiniteEtale (Spec R)) [IsConnected Y] :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra R Y.left.functionField := finiteEtaleSpecFunctionFieldAlgebra R Y
    ∀ (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      [Algebra K Y.left.functionField] [IsScalarTower R K Y.left.functionField]
      (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra R B]
      (F : Type u) [Field F] [Algebra R F] [Algebra B F] [Algebra K F]
      [IsScalarTower R B F] [IsScalarTower R K F] [IsFractionRing B F],
      ∃ e : Spec (.of (integralClosure B (F ⊗[K] Y.left.functionField))) ≅
          pullback (Y.hom : Y.left ⟶ Spec R)
            (Spec.map (CommRingCat.ofHom (algebraMap R B))),
        e.hom ≫ pullback.snd _ _ =
          Spec.map (CommRingCat.ofHom
            (algebraMap B (integralClosure B (F ⊗[K] Y.left.functionField)))) := by
  intro hIntegralY aRL K hFieldK aRK hFractionRK aKL hRKL
    B hRingB hDomainB hNormalB aRB F hFieldF aRF aBF aKF hRBF hRKF hFractionBF
  let f : Y.left ⟶ Spec R := Y.hom
  have : IsFiniteEtale f := Y.prop
  have : IsAffine Y.left := isAffine_of_isAffineHom f
  have : Nonempty (⊤ : Y.left.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Y.left), trivial⟩⟩
  let T := Γ(Y.left, ⊤)
  let L := Y.left.functionField
  let : Algebra R T := finiteEtaleAffineSectionAlgebra R Y
  have : Module.Finite R T := (finiteEtaleAffineSections_finite_etale R Y).1
  have : Algebra.Etale R T := (finiteEtaleAffineSections_finite_etale R Y).2
  let : Algebra T L := topSectionFunctionFieldAlgebra Y.left
  have : IsScalarTower R T L := finiteEtaleAffineSections_functionField_isScalarTower R Y
  have : IsFractionRing T L :=
    functionField_isFractionRing_of_isAffineOpen Y.left ⊤ (isAffineOpen_top Y.left)
  let U := B ⊗[R] T
  let C := integralClosure B (F ⊗[K] L)
  let e : U ≃ₐ[B] C := finiteEtaleBaseChangeIntegralClosureEquiv R B T K L F
  let i : T →+* U := Algebra.TensorProduct.includeRight.toRingHom
  let eSpec : Spec (.of C) ≅ Spec (.of U) :=
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op
  let g : Spec (.of C) ⟶ Y.left :=
    Spec.map (CommRingCat.ofHom (e.toRingHom.comp i)) ≫ Y.left.isoSpec.inv
  have hTensor := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R B T)).flip
  have hSquare : IsPullback g
      (Spec.map (CommRingCat.ofHom (algebraMap B C))) f
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    apply hTensor.of_iso' eSpec Y.left.isoSpec (Iso.refl _) (Iso.refl _)
    · change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom i) =
        (Spec.map (CommRingCat.ofHom (e.toRingHom.comp i)) ≫ Y.left.isoSpec.inv) ≫
          Y.left.isoSpec.hom
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, ← Spec.map_comp]
      rfl
    · change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B U)) =
        Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ 𝟙 _
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      exact e.commutes b
    · simp only [Iso.refl_hom, Category.comp_id]
      exact finiteEtaleAffineSectionsIso_hom_base R Y
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  exact ⟨hSquare.isoPullback, hSquare.isoPullback_hom_snd⟩

end EtaleFundamentalGroups
