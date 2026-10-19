/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.AffineFunctionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The original affine cover in the generic pullback square

For a connected finite étale cover of a normal affine domain, the spectrum
of its actual function field is the pullback of the original cover to
any compatible chosen fraction field of the base. The top map uses the
actual germs of global sections and the original affine comparison.

The proof first constructs the algebra pushout using the whole generic
tensor comparison, and then transports the affine square back to the
original scheme. Thus the resulting square retains the original cover
morphism, which is needed when comparing root extensions on overlaps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- The actual function field of a connected finite étale affine cover
is its generic pullback, with the original structure morphism of the cover. -/
theorem isPullback_finiteEtaleAffine_generic
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R]
    (Y : FiniteEtale (Spec R)) [IsConnected Y] :
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : IsAffine Y.left :=
      isAffine_of_isAffineHom (X := Y.left) (Y := Spec R) Y.hom
    let : Algebra Γ(Y.left, ⊤) Y.left.functionField := topSectionFunctionFieldAlgebra Y.left
    let : Algebra R Y.left.functionField := finiteEtaleSpecFunctionFieldAlgebra R Y
    ∀ (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      [Algebra K Y.left.functionField] [IsScalarTower R K Y.left.functionField],
      IsPullback
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y.left, ⊤) Y.left.functionField)) ≫
          Y.left.isoSpec.inv)
        (Spec.map (CommRingCat.ofHom (algebraMap K Y.left.functionField)))
        Y.hom (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  intro hIntegralY hAffineY aTL aRL K hFieldK aRK hFractionRK aKL hRKL
  let T := Γ(Y.left, ⊤)
  let L := Y.left.functionField
  let : Algebra R T := finiteEtaleAffineSectionAlgebra R Y
  have : IsScalarTower R T L := finiteEtaleAffineSections_functionField_isScalarTower R Y
  let G := T ⊗[R] K
  let : Algebra K G := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R K G := Algebra.TensorProduct.right_isScalarTower
  let e : G ≃ₐ[K] L := finiteEtaleAffineGenericFiberAlgEquiv R Y K
  have : Algebra.IsPushout R K T G :=
    (inferInstance : Algebra.IsPushout R T K G).symm
  have hPushout : Algebra.IsPushout R K T L := by
    apply Algebra.IsPushout.of_equiv (R := R) (R' := K) (S := T) (S' := G) e
    apply RingHom.ext
    intro t
    change e (algebraMap T G t) = algebraMap T L t
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self]
    change finiteEtaleAffineGenericFiberAlgEquiv R Y K (t ⊗ₜ[R] 1) = algebraMap T L t
    rw [finiteEtaleAffineGenericFiberAlgEquiv_tmul, map_one, mul_one]
  have : Algebra.IsPushout R T K L := hPushout.symm
  have hSquare := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R T K L)
  exact hSquare.of_iso (Iso.refl _) Y.left.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Iso.symm_hom, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    (by
      simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id]
      rw [← finiteEtaleAffineSectionsIso_hom_base R Y, Iso.inv_hom_id_assoc])
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])

end EtaleFundamentalGroups
