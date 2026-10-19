/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadical
import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import Nyll.SchemeTheory.RingTheory.Smooth.RegularBase
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Smooth base change of a uniformizer root

For a smooth algebra `A` over a DVR `V`, adjoining a root of a base
uniformizer on the actual affine chart is the base change of the root
extension of `V`. We construct its root-algebra structure, retain the
coefficient and root maps, and prove the corresponding scheme square is
cartesian. The chart is smooth over the root DVR and hence regular.

This supplies the regularity of the new base in the purity step of
Stacks Project, Proposition 58.30.2, without assuming regularity of that
base change or a comparison with the polynomial root chart.
https://stacks.math.columbia.edu/tag/0C0Q
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

private def rootBaseChangeAlgEquiv
    (V A : Type u) [CommRing V] [CommRing A] [Algebra V A]
    (n : ℕ) (a : V) :
    A ⊗[V] AdjoinRoot (X ^ n - C a) ≃ₐ[A]
      AdjoinRoot (X ^ n - C (algebraMap V A a)) :=
  (adjoinRootBaseChangeAlgEquiv (X ^ n - C a)).trans
    (AdjoinRoot.algEquivOfEq A _ _ (by
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]))

/-- The root DVR acts on the root chart through the original base-change
map, which sends the original distinguished root to the chart's root. -/
@[instance_reducible]
def rootBaseChangeRootAlgebra
    (V A : Type u) [CommRing V] [CommRing A] [Algebra V A]
    (n : ℕ) (a : V) :
    Algebra (AdjoinRoot (X ^ n - C a))
      (AdjoinRoot (X ^ n - C (algebraMap V A a))) :=
  ((rootBaseChangeAlgEquiv V A n a).toRingHom.comp
    (Algebra.TensorProduct.includeRight : AdjoinRoot (X ^ n - C a) →ₐ[V]
      A ⊗[V] AdjoinRoot (X ^ n - C a)).toRingHom).toAlgebra

/-- The actual root map preserves the distinguished root. -/
theorem rootBaseChangeRootAlgebra_root
    (V A : Type u) [CommRing V] [CommRing A] [Algebra V A]
    (n : ℕ) (a : V) :
    let W := AdjoinRoot (X ^ n - C a)
    let D := AdjoinRoot (X ^ n - C (algebraMap V A a))
    let : Algebra W D := rootBaseChangeRootAlgebra V A n a
    algebraMap W D (AdjoinRoot.root (X ^ n - C a)) =
      AdjoinRoot.root (X ^ n - C (algebraMap V A a)) := by
  intro W D aWD
  change (rootBaseChangeAlgEquiv V A n a)
    (1 ⊗ₜ[V] AdjoinRoot.root (X ^ n - C a)) = _
  simp only [rootBaseChangeAlgEquiv, AlgEquiv.trans_apply,
    adjoinRootBaseChangeAlgEquiv_tmul_root, AdjoinRoot.algEquivOfEq_root]

/-- The root-algebra map and the original chart coefficient map define
the same map from `V`. -/
theorem rootBaseChangeRootAlgebra_base
    (V A : Type u) [CommRing V] [CommRing A] [Algebra V A]
    (n : ℕ) (a v : V) :
    let W := AdjoinRoot (X ^ n - C a)
    let D := AdjoinRoot (X ^ n - C (algebraMap V A a))
    let : Algebra W D := rootBaseChangeRootAlgebra V A n a
    algebraMap W D (algebraMap V W v) =
      algebraMap A D (algebraMap V A v) := by
  intro W D aWD
  change (rootBaseChangeAlgEquiv V A n a) (1 ⊗ₜ[V] algebraMap V W v) = _
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  exact (rootBaseChangeAlgEquiv V A n a).commutes (algebraMap V A v)

/-- The root chart is the original tensor-product base change, as an
algebra over the root ring. -/
def rootBaseChangeOverRootAlgEquiv
    (V A : Type u) [CommRing V] [CommRing A] [Algebra V A]
    (n : ℕ) (a : V) :
    let W := AdjoinRoot (X ^ n - C a)
    let D := AdjoinRoot (X ^ n - C (algebraMap V A a))
    let : Algebra W D := rootBaseChangeRootAlgebra V A n a
    W ⊗[V] A ≃ₐ[W] D := by
  intro W D aWD
  let : Algebra W (A ⊗[V] W) := Algebra.TensorProduct.rightAlgebra
  let e : (A ⊗[V] W) ≃ₐ[W] D :=
    { (rootBaseChangeAlgEquiv V A n a).toRingEquiv with commutes' := fun _ ↦ rfl }
  exact (Algebra.TensorProduct.commRight V W A).trans e

/-- Smooth affine charts remain regular after an actual positive root
extension of the base uniformizer. The displayed square is the original
scheme base change with its coefficient maps. -/
theorem uniformizerRoot_smoothBaseChange_regular
    (V A : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing A] [Algebra V A] [Algebra.Smooth V A]
    (n : ℕ) (hn : 0 < n) (π : V) (hπ : Prime π) :
    let W := AdjoinRoot (X ^ n - C π)
    let D := AdjoinRoot (X ^ n - C (algebraMap V A π))
    let : Algebra W D := rootBaseChangeRootAlgebra V A n π
    Algebra.Smooth W D ∧ IsRegularRing D ∧
      IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A D)))
        (Spec.map (CommRingCat.ofHom (algebraMap W D)))
        (Spec.map (CommRingCat.ofHom (algebraMap V A)))
        (Spec.map (CommRingCat.ofHom (algebraMap V W))) := by
  intro W D aWD
  have : IsDomain W := isDomain_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
  have : IsDiscreteValuationRing W :=
    isDiscreteValuationRing_adjoinRoot_X_pow_sub_C_of_prime hn π hπ
  have : Algebra.Smooth W D :=
    Algebra.Smooth.of_equiv (rootBaseChangeOverRootAlgEquiv V A n π)
  have hregular : IsRegularRing D := Algebra.Smooth.isRegularRing_of_isRegularRing W D
  have : IsScalarTower V W D := by
    apply IsScalarTower.of_algebraMap_eq
    intro v
    exact (rootBaseChangeRootAlgebra_base V A n π v).symm
  have : Algebra.IsPushout V A W D := by
    let : Algebra W (A ⊗[V] W) := Algebra.TensorProduct.rightAlgebra
    apply Algebra.IsPushout.of_equiv (R := V) (R' := A) (S := W)
      (S' := A ⊗[V] W) (T := D) (rootBaseChangeAlgEquiv V A n π)
    apply RingHom.ext
    intro w
    rfl
  exact ⟨inferInstance, hregular,
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout V A W D)⟩

end EtaleFundamentalGroups.Kummer
