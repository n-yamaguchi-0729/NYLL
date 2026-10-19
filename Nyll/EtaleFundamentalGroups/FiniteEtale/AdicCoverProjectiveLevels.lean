/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.CoefficientMapComposition
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# The projective spaces of the actual adic cover tower

The original tower uses recursively defined positive ideal powers. Their
proved equality with the corresponding powers induces the actual quotient
spectrum isomorphism. Projective-space base change then identifies its
original pullback level with projective space over the coefficient quotient.

The successive coefficient map commutes with these isomorphisms and the
original tower transition. Thus transport to the quotient projective spaces
retains the original transition maps, not just the objects at each level.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)

/-- The coefficient equivalence uses the proved equality of the original
recursive ideal with the corresponding positive power. -/
def projectiveLevelQuotientEquiv (k : ℕ) :
    (R ⧸ levelIdeal I k) ≃ₐ[R] R ⧸ I ^ (k + 1) :=
  Ideal.quotientEquivAlgOfEq R (levelIdeal_eq_pow I k)

/-- The actual isomorphism of quotient spectra underlying the two
descriptions of a projective tower level. -/
def projectiveLevelBaseIso (k : ℕ) :
    Spec (CommRingCat.of (R ⧸ I ^ (k + 1))) ≅ base I k :=
  Scheme.Spec.mapIso (projectiveLevelQuotientEquiv R I k).toRingEquiv.toCommRingCatIso.op

theorem projectiveLevelBaseIso_hom_comp (k : ℕ) :
    (projectiveLevelBaseIso R I k).hom ≫ baseInclusion I k =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))) := by
  have he : (projectiveLevelQuotientEquiv R I k).toRingHom.comp
      (Ideal.Quotient.mk (levelIdeal I k)) = Ideal.Quotient.mk (I ^ (k + 1)) := by
    ext r
    exact Ideal.quotientEquivAlgOfEq_mk R (levelIdeal_eq_pow I k) r
  change Spec.map (CommRingCat.ofHom (projectiveLevelQuotientEquiv R I k).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I k))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, he]

/-- The literal coefficient morphism is a pullback over the original
quotient-spectrum inclusion of the adic cover tower. -/
theorem projectiveLevel_isPullback (k : ℕ) :
    IsPullback (ProjSpace.map R (R ⧸ I ^ (k + 1)) n)
      (ProjSpace.π (R ⧸ I ^ (k + 1)) n ≫ (projectiveLevelBaseIso R I k).hom)
      (ProjSpace.π R n) (baseInclusion I k) := by
  apply (ProjSpace.isPullback_map R (R ⧸ I ^ (k + 1)) n).of_iso
    (Iso.refl _) (Iso.refl _) (projectiveLevelBaseIso R I k) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · rw [Iso.refl_hom, Category.comp_id]
    exact (projectiveLevelBaseIso_hom_comp R I k).symm

/-- The actual projective-space base-change isomorphism at every level. -/
def projectiveLevelIso (k : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (R ⧸ I ^ (k + 1))) ≅
      level (ProjSpace.π R n) I k :=
  (projectiveLevel_isPullback R I n k).isoPullback

theorem projectiveLevelIso_hom_fst (k : ℕ) :
    (projectiveLevelIso R I n k).hom ≫
        pullback.fst (ProjSpace.π R n) (baseInclusion I k) =
      ProjSpace.map R (R ⧸ I ^ (k + 1)) n :=
  (projectiveLevel_isPullback R I n k).isoPullback_hom_fst

theorem projectiveLevelIso_hom_snd (k : ℕ) :
    (projectiveLevelIso R I n k).hom ≫
        pullback.snd (ProjSpace.π R n) (baseInclusion I k) =
      ProjSpace.π (R ⧸ I ^ (k + 1)) n ≫ (projectiveLevelBaseIso R I k).hom :=
  (projectiveLevel_isPullback R I n k).isoPullback_hom_snd

theorem projectiveLevelIso_inv_map (k : ℕ) :
    (projectiveLevelIso R I n k).inv ≫ ProjSpace.map R (R ⧸ I ^ (k + 1)) n =
      pullback.fst (ProjSpace.π R n) (baseInclusion I k) :=
  (projectiveLevel_isPullback R I n k).isoPullback_inv_fst

/-- The successive transition is the original Proj map induced by the
literal homomorphism between successive coefficient quotients. -/
def projectiveLevelTransition (k : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (R ⧸ I ^ (k + 1))) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (R ⧸ I ^ (k + 1 + 1))) :=
  let : Algebra (R ⧸ I ^ (k + 1 + 1)) (R ⧸ I ^ (k + 1)) :=
    (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))).toAlgebra
  ProjSpace.map (R ⧸ I ^ (k + 1 + 1)) (R ⧸ I ^ (k + 1)) n

theorem projectiveLevelTransition_comp_map (k : ℕ) :
    projectiveLevelTransition R I n k ≫
        ProjSpace.map R (R ⧸ I ^ (k + 1 + 1)) n =
      ProjSpace.map R (R ⧸ I ^ (k + 1)) n := by
  let : Algebra (R ⧸ I ^ (k + 1 + 1)) (R ⧸ I ^ (k + 1)) :=
    (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))).toAlgebra
  have hcoeff :
      (algebraMap (R ⧸ I ^ (k + 1 + 1)) (R ⧸ I ^ (k + 1))).comp
        (algebraMap R (R ⧸ I ^ (k + 1 + 1))) =
      algebraMap R (R ⧸ I ^ (k + 1)) := by
    change (Ideal.Quotient.factorPow I (Nat.le_succ (k + 1))).comp
        (Ideal.Quotient.mk (I ^ (k + 1 + 1))) = Ideal.Quotient.mk (I ^ (k + 1))
    exact Ideal.Quotient.factor_comp_mk _
  exact ProjSpace.map_comp_of_algebraMap_comp_eq
    R (R ⧸ I ^ (k + 1 + 1)) (R ⧸ I ^ (k + 1)) n hcoeff

/-- The level isomorphisms intertwine the original tower transition with
the actual successive coefficient map. -/
theorem projectiveLevelIso_transition (k : ℕ) :
    (projectiveLevelIso R I n k).hom ≫ transition (ProjSpace.π R n) I k =
      projectiveLevelTransition R I n k ≫ (projectiveLevelIso R I n (k + 1)).hom := by
  have : IsClosedImmersion (baseInclusion I (k + 1)) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I (k + 1))))
      Ideal.Quotient.mk_surjective
  apply (cancel_mono (pullback.fst (ProjSpace.π R n) (baseInclusion I (k + 1)))).mp
  rw [Category.assoc, transition_fst, projectiveLevelIso_hom_fst,
    Category.assoc, projectiveLevelIso_hom_fst, projectiveLevelTransition_comp_map]

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
