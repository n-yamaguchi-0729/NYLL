/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RelativeNormalization
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.StandardCover
import Nyll.SchemeTheory.Normalization.GenericFiber.IntegralClosure
import Nyll.SchemeTheory.Normalization.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The actual normalization of a standard Kummer chart

Let `B = A[X] / (X ^ n - f)` and `T = B[1/f]`, where `n` is positive,
`f` is a nonzerodivisor, and `A / (f)` is reduced. The actual relative
normalization of `Spec A` in `Spec T` is identified with `Spec B`.
The isomorphism intertwines both canonical morphisms: the map from
`Spec T` is the original localization map, and the map to `Spec A`
is the original coefficient map.

When `n` is invertible in `A`, the normalization morphism is finite,
flat, locally of finite presentation, and of rank `n` at every point.
The integral-closure calculation is supplied by `RelativeNormalization`;
the affine normalization comparison and uniqueness of integral closures
are reused rather than reconstructed.

This is the standard-chart normalization calculation in Stacks Project,
Lemma 58.31.6. It does not assert the étale chart-existence theorem 58.31.5
or the descent of these local descriptions to arbitrary schemes.
https://stacks.math.columbia.edu/tag/0BSE
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace EtaleFundamentalGroups.Kummer

/-- The actual relative normalization of the standard away algebra is the
spectrum of the original root algebra. No normality of the base is needed. -/
def standardKummerNormalizationIso
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))] :
    let B := AdjoinRoot (X ^ n - C f)
    let T := Localization.Away (algebraMap A B f)
    (Spec.map (CommRingCat.ofHom (algebraMap A T))).normalization ≅
      Spec (CommRingCat.of B) := by
  intro B T
  have : IsIntegralClosure B A T := standardKummerCover_isIntegralClosure_away hn f hf
  let e : B ≃ₐ[A] integralClosure A T :=
    IsIntegralClosure.equiv A B T (integralClosure A T)
  exact specNormalizationIso A T ≪≫ Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- The canonical map into the normalization becomes the literal
localization map into `B[1/f]` on coordinate rings. -/
@[reassoc]
theorem toNormalization_standardKummerNormalizationIso_hom
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))] :
    let B := AdjoinRoot (X ^ n - C f)
    let T := Localization.Away (algebraMap A B f)
    (Spec.map (CommRingCat.ofHom (algebraMap A T))).toNormalization ≫
        (standardKummerNormalizationIso hn f hf).hom =
      Spec.map (CommRingCat.ofHom (algebraMap B T)) := by
  intro B T
  have : IsIntegralClosure B A T := standardKummerCover_isIntegralClosure_away hn f hf
  let e : B ≃ₐ[A] integralClosure A T :=
    IsIntegralClosure.equiv A B T (integralClosure A T)
  change (Spec.map (CommRingCat.ofHom (algebraMap A T))).toNormalization ≫
      ((specNormalizationIso A T).hom ≫
        Spec.map (CommRingCat.ofHom e.toRingHom)) = _
  rw [← Category.assoc, toNormalization_specNormalizationIso_hom, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact IsIntegralClosure.algebraMap_equiv A B T (integralClosure A T) b

/-- The normalization comparison is over the original `Spec A`, with its
actual coefficient map rather than an unspecified isomorphic map. -/
@[reassoc]
theorem standardKummerNormalizationIso_hom_base
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))] :
    let B := AdjoinRoot (X ^ n - C f)
    let T := Localization.Away (algebraMap A B f)
    (standardKummerNormalizationIso hn f hf).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      (Spec.map (CommRingCat.ofHom (algebraMap A T))).fromNormalization := by
  intro B T
  have : IsIntegralClosure B A T := standardKummerCover_isIntegralClosure_away hn f hf
  let e : B ≃ₐ[A] integralClosure A T :=
    IsIntegralClosure.equiv A B T (integralClosure A T)
  change ((specNormalizationIso A T).hom ≫
      Spec.map (CommRingCat.ofHom e.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) = _
  have hbase : CommRingCat.ofHom (algebraMap A B) ≫
      CommRingCat.ofHom e.toRingHom =
        CommRingCat.ofHom (algebraMap A (integralClosure A T)) :=
    CommRingCat.hom_ext (RingHom.ext e.commutes)
  rw [Category.assoc, ← Spec.map_comp, hbase]
  exact specNormalizationIso_hom_base A T

/-- The actual normalization morphism of the standard away cover is finite
locally free of rank `n`, expressed by its native finite, flat,
finite-presentation, and pointwise rank predicates. -/
theorem standardKummerNormalization_finiteFlat
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (hnUnit : IsUnit (n : A)) (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))] :
    let B := AdjoinRoot (X ^ n - C f)
    let T := Localization.Away (algebraMap A B f)
    let ν := (Spec.map (CommRingCat.ofHom (algebraMap A T))).fromNormalization
    IsFinite ν ∧ Flat ν ∧ LocallyOfFinitePresentation ν ∧
      ∀ x : PrimeSpectrum A, ν.finrank x = n := by
  intro B T ν
  let π := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let e := standardKummerNormalizationIso hn f hf
  obtain ⟨_, hfinite, hflat, hfp, hrank, _, _⟩ :=
    standardKummerCover_finiteFlat_and_etaleAway hn hnUnit f
  have : IsFinite π := hfinite
  have : Flat π := hflat
  have : LocallyOfFinitePresentation π := hfp
  have hbase : e.hom ≫ π = ν := standardKummerNormalizationIso_hom_base hn f hf
  have hfiniteν : IsFinite ν := by
    rw [← hbase]
    infer_instance
  have hflatν : Flat ν := by
    rw [← hbase]
    infer_instance
  have hfpν : LocallyOfFinitePresentation ν := by
    rw [← hbase]
    infer_instance
  refine ⟨hfiniteν, hflatν, hfpν, ?_⟩
  intro x
  rw [← hbase, Scheme.Hom.finrank_comp_left_of_isIso]
  exact hrank x

end EtaleFundamentalGroups.Kummer
