/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkTensorLocal
import Nyll.SchemeTheory.FiniteEtale.Henselian.PointedEtale
import Nyll.SchemeTheory.RingTheory.Localization.LocalMapLocalizationSurjective
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Local rings on triple overlaps of the actual geometric stalk

Let `H` be the actual geometric etale stalk of `R`, and let `T` be a
strictly Henselian local `R`-algebra. The local ring of
`(T ⊗[R] H) ⊗[R] H` at every point over the closed point of `T` is `T`.
Both maps from `H` are the actual tensor-factor maps. Their images lie
in `T` by the existing affine-etale germ construction. The standard
generation theorem for a tensor product then handles the entire triple
ring, and localness handles its denominators.

This supplies the triple-overlap local comparison used in Stacks Project,
Lemma 58.10.6 (https://stacks.math.columbia.edu/tag/0BSB). It does not yet
supply the punctured-cover descent or the lemma's fundamental-group sequence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem tensor_hom_mem_of_factor_images
    {R A B L : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing L]
    [Algebra R A] [Algebra R B] (f : A ⊗[R] B →+* L) (S : Subring L)
    (hA : ∀ a : A,
      f ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) a) ∈ S)
    (hB : ∀ b : B,
      f ((Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) b) ∈ S)
    (x : A ⊗[R] B) : f x ∈ S := by
  have hle : Subring.closure
      (Set.range (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B) ∪
        Set.range (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B)) ≤
      S.comap f := by
    apply Subring.closure_le.mpr
    rintro y (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact hA a
    · exact hB b
  rw [Algebra.TensorProduct.closure_range_union_range_eq_top] at hle
  exact hle (show x ∈ (⊤ : Subring (A ⊗[R] B)) from trivial)

/-- The closed-point local rings of the actual triple tensor overlap
are the original strictly Henselian local base. -/
theorem geometricStalk_tripleTensor_localizationAtPrime_bijective
    {R Ω T : Type u} [CommRing R] [Field Ω] [CommRing T] [Algebra R T]
    [HenselianLocalRing T] [IsSepClosed (IsLocalRing.ResidueField T)]
    (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    ∀ (q : Ideal ((T ⊗[R] H) ⊗[R] H)) [q.IsPrime]
      [q.LiesOver (IsLocalRing.maximalIdeal T)],
      Function.Bijective (algebraMap T (Localization.AtPrime q)) := by
  intro H hH q hq hqover
  let B := T ⊗[R] H
  let D := B ⊗[R] H
  let L := Localization.AtPrime q
  have : Module.Flat R H := geometricStalkStructureMap_flat φ
  have : Module.Flat T D := Module.Flat.trans T B D
  have : Module.Flat T L := Module.Flat.trans T D L
  have : IsLocalHom (algebraMap T L) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal q
  have : Module.FaithfullyFlat T L :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom (A := T) (B := L)
  refine ⟨(faithfulSMul_iff_algebraMap_injective T L).mp
    (Module.FaithfullyFlat.faithfulSMul (A := T) (B := L)), ?_⟩
  let l : D →ₐ[R] L := IsScalarTower.toAlgHom R D L
  let i : B →ₐ[R] D := Algebra.TensorProduct.includeLeft
  let g₁ : H →ₐ[R] L := (l.comp i).comp
    (Algebra.TensorProduct.includeRight : H →ₐ[R] B)
  let g₂ : H →ₐ[R] L := l.comp
    (Algebra.TensorProduct.includeRight : H →ₐ[R] D)
  have hg₁ (a : H) : g₁ a ∈ (algebraMap T L).range := by
    change ∃ t : T, algebraMap T L t = g₁ a
    exact geometricStalk_hom_exists_strictHenselian_preimage
      (R := R) (Ω := Ω) (T := T) (L := L) φ g₁.toRingHom
      (RingHom.ext g₁.commutes) a
  have hg₂ (a : H) : g₂ a ∈ (algebraMap T L).range := by
    change ∃ t : T, algebraMap T L t = g₂ a
    exact geometricStalk_hom_exists_strictHenselian_preimage
      (R := R) (Ω := Ω) (T := T) (L := L) φ g₂.toRingHom
      (RingHom.ext g₂.commutes) a
  have hB (b : B) : l (i b) ∈ (algebraMap T L).range := by
    refine tensor_hom_mem_of_factor_images (R := R) (A := T) (B := H) (L := L)
      (l.comp i).toRingHom (algebraMap T L).range ?_ ?_ b
    · intro t
      change algebraMap D L (algebraMap B D (algebraMap T B t)) ∈
        (algebraMap T L).range
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact ⟨t, rfl⟩
    · exact hg₁
  apply IsLocalization.surjective_algebraMap_of_numerators_mem_range
    (T := T) (B := D) (L := L) q.primeCompl
  intro d
  change algebraMap D L d ∈ (algebraMap T L).range
  exact tensor_hom_mem_of_factor_images (R := R) (A := B) (B := H) (L := L)
    l.toRingHom (algebraMap T L).range hB hg₂ d

end EtaleFundamentalGroups.StrictHenselian
