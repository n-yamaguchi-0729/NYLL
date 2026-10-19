/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkTensorLocal
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkTripleTensorLocal
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Logic.Function.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Actual localization maps from double to triple geometric-stalk overlaps

A prime of the triple overlap pulls back to the prime of each double overlap.
For every face preserving the first strictly Henselian factor, the canonical
map of these localizations is an isomorphism. Both coefficient maps are the
proved local comparisons, and the actual localization map commutes with them.

The nonadjacent face is constructed from the tensor universal property and
computed on original tensor numerators. No comparison or commutativity is
assumed. Composition of these localization maps is already supplied by
`Localization.localRingHom_comp`; no second cocycle API is introduced here.
This remains local overlap algebra for Stacks 0BSB, not effective descent of
finite etale covers or the fundamental-group exact sequence.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every actual face over the first factor induces an isomorphism of the
local rings at the selected triple prime and its literal inverse image. -/
theorem geometricStalk_tripleTensor_localAlgHom_bijective
    {R Ω T : Type u} [CommRing R] [Field Ω] [CommRing T] [Algebra R T]
    [HenselianLocalRing T] [IsSepClosed (IsLocalRing.ResidueField T)]
    (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    ∀ (q : Ideal ((T ⊗[R] H) ⊗[R] H)) [q.IsPrime]
      [q.LiesOver (IsLocalRing.maximalIdeal T)]
      (f : (T ⊗[R] H) →ₐ[T] ((T ⊗[R] H) ⊗[R] H)),
      Function.Bijective (Localization.localAlgHom (q.comap f) q f rfl) := by
  intro H hH q hq hqover f
  let B := T ⊗[R] H
  let D := B ⊗[R] H
  let qB : Ideal B := q.comap f
  have : qB.LiesOver (IsLocalRing.maximalIdeal T) := by
    constructor
    change IsLocalRing.maximalIdeal T =
      (q.comap f).comap (algebraMap T B)
    apply Ideal.ext
    intro t
    change t ∈ IsLocalRing.maximalIdeal T ↔ f (algebraMap T B t) ∈ q
    have ht : t ∈ IsLocalRing.maximalIdeal T ↔ algebraMap T D t ∈ q :=
      SetLike.ext_iff.mp (q.over_def (IsLocalRing.maximalIdeal T)) t
    exact ht.trans (congrArg (fun z : D => z ∈ q) (f.commutes t).symm).to_iff
  let L₁ := Localization.AtPrime qB
  let L₂ := Localization.AtPrime q
  let l : L₁ →ₐ[T] L₂ := Localization.localAlgHom qB q f rfl
  have h₁ : Function.Bijective (algebraMap T L₁) :=
    geometricStalk_tensor_localizationAtPrime_bijective φ qB
  have h₂ : Function.Bijective (algebraMap T L₂) :=
    geometricStalk_tripleTensor_localizationAtPrime_bijective φ q
  apply (Function.Bijective.of_comp_iff (l : L₁ → L₂) h₁).mp
  have hcomp : (l : L₁ → L₂) ∘ algebraMap T L₁ = algebraMap T L₂ :=
    funext l.commutes
  rw [hcomp]
  exact h₂

/-- The nonadjacent tensor face is an isomorphism on the selected local
rings and has the expected formula on actual tensor numerators. -/
theorem geometricStalk_tripleTensor_nonadjacent_face
    {R Ω T : Type u} [CommRing R] [Field Ω] [CommRing T] [Algebra R T]
    [HenselianLocalRing T] [IsSepClosed (IsLocalRing.ResidueField T)]
    (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    let B := T ⊗[R] H
    let D := B ⊗[R] H
    let f : B →ₐ[T] D := (AlgHom.liftEquiv R T H D)
      (Algebra.TensorProduct.includeRight : H →ₐ[R] D)
    ∀ (q : Ideal D) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal T)],
      Function.Bijective (Localization.localAlgHom (q.comap f) q f rfl) ∧
      ∀ (t : T) (h : H),
        Localization.localAlgHom (q.comap f) q f rfl
          (algebraMap B (Localization.AtPrime (q.comap f)) (t ⊗ₜ[R] h)) =
        algebraMap D (Localization.AtPrime q) ((t ⊗ₜ[R] (1 : H)) ⊗ₜ[R] h) := by
  intro H hH B D f q hq hqover
  refine ⟨geometricStalk_tripleTensor_localAlgHom_bijective φ q f, ?_⟩
  intro t h
  have hmap : Localization.localAlgHom (q.comap f) q f rfl
      (algebraMap B (Localization.AtPrime (q.comap f)) (t ⊗ₜ[R] h)) =
      algebraMap D (Localization.AtPrime q) (f (t ⊗ₜ[R] h)) :=
    Localization.localRingHom_to_map (q.comap f) q f.toRingHom rfl (t ⊗ₜ[R] h)
  have hf : f (t ⊗ₜ[R] h) = (t ⊗ₜ[R] (1 : H)) ⊗ₜ[R] h := by
    change (AlgHom.liftEquiv R T H D)
      (Algebra.TensorProduct.includeRight : H →ₐ[R] D) (t ⊗ₜ[R] h) =
        (t ⊗ₜ[R] (1 : H)) ⊗ₜ[R] h
    rw [AlgHom.liftEquiv_tmul]
    change t • ((1 : B) ⊗ₜ[R] h) = (t ⊗ₜ[R] (1 : H)) ⊗ₜ[R] h
    rw [TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  exact hmap.trans (congrArg (algebraMap D (Localization.AtPrime q)) hf)

end EtaleFundamentalGroups.StrictHenselian
