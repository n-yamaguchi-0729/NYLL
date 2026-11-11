/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.SmoothPrimeCotangentBasis
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Clearing the original relation denominators at a smooth prime

The basis is selected from the original relations by smoothness. A single
actual polynomial, outside the specified prime, then multiplies every
original relation into the selected relation ideal plus the original
relation ideal squared.
-/

@[expose] public section

noncomputable section

universe u v w t

open scoped TensorProduct BigOperators

private theorem exists_smul_mem_span_of_localized_span_eq_top
    {B T N : Type*} [CommRing B] [CommRing T] [Algebra B T]
    [AddCommGroup N] [Module B N] (M : Submonoid B) [IsLocalization M T]
    {ι : Type*} (v : ι → N)
    (hv : Submodule.span T (Set.range (fun i => (1 : T) ⊗ₜ[B] v i)) = ⊤) (x : N) :
    ∃ s : M, (s : B) • x ∈ Submodule.span B (Set.range v) := by
  let f : N →ₗ[B] T ⊗[B] N := TensorProduct.mk B T N 1
  let K := Submodule.span B (Set.range v)
  have hle : Submodule.span T (Set.range (fun i => (1 : T) ⊗ₜ[B] v i)) ≤
      K.localized' T M f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨v i, Submodule.subset_span (Set.mem_range_self i), 1,
      IsLocalizedModule.mk'_one M f (v i)⟩
  have hx : f x ∈ K.localized' T M f := hle (hv ▸ Submodule.mem_top)
  obtain ⟨y, hy, s, hs⟩ := hx
  have heq : f y = f ((s : B) • x) :=
    ((IsLocalizedModule.mk'_eq_iff (S := M) (f := f)).mp hs).trans
      (f.map_smul (s : B) x).symm
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := M) heq
  change (c : B) • y = (c : B) • ((s : B) • x) at hc
  refine ⟨c * s, ?_⟩
  change ((c : B) * (s : B)) • x ∈ K
  rw [mul_smul, ← hc]
  exact K.smul_mem (c : B) hy

private theorem exists_common_smul_mem_span_of_localized_span_eq_top
    {B T N : Type*} [CommRing B] [CommRing T] [Algebra B T]
    [AddCommGroup N] [Module B N] (M : Submonoid B) [IsLocalization M T]
    {ι κ : Type*} [Finite κ] (v : ι → N)
    (hv : Submodule.span T (Set.range (fun i => (1 : T) ⊗ₜ[B] v i)) = ⊤) (x : κ → N) :
    ∃ s : M, ∀ j, (s : B) • x j ∈ Submodule.span B (Set.range v) := by
  classical
  let _ : Fintype κ := Fintype.ofFinite κ
  choose s hs using fun j => exists_smul_mem_span_of_localized_span_eq_top M v hv (x j)
  refine ⟨∏ j, s j, fun j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ j)
  rw [hc]
  change ((s j : B) * (c : B)) • x j ∈ _
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem _ (c : B) (hs j)

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

private theorem cotangent_span_has_relation_representative
    (P : Extension R B) {κ : Type*} (v : κ → P.ker) (z : P.Cotangent)
    (hz : z ∈ Submodule.span B (Set.range (fun i => Extension.Cotangent.mk (P := P) (v i)))) :
    ∃ y : P.ker, y.val ∈ Ideal.span (Set.range (fun i => (v i).val)) ∧
      Extension.Cotangent.mk (P := P) y = z := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact ⟨v i, Ideal.subset_span (Set.mem_range_self i), rfl⟩
  | zero => exact ⟨0, Ideal.zero_mem _, map_zero _⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨y, hy, hyy⟩ := hz
    obtain ⟨y', hy', hyy'⟩ := hz'
    exact ⟨y + y', Ideal.add_mem _ hy hy', by rw [map_add, hyy, hyy']⟩
  | smul r z _ hz =>
    obtain ⟨y, hy, hyy⟩ := hz
    refine ⟨P.σ r • y, ?_, ?_⟩
    · exact (Ideal.span (Set.range (fun i => (v i).val))).mul_mem_left (P.σ r) hy
    · rw [map_smul, hyy, ← algebraMap_smul B, P.algebraMap_σ]

private theorem relation_mul_mem_of_cotangent_smul_mem_span
    (P : Extension R B) {κ : Type*} (v : κ → P.ker) (x : P.ker) (s : B)
    (hs : s • Extension.Cotangent.mk (P := P) x ∈
      Submodule.span B (Set.range (fun i => Extension.Cotangent.mk (P := P) (v i)))) :
    P.σ s * x.val ∈ Ideal.span (Set.range (fun i => (v i).val)) ⊔ P.ker ^ 2 := by
  obtain ⟨y, hy, heq⟩ := cotangent_span_has_relation_representative P v _ hs
  have hmk : Extension.Cotangent.mk (P := P) (P.σ s • x) = Extension.Cotangent.mk (P := P) y := by
    rw [heq, map_smul, ← algebraMap_smul B, P.algebraMap_σ]
  have hdiff := (Extension.Cotangent.mk_eq_mk_iff_sub_mem (P.σ s • x) y).mp hmk
  change P.σ s * x.val - y.val ∈ P.ker ^ 2 at hdiff
  have hsum := (Ideal.span (Set.range (fun i => (v i).val)) ⊔ P.ker ^ 2).add_mem
    ((show P.ker ^ 2 ≤ Ideal.span (Set.range (fun i => (v i).val)) ⊔ P.ker ^ 2
      from le_sup_right) hdiff)
    ((show Ideal.span (Set.range (fun i => (v i).val)) ≤
      Ideal.span (Set.range (fun i => (v i).val)) ⊔ P.ker ^ 2 from le_sup_left) hy)
  simpa only [sub_add_cancel] using hsum

/-- Smoothness selects original relation classes and an actual common
polynomial denominator for every original residual relation. -/
theorem Presentation.exists_relationBasis_and_residualParameter_at_smoothPrime
    {ι : Type w} {σ : Type t} [Finite σ] (P : Presentation R B ι σ)
    (p : Ideal B) [p.IsPrime] [IsSmoothAt R p] :
    ∃ (κ : Type t) (_ : Fintype κ) (a : κ → σ)
      (b : Module.Basis κ (Localization.AtPrime p)
        (Localization.AtPrime p ⊗[B] P.toExtension.Cotangent)) (d : P.Ring),
      (∀ i, b i = (1 : Localization.AtPrime p) ⊗ₜ[B]
        Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation (a i), P.relation_mem_ker (a i)⟩) ∧
      algebraMap P.Ring B d ∉ p ∧
      ∀ j, d * P.relation j ∈
        Ideal.span (Set.range (fun i => P.relation (a i))) ⊔ P.ker ^ 2 := by
  obtain ⟨κ, hκ, a, b, hb⟩ := P.exists_finite_cotangentBasis_at_smoothPrime p
  let v : κ → P.toExtension.ker := fun i =>
    ⟨P.relation (a i), P.relation_mem_ker (a i)⟩
  let x : σ → P.toExtension.ker := fun j => ⟨P.relation j, P.relation_mem_ker j⟩
  have hspan : Submodule.span (Localization.AtPrime p)
      (Set.range (fun i => (1 : Localization.AtPrime p) ⊗ₜ[B]
        Extension.Cotangent.mk (P := P.toExtension) (v i))) = ⊤ := by
    have heq : (fun i => (1 : Localization.AtPrime p) ⊗ₜ[B]
        Extension.Cotangent.mk (P := P.toExtension) (v i)) = b := funext (fun i => (hb i).symm)
    rw [heq]
    exact b.span_eq
  obtain ⟨s, hs⟩ := exists_common_smul_mem_span_of_localized_span_eq_top
    p.primeCompl (fun i => Extension.Cotangent.mk (P := P.toExtension) (v i)) hspan
    (fun j => Extension.Cotangent.mk (P := P.toExtension) (x j))
  refine ⟨κ, hκ, a, b, P.toExtension.σ s, hb, ?_, fun j => ?_⟩
  · change algebraMap P.toExtension.Ring B (P.toExtension.σ s) ∉ p
    rw [P.toExtension.algebraMap_σ]
    exact s.property
  · exact relation_mul_mem_of_cotangent_smul_mem_span P.toExtension v (x j) s (hs j)

end Algebra
