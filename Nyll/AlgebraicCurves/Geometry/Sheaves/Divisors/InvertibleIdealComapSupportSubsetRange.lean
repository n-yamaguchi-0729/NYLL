/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Tactic.Push
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealComapOpenCover

/-!
# Scheme Ideal Sheaf Data Is Invertible of comap of support subset range
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range

universe u

namespace InvLocal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

variable {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData)

theorem exists_of_not_mem_support (x : X) (hx : x ∉ I.support) :
    ∃ (U : X.affineOpens) (f : Γ(X, U)), x ∈ X.basicOpen f ∧
      ∃ g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f), I.ideal (X.affineBasicOpen f) = Ideal.span
        {g} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hx' : x ∉ X.zeroLocus (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
    rwa [← Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hxU]
  rw [Scheme.mem_zeroLocus_iff] at hx'
  push Not at hx'
  obtain ⟨s, hs, hxs⟩ := hx'
  refine ⟨⟨U, hU⟩, s, hxs, 1, one_mem _, ?_⟩
  rw [Ideal.span_singleton_one, ← I.map_ideal_basicOpen]
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hs)
  exact RingedSpace.isUnit_res_basicOpen X.toRingedSpace s

theorem main
    {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData)
    (hsupp : (I.support : Set ↥X) ⊆ Set.range ⇑j) (h : (I.comap j).IsInvertible) :
    I.IsInvertible := by
  classical
  intro x
  by_cases hxW : x ∈ Set.range j
  · obtain ⟨w, rfl⟩ := hxW
    exact Scheme_IdealSheafData_IsInvertible_of_forall_comap_openCover.INVLOCALCOVER.at_image
      j I h w
  · exact exists_of_not_mem_support I x (fun hx => hxW (hsupp hx))

end InvLocal

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.of_comap_of_support_subset_range
    {W X : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData)
    (hsupp : (I.support : Set ↥X) ⊆ Set.range ⇑j) (h : (I.comap j).IsInvertible) :
    I.IsInvertible :=
  InvLocal.main j I hsupp h
end Scheme_IdealSheafData_IsInvertible_of_comap_of_support_subset_range
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
