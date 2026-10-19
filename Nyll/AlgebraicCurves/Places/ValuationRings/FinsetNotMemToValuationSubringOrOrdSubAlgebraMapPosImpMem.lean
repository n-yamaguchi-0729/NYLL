/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Places.Basic

/-!
# Place exists finset forall not Mem to Valuation Subring or ord sub algebra Map pos imp mem
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem

open AlgebraicCurve IsLocalRing

theorem ExistsBadset.ord_neg_of_notMem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {f : F} (hf : f ∉ w.toValuationSubring) : w.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ zero_mem _)
  exact lt_of_not_ge fun h => hf (w.mem_of_ord_nonneg hf0 h)

theorem ExistsBadset.exists_finset_forall_notMem_or_ord_sub_pos_imp_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (jel : F) (hnc : ∀ c : K, jel ≠ algebraMap K F c) (S : Finset K) :
    ∃ T : Finset (Place K F), ∀ t : Place K F,
      (jel ∉ t.toValuationSubring ∨ ∃ s ∈ S, 0 < t.ord (jel - algebraMap K F s)) → t ∈ T := by
  classical
  have hjne : jel ≠ 0 := by
    intro h0
    exact hnc 0 (by rw [h0, map_zero])
  obtain ⟨Dinf, hDinf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) jel hjne
  set Ds : K → Divisor K F :=
    fun s => if h : jel - algebraMap K F s ≠ 0 then
        (HasPrincipalDivisors.exists_divisor (K := K) (F := F) _ h).choose
      else 0 with hDs_def
  have hDs_spec : ∀ s (v : Place K F) (h : jel - algebraMap K F s ≠ 0),
      (Ds s) v = v.ord (jel - algebraMap K F s) := by
    intro s v h
    rw [hDs_def]
    simp only [dite_eq_left h]
    exact ((HasPrincipalDivisors.exists_divisor (K := K) (F := F) _ h).choose_spec).1 v
  refine ⟨Dinf.support ∪ S.biUnion (fun s => (Ds s).support), ?_⟩
  intro t ht
  rcases ht with hpole | ⟨s, hs, hzero⟩
  · refine Finset.mem_union_left _ ?_
    rw [Finsupp.mem_support_iff, hDinf t]
    have hneg := ExistsBadset.ord_neg_of_notMem hpole
    omega
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩)
    have hne : jel - algebraMap K F s ≠ 0 := by
      intro h0
      rw [h0, Place.ord_zero] at hzero
      omega
    rw [Finsupp.mem_support_iff, hDs_spec s t hne]
    omega

end Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
end AlgebraicCurves.Places.Proofs

namespace AlgebraicCurve.Place



open _root_.AlgebraicCurves.Places.Proofs in
open Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem in
open AlgebraicCurve IsLocalRing in
theorem exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : F) (hx : ∀ c : K, x ≠ algebraMap K F c) (S : Finset K) :
    ∃ T : Finset (Place K F), ∀ t : Place K F,
      (x ∉ t.toValuationSubring ∨ ∃ s ∈ S, 0 < t.ord (x - algebraMap K F s)) → t ∈ T :=
  ExistsBadset.exists_finset_forall_notMem_or_ord_sub_pos_imp_mem x hx S
end AlgebraicCurve.Place
end ProofImplementation
