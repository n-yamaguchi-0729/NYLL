/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_toNat_add_toNat_le_finrank_H0_gluedLinesSections_add.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Algebra.Subalgebra.Prod
import Mathlib.RingTheory.Polynomial.DegreeLT
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.FinrankH0GluedLinesSections
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.GluedLines
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.FinrankH0SubFinrankH1GluedLinesSections

/-!
# Two Chart Cech to Nat add to Nat le finrank H0 glued Lines Sections add
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartToNatAddToNatLeFinrankH0

open _root_.LaurentPolynomial
open _root_.TwoChartCech
open _root_.Polynomial


universe u

open GluedLinesH0NegativeTwist.GLH0Neg

namespace GLH0Neg

variable {k : Type u} [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (n m : ℤ)

theorem toLaurent_conds {p : k[X]} {N : ℕ} (hp : p ∈ degreeLT k N) (hN : ∀ d : ℕ, d < N → (d : ℤ) ≤
  n) :
    toLaurent p ∈ polyPart k ∧ toLaurent p * T (-n) ∈ invPolyPart k := by
  have hb := toLaurent_support_bound hp
  refine ⟨(mem_polyPart_iff k).mpr fun d hd => (hb d hd).1, (mem_invPolyPart_iff k).mpr fun d hd =>
    ?_⟩
  rw [support_mul_T, Finset.mem_map] at hd
  obtain ⟨e, he, rfl⟩ := hd
  have h0 := (hb e he).1
  have h1 := (hb e he).2
  have h2 := hN e.toNat (by omega)
  change e + -n ≤ 0
  omega

/-- The differences of the two polynomial values at the nodes, weighted by the gluing units. -/
noncomputable def nodeDiff (N M : ℕ) : (↥(degreeLT k N) × ↥(degreeLT k M)) →ₗ[k] (Fin s → k) :=
  (evalAt a N).comp (LinearMap.fst k _ _) -
    (LinearMap.pi fun i => (lam i : k) • LinearMap.proj i).comp
      ((evalAt b M).comp (LinearMap.snd k _ _))

theorem finrank_H0_ge (ha : Function.Injective a) (N M : ℕ) (hN : ∀ d : ℕ, d < N → (d : ℤ) ≤ n) (hM
  : ∀ d : ℕ, d < M → (d : ℤ) ≤ m) :
    N + M ≤ Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 + s := by
  classical
  let V := LinearMap.ker (nodeDiff a b lam N M)
  have cond : ∀ pq : V, GluedCond a b lam (toLaurent (pq.1.1.1), toLaurent (pq.1.2.1)) := by
    intro pq i
    have h0 : (pq.1.1.1).eval (a i : k) - (lam i : k) * (pq.1.2.1).eval (b i : k) = 0 :=
      congrFun (LinearMap.mem_ker.mp pq.2) i
    simp only [levalUnit_toLaurent]
    exact sub_eq_zero.mp h0
  let Ψ : V →ₗ[k] ↥(gluedLinesSections k a b lam n m).H0 :=
    { toFun := fun pq => mkH0 a b lam n m (toLaurent pq.1.1.1, toLaurent pq.1.2.1) (cond pq)
        (Subalgebra.mem_prod.mpr ⟨(toLaurent_conds n pq.1.1.2 hN).1, (toLaurent_conds m pq.1.2.2
          hM).1⟩)
        (toLaurent_conds n pq.1.1.2 hN).2 (toLaurent_conds m pq.1.2.2 hM).2
      map_add' := fun p q => by
        apply ext_of_fst_snd
        · simpa only [fstL_add, fstL_mkH0, Submodule.coe_add, Prod.fst_add] using
            map_add Polynomial.toLaurent p.1.1.1 q.1.1.1
        · simpa only [sndL_add, sndL_mkH0, Submodule.coe_add, Prod.snd_add] using
            map_add Polynomial.toLaurent p.1.2.1 q.1.2.1
      map_smul' := fun c p => by
        apply ext_of_fst_snd
        · simp only [fstL_mkH0, RingHom.id_apply, fstL_smul]
          change toLaurent (c • p.1.1.1) = c • toLaurent p.1.1.1
          rw [Polynomial.smul_eq_C_mul, map_mul, Polynomial.toLaurent_C,
            LaurentPolynomial.smul_eq_C_mul]
        · simp only [sndL_mkH0, RingHom.id_apply, sndL_smul]
          change toLaurent (c • p.1.2.1) = c • toLaurent p.1.2.1
          rw [Polynomial.smul_eq_C_mul, map_mul, Polynomial.toLaurent_C,
            LaurentPolynomial.smul_eq_C_mul] }
  have hΨ : Function.Injective Ψ := by
    intro p q hpq
    have h1 := congrArg (fstL a b lam n m) hpq
    have h2 := congrArg (sndL a b lam n m) hpq
    simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, fstL_mkH0, sndL_mkH0] at h1 h2
    exact Subtype.ext (Prod.ext (Subtype.ext (Polynomial.toLaurent_injective h1))
      (Subtype.ext (Polynomial.toLaurent_injective h2)))
  have hV : N + M ≤ Module.finrank k V + s := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (nodeDiff a b lam N M)
    have h2 : Module.finrank k (↥(degreeLT k N) × ↥(degreeLT k M)) = N + M := by
      rw [Module.finrank_prod, LinearEquiv.finrank_eq (degreeLTEquiv k N), LinearEquiv.finrank_eq
        (degreeLTEquiv k M),
        Module.finrank_fin_fun, Module.finrank_fin_fun]
    have h3 : Module.finrank k (LinearMap.range (nodeDiff a b lam N M)) ≤ s := by
      calc Module.finrank k (LinearMap.range (nodeDiff a b lam N M)) ≤ Module.finrank k (Fin s → k)
        :=
            Submodule.finrank_le _
        _ = s := Module.finrank_fin_fun k
    change N + M ≤ Module.finrank k (LinearMap.ker (nodeDiff a b lam N M)) + s
    rw [h2] at h1
    omega
  have hfin : Module.Finite k ↥(gluedLinesSections k a b lam n m).H0 :=
    (TwoChartCech.finrank_H0_sub_finrank_H1_gluedLinesSections k a b lam ha n m).1
  have := LinearMap.finrank_le_finrank_of_injective hΨ
  omega

end GLH0Neg

theorem _root_.TwoChartCech.toNat_add_toNat_le_finrank_H0_gluedLinesSections_add
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) (n m : ℤ) :
    (n + 1).toNat + (m + 1).toNat ≤ Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 + s :=
  GLH0Neg.finrank_H0_ge a b lam n m ha (n + 1).toNat (m + 1).toNat (fun d hd =>
    by omega) (fun d hd => by omega)
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartToNatAddToNatLeFinrankH0
end ProofImplementation
