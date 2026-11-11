/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.RegularLocal.DepthTwoRegularPair
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Noetherian.Basic
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# Regular pairs and boundary depth of dual modules

A regular pair on the target module remains regular on a module of linear
maps. The second regularity statement is proved by uniquely dividing each
value by the first parameter and checking that the resulting map is linear.
In particular, duals and double duals have depth at least two over any
Noetherian local ring of depth at least two. No domain assumption is used.

This is an algebraic input to the reflexive extension of Stacks 0EY6.
It does not assert coherence of the open direct image or surjectivity of
the bidual evaluation map.
-/

@[expose] public section

noncomputable section

open RingTheory IsLocalRing
open scoped Pointwise

namespace SchemeTheory

variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private theorem exists_linearMap_smul_eq_of_values_mem
    {x : R} (hx : IsSMulRegular N x) (f : M →ₗ[R] N)
    (hf : ∀ m, f m ∈ x • (⊤ : Submodule R N)) :
    ∃ g : M →ₗ[R] N, x • g = f := by
  have hdiv (m : M) : ∃ n : N, x • n = f m := by
    obtain ⟨n, -, hn⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists (f m) x ⊤).mp (hf m)
    exact ⟨n, hn⟩
  choose g hg using hdiv
  let gₗ : M →ₗ[R] N :=
    { toFun := g
      map_add' := fun a b => by
        apply hx
        change x • g (a + b) = x • (g a + g b)
        rw [hg, smul_add, hg, hg, map_add]
      map_smul' := fun r m => by
        apply hx
        change x • g (r • m) = x • (r • g m)
        rw [hg, smul_comm x r, hg, f.map_smul] }
  refine ⟨gₗ, ?_⟩
  ext m
  exact hg m

/-- A regular element on the target acts regularly on all linear maps
into that target. -/
theorem isSMulRegular_linearMap_of_target {x : R} (hx : IsSMulRegular N x) :
    IsSMulRegular (M →ₗ[R] N) x := by
  intro f g hfg
  ext m
  apply hx
  exact congrArg (fun h : M →ₗ[R] N => h m) hfg

/-- A regular pair on the target remains regular on a module of linear
maps. This applies to duals without requiring a domain or projectivity. -/
theorem isWeaklyRegular_pair_linearMap
    {x y : R} (hxy : Sequence.IsWeaklyRegular N [x, y]) :
    Sequence.IsWeaklyRegular (M →ₗ[R] N) [x, y] := by
  obtain ⟨hx, hy⟩ := (Sequence.isWeaklyRegular_cons_iff N x [y]).mp hxy
  have hy' : IsSMulRegular (QuotSMulTop x N) y :=
    (Sequence.isWeaklyRegular_singleton_iff (QuotSMulTop x N) y).mp hy
  apply Sequence.IsWeaklyRegular.cons (isSMulRegular_linearMap_of_target hx)
  apply Sequence.IsWeaklyRegular.cons
  · apply (isSMulRegular_quotient_iff_mem_of_smul_mem
      (x • (⊤ : Submodule R (M →ₗ[R] N))) y).mpr
    intro f hf
    obtain ⟨g, -, hg⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists (y • f) x ⊤).mp hf
    have hfvalues (m : M) : f m ∈ x • (⊤ : Submodule R N) := by
      apply mem_of_isSMulRegular_quotient_of_smul_mem hy'
      apply (Submodule.mem_smul_pointwise_iff_exists (y • f m) x ⊤).mpr
      refine ⟨g m, Submodule.mem_top, ?_⟩
      exact congrArg (fun h : M →ₗ[R] N => h m) hg
    obtain ⟨g', hg'⟩ := exists_linearMap_smul_eq_of_values_mem hx f hfvalues
    exact (Submodule.mem_smul_pointwise_iff_exists f x ⊤).mpr
      ⟨g', Submodule.mem_top, hg'⟩
  · exact Sequence.IsWeaklyRegular.nil R _

/-- The actual dual has depth at least two wherever the base local ring
does. The module being dualized need not be finite. -/
theorem two_le_depth_dual
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (hdepth : (2 : ℕ∞) ≤ Module.depth R R) :
    (2 : ℕ∞) ≤ Module.depth R (Module.Dual R M) := by
  obtain ⟨x, hx, y, hy, hxy, -⟩ := exists_regular_pair_of_two_le_depth R hdepth
  have hpair : Sequence.IsWeaklyRegular (Module.Dual R M) [x, y] :=
    isWeaklyRegular_pair_linearMap hxy
  have hmem : ∀ r ∈ [x, y], r ∈ maximalIdeal R := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hx
    · exact (List.mem_singleton.mp hr) ▸ hy
  exact le_sSup ⟨[x, y], hpair, hmem, rfl⟩

/-- The evaluation map of a dual has its actual canonical left inverse:
precomposition with the evaluation map of the original module. -/
theorem dual_eval_leftInverse :
    Function.LeftInverse
      (Module.Dual.eval R M).dualMap (Module.Dual.eval R (Module.Dual R M)) := by
  intro f
  ext m
  rfl

/-- The double dual of a finite module is finite, has an injective
canonical evaluation map, and has depth at least two under the boundary
depth hypothesis. Reflexivity additionally requires surjectivity. -/
theorem finite_bidual_depth_and_eval_injective
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdepth : (2 : ℕ∞) ≤ Module.depth R R) :
    Module.Finite R (Module.Dual R (Module.Dual R M)) ∧
      (2 : ℕ∞) ≤ Module.depth R (Module.Dual R (Module.Dual R M)) ∧
      Function.Injective
        (Module.Dual.eval R (Module.Dual R (Module.Dual R M))) := by
  refine ⟨inferInstance, two_le_depth_dual R (Module.Dual R M) hdepth, ?_⟩
  exact (dual_eval_leftInverse (R := R) (M := Module.Dual R M)).injective

end SchemeTheory
