/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Ideal.Operations

/-!
# Surjectivity lifted across a nilpotent module quotient

If a submodule generates modulo an ideal whose power annihilates the
ambient module, iteration of the ideal action shows that it generates
the entire module. This argument does not require finite generation.

For actual linear maps `P → M → N`, surjectivity of the composite and
containment of the second map's kernel in `J M` therefore imply
surjectivity of the first map when a power of `J` annihilates `M`.
This is the generator-lifting step used on the original affine modules
of an adic sheaf tower.
-/

universe u v w z

namespace Submodule

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Generation modulo an ideal with nilpotent action gives actual
generation, without any finite-generation hypothesis on the module. -/
theorem eq_top_of_sup_smul_eq_top_of_pow_smul_eq_bot
    (J : Ideal R) (L : Submodule R M) (e : ℕ)
    (h : L ⊔ J • (⊤ : Submodule R M) = ⊤)
    (hpow : J ^ e • (⊤ : Submodule R M) = ⊥) : L = ⊤ := by
  have hiter : ∀ k : ℕ, L ⊔ J ^ k • (⊤ : Submodule R M) = ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul, sup_top_eq]
    | succ k ih =>
      have hmul : J • (J ^ k • (⊤ : Submodule R M)) =
          J ^ (k + 1) • (⊤ : Submodule R M) :=
        (Submodule.mul_smul J (J ^ k) (⊤ : Submodule R M)).symm.trans
          (congrArg (fun K : Ideal R => K • (⊤ : Submodule R M)) (pow_succ' J k).symm)
      have hle : J • (⊤ : Submodule R M) ≤ L ⊔ J ^ (k + 1) • ⊤ := by
        calc
          J • (⊤ : Submodule R M) = J • (L ⊔ J ^ k • ⊤) :=
            congrArg (fun T : Submodule R M => J • T) ih.symm
          _ = J • L ⊔ J • (J ^ k • ⊤) := Submodule.smul_sup J L _
          _ ≤ L ⊔ J ^ (k + 1) • ⊤ := sup_le_sup Submodule.smul_le_right hmul.le
      apply top_unique
      calc
        (⊤ : Submodule R M) = L ⊔ J • ⊤ := h.symm
        _ ≤ L ⊔ (L ⊔ J ^ (k + 1) • ⊤) := sup_le_sup_left hle L
        _ = L ⊔ J ^ (k + 1) • ⊤ := sup_left_idem L (J ^ (k + 1) • ⊤)
  have he : L ⊔ J ^ e • (⊤ : Submodule R M) = ⊤ := hiter e
  rw [hpow, sup_bot_eq] at he
  exact he

end Submodule

namespace LinearMap

variable {R : Type u} [CommRing R]
  {P : Type v} [AddCommGroup P] [Module R P]
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type z} [AddCommGroup N] [Module R N]

/-- A surjective composite lifts through a quotient whose kernel is
contained in an ideal with nilpotent action on the middle module. -/
theorem surjective_of_comp_surjective_of_ker_le_smul_of_pow_smul_eq_bot
    (ψ : P →ₗ[R] M) (q : M →ₗ[R] N) (J : Ideal R) (e : ℕ)
    (hcomp : Function.Surjective (q.comp ψ))
    (hker : q.ker ≤ J • (⊤ : Submodule R M))
    (hpow : J ^ e • (⊤ : Submodule R M) = ⊥) : Function.Surjective ψ := by
  have hsup : ψ.range ⊔ J • (⊤ : Submodule R M) = ⊤ := by
    apply top_unique
    intro x _hx
    obtain ⟨p, hp⟩ := hcomp (q x)
    have hq : q (x - ψ p) = 0 :=
      (map_sub q x (ψ p)).trans (sub_eq_zero.mpr hp.symm)
    have hk : x - ψ p ∈ q.ker := LinearMap.mem_ker.mpr hq
    apply Submodule.mem_sup.mpr
    refine ⟨ψ p, LinearMap.mem_range_self ψ p, x - ψ p, hker hk, ?_⟩
    exact (add_comm (ψ p) (x - ψ p)).trans (sub_add_cancel x (ψ p))
  exact LinearMap.range_eq_top.mp
    (Submodule.eq_top_of_sup_smul_eq_top_of_pow_smul_eq_bot J ψ.range e hsup hpow)

end LinearMap
