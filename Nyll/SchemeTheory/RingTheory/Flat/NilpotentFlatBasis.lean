/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Lifting arbitrary bases across a nilpotent maximal ideal

If the maximal ideal of a local ring is nilpotent, a generating family of
the closed fibre generates an arbitrary module. For a flat module, the
existing linear-independence criterion then lifts every prescribed basis
of that fibre. Neither the module nor the chosen basis is required to be
finite. This is the form of Stacks, Tag 051F used for the compatible
infinitesimal quotients of a strict henselization.
-/

noncomputable section

open Module TensorProduct

universe u v w

namespace Submodule

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The nilpotent-ideal form of Nakayama does not require finite generation. -/
theorem eq_top_of_sup_smul_eq_top_of_isNilpotent (I : Ideal R)
    (hI : IsNilpotent I) (N : Submodule R M)
    (hN : N ⊔ I • (⊤ : Submodule R M) = ⊤) : N = ⊤ := by
  have hpow : ∀ n : ℕ, N ⊔ I ^ n • (⊤ : Submodule R M) = ⊤ := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul, sup_top_eq]
    | succ n ih =>
      symm
      calc
        (⊤ : Submodule R M) = N ⊔ I ^ n • (⊤ : Submodule R M) := ih.symm
        _ = N ⊔ I ^ n • (N ⊔ I • (⊤ : Submodule R M)) :=
          congrArg (fun P : Submodule R M => N ⊔ I ^ n • P) hN.symm
        _ = N ⊔ (I ^ n • N ⊔ (I ^ n * I) • (⊤ : Submodule R M)) := by
          rw [smul_sup, mul_smul]
        _ = N ⊔ I ^ (n + 1) • (⊤ : Submodule R M) := by
          have hsup : N ⊔ I ^ n • N = N :=
            sup_of_le_left (show I ^ n • N ≤ N from smul_le_right)
          rw [← pow_succ, ← sup_assoc, hsup]
  obtain ⟨n, hn⟩ := hI
  have hn' : I ^ n = ⊥ := hn
  have h := hpow n
  rw [hn', bot_smul, sup_bot_eq] at h
  exact h

end Submodule

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- A family spanning the closed fibre spans the entire module when the
maximal ideal is nilpotent, without any finiteness assumption. -/
theorem span_eq_top_of_tensorProduct_span_eq_top_of_isNilpotent
    (hNil : IsNilpotent (maximalIdeal R)) {ι : Type w} (v : ι → M)
    (hv : Submodule.span (ResidueField R)
      (Set.range (TensorProduct.mk R (ResidueField R) M 1 ∘ v)) = ⊤) :
    Submodule.span R (Set.range v) = ⊤ := by
  let μ : M →ₗ[R] ResidueField R ⊗[R] M :=
    TensorProduct.mk R (ResidueField R) M 1
  have hmap : (Submodule.span R (Set.range v)).map μ = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp,
      ← Submodule.restrictScalars_span R (ResidueField R)
        Ideal.Quotient.mk_surjective]
    change (Submodule.span (ResidueField R)
      (Set.range (TensorProduct.mk R (ResidueField R) M 1 ∘ v))).restrictScalars R = ⊤
    rw [hv, Submodule.restrictScalars_top]
  have hsup := congrArg (Submodule.comap μ) hmap
  rw [Submodule.comap_map_eq, Submodule.comap_top] at hsup
  have hker : LinearMap.ker μ = maximalIdeal R • (⊤ : Submodule R M) :=
    LinearMap.ker_tensorProductMk M
  rw [hker] at hsup
  exact Submodule.eq_top_of_sup_smul_eq_top_of_isNilpotent
    (maximalIdeal R) hNil (Submodule.span R (Set.range v)) hsup

/-- Every prescribed basis of the closed fibre of a flat module lifts
along every choice of representatives. This is Stacks, Tag 051F; the
index type and the module may be infinite. -/
theorem exists_basis_of_flat_of_isNilpotent_maximalIdeal [Module.Flat R M]
    (hNil : IsNilpotent (maximalIdeal R)) {ι : Type w} (v : ι → M)
    (b : Basis ι (ResidueField R) (ResidueField R ⊗[R] M))
    (hb : ∀ i, 1 ⊗ₜ[R] v i = b i) :
    ∃ bR : Basis ι R M, ∀ i, bR i = v i := by
  have hfamily : TensorProduct.mk R (ResidueField R) M 1 ∘ v = b := funext hb
  have hli : LinearIndependent (ResidueField R)
      (TensorProduct.mk R (ResidueField R) M 1 ∘ v) := by
    rw [hfamily]
    exact b.linearIndependent
  have hspan : Submodule.span (ResidueField R)
      (Set.range (TensorProduct.mk R (ResidueField R) M 1 ∘ v)) = ⊤ := by
    rw [hfamily, b.span_eq]
  have hliR : LinearIndependent R v := Module.IsLocalRing.linearIndependent_of_flat v hli
  have hspanR : Submodule.span R (Set.range v) = ⊤ :=
    span_eq_top_of_tensorProduct_span_eq_top_of_isNilpotent hNil v hspan
  refine ⟨Basis.mk hliR hspanR.ge, ?_⟩
  intro i
  exact Basis.mk_apply hliR hspanR.ge i

/-- Every flat module over a local ring with nilpotent maximal ideal is
free, including modules of infinite rank. -/
theorem free_of_flat_of_isNilpotent_maximalIdeal [Module.Flat R M]
    (hNil : IsNilpotent (maximalIdeal R)) : Module.Free R M := by
  let b := Module.Free.chooseBasis (ResidueField R) (ResidueField R ⊗[R] M)
  obtain ⟨v, hv⟩ :=
    (TensorProduct.mk_surjective R M (ResidueField R) Ideal.Quotient.mk_surjective).comp_left b
  obtain ⟨bR, _⟩ := exists_basis_of_flat_of_isNilpotent_maximalIdeal
    hNil v b (fun i => congrFun hv i)
  exact Module.Free.of_basis bR

end IsLocalRing
