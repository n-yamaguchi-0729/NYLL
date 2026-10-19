/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Trace on finite projective modules over a commutative ring

Contraction gives a trace without a freeness assumption. Its rank-one formula
proves cyclicity, invariance under isomorphisms, and direct-sum additivity.
The comparison with the trace on any finite free retract identifies this with
the commutative case of the construction in Stacks Project, Section 64.4
(https://stacks.math.columbia.edu/tag/03SZ).

This is the degreewise trace needed for bounded complexes of finite projective
modules. Traces of complexes and traces over noncommutative rings are separate
constructions.
-/

noncomputable section

open Module TensorProduct

namespace LinearMap

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

/-- The trace on a finite projective module, using the canonical contraction
pairing and the dual-tensor description of its endomorphisms. -/
def projectiveTrace : (M →ₗ[R] M) →ₗ[R] R :=
  contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap

@[simp]
theorem projectiveTrace_dualTensorHom (t : Module.Dual R M ⊗[R] M) :
    projectiveTrace R M (dualTensorHom R M M t) = contractLeft R M t := by
  change contractLeft R M ((dualTensorHomEquiv R M M).symm
    (dualTensorHom R M M t)) = contractLeft R M t
  rw [dualTensorHomEquiv_symm_dualTensorHom]

/-- The trace of a rank-one endomorphism is the evaluation pairing. -/
@[simp]
theorem projectiveTrace_smulRight (φ : Module.Dual R M) (m : M) :
    projectiveTrace R M (φ.smulRight m) = φ m := by
  change projectiveTrace R M (dualTensorHom R M M (φ ⊗ₜ[R] m)) = φ m
  rw [projectiveTrace_dualTensorHom, contractLeft_apply]

/-- On a finite free module the projective trace is the usual linear-map trace. -/
theorem projectiveTrace_eq_trace [Module.Free R M] :
    projectiveTrace R M = trace R M :=
  (trace_eq_contract' R M).symm

variable {R M}
variable {N : Type*} [AddCommGroup N] [Module R N]
variable [Module.Finite R N] [Module.Projective R N]

/-- Cyclicity for maps between different finite projective modules. -/
theorem projectiveTrace_comp_comm (f : M →ₗ[R] N) (g : N →ₗ[R] M) :
    projectiveTrace R M (g ∘ₗ f) = projectiveTrace R N (f ∘ₗ g) := by
  obtain ⟨t, rfl⟩ :=
    (show Function.Surjective (dualTensorHom R M N) from
      (dualTensorHomEquiv R M N).surjective) f
  induction t using TensorProduct.inductionOn with
  | tmul φ n =>
      have hleft : g ∘ₗ dualTensorHom R M N (φ ⊗ₜ[R] n) = φ.smulRight (g n) := by
        ext m
        exact g.map_smul (φ m) n
      have hright : dualTensorHom R M N (φ ⊗ₜ[R] n) ∘ₗ g = (φ ∘ₗ g).smulRight n := by
        ext m
        rfl
      rw [hleft, hright, projectiveTrace_smulRight, projectiveTrace_smulRight, comp_apply]
  | add s t hs ht =>
      rw [map_add, comp_add, add_comp, map_add, map_add, hs, ht]

/-- Transporting an endomorphism through a linear isomorphism preserves trace. -/
@[simp]
theorem projectiveTrace_conj (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) :
    projectiveTrace R N (e.conj f) = projectiveTrace R M f := by
  rw [e.conj_apply, projectiveTrace_comp_comm, ← comp_assoc,
    LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    id_comp]

/-- The projective trace can be computed using any embedding into a finite free
module together with a retraction. This is the defining computation of the
commutative projective trace in Stacks Project, Section 64.4. -/
theorem projectiveTrace_eq_trace_of_retraction [Module.Free R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) (h : b ∘ₗ a = id) (f : M →ₗ[R] M) :
    projectiveTrace R M f = trace R N (a ∘ₗ f ∘ₗ b) := by
  calc
    projectiveTrace R M f = projectiveTrace R M ((b ∘ₗ a) ∘ₗ f) := by
      rw [h, id_comp]
    _ = projectiveTrace R N ((a ∘ₗ f) ∘ₗ b) := by
      rw [comp_assoc, projectiveTrace_comp_comm]
    _ = trace R N (a ∘ₗ f ∘ₗ b) := by
      rw [projectiveTrace_eq_trace, comp_assoc]

/-- Additivity on direct sums of finite projective modules. -/
theorem projectiveTrace_prodMap (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    projectiveTrace R (M × N) (f.prodMap g) =
      projectiveTrace R M f + projectiveTrace R N g := by
  have h : f.prodMap g =
      (inl R M N ∘ₗ f) ∘ₗ fst R M N + (inr R M N ∘ₗ g) ∘ₗ snd R M N := by
    apply LinearMap.ext
    intro x
    change (f x.1, g x.2) = (f x.1, 0) + (0, g x.2)
    rw [Prod.mk_add_mk, add_zero, zero_add]
  rw [h, map_add,
    projectiveTrace_comp_comm (fst R M N) (inl R M N ∘ₗ f),
    projectiveTrace_comp_comm (snd R M N) (inr R M N ∘ₗ g),
    ← comp_assoc, fst_comp_inl, id_comp, ← comp_assoc, snd_comp_inr, id_comp]

end LinearMap
