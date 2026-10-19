/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.DirectSumExactness
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FinitePiCoefficients
import Nyll.SchemeTheory.RingTheory.AdicCompletion.CommonBasis
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness of the completion of an arbitrary free module

Given a finite relation in the completed free module, use its original
matrix over the base ring. Its kernel is a finite module. Uniform
Artin–Rees exactness for direct sums lifts the completed relation to the
completion of this kernel, and a finite set of generators lifts it to
a finite coefficient vector. The original relation is therefore
trivial in the equational criterion for flatness.

The index set of the free module is arbitrary. In particular, this
argument does not identify the completion of an infinite direct sum
with its tensor product with the completed base ring.

For a local base ring, a single family lifting a residue-field basis
then proves flatness of the maximal-ideal completion of any flat module.

## Reference

Stacks Project, Lemma 15.28.2, Tag 06LE.
-/

noncomputable section

namespace AdicCompletion

universe u v a

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)

/-- The adic completion of a free module on any index set is flat. -/
@[stacks 06LE]
theorem flat_finsupp (α : Type a) : Module.Flat R (AdicCompletion I (α →₀ R)) := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hfx
  let g : (Fin l → R) →ₗ[R] R := ∑ i : Fin l, f i • LinearMap.proj i
  have hg (v : Fin l → R) : g v = ∑ i : Fin l, f i * v i := by
    simp only [g, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
  have hgb (j : Fin l) : g (fun i => if j = i then 1 else 0) = f j := by
    rw [hg]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_eq_left]
  let E := finsuppPiCompletion α (Fin l) I
  let z : AdicCompletion I (α →₀ (Fin l → R)) := E.symm x
  have hz : map I (Finsupp.mapRange.linearMap (α := α) g) z = 0 := by
    rw [map_finsupp_functional]
    have heval (i : Fin l) : finsuppPiCompletion α (Fin l) I z i = x i :=
      congrFun (E.apply_symm_apply x) i
    simp only [hgb, heval]
    exact hfx
  have hexact := map_finsupp_exact_of_finite I α
    (LinearMap.ker g).subtype g (Submodule.injective_subtype _)
    g.exact_subtype_ker_map
  obtain ⟨w, hw⟩ := (hexact z).mp hz
  obtain ⟨k, p, hp⟩ := Module.Finite.exists_fin' R (LinearMap.ker g)
  have hpmap : Function.Surjective (Finsupp.mapRange.linearMap (α := α) p) :=
    Finsupp.mapRange_surjective p p.map_zero hp
  obtain ⟨y, hy⟩ := AdicCompletion.map_surjective I hpmap w
  let p' : (Fin k → R) →ₗ[R] (Fin l → R) := (LinearMap.ker g).subtype.comp p
  have hpre : map I (Finsupp.mapRange.linearMap (α := α) p') y = z := by
    change map I (Finsupp.mapRange.linearMap (α := α)
      ((LinearMap.ker g).subtype.comp p)) y = z
    rw [map_finsupp_comp_apply I α p (LinearMap.ker g).subtype y, hy, hw]
  refine ⟨k, fun i j => p' (fun a => if j = a then 1 else 0) i,
    finsuppPiCompletion α (Fin k) I y, ?_, ?_⟩
  · intro i
    calc
      x i = finsuppPiCompletion α (Fin l) I z i :=
        (congrFun (E.apply_symm_apply x) i).symm
      _ = finsuppPiCompletion α (Fin l) I
          (map I (Finsupp.mapRange.linearMap (α := α) p') y) i :=
        congrArg (fun q => finsuppPiCompletion α (Fin l) I q i) hpre.symm
      _ = ∑ j : Fin k, p' (fun a => if j = a then 1 else 0) i •
          finsuppPiCompletion α (Fin k) I y j :=
        finsuppPiCompletion_map α (Fin k) I (Fin l) p' y i
  · intro j
    rw [← hg]
    exact (p (fun a => if j = a then 1 else 0)).property

/-- The completion of any free module over a Noetherian ring is flat,
with no finiteness assumption on its basis. -/
theorem flat_of_free (M : Type v) [AddCommGroup M] [Module R M] [Module.Free R M] :
    Module.Flat R (AdicCompletion I M) := by
  let e := Module.Free.chooseBasis R M
  have hflat := flat_finsupp I (Module.Free.ChooseBasisIndex R M)
  exact (Module.Flat.equiv_iff
    ((congr I e.repr).restrictScalars R).symm).mp hflat

/-- Over a Noetherian local ring, the maximal-ideal completion of an
arbitrary flat module is flat. The comparison with a completed free
module is constructed from actual representatives of a residue basis. -/
theorem flat_maximalIdeal_of_flat [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Flat R M] :
    Module.Flat R (AdicCompletion (IsLocalRing.maximalIdeal R) M) := by
  obtain ⟨ι, _, e, _⟩ :=
    exists_finsupp_completion_equiv_of_flat (R := R) (M := M)
  exact (Module.Flat.equiv_iff (e.restrictScalars R)).mp
    (flat_finsupp (IsLocalRing.maximalIdeal R) ι)

end AdicCompletion
