/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.GradedReesAlgebra

/-!
# Degree-one generation of the Rees algebra

The degree-one elements associated to the original ideal generate the actual
Rees subalgebra. This identifies the degree-one affine charts of its Proj.
-/

noncomputable section

universe u

open Polynomial

namespace ReesAlgebra

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual degree-one element `aT` attached to `a ∈ I`. -/
def degreeOne (a : I) : reesAlgebra I :=
  monomial I 1 ⟨a.val, by rw [pow_one]; exact a.property⟩

lemma degreeOne_mem (a : I) : degreeOne I a ∈ homogeneousPart I 1 :=
  ⟨⟨a.val, by rw [pow_one]; exact a.property⟩, rfl⟩

/-- The ideal's degree-one elements generate its actual Rees algebra. -/
theorem adjoin_degreeOne : Algebra.adjoin R (Set.range (degreeOne I)) = ⊤ := by
  apply Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  have hi : (reesAlgebra I).val '' Set.range (degreeOne I) =
      (Submodule.map (Polynomial.monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
    apply Set.ext
    intro p
    constructor
    · rintro ⟨q, ⟨a, rfl⟩, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨degreeOne I ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  rw [hi]
  exact adjoin_monomial_eq_reesAlgebra (R := R) (I := I)

/-- The same concrete degree-one family generates over the native degree-zero
ring used by Proj. -/
theorem adjoin_degreeOne_degreeZero :
    Algebra.adjoin (homogeneousPart I 0) (Set.range (degreeOne I)) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ Algebra.adjoin R (Set.range (degreeOne I)) := by
    rw [adjoin_degreeOne]
    trivial
  refine Algebra.adjoin_induction (R := R)
    (p := fun x _ => x ∈ Algebra.adjoin (homogeneousPart I 0) (Set.range (degreeOne I)))
    (fun x hx => Algebra.subset_adjoin hx) (fun r => ?_)
    (fun x y _ _ hx hy => Subalgebra.add_mem _ hx hy)
    (fun x y _ _ hx hy => Subalgebra.mul_mem _ hx hy) hx
  exact (Algebra.adjoin (homogeneousPart I 0) (Set.range (degreeOne I))).algebraMap_mem
    (degreeZeroEquiv I r)

end ReesAlgebra
