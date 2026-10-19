/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkPuncture
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Nyll.SchemeTheory.RingTheory.Flat.LocalAdicBasis
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# A common basis in the actual adic quotients of a geometric stalk

For a closed geometric point of a local ring, the actual structure map is
flat and its extended maximal ideal is the maximal ideal of the actual
geometric stalk. The tensor-product bases of a flat module therefore give
bases of the geometric stalk's actual infinitesimal quotients. Every basis
uses the same family of elements of the stalk. This constructs the data in
Stacks, Tag 07QM, part (4), with the original structure homomorphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module IsLocalRing TensorProduct

universe u

namespace EtaleFundamentalGroups.StrictHenselian

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [Field Ω]
  (φ : R →+* Ω) [IsLocalHom φ]

/-- One family of actual germs gives bases in all positive adic quotients.
The quotient ideals are identified with powers of the actual maximal
ideal, and the scalar maps are induced by the original structure map. -/
theorem geometricStalk_exists_common_quotient_bases :
    let H : Type u := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let _ : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    ∃ (ι : Type u) (x : ι → H), ∀ n : ℕ,
      (maximalIdeal R ^ (n + 1)).map (algebraMap R H) = maximalIdeal H ^ (n + 1) ∧
      ∃ bₙ : Basis ι (R ⧸ maximalIdeal R ^ (n + 1))
          (H ⧸ (maximalIdeal R ^ (n + 1)).map (algebraMap R H)),
        ∀ i, bₙ i = Ideal.Quotient.mk
          ((maximalIdeal R ^ (n + 1)).map (algebraMap R H)) (x i) := by
  intro H algebraH
  have : Module.Flat R H := geometricStalkStructureMap_flat φ
  obtain ⟨ι, x, _, hx⟩ := IsLocalRing.exists_common_basis_tensor_quotient_pow (R := R) (M := H)
  refine ⟨ι, x, ?_⟩
  intro n
  constructor
  · rw [Ideal.map_pow]
    exact congrArg (fun I : Ideal H => I ^ (n + 1))
      (geometricStalkStructureMap_map_maximalIdeal φ)
  · obtain ⟨b, hb⟩ := hx n
    let I : Ideal R := maximalIdeal R ^ (n + 1)
    let e : (H ⧸ I.map (algebraMap R H)) ≃ₐ[R ⧸ I] (R ⧸ I) ⊗[R] H :=
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor H I
    refine ⟨b.map e.symm.toLinearEquiv, ?_⟩
    intro i
    apply e.injective
    change e (e.symm (b i)) = e (Ideal.Quotient.mk (I.map (algebraMap R H)) (x i))
    rw [e.apply_symm_apply, hb i,
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]

end EtaleFundamentalGroups.StrictHenselian
