/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.FieldTheory.IsSepClosed

/-!
# A constant closure embedded through an actual field point

An actual geometric point over an intermediate field fixes its embedding
into the geometric coefficient field. A separable closure of that same
intermediate field can be embedded extending this specified point. The
construction therefore supplies one coefficient embedding compatible with
an already chosen constant-cover point, rather than identifying unrelated
geometric points selected by different fiber comparisons.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace SchemeTheory

universe u

/-- Extend the actual intermediate-field point to its specified separable
closure, retaining its original map over the ground field. -/
theorem exists_constantClosureEmbedding_over_point
    (k E κ Ω : Type u) [Field k] [Field E] [Field κ] [Field Ω]
    [Algebra k E] [Algebra E κ] [Algebra k κ] [IsScalarTower k E κ]
    [Algebra k Ω] [IsSepClosure E κ] [IsSepClosed Ω]
    (p : SchemeHomOver (Spec.algebraMap k Ω) (Spec.algebraMap k E)) :
    ∃ a : κ →ₐ[k] Ω,
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ Spec.algebraMap E κ = p.val := by
  let β : E →ₐ[k] Ω := Spec.homEquivAlgHom p
  let : Algebra E Ω := β.toRingHom.toAlgebra
  have : IsScalarTower k E Ω := IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
  let α : κ →ₐ[E] Ω := IsSepClosed.lift (K := E) (L := κ) (M := Ω)
  refine ⟨α.restrictScalars k, ?_⟩
  have hring : (α.restrictScalars k).toRingHom.comp (algebraMap E κ) = β.toRingHom :=
    α.comp_algebraMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hring]
  exact Spec.map_preimage p.val

end SchemeTheory
