/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.PointedCoverStabilizerPreimage

/-!
# The actual embedded field selected by a finite-cover point

The original point stabilizer, pulled back along the original generic
Galois map, is exactly the fixing subgroup of the literal embedded
function field. The embedding is the one supplied by that same point.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The selected point of an arbitrary connected finite étale cover
determines its actual embedded function field through its fixing subgroup. -/
theorem finiteEtaleGenericFieldRange_fixingSubgroup
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U] [IsLocallyNoetherian U]
    (Ω : Type u) [Field Ω] [Algebra U.functionField Ω]
    [IsSepClosure U.functionField Ω] [IsSepClosed Ω]
    (W : FiniteEtale U) [IsConnected W]
    (w : (fiber (U.genericExtensionMorphism Ω)).obj W) :
    let : IsIntegral W.left := isIntegral_left_of_isConnected_finiteEtale W
    let : Algebra U.functionField W.left.functionField := finiteEtaleFunctionFieldAlgebra W
    let g := fiberObjEquivHom (U.genericExtensionMorphism Ω) W w
    let β := finiteEtaleGenericHomFunctionFieldAlgHom W g
    β.fieldRange.fixingSubgroup =
      (MulAction.stabilizer π₁ᵉᵗ(U.genericExtensionMorphism Ω) w).comap
        (absoluteGenericGaloisToFundamentalGroup U Ω) := by
  intro intW algKL g β
  let : Algebra W.left.functionField Ω := β.toRingHom.toAlgebra
  have : IsScalarTower U.functionField W.left.functionField Ω :=
    IsScalarTower.of_algebraMap_eq' β.comp_algebraMap.symm
  rw [pointedCoverStabilizer_comap_absoluteGenericGalois Ω W w]
  apply Subgroup.ext
  intro σ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ
    let τ : Gal(Ω/W.left.functionField) :=
      { σ with commutes' := fun a => hσ (β a) ⟨a, rfl⟩ }
    exact ⟨τ, AlgEquiv.ext (fun _ => rfl)⟩
  · rintro ⟨τ, rfl⟩ x ⟨a, rfl⟩
    exact τ.commutes a

end EtaleFundamentalGroups.Inertia
