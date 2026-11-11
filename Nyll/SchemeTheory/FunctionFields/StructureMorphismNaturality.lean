/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.GenericFieldSourceNaturality
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-! # Structural coefficients of the actual map of function fields -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicCurve

universe u

/-- Pullback of rational functions preserves the original structural
coefficient map. The equality follows from the actual generic-point square. -/
theorem functionFieldMap_comp_baseToFunctionField
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    (c : X ⟶ Spec (.of k)) (f : Y ⟶ X) (hf : DenseRange f) :
    (f.functionFieldMap hf).comp (baseToFunctionField c) =
      baseToFunctionField (f ≫ c) := by
  have h : CommRingCat.ofHom
      ((f.functionFieldMap hf).comp (baseToFunctionField c)) =
        CommRingCat.ofHom (baseToFunctionField (f ≫ c)) := by
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom (baseToFunctionField c) ≫
      CommRingCat.ofHom (f.functionFieldMap hf)) = _
    rw [Spec.map_comp, ← fromSpecStalk_genericPoint_comp_base c,
      ← Category.assoc,
      EtaleFundamentalGroups.Spec_functionFieldMap_fromSpecStalk f hf,
      Category.assoc, fromSpecStalk_genericPoint_comp_base (f ≫ c)]
  exact congrArg CommRingCat.Hom.hom h

end AlgebraicCurve
