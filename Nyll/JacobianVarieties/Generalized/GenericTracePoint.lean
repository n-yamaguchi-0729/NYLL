/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.StructureMorphism
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Generic points for evaluating curve traces

The actual function-field point factors through every nonempty open of an
integral scheme. Scalar algebra maps provide its evaluation points over
extensions and formal rings.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory
namespace AlgebraicGeometry.GeneralizedJacobian

/-- The actual scalar-extension point map used to evaluate the generic trace. -/
def traceScalarPointMap
    {K A B : Type u} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext f.comp_algebraMap))

/-- The original curve generic point, factored through its given nonempty open. -/
def genericOpenPoint {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) (U : C.Opens) (hU : (U : Set C).Nonempty) :
    let _ : Algebra K C.functionField := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K C.functionField))) ⟶
      Over.mk (U.ι ≫ c) := by
  intro alg
  have hη : genericPoint C ∈ U :=
    ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  refine Over.homMk (U.fromSpecStalkOfMem (genericPoint C) hη) ?_
  change U.fromSpecStalkOfMem (genericPoint C) hη ≫ U.ι ≫ c =
    Spec.map (CommRingCat.ofHom (algebraMap K C.functionField))
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    AlgebraicCurve.fromSpecStalk_genericPoint_comp_base]

/-- The generic open point is the actual function-field point of the original curve. -/
theorem genericOpenPoint_comp {K : Type u} [Field K] {C : Scheme.{u}} [IsIntegral C]
    (c : C ⟶ Spec (.of K)) (U : C.Opens) (hU : (U : Set C).Nonempty) :
    (genericOpenPoint c U hU).left ≫ U.ι = C.fromSpecStalk (genericPoint C) :=
  Scheme.Opens.fromSpecStalkOfMem_ι _ _ _

end AlgebraicGeometry.GeneralizedJacobian
