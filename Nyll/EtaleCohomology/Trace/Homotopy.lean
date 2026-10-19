/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Trace.Complex
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Trace on actual homotopy classes

The alternating trace descends through the native homotopy-category quotient.
It is linear, cyclic, and invariant under isomorphisms between bounded finite
projective complexes in that category.
-/

noncomputable section

universe u v

open CategoryTheory

namespace EtaleCohomology

variable (R : Type u) [CommRing R]
variable (C : CochainComplex (ModuleCat.{v} R) ℤ)
variable [∀ i : ℤ, Module.Finite R (C.X i)]
  [∀ i : ℤ, Module.Projective R (C.X i)]
variable (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]

private def homotopyTraceValue
    (f : (HomotopyCategory.quotient _ _).obj C ⟶
      (HomotopyCategory.quotient _ _).obj C) : R :=
  boundedComplexTrace R C a b f.out

private theorem homotopyTraceValue_map (f : C ⟶ C) :
    homotopyTraceValue R C a b ((HomotopyCategory.quotient _ _).map f) =
      boundedComplexTrace R C a b f :=
  boundedComplexTrace_homotopy R C a b (HomotopyCategory.homotopyOutMap f)

/-- The alternating trace on endomorphisms in the native homotopy category. -/
def homotopyComplexTrace :
    ((HomotopyCategory.quotient _ _).obj C ⟶
      (HomotopyCategory.quotient _ _).obj C) →ₗ[R] R where
  toFun := homotopyTraceValue R C a b
  map_add' f g := by
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
    rw [← Functor.map_add, homotopyTraceValue_map, homotopyTraceValue_map,
      homotopyTraceValue_map, map_add]
  map_smul' r f := by
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    rw [← Functor.map_smul, homotopyTraceValue_map, homotopyTraceValue_map, map_smul]
    rfl

/-- Computing the quotient trace on an actual chain map gives its alternating trace. -/
@[simp]
theorem homotopyComplexTrace_map (f : C ⟶ C) :
    homotopyComplexTrace R C a b ((HomotopyCategory.quotient _ _).map f) =
      boundedComplexTrace R C a b f :=
  homotopyTraceValue_map R C a b f

/-- The quotient trace does not depend on the bounding interval. -/
theorem homotopyComplexTrace_independent_bounds
    (a' b' : ℤ) [C.IsStrictlyGE a'] [C.IsStrictlyLE b'] :
    homotopyComplexTrace R C a b = homotopyComplexTrace R C a' b' := by
  apply LinearMap.ext
  intro f
  rfl

variable {C}
variable {D : CochainComplex (ModuleCat.{v} R) ℤ}
variable [∀ i : ℤ, Module.Finite R (D.X i)]
  [∀ i : ℤ, Module.Projective R (D.X i)]
variable (c d : ℤ) [D.IsStrictlyGE c] [D.IsStrictlyLE d]

/-- Cyclicity for arbitrary homotopy classes between bounded finite projective complexes. -/
theorem homotopyComplexTrace_comp_comm
    (f : (HomotopyCategory.quotient _ _).obj C ⟶
      (HomotopyCategory.quotient _ _).obj D)
    (g : (HomotopyCategory.quotient _ _).obj D ⟶
      (HomotopyCategory.quotient _ _).obj C) :
    homotopyComplexTrace R C a b (f ≫ g) = homotopyComplexTrace R D c d (g ≫ f) := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← Functor.map_comp, ← Functor.map_comp,
    homotopyComplexTrace_map, homotopyComplexTrace_map]
  exact boundedComplexTrace_comp_comm R a b c d f g

/-- Isomorphism invariance in the actual homotopy category. -/
theorem homotopyComplexTrace_iso
    (e : (HomotopyCategory.quotient _ _).obj C ≅
      (HomotopyCategory.quotient _ _).obj D)
    (f : (HomotopyCategory.quotient _ _).obj C ⟶
      (HomotopyCategory.quotient _ _).obj C) :
    homotopyComplexTrace R D c d (e.inv ≫ f ≫ e.hom) =
      homotopyComplexTrace R C a b f := by
  rw [homotopyComplexTrace_comp_comm R c d a b e.inv (f ≫ e.hom),
    Category.assoc, e.hom_inv_id, Category.comp_id]

end EtaleCohomology
