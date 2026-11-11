/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.FiniteProjectiveTrace
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Trace additivity in short exact sequences

An endomorphism of an actual short exact sequence of finite projective modules
has middle trace equal to the sum of its outer traces. The splitting used in
the proof is supplied by projectivity; it need not commute with the given
endomorphism. This is the algebraic cancellation used in cohomological trace
calculations.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace EtaleCohomology

variable {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{v} R)}
  [Module.Finite R S.X₁] [Module.Projective R S.X₁]
  [Module.Finite R S.X₂] [Module.Projective R S.X₂]
  [Module.Finite R S.X₃] [Module.Projective R S.X₃]

/-- Additivity of trace on a split sequence, without an equivariant splitting. -/
theorem projectiveTrace_eq_add_of_splitting (s : S.Splitting) (φ : S ⟶ S) :
    LinearMap.projectiveTrace R S.X₂ φ.τ₂.hom =
      LinearMap.projectiveTrace R S.X₁ φ.τ₁.hom +
        LinearMap.projectiveTrace R S.X₃ φ.τ₃.hom := by
  have h : φ.τ₂ = (φ.τ₂ ≫ s.r) ≫ S.f + (φ.τ₂ ≫ S.g) ≫ s.s := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, s.id,
      Category.comp_id]
  rw [h, ModuleCat.hom_add, map_add]
  have hleft :
      LinearMap.projectiveTrace R S.X₂ ((φ.τ₂ ≫ s.r) ≫ S.f).hom =
        LinearMap.projectiveTrace R S.X₁ φ.τ₁.hom := by
    rw [ModuleCat.hom_comp, LinearMap.projectiveTrace_comp_comm]
    change LinearMap.projectiveTrace R S.X₁ (S.f ≫ φ.τ₂ ≫ s.r).hom = _
    rw [← φ.comm₁₂_assoc, s.f_r, Category.comp_id]
  have hright :
      LinearMap.projectiveTrace R S.X₂ ((φ.τ₂ ≫ S.g) ≫ s.s).hom =
        LinearMap.projectiveTrace R S.X₃ φ.τ₃.hom := by
    rw [φ.comm₂₃, ModuleCat.hom_comp, LinearMap.projectiveTrace_comp_comm]
    change LinearMap.projectiveTrace R S.X₃ (s.s ≫ S.g ≫ φ.τ₃).hom = _
    rw [s.s_g_assoc]
  rw [hleft, hright]

/-- The projective trace is additive in every short exact sequence of finite
projective modules. No splitting is an input to this theorem. -/
theorem projectiveTrace_eq_add_of_shortExact (hS : S.ShortExact) (φ : S ⟶ S) :
    LinearMap.projectiveTrace R S.X₂ φ.τ₂.hom =
      LinearMap.projectiveTrace R S.X₁ φ.τ₁.hom +
        LinearMap.projectiveTrace R S.X₃ φ.τ₃.hom :=
  projectiveTrace_eq_add_of_splitting hS.splittingOfProjective φ

end EtaleCohomology
