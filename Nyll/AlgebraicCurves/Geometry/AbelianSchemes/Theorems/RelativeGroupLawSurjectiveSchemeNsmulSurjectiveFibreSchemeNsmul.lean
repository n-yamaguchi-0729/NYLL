/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Data.Set.Operations
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Fibre
public import Nyll.SchemeTheory.Fibers.SchemeFibreEndo
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.RelativeGroupLawFibreSchemeNsmulEqSchemeFibreEndo

public import Nyll.AbelianVarieties.Basic

/-!
# Relative Group Law surjective scheme Nsmul of forall surjective fibre scheme Nsmul
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs
namespace RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian


theorem FibSurj.surjective_of_forall_surjective_schemeFibreEndo'
    {S X : Scheme.{u}} (f : X ⟶ S) (h : X ⟶ X) (hh : h ≫ f = f)
    (hfib : ∀ s : S, Surjective (schemeFibreEndo f h hh s)) :
    Surjective h := by
  rw [surjective_iff]
  intro x
  obtain ⟨x', hx'⟩ : x ∈ Set.range (f.fiberι (f.base x)) := by
    rw [Scheme.Hom.range_fiberι]
    exact rfl
  obtain ⟨y', hy'⟩ := (hfib (f.base x)).1 x'
  refine ⟨(pullback.fst f (S.fromSpecResidueField (f.base x))).base y', ?_⟩
  have key : (schemeFibreEndo f h hh (f.base x) ≫ pullback.fst f (S.fromSpecResidueField (f.base
    x))) y' =
      (pullback.fst f (S.fromSpecResidueField (f.base x)) ≫ h) y' := by
    rw [schemeFibreEndo_fst]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy'] at key
  rw [← key]
  exact hx'

end RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul
end AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open _root_.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.Proofs in
open RelativeGroupLaw_surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian in
theorem surjective_schemeNsmul_of_forall_surjective_fibre_schemeNsmul
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ)
    (hfib : ∀ s : (Spec (CommRingCat.of R) : Scheme.{u}), Surjective ((G.fibre s).schemeNsmul n)) :
    Surjective (G.schemeNsmul n) := by
  apply FibSurj.surjective_of_forall_surjective_schemeFibreEndo' f (G.schemeNsmul n)
    (G.schemeNsmul_over n)
  intro s
  rw [← GoodReductionJacobian.RelativeGroupLaw.fibre_schemeNsmul_eq_schemeFibreEndo]
  exact hfib s
end GoodReductionJacobian.RelativeGroupLaw
end ProofImplementation

attribute [-simp] AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst
