/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedGlobalSections
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedFreeHom
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedAdicSystem
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedNumeratorLifting
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModules
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Finite homogeneous generators of an actual adic limit

Lift the actual generator images of a presentation at stage zero to
homogeneous compatible sequences. The commuting coordinate operators define
a genuine graded homomorphism on these lifted elements. Its reduction is
the original stage-zero presentation, with the same polynomial coefficients.

Degreewise Nakayama propagates this surjectivity to all finite stages.
Completeness of the finite free homogeneous source then gives surjectivity
onto each homogeneous degree of the actual limit. This constructs a finite
presentation of the limit from the stage-zero presentation; finite generation
of the limit and a lifted presentation are not hypotheses.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

variable {R : Type u} [CommRing R] {dim : ℕ}
  (D : ℕ → GradedModule R dim) (t : ∀ k : ℕ, Hom (D (k + 1)) (D k))
  (I : Ideal R) [IsAdicComplete I R]
  [∀ (k : ℕ) (d : ℤ), Module.Finite R ((D k).grade d)]
  (ht : ∀ (d : ℤ) (k : ℕ), Function.Surjective ((t k).gradeMap d))
  (hker : ∀ (d : ℤ) (k : ℕ), ((t k).gradeMap d).ker =
    I ^ (k + 1) • (⊤ : Submodule R ((D (k + 1)).grade d)))

private def presentationGenerator (σ : Presentation (D 0)) (j : σ.J) :
    (D 0).grade (-σ.d₀ j) := by
  classical
  have h1 : (1 : MvPolynomial (Fin (dim + 1)) R) ∈
      (FD R dim (σ.d₀ j)).grade (-σ.d₀ j) := by
    change (1 : MvPolynomial (Fin (dim + 1)) R) ∈ freeGrade R dim (-σ.d₀ j + σ.d₀ j)
    rw [neg_add_cancel, freeGrade_of_nonneg R dim (le_refl (0 : ℤ))]
    exact MvPolynomial.isHomogeneous_one (Fin (dim + 1)) R
  refine ⟨σ.hom.toLinearMap (Pi.single j (1 : MvPolynomial (Fin (dim + 1)) R)), ?_⟩
  exact σ.hom.mem_grade (-σ.d₀ j) _
    ((freeSummandInclusion (R := R) (n := dim) σ.d₀ j).mem_grade
      (-σ.d₀ j) (1 : MvPolynomial (Fin (dim + 1)) R) h1)

private def adicGenerator (σ : Presentation (D 0)) (j : σ.J) :
    (adicLimit D t).grade (-σ.d₀ j) :=
  (adicEval_gradeMap_surjective D t I ht hker (-σ.d₀ j) 0
    (presentationGenerator D σ j)).choose

private theorem adicGenerator_eval (σ : Presentation (D 0)) (j : σ.J) :
    (adicEval D t 0).toLinearMap (adicGenerator D t I ht hker σ j).val =
      (presentationGenerator D σ j).val :=
  congrArg Subtype.val
    (adicEval_gradeMap_surjective D t I ht hker (-σ.d₀ j) 0
      (presentationGenerator D σ j)).choose_spec

/-- The graded homomorphism defined by actual homogeneous lifts of the first-stage generators. -/
def adicPresentationHom (σ : Presentation (D 0)) : Hom σ.F (adicLimit D t) :=
  fromHomogeneousFamily σ.d₀ (adicLimit D t)
    (fun j => (adicGenerator D t I ht hker σ j).val)
    (fun j => (adicGenerator D t I ht hker σ j).property)

/-- The lifted generator map reduces to the original presentation with its original coefficients. -/
theorem adicPresentationHom_eval_zero (σ : Presentation (D 0)) (p : σ.F.M) :
    (adicEval D t 0).toLinearMap ((adicPresentationHom D t I ht hker σ).toLinearMap p) =
      σ.hom.toLinearMap p := by
  classical
  change (adicEval D t 0).toLinearMap
    ((fromHomogeneousFamily σ.d₀ (adicLimit D t)
      (fun j => (adicGenerator D t I ht hker σ j).val)
      (fun j => (adicGenerator D t I ht hker σ j).property)).toLinearMap p) = _
  rw [fromHomogeneousFamily_apply, map_sum, Hom.fromFamily_apply σ.d₀ σ.hom p]
  apply Finset.sum_congr rfl
  intro j _
  change (adicEval D t 0).toLinearMap
      (freeLinear (adicLimit D t) (adicGenerator D t I ht hker σ j).val (p j)) =
    freeLinear (D 0) (presentationGenerator D σ j).val (p j)
  exact (LinearMap.congr_fun
    ((adicEval D t 0).map_freeLinear (adicGenerator D t I ht hker σ j).val) (p j)).trans
      (congrArg (fun v => freeLinear (D 0) v (p j))
        (adicGenerator_eval D t I ht hker σ j))

variable [IsNoetherianRing R]
  (hpow : ∀ (d : ℤ) (k : ℕ),
    I ^ (k + 1) • (⊤ : Submodule R ((D k).grade d)) = ⊥)

include hpow in
/-- The actual lifted finite family generates every homogeneous degree of the limit. -/
theorem adicPresentationHom_gradeMap_surjective (σ : Presentation (D 0)) (d : ℤ) :
    Function.Surjective ((adicPresentationHom D t I ht hker σ).gradeMap d) := by
  let self : Presentation σ.F :=
    { J := σ.J
      d₀ := σ.d₀
      hom :=
        { toLinearMap := LinearMap.id
          mem_grade := fun _ _ h => h
          xMul_comm := fun _ => rfl }
      surj := fun _ m hm => ⟨m, hm, rfl⟩ }
  have : Module.Finite R (σ.F.grade d) := finite_grade σ.F ⟨self⟩ d
  have : IsAdicComplete I (σ.F.grade d) := IsAdicComplete.of_module_finite I (σ.F.grade d)
  let e := adicGradeEquiv D t d
  let F : σ.F.grade d →ₗ[R]
      AdicModuleSystem.sections (fun k => (D k).grade d) (fun k => (t k).gradeMap d) :=
    e.toLinearMap.comp ((adicPresentationHom D t I ht hker σ).gradeMap d)
  have hF0 : Function.Surjective
      ((AdicModuleSystem.eval (fun k => (D k).grade d)
        (fun k => (t k).gradeMap d) 0).comp F) := by
    intro x
    obtain ⟨p, hp, hpx⟩ := σ.surj d x.val x.property
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    change (adicEval D t 0).toLinearMap
      ((adicPresentationHom D t I ht hker σ).toLinearMap p) = x.val
    rw [adicPresentationHom_eval_zero, hpx]
  have hFn := AdicModuleSystem.surjective_components_of_surjective_zero
    (fun k => (D k).grade d) (fun k => (t k).gradeMap d) I (hker d) F hF0
  have hF := AdicModuleSystem.surjective_of_surjective_components
    (fun k => (D k).grade d) (fun k => (t k).gradeMap d) I (hker d) (hpow d) F hFn
  intro x
  obtain ⟨p, hp⟩ := hF (e x)
  exact ⟨p, e.injective hp⟩

/-- A finite presentation of the actual adic limit, constructed from
the first-stage presentation. -/
def adicPresentation (σ : Presentation (D 0)) : Presentation (adicLimit D t) where
  J := σ.J
  d₀ := σ.d₀
  hom := adicPresentationHom D t I ht hker σ
  surj d m hm := by
    obtain ⟨p, hp⟩ := adicPresentationHom_gradeMap_surjective D t I ht hker hpow σ d ⟨m, hm⟩
    exact ⟨p.val, p.property, congrArg Subtype.val hp⟩

end ProjSpaceCech.GradedModule
