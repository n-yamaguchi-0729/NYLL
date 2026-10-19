/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedGlobalSections
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Nyll.SchemeTheory.RingTheory.AdicCompletion.ModuleSystemHom
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The actual limit of an adic system of graded modules

Compatible sequences carry the original grading and coordinate operators
component by component. Each homogeneous component is explicitly identified
with the compatible-sequence module of the corresponding homogeneous pieces.
For an adic system of finite pieces over a complete Noetherian ring, this
computes the finiteness and every actual reduction of the constructed limit.

The transition kernels and annihilation hypotheses concern the supplied
finite stages. No effective graded module, finite presentation of the limit,
or quotient comparison is supplied as an input.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

variable {R : Type u} [CommRing R] {dim : ℕ}
  (D : ℕ → GradedModule R dim) (t : ∀ k : ℕ, Hom (D (k + 1)) (D k))

/-- Homogeneous compatible sequences in the original carrier modules. -/
def adicGrade (d : ℤ) :
    Submodule R (AdicModuleSystem.sections (fun k => (D k).M)
      (fun k => (t k).toLinearMap)) where
  carrier := {x | ∀ k : ℕ, x.val k ∈ (D k).grade d}
  zero_mem' := fun k => Submodule.zero_mem ((D k).grade d)
  add_mem' := by
    intro x y hx hy k
    exact Submodule.add_mem _ (hx k) (hy k)
  smul_mem' := by
    intro r x hx k
    exact Submodule.smul_mem _ r (hx k)

/-- Each coordinate acts on compatible sequences by its given stage operators. -/
def adicXMul (j : Fin (dim + 1)) :
    AdicModuleSystem.sections (fun k => (D k).M) (fun k => (t k).toLinearMap) →ₗ[R]
      AdicModuleSystem.sections (fun k => (D k).M) (fun k => (t k).toLinearMap) :=
  AdicModuleSystem.sectionsMap (fun k => (D k).M) (fun k => (t k).toLinearMap)
    (fun k => (D k).M) (fun k => (t k).toLinearMap)
    ⟨fun k => (D k).xMul j, fun k x => LinearMap.congr_fun ((t k).xMul_comm j) x⟩

/-- The constructed coordinate action retains every stage value. -/
theorem adicXMul_apply (j : Fin (dim + 1))
    (x : AdicModuleSystem.sections (fun k => (D k).M) (fun k => (t k).toLinearMap))
    (k : ℕ) : (adicXMul D t j x).val k = (D k).xMul j (x.val k) := rfl

/-- The graded module of actual compatible sequences of the supplied system. -/
def adicLimit : GradedModule R dim where
  M := AdicModuleSystem.sections (fun k => (D k).M) (fun k => (t k).toLinearMap)
  grade := adicGrade D t
  xMul := adicXMul D t
  xMul_mem_grade j d x hx k := (D k).xMul_mem_grade j d (x.val k) (hx k)
  xMul_comm i j := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    exact LinearMap.congr_fun ((D k).xMul_comm i j) (x.val k)

/-- Projection of the actual graded limit to an original finite stage. -/
def adicEval (k : ℕ) : Hom (adicLimit D t) (D k) where
  toLinearMap := AdicModuleSystem.eval (fun k => (D k).M)
    (fun k => (t k).toLinearMap) k
  mem_grade _ _ hx := hx k
  xMul_comm j := by
    apply LinearMap.ext
    intro x
    exact adicXMul_apply D t j x k

/-- The degree of a compatible sequence is equivalent to a sequence of degree pieces. -/
def adicGradeEquiv (d : ℤ) :
    (adicLimit D t).grade d ≃ₗ[R]
      AdicModuleSystem.sections (fun k => (D k).grade d) (fun k => (t k).gradeMap d) where
  toFun x := ⟨fun k => ⟨x.val.val k, x.property k⟩, fun k =>
    Subtype.ext (x.val.property k)⟩
  invFun y := ⟨⟨fun k => (y.val k).val, fun k =>
    congrArg Subtype.val (y.property k)⟩, fun k => (y.val k).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rfl
  right_inv y := by
    apply Subtype.ext
    funext k
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    funext k
    apply Subtype.ext
    rfl
  map_smul' r x := by
    apply Subtype.ext
    funext k
    apply Subtype.ext
    rfl

/-- The component comparison preserves the original evaluation maps. -/
theorem adicGradeEquiv_eval (d : ℤ) (k : ℕ) (x : (adicLimit D t).grade d) :
    AdicModuleSystem.eval (fun k => (D k).grade d) (fun k => (t k).gradeMap d) k
      (adicGradeEquiv D t d x) = (adicEval D t k).gradeMap d x := rfl

section Adic

variable (I : Ideal R) [IsAdicComplete I R]
  [∀ (k : ℕ) (d : ℤ), Module.Finite R ((D k).grade d)]
  (ht : ∀ (d : ℤ) (k : ℕ), Function.Surjective ((t k).gradeMap d))
  (hker : ∀ (d : ℤ) (k : ℕ), ((t k).gradeMap d).ker =
    I ^ (k + 1) • (⊤ : Submodule R ((D (k + 1)).grade d)))
  (hpow : ∀ (d : ℤ) (k : ℕ),
    I ^ (k + 1) • (⊤ : Submodule R ((D k).grade d)) = ⊥)

include ht hker in
/-- Every prescribed homogeneous element at any stage has an actual homogeneous lift. -/
theorem adicEval_gradeMap_surjective (d : ℤ) (k : ℕ) :
    Function.Surjective ((adicEval D t k).gradeMap d) := by
  intro x
  obtain ⟨y, hy⟩ := AdicModuleSystem.eval_surjective
    (fun k => (D k).grade d) (fun k => (t k).gradeMap d) I (ht d) (hker d) k x
  refine ⟨(adicGradeEquiv D t d).symm y, ?_⟩
  rw [← adicGradeEquiv_eval, LinearEquiv.apply_symm_apply, hy]

include ht hker hpow in
/-- Every degree of the constructed limit is finite over the coefficient ring. -/
theorem adicLimit_finite_grade [IsNoetherianRing R] (d : ℤ) :
    Module.Finite R ((adicLimit D t).grade d) := by
  have : Module.Finite R
      (AdicModuleSystem.sections (fun k => (D k).grade d) (fun k => (t k).gradeMap d)) :=
    AdicModuleSystem.finite (fun k => (D k).grade d) (fun k => (t k).gradeMap d)
      I (ht d) (hker d) (hpow d)
  exact Module.Finite.of_surjective (adicGradeEquiv D t d).symm.toLinearMap
    (adicGradeEquiv D t d).symm.surjective

include ht hker hpow in
/-- The kernel of the original homogeneous projection is the computed ideal power. -/
theorem ker_adicEval_gradeMap [IsNoetherianRing R] (d : ℤ) (k : ℕ) :
    ((adicEval D t k).gradeMap d).ker =
      I ^ (k + 1) • (⊤ : Submodule R ((adicLimit D t).grade d)) := by
  apply le_antisymm
  · intro x hx
    have he : adicGradeEquiv D t d x ∈
        (AdicModuleSystem.eval (fun k => (D k).grade d)
          (fun k => (t k).gradeMap d) k).ker := by
      apply LinearMap.mem_ker.mpr
      rw [adicGradeEquiv_eval]
      exact LinearMap.mem_ker.mp hx
    rw [AdicModuleSystem.ker_eval (fun k => (D k).grade d)
      (fun k => (t k).gradeMap d) I (ht d) (hker d) (hpow d) k] at he
    have hmem := Submodule.smul_top_le_comap_smul_top (I ^ (k + 1))
      (adicGradeEquiv D t d).symm.toLinearMap he
    change (adicGradeEquiv D t d).symm (adicGradeEquiv D t d x) ∈
      I ^ (k + 1) • (⊤ : Submodule R ((adicLimit D t).grade d)) at hmem
    rw [LinearEquiv.symm_apply_apply] at hmem
    exact hmem
  · intro x hx
    have hmem := Submodule.smul_top_le_comap_smul_top (I ^ (k + 1))
      ((adicEval D t k).gradeMap d) hx
    rw [hpow d k] at hmem
    exact LinearMap.mem_ker.mpr hmem

/-- Reduction of each constructed degree recovers the supplied stage through evaluation. -/
def adicGradeQuotientEquiv [IsNoetherianRing R] (d : ℤ) (k : ℕ) :
    ((adicLimit D t).grade d ⧸
      (I ^ (k + 1) • (⊤ : Submodule R ((adicLimit D t).grade d)))) ≃ₗ[R] (D k).grade d :=
  (Submodule.quotEquivOfEq _ _ (ker_adicEval_gradeMap D t I ht hker hpow d k).symm).trans
    (((adicEval D t k).gradeMap d).quotKerEquivOfSurjective
      (adicEval_gradeMap_surjective D t I ht hker d k))

/-- The quotient comparison is induced by the literal projection of compatible sequences. -/
theorem adicGradeQuotientEquiv_mk [IsNoetherianRing R]
    (d : ℤ) (k : ℕ) (x : (adicLimit D t).grade d) :
    adicGradeQuotientEquiv D t I ht hker hpow d k (Submodule.Quotient.mk x) =
      (adicEval D t k).gradeMap d x :=
  ((adicEval D t k).gradeMap d).quotKerEquivOfSurjective_apply_mk
    (adicEval_gradeMap_surjective D t I ht hker d k) x

end Adic

end ProjSpaceCech.GradedModule
