/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule

/-!
# Shifting a fixed finite graded presentation

Shifting a graded module shifts the degrees of the generators in one
fixed presentation. The underlying linear map is unchanged, and the
kernel of the shifted presentation is the shift of the original kernel.
These concrete comparisons make it possible to choose a twist bound
uniformly while descending through a finite graded resolution.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

variable {R : Type u} [CommRing R] {n : ℕ} {D : GradedModule R n}

/-- Shift a fixed finite presentation by adding the twist to the degree
of every free generator. The underlying linear map is retained. -/
def Presentation.shift (σ : Presentation D) (e : ℤ) : Presentation (D.shift e) where
  J := σ.J
  fJ := σ.fJ
  d₀ k := e + σ.d₀ k
  hom := {
    toLinearMap := σ.hom.toLinearMap
    mem_grade := by
      intro a m hm
      change σ.hom.toLinearMap m ∈ D.grade (a + e)
      apply σ.hom.mem_grade (a + e) m
      change m ∈ Submodule.pi Set.univ
        (fun k => freeGrade R n ((a + e) + σ.d₀ k))
      change m ∈ Submodule.pi Set.univ
        (fun k => freeGrade R n (a + (e + σ.d₀ k))) at hm
      simpa only [add_assoc] using hm
    xMul_comm := σ.hom.xMul_comm
  }
  surj := by
    intro a m hm
    obtain ⟨m', hm', hmap⟩ := σ.surj (a + e) m hm
    refine ⟨m', ?_, hmap⟩
    change m' ∈ Submodule.pi Set.univ
      (fun k => freeGrade R n (a + (e + σ.d₀ k)))
    change m' ∈ Submodule.pi Set.univ
      (fun k => freeGrade R n ((a + e) + σ.d₀ k)) at hm'
    simpa only [add_assoc] using hm'

theorem Presentation.shift_toLinearMap (σ : Presentation D) (e : ℤ) :
    (σ.shift e).hom.toLinearMap = σ.hom.toLinearMap := rfl

/-- The grades of the newly constructed free source are precisely the
shifted grades of the original free source. -/
theorem Presentation.shift_F_grade (σ : Presentation D) (e a : ℤ) :
    (σ.shift e).F.grade a = σ.F.grade (a + e) := by
  change Submodule.pi Set.univ (fun k => freeGrade R n (a + (e + σ.d₀ k))) =
    Submodule.pi Set.univ (fun k => freeGrade R n ((a + e) + σ.d₀ k))
  simp only [add_assoc]

/-- Shifting the fixed presentation commutes with forming its actual
graded kernel. Only the grading changes. -/
theorem Presentation.shift_ker (σ : Presentation D) (e : ℤ) :
    (σ.shift e).ker = σ.ker.shift e := by
  unfold Presentation.ker GradedModule.sub GradedModule.shift
  congr 1
  funext a
  exact congrArg (fun U : Submodule R σ.F.M => U ⊓ σ.K)
    (Presentation.shift_F_grade σ e a)

end ProjSpaceCech.GradedModule
