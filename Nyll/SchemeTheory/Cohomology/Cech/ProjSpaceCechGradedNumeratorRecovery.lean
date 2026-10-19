/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModuleHEquivPi
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModulePresentationFiniteH
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModulePresentationKerIsFG
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedPresentationShift
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedGlobalSections
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedNumeratorLifting
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistFiniteCohomology
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Recovery of sufficiently positive homogeneous degree pieces

A free polynomial numerator vanishing on a coordinate chart is zero,
because multiplication by a coordinate monomial is injective. For a
finite graded presentation, a numerator with zero global section lifts
to a global section of the actual presentation kernel. In sufficiently
large degree that kernel section itself has a homogeneous numerator.
Injectivity in the free source then shows that the original numerator
was zero.

Together with numerator lifting, this proves that the canonical
augmentation is bijective in every sufficiently large degree. The
comparison uses its actual fraction evaluations throughout; the
identification is not an input or a chosen abstract module isomorphism.
-/

noncomputable section

namespace ProjSpaceCech.GradedModule

universe u

open AlgebraicCurves.Cohomology.Cech.Proofs
open ProjSpaceCech_GradedModule_nonempty_HEquiv_pi.ProjSpaceCech.GradedModule
open ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses.ProjSpaceCech.GradedModule
open ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Coordinate localization does not kill any homogeneous polynomial
numerator, in any twist. -/
theorem augmentation_FD_injective (e : ℤ) :
    Function.Injective (augmentation (FD R n e)) := by
  intro x y hxy
  let I : Finset (Fin (n + 1)) := Idx.img n (vtx (0 : Fin (n + 1)))
  have hchart : zeroSectionMap (FD R n e) I x = zeroSectionMap (FD R n e) I y :=
    congrFun (congrArg Subtype.val hxy) (vtx (0 : Fin (n + 1)))
  obtain ⟨c, _hc, hnum⟩ := (sec_mk_eq (FD R n e) I).mp hchart
  apply Subtype.ext
  exact free_monMul_injective (R := R) (n := n) (c + 0) hnum

/-- Componentwise injectivity of numerator evaluation gives injectivity
for a finite product of graded modules. -/
theorem augmentation_pi_injective {ι : Type} [Fintype ι]
    (D : ι → GradedModule R n) (hD : ∀ k : ι, Function.Injective (augmentation (D k))) :
    Function.Injective (augmentation (pi D)) := by
  intro x y hxy
  apply Subtype.ext
  funext k
  let xk : (D k).grade 0 := ⟨x.val k, x.property k (Set.mem_univ k)⟩
  let yk : (D k).grade 0 := ⟨y.val k, y.property k (Set.mem_univ k)⟩
  have hcomponent : augmentation (D k) xk = augmentation (D k) yk := by
    apply Subtype.ext
    funext s
    exact congrArg (secPiProj D (Idx.img n s) k)
      (congrFun (congrArg Subtype.val hxy) s)
  exact congrArg Subtype.val (hD k hcomponent)

private theorem lift_kernel_H0 {D : GradedModule R n} (σ : Presentation D)
    (z : H σ.F 0) (hz : Hom.HMap σ.hom 0 z = 0) :
    ∃ w : H σ.ker 0, Hom.HMap σ.kerIncl 0 w = z := by
  have hzcochain : Hom.cochainMap σ.hom 0 z.val = 0 := congrArg Subtype.val hz
  have hmem : z.val ∈ LinearMap.range (Hom.cochainMap σ.kerIncl 0) :=
    (altC_exact σ 0).le (LinearMap.mem_ker.mpr hzcochain)
  obtain ⟨a, ha⟩ := hmem
  have hcycle : d σ.ker 0 a = 0 := by
    apply iotaC_injective σ 1
    calc
      Hom.cochainMap σ.kerIncl 1 (d σ.ker 0 a) =
          d σ.F 0 (Hom.cochainMap σ.kerIncl 0 a) :=
        (LinearMap.congr_fun (Hom.cochainMap_comm σ.kerIncl 0) a).symm
      _ = d σ.F 0 z.val := congrArg (d σ.F 0) ha
      _ = 0 := LinearMap.mem_ker.mp z.property
      _ = Hom.cochainMap σ.kerIncl 1 0 := (map_zero (Hom.cochainMap σ.kerIncl 1)).symm
  exact ⟨⟨a, LinearMap.mem_ker.mpr hcycle⟩, Subtype.ext ha⟩

private theorem augmentation_injective_of_kernel_surjective
    {D : GradedModule R n} (σ : Presentation D)
    (hfree : Function.Injective (augmentation σ.F))
    (hkernel : Function.Surjective (augmentation σ.ker)) :
    Function.Injective (augmentation D) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff (LinearMap.ker (augmentation D))).mpr
  intro m hm
  obtain ⟨p, hp, hpm⟩ := σ.surj 0 m.val m.property
  let numerator : σ.F.grade 0 := ⟨p, hp⟩
  have hmap : σ.hom.gradeMap 0 numerator = m := Subtype.ext hpm
  have hzero : Hom.HMap σ.hom 0 (augmentation σ.F numerator) = 0 :=
    (augmentation_naturality σ.hom numerator).trans
      ((congrArg (augmentation D) hmap).trans (LinearMap.mem_ker.mp hm))
  obtain ⟨w, hw⟩ := lift_kernel_H0 σ (augmentation σ.F numerator) hzero
  obtain ⟨q, hq⟩ := hkernel w
  have hsection : augmentation σ.F (σ.kerIncl.gradeMap 0 q) =
      augmentation σ.F numerator :=
    (augmentation_naturality σ.kerIncl q).symm.trans
      ((congrArg (Hom.HMap σ.kerIncl 0) hq).trans hw)
  have hnumerator : σ.kerIncl.gradeMap 0 q = numerator := hfree hsection
  have hnum : q.val = p := congrArg Subtype.val hnumerator
  have hpK : p ∈ σ.K := hnum ▸ q.property.2
  apply Subtype.ext
  exact hpm.symm.trans (LinearMap.mem_ker.mp hpK)

/-- The canonical degree-piece map to global Čech sections is bijective
in all sufficiently large twists of a finitely generated graded module. -/
theorem exists_twist_bound_bijective_augmentation [IsNoetherianRing R]
    (D : GradedModule R n) (hD : IsFG D) :
    ∃ b : ℤ, ∀ e : ℤ, b ≤ e → Function.Bijective (augmentation (D.shift e)) := by
  obtain ⟨σ⟩ := hD
  obtain ⟨bD, hDsurj⟩ := exists_twist_bound_surjective_augmentation D ⟨σ⟩
  obtain ⟨bK, hKsurj⟩ := exists_twist_bound_surjective_augmentation σ.ker
    (Presentation.ker_isFG σ)
  refine ⟨max bD bK, ?_⟩
  intro e he
  refine ⟨?_, hDsurj e ((le_max_left bD bK).trans he)⟩
  apply augmentation_injective_of_kernel_surjective (σ.shift e)
  · apply augmentation_pi_injective
    intro k
    exact augmentation_FD_injective (e + σ.d₀ k)
  · rw [Presentation.shift_ker]
    exact hKsurj e ((le_max_right bD bK).trans he)

end ProjSpaceCech.GradedModule
