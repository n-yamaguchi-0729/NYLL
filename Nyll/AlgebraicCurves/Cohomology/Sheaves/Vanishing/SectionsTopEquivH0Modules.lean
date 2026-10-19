/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_sections_top_equiv_H0_ofModules.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.OModulePresheafOfModules
import Nyll.AlgebraicCurves.Cohomology.Sheaves.Complexes.DZeroModulesEqZeroIffUnique

/-!
# OModule Presheaf nonempty sections top equiv H0 of Modules
-/

section ProofImplementation


namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.GlobalSectionsH0

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace AC3Aux

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (M :
  V.Modules)
  (K : V.OrderedAffineCover)

/-- The module presheaf of sections of the given sheaf of modules. -/
abbrev F : OModulePresheaf π := OModulePresheaf.ofModules π M

theorem res_mem_H0 (x : (F π M).obj ⊤) : (fun s : K.Idx 0 => (F π M).res (le_top : K.inter s ≤ ⊤)
  x) ∈ (F π M).H0 K := by
  rw [LinearMap.mem_ker]
  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul,
    OModulePresheaf.res_res]
  exact add_neg_cancel _

/-- The linear map sending a global section to its Čech zero-cocycle. -/
def toH0 : (F π M).obj ⊤ →ₗ[R] (F π M).H0 K :=
  LinearMap.codRestrict ((F π M).H0 K) (LinearMap.pi fun s : K.Idx 0 => (F π M).res (le_top :
    K.inter s ≤ ⊤))
    (res_mem_H0 π M K)

theorem toH0_apply (x : (F π M).obj ⊤) (s : K.Idx 0) : (toH0 π M K x : (F π M).cochain K 0) s = (F
  π M).res le_top x := rfl

theorem toH0_injective : Function.Injective (toH0 π M K) := by
  intro x y hxy
  obtain ⟨z, _, huniq⟩ :=
    (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K
      ((toH0 π M K x : (F π M).H0 K) : (F π M).cochain K 0)).mp
      (LinearMap.mem_ker.mp (toH0 π M K x).2)
  have hx : x = z := huniq x (fun _ => rfl)
  have hy : y = z := huniq y (fun s =>
    congrArg (fun c : (F π M).H0 K => (c : (F π M).cochain K 0) s) hxy)
  exact hx.trans hy.symm

theorem toH0_surjective : Function.Surjective (toH0 π M K) := by
  intro c
  obtain ⟨x, hx, _⟩ :=
    (OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique π M K
      (c : (F π M).cochain K 0)).mp (LinearMap.mem_ker.mp c.2)
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact funext fun s => (hx s).symm

end AC3Aux

end

open AC3Aux in
theorem _root_.AlgebraicGeometry.OModulePresheaf.nonempty_sections_top_equiv_H0_ofModules
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    (M : V.Modules) (K : V.OrderedAffineCover) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom π M ⊤
    Nonempty (Γ(M, ⊤) ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K) := by
  exact ⟨LinearEquiv.ofBijective (toH0 π M K) ⟨toH0_injective π M K, toH0_surjective π M K⟩⟩
end AlgebraicCurves.Cohomology.Sheaves.Proofs.GlobalSectionsH0
end ProofImplementation
