/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafDEqDDMemPow
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesImageAffineCoefficients
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesImageModule
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorModule
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorRestrictions
import Nyll.SchemeTheory.Modules.Functoriality.PullbackSections
import Nyll.SchemeTheory.Modules.Functoriality.PullbackSectionRestriction
import Nyll.SchemeTheory.Modules.Tensor.PullbackTensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Native Rees tensor sections on the original affine intersections

The actual Rees image comparison and the actual affine pullback tensor
comparison identify the original polynomial tensors with sections of
the constructed Rees coefficient sheaf. The formula retains the native
image inclusion and the original pullback unit.

Every face restriction commutes with this additive equivalence. The
two presheaves keep their original base rings; their section groups are
compared without replacing either scalar action.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry Scheme.Modules Scheme.Modules.ReesTensor

variable {A : Type u} [CommRing A] (I : Ideal A)
  {P : Scheme.{u}} (q : P ⟶ Spec (.of A)) [IsSeparated q]
  (K : P.OrderedAffineCover) (M : P.Modules) [M.IsQuasicoherent]

/-- The original Rees tensors on an affine intersection identify
with the actual coefficient sheaf's sections on its original pullback. -/
def imageTensorAffineSectionsEquiv {i : ℕ} (s : K.Idx i) :
    (reesTensorPresheaf q I M).obj (K.inter s) ≃+
      (toOModulePresheaf (π' I q) (imageTensorModule I q M)).obj
        ((K' I q K).inter (indexEquiv I q K s)) := by
  let U := K.inter s
  let W := (K' I q K).inter (indexEquiv I q K s)
  have hU : IsAffineOpen U := haff q K s
  have hW : IsAffineOpen W := by
    change IsAffineOpen ((K' I q K).inter (indexEquiv I q K s))
    rw [K'_inter]
    exact hU.preimage (fst' I q)
  have : (imageModule I q).IsQuasicoherent := imageModule_isQuasicoherent I q
  let eR : ↥(reesAlgebra (sectionsIdeal q I U)) ≃ₗ[Γ(P, U)]
      imageAffineModuleOverOriginal I q K s := (imageAffineReesEquiv I q K s).symm
  let e₁ := TensorProduct.congr eR (LinearEquiv.refl Γ(P, U) Γ(M, U))
  let e₂ := affinePullbackTensorSectionsEquiv (fst' I q) U W (e'_s I q K s)
    (imageModule I q) M hU hW
  exact (e₁.trans e₂).toAddEquiv

/-- A pure tensor becomes the actual tensor section of its native
Rees image preimage and the original restricted pullback unit. -/
theorem imageTensorAffineSectionsEquiv_tmul {i : ℕ} (s : K.Idx i)
    (p : ↥(reesAlgebra (sectionsIdeal q I (K.inter s)))) (x : Γ(M, K.inter s)) :
    imageTensorAffineSectionsEquiv I q K M s (p ⊗ₜ[Γ(P, K.inter s)] x) =
      tensorSections
        (show Γ(imageModule I q, (K' I q K).inter (indexEquiv I q K s)) from
          (imageAffineReesEquiv I q K s).symm p)
        ((pullbackUnitSections (fst' I q) (K.inter s)
          ((K' I q K).inter (indexEquiv I q K s)) (e'_s I q K s)).app M x) := by
  let U := K.inter s
  let W := (K' I q K).inter (indexEquiv I q K s)
  have hU : IsAffineOpen U := haff q K s
  have hW : IsAffineOpen W := by
    change IsAffineOpen ((K' I q K).inter (indexEquiv I q K s))
    rw [K'_inter]
    exact hU.preimage (fst' I q)
  have : (imageModule I q).IsQuasicoherent := imageModule_isQuasicoherent I q
  let eR : ↥(reesAlgebra (sectionsIdeal q I U)) ≃ₗ[Γ(P, U)]
      imageAffineModuleOverOriginal I q K s := (imageAffineReesEquiv I q K s).symm
  let e₂ := affinePullbackTensorSectionsEquiv (fst' I q) U W (e'_s I q K s)
    (imageModule I q) M hU hW
  have h₁ := congrArg e₂
    (TensorProduct.congr_tmul eR (LinearEquiv.refl Γ(P, U) Γ(M, U)) p x)
  have h₂ := affinePullbackTensorSectionsEquiv_tmul (fst' I q) U W (e'_s I q K s)
    (imageModule I q) M hU hW (eR p) x
  exact h₁.trans h₂

private theorem imageAffineReesEquiv_symm_face {i : ℕ} (s : K.Idx (i + 1))
    (j : Fin (i + 2))
    (p : ↥(reesAlgebra (sectionsIdeal q I (K.inter (K.face s j))))) :
    (imageModule I q).presheaf.map (homOfLE (K'_inter_le_inter_face I q K s j)).op
        ((imageAffineReesEquiv I q K (K.face s j)).symm p) =
      (imageAffineReesEquiv I q K s).symm
        (reesRestriction q I (K.inter_le_inter_face s j) p) := by
  apply (imageAffineReesEquiv I q K s).injective
  apply Subtype.ext
  have h := imageAffineReesEquiv_face I q K s j
    ((imageAffineReesEquiv I q K (K.face s j)).symm p)
  have h₁ := congrArg
    (fun z : ↥(reesAlgebra (sectionsIdeal q I (K.inter (K.face s j)))) =>
      Polynomial.map (P.presheaf.map (homOfLE (K.inter_le_inter_face s j)).op).hom z.val)
    ((imageAffineReesEquiv I q K (K.face s j)).apply_symm_apply p)
  have h₂ := congrArg Subtype.val
    ((imageAffineReesEquiv I q K s).apply_symm_apply
      (reesRestriction q I (K.inter_le_inter_face s j) p))
  exact h.trans (h₁.trans h₂.symm)

/-- The original polynomial and module face restrictions correspond to
the actual restriction of the native Rees coefficient sheaf. -/
theorem imageTensorAffineSectionsEquiv_face {i : ℕ} (s : K.Idx (i + 1))
    (j : Fin (i + 2))
    (z : (reesTensorPresheaf q I M).obj (K.inter (K.face s j))) :
    imageTensorAffineSectionsEquiv I q K M s
        ((reesTensorPresheaf q I M).res (K.inter_le_inter_face s j) z) =
      (toOModulePresheaf (π' I q) (imageTensorModule I q M)).res
        (K'_inter_le_inter_face I q K s j)
        (imageTensorAffineSectionsEquiv I q K M (K.face s j) z) := by
  let U := K.inter (K.face s j)
  let V := K.inter s
  let W := (K' I q K).inter (indexEquiv I q K (K.face s j))
  let W' := (K' I q K).inter (indexEquiv I q K s)
  let iU : V ⟶ U := homOfLE (K.inter_le_inter_face s j)
  let iW : W' ⟶ W := homOfLE (K'_inter_le_inter_face I q K s j)
  let N : (P' I q).Modules := (pullback (fst' I q)).obj M
  induction z using TensorProduct.inductionOn with
  | tmul p x =>
      let a : Γ(imageModule I q, W) :=
        (imageAffineReesEquiv I q K (K.face s j)).symm p
      let b : Γ(N, W) :=
        (pullbackUnitSections (fst' I q) U W (e'_s I q K (K.face s j))).app M x
      have hres : (reesTensorPresheaf q I M).res (K.inter_le_inter_face s j)
          (p ⊗ₜ[Γ(P, U)] x) =
          reesRestriction q I (K.inter_le_inter_face s j) p ⊗ₜ[Γ(P, V)]
            M.presheaf.map iU.op x :=
        TensorProduct.map_tmul _ _ p x
      have hleft := imageTensorAffineSectionsEquiv_tmul I q K M s
        (reesRestriction q I (K.inter_le_inter_face s j) p) (M.presheaf.map iU.op x)
      have hright := congrArg
        (fun y : Γ(imageTensorModule I q M, W) =>
          (imageTensorModule I q M).presheaf.map iW.op y)
        (imageTensorAffineSectionsEquiv_tmul I q K M (K.face s j) p x)
      have ht := map_tensorSections iW a b
      have ha := imageAffineReesEquiv_symm_face I q K s j p
      have hb := pullbackUnitSections_restriction (fst' I q) M iU iW
        (e'_s I q K (K.face s j)) (e'_s I q K s) x
      have hab := congrArg₂
        (fun c : Γ(imageModule I q, W') => fun d : Γ(N, W') => tensorSections c d) ha hb
      exact (congrArg (imageTensorAffineSectionsEquiv I q K M s) hres).trans
        (hleft.trans (hab.symm.trans (ht.symm.trans hright.symm)))
  | add z w hz hw =>
      let F := reesTensorPresheaf q I M
      let G := toOModulePresheaf (π' I q) (imageTensorModule I q M)
      let z₀ : F.obj U := z
      let w₀ : F.obj U := w
      let l : F.obj U →+ G.obj W' :=
        (imageTensorAffineSectionsEquiv I q K M s).toAddMonoidHom.comp
          (F.res (K.inter_le_inter_face s j)).toAddMonoidHom
      let r : F.obj U →+ G.obj W' :=
        (G.res (K'_inter_le_inter_face I q K s j)).toAddMonoidHom.comp
          (imageTensorAffineSectionsEquiv I q K M (K.face s j)).toAddMonoidHom
      exact (l.map_add z₀ w₀).trans
        ((congrArg₂ (fun a b : G.obj W' => a + b) hz hw).trans (r.map_add z₀ w₀).symm)

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS
