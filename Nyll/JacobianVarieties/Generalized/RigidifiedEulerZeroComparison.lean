/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedIdentityBaseChange
import Nyll.JacobianVarieties.Generalized.RigidifiedEulerDegree
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The actual Euler-degree kernel and the original modulus Picard-zero group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : D ⟶ C) [IsClosedImmersion i]

/-- The closed modulus is its entire kernel subscheme, with its nilpotent structure. -/
theorem closedModulus_square :
    i ≫ 𝟙 C = (asIso i.toImage).hom ≫ i.ker.subschemeι :=
  (Category.comp_id i).trans i.toImage_imageι.symm

/-- Transport the actual canonical ideal rigidification to the original closed immersion. -/
def closedModulusClassesEquiv :
    RigidifiedLineBundle.Classes i.ker.subschemeι ≃* RigidifiedLineBundle.Classes i :=
  RigidifiedLineBundle.classesPullbackMulEquiv (Iso.refl C) (asIso i.toImage)
    (closedModulus_square i)

/-- Full-modulus classes on the curve are the original identity-test classes. -/
def closedModulusIdentityClassesEquiv :
    RigidifiedLineBundle.Classes i.ker.subschemeι ≃*
      RigidifiedLineBundle.Classes (modulusBaseChange c i (𝟙 (Spec (CommRingCat.of K)))) :=
  (closedModulusClassesEquiv i).trans (modulusIdentityBaseChangeClassesEquiv c i)

variable [IsAlgClosed K]

/-- Both actual square comparisons preserve the original bundle's algebraic triviality. -/
theorem closedModulusIdentityClassesEquiv_zero_iff
    (M : RigidifiedLineBundle i.ker.subschemeι) :
    closedModulusIdentityClassesEquiv c i (RigidifiedLineBundle.classOf M) ∈
        modulusPicardZeroSubgroup c i (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ↔
      RelPicard.IsAlgEquivZero c M.L := by
  let N := M.pullback (𝟙 C) i.toImage (closedModulus_square i)
  have h := modulusIdentityBaseChangeClassesEquiv_zero_iff c i N
  change closedModulusIdentityClassesEquiv c i (RigidifiedLineBundle.classOf M) ∈
      modulusPicardZeroSubgroup c i (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ↔
    RelPicard.IsAlgEquivZero c ((Scheme.Modules.pullback (𝟙 C)).obj M.L) at h
  refine h.trans ⟨?_, ?_⟩
  · exact fun hM => hM.of_iso ((Scheme.Modules.pullbackId C).app M.L)
  · exact fun hM => hM.of_iso ((Scheme.Modules.pullbackId C).app M.L).symm

variable [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
  (𝒱 : C.TwoAffineOpenCover)

/-- The original geometric-fibre condition is exactly the Euler-degree kernel. -/
theorem closedModulusIdentityClassesEquiv_mem_zero_iff
    (x : RigidifiedLineBundle.Classes i.ker.subschemeι) :
    closedModulusIdentityClassesEquiv c i x ∈
        modulusPicardZeroSubgroup c i (Over.mk (𝟙 (Spec (CommRingCat.of K)))) ↔
      RigidifiedLineBundle.eulerDegree c 𝒱 i.ker.subschemeι (Additive.ofMul x) = 0 := by
  induction x using Quotient.ind with
  | _ M =>
    exact (closedModulusIdentityClassesEquiv_zero_iff c i M).trans
      (RigidifiedLineBundle.eulerDegree_classOf_eq_zero_iff c 𝒱 i.ker.subschemeι M).symm

/-- The function-field comparison's concrete degree-zero target is the existing raw group. -/
def closedModulusEulerZeroEquiv :
    (RigidifiedLineBundle.eulerDegree c 𝒱 i.ker.subschemeι).ker ≃+
      Additive (modulusPicardZeroSubgroup c i (Over.mk (𝟙 (Spec (CommRingCat.of K))))) where
  toFun x := Additive.ofMul ⟨closedModulusIdentityClassesEquiv c i x.1.toMul,
    (closedModulusIdentityClassesEquiv_mem_zero_iff c i 𝒱 x.1.toMul).mpr x.2⟩
  invFun y := ⟨Additive.ofMul ((closedModulusIdentityClassesEquiv c i).symm y.toMul.1),
    (closedModulusIdentityClassesEquiv_mem_zero_iff c i 𝒱 _).mp (by
      rw [MulEquiv.apply_symm_apply]
      exact y.toMul.2)⟩
  left_inv x := Subtype.ext (congrArg Additive.ofMul
    ((closedModulusIdentityClassesEquiv c i).symm_apply_apply x.1.toMul))
  right_inv y := by
    change (⟨closedModulusIdentityClassesEquiv c i
      ((closedModulusIdentityClassesEquiv c i).symm y.toMul.1), _⟩ :
        modulusPicardZeroSubgroup c i (Over.mk (𝟙 (Spec (CommRingCat.of K))))) = y.toMul
    exact Subtype.ext ((closedModulusIdentityClassesEquiv c i).apply_symm_apply y.toMul.1)
  map_add' x y := by
    apply Subtype.ext
    exact (closedModulusIdentityClassesEquiv c i).map_mul x.1.toMul y.1.toMul

end AlgebraicGeometry.GeneralizedJacobian
