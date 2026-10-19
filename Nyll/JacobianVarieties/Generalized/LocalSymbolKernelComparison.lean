/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.UniversalFactorLocalSymbol
import Nyll.JacobianVarieties.Generalized.DivisorClassTransitionPoints
import Nyll.JacobianVarieties.Generalized.LocalUnitKernel

/-! # Local symbols on the actual empty-modulus transition kernel

Every point killed by the scheme transition to the empty-modulus Jacobian
is the actual point of a principal unit boundary. The original universal
group factor evaluates that point by the negative sum of local symbols.
Isolated full jets then identify vanishing on the entire transition kernel
with vanishing of each local symbol on local units at the modulus places.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.GeneralizedJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)
  [GeometricallyIntegral M.toBase]
  {d : ℕ} (D : RelEffCartierDiv M.toBase d (𝟙 (Spec (CommRingCat.of K))))
  (D₀ : RelEffCartierDiv M.toBase 0 (𝟙 (Spec (CommRingCat.of K))))

/-- All points of the actual transition kernel, and only those points,
are represented by principal unit boundaries with the full modulus. -/
theorem emptyTransition_kernel_iff_exists_unitBoundary :
    let hc : IsCurveOver K F :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase M.ffEquiv M.ffEquiv_algebraMap
    let _ : HasPrincipalDivisors K F := hc.toHasPrincipalDivisors
    let hD₀ : D.I ≤ D₀.I := D₀.I_eq_top_of_degree_zero.symm ▸ le_top
    ∀ p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D).X,
      p ≫ (GeneralizedJacobian.transition M.toBase D D₀ hD₀).hom.hom.hom = 1 ↔
        ∃ f : (M.functionFieldModulus D).awayUnits,
          (M.divisorClassPointEquiv D
            ((M.functionFieldModulus D).unitBoundary (Additive.ofMul f))).toMul = p := by
  intro hc principals hD₀ p
  obtain ⟨z, hz⟩ := (M.divisorClassPointEquiv D).surjective (Additive.ofMul p)
  have hp : (M.divisorClassPointEquiv D z).toMul = p := congrArg Additive.toMul hz
  have hh : (M.divisorClassPointEquiv D z).toMul ≫
      (GeneralizedJacobian.transition M.toBase D D₀ hD₀).hom.hom.hom = 1 ↔
        (M.functionFieldModulus D).toPic0 z = 0 :=
    M.divisorClassPointEquiv_emptyTransition_kernel D D₀ z
  rw [← hp, hh]
  constructor
  · intro hzero
    have hmem : z ∈ (M.functionFieldModulus D).unitBoundary.range := by
      rw [Modulus.range_unitBoundary]
      exact hzero
    obtain ⟨f, hf⟩ := hmem
    refine ⟨f.toMul, ?_⟩
    exact congrArg (fun y => (M.divisorClassPointEquiv D y).toMul) hf
  · rintro ⟨f, hf⟩
    have hclass : (M.functionFieldModulus D).unitBoundary (Additive.ofMul f) = z :=
      (M.divisorClassPointEquiv D).injective (Additive.toMul.injective hf)
    exact (congrArg (M.functionFieldModulus D).toPic0 hclass).symm.trans
      ((M.functionFieldModulus D).toPic0_unitBoundary (Additive.ofMul f))

variable
  (ε : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶
    Over.mk ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase))
  (G : CommGrp (Over (Spec (CommRingCat.of K))))
  (q : SchemeHomOver ((modulusComplement (modulusCurveMap D)).ι ≫ M.toBase) G.X.hom)
  (hmod : M.regularMapHasModulus D G q)
  (hε : ε ≫ Over.homMk q.1 q.2 = 1)
  (φ : groupScheme M.toBase D ⟶ G)
  (hφ : modulusAbelMap M.toBase D ε ≫ φ.hom.hom.hom = Over.homMk q.1 q.2)

include hε hφ

/-- Every actual kernel point has a principal unit representative whose
local symbols compute its value under the original universal group factor. -/
theorem groupFactor_emptyTransition_kernel_value :
    let hc : IsCurveOver K F :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase M.ffEquiv M.ffEquiv_algebraMap
    let _ : HasPrincipalDivisors K F := hc.toHasPrincipalDivisors
    let hD₀ : D.I ≤ D₀.I := D₀.I_eq_top_of_degree_zero.symm ▸ le_top
    ∀ p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D).X,
      p ≫ (GeneralizedJacobian.transition M.toBase D D₀ hD₀).hom.hom.hom = 1 →
        ∃ f : (M.functionFieldModulus D).awayUnits,
          (M.divisorClassPointEquiv D
            ((M.functionFieldModulus D).unitBoundary (Additive.ofMul f))).toMul = p ∧
          Additive.ofMul (p ≫ φ.hom.hom.hom) =
            -∑ w ∈ (M.functionFieldModulus D).support,
              hmod.localSymbol w (Additive.ofMul f.1) := by
  intro hc principals hD₀ p hp
  obtain ⟨f, hf⟩ := (M.emptyTransition_kernel_iff_exists_unitBoundary D D₀ p).mp hp
  refine ⟨f, hf, ?_⟩
  exact (congrArg (fun y => Additive.ofMul (y ≫ φ.hom.hom.hom)) hf).symm.trans
    (M.groupFactor_unitBoundary D ε G q hmod hε φ hφ f)

/-- The actual group factor kills the entire empty-modulus transition
kernel exactly when its local symbols vanish on local units at every
modulus place. The reverse test is supplied by constructed isolated jets. -/
theorem groupFactor_kills_emptyTransition_kernel_iff :
    let hc : IsCurveOver K F :=
      isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
        M.toBase M.ffEquiv M.ffEquiv_algebraMap
    let _ : HasPrincipalDivisors K F := hc.toHasPrincipalDivisors
    let hD₀ : D.I ≤ D₀.I := D₀.I_eq_top_of_degree_zero.symm ▸ le_top
    (∀ p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D).X,
      p ≫ (GeneralizedJacobian.transition M.toBase D D₀ hD₀).hom.hom.hom = 1 →
        p ≫ φ.hom.hom.hom = 1) ↔
      ∀ w : Place K F, M.functionFieldModulus D w ≠ 0 →
        ∀ g : Fˣ, w.ord (g : F) = 0 → hmod.localSymbol w (Additive.ofMul g) = 0 := by
  intro hc principals hD₀
  constructor
  · intro hkill w hw g hg
    obtain ⟨f, _, _, hvalue⟩ :=
      M.groupFactor_exists_isolated_boundary D ε G q hmod hε φ hφ w hw g hg
    let p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ (groupScheme M.toBase D).X :=
      (M.divisorClassPointEquiv D
        ((M.functionFieldModulus D).unitBoundary (Additive.ofMul f))).toMul
    have hp : p ≫
        (GeneralizedJacobian.transition M.toBase D D₀ hD₀).hom.hom.hom = 1 :=
      (M.emptyTransition_kernel_iff_exists_unitBoundary D D₀ p).mpr ⟨f, rfl⟩
    change Additive.ofMul (p ≫ φ.hom.hom.hom) = _ at hvalue
    rw [hkill p hp] at hvalue
    exact neg_eq_zero.mp hvalue.symm
  · intro hlocal p hp
    obtain ⟨f, _, hvalue⟩ :=
      M.groupFactor_emptyTransition_kernel_value D D₀ ε G q hmod hε φ hφ p hp
    have hsum : (∑ w ∈ (M.functionFieldModulus D).support,
        hmod.localSymbol w (Additive.ofMul f.1)) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hw' : M.functionFieldModulus D w ≠ 0 := Finsupp.mem_support_iff.mp hw
      exact hlocal w hw' f.1 (f.2 w hw')
    apply Additive.ofMul.injective
    change Additive.ofMul (p ≫ φ.hom.hom.hom) = 0
    exact hvalue.trans ((congrArg Neg.neg hsum).trans neg_zero)

end AlgebraicCurve.CurveModel
