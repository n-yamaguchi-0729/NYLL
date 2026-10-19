/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalSimpleRoot
import Mathlib.FieldTheory.PrimitiveElement

/-! # Formal lifting through a finite separable field extension

A deformation of the base field into power series, with its given constant
coefficient, extends uniquely to a finite separable extension. A primitive
element and its separable minimal polynomial supply the actual Hensel root;
the power basis then constructs the homomorphism on the whole extension.
-/

noncomputable section

namespace PowerSeries

variable {R F : Type*} [Field R] [Field F] [Algebra R F]
  [FiniteDimensional R F] [Algebra.IsSeparable R F]

/-- A formal deformation of the base embedding lifts uniquely through any
finite separable field extension, with identity constant coefficient. -/
theorem existsUnique_formalLift_finiteSeparable
    (τ : R →+* PowerSeries F)
    (hτ : constantCoeff.comp τ = algebraMap R F) :
    ∃! σ : F →+* PowerSeries F,
      σ.comp (algebraMap R F) = τ ∧ constantCoeff.comp σ = RingHom.id F := by
  let pb := Field.powerBasisOfFiniteOfSeparable R F
  let p := minpoly R pb.gen
  have hp : p.Monic := minpoly.monic pb.isIntegral_gen
  have hmap : (p.map τ).map constantCoeff = p.map (algebraMap R F) := by
    rw [Polynomial.map_map, hτ]
  have hroot : ((p.map τ).map constantCoeff).eval pb.gen = 0 := by
    rw [hmap, Polynomial.eval_map]
    exact minpoly.aeval R pb.gen
  have hder : ((p.map τ).map constantCoeff).derivative.eval pb.gen ≠ 0 := by
    rw [hmap, Polynomial.derivative_map, Polynomial.eval_map]
    exact (Algebra.IsSeparable.isSeparable R pb.gen).aeval_derivative_ne_zero
      (minpoly.aeval R pb.gen)
  obtain ⟨A, hA, hUnique⟩ := existsUnique_monic_root_of_constantCoeff
    (p.map τ) (hp.map τ) pb.gen hroot hder
  let : Algebra R (PowerSeries F) := τ.toAlgebra
  have hAeval : Polynomial.aeval A (minpoly R pb.gen) = 0 := by
    change Polynomial.eval₂ τ A p = 0
    simpa only [Polynomial.eval_map] using hA.1
  let φ : F →ₐ[R] PowerSeries F := pb.lift A hAeval
  let ρ : PowerSeries F →ₐ[R] F :=
    { toRingHom := constantCoeff
      commutes' := fun x => RingHom.congr_fun hτ x }
  have hρ : ρ.comp φ = AlgHom.id R F := by
    apply pb.algHom_ext
    change constantCoeff (φ pb.gen) = pb.gen
    rw [PowerBasis.lift_gen]
    exact hA.2
  refine ⟨φ.toRingHom, ⟨?_, ?_⟩, ?_⟩
  · apply RingHom.ext
    intro x
    exact φ.commutes x
  · exact congrArg AlgHom.toRingHom hρ
  · intro σ hσ
    let ψ : F →ₐ[R] PowerSeries F :=
      { toRingHom := σ
        commutes' := fun x => RingHom.congr_fun hσ.1 x }
    have hψroot : (p.map τ).eval (ψ pb.gen) = 0 := by
      rw [Polynomial.eval_map]
      change Polynomial.aeval (ψ pb.gen) (minpoly R pb.gen) = 0
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    have hψres : constantCoeff (ψ pb.gen) = pb.gen :=
      RingHom.congr_fun hσ.2 pb.gen
    have hψgen : ψ pb.gen = φ pb.gen := by
      rw [PowerBasis.lift_gen]
      exact hUnique (ψ pb.gen) ⟨hψroot, hψres⟩
    exact congrArg AlgHom.toRingHom (pb.algHom_ext hψgen)

end PowerSeries
