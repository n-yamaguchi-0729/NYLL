/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicIsomorphism
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.JacobianVarieties.Kummer.CurveNativeAdicH2
public import Nyll.JacobianVarieties.Kummer.CurveNativeH2Degree
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Original H² degree through an actual curve-model isomorphism

An actual scheme isomorphism transports the native finite, integral, and
rational H² degree comparisons by the original pullbacks. The same
isomorphism is retained at every finite coefficient level and every
inverse-limit projection. This allows a shared curve model to be used in
geometric and arithmetic calculations without replacing the original
cohomology groups.

These comparisons use the chosen coherent roots. Arithmetic equivariance
and independence of the curve-model isomorphism are separate statements.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleCohomology.Classical
open scoped TensorProduct

namespace AlgebraicCurve.CurveModel

variable {K F : Type u} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  (M : CurveModel K F) {X : Scheme.{u}} (e : M.C ≅ X)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- Degree on the original finite H² of a scheme isomorphic to the
given actual curve model, using pullback along that same isomorphism. -/
def nativeFiniteLevelH2DegreeEquivOfIso (n : ℕ) :
    finiteLevelCohomology X ℓ n 2 ≃+ ZMod (ℓ ^ (n + 1)) :=
  (finiteLevelCohomologyIso ℓ e n 2).toAddEquiv.trans
    (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n)

/-- The transported finite comparison retains the original pullback. -/
theorem nativeFiniteLevelH2DegreeEquivOfIso_apply (n : ℕ)
    (a : finiteLevelCohomology X ℓ n 2) :
    M.nativeFiniteLevelH2DegreeEquivOfIso e ℓ hℓ n a =
      M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
        (finiteLevelCohomologyPullback ℓ e.hom n 2 a) := rfl

/-- The same original coefficient reductions are retained after
transport through the actual curve-model isomorphism. -/
theorem nativeFiniteLevelH2DegreeEquivOfIso_reduction (n : ℕ)
    (a : finiteLevelCohomology X ℓ (n + 1) 2) :
    M.nativeFiniteLevelH2DegreeEquivOfIso e ℓ hℓ n
        (finiteLevelReduction X ℓ n 2 a) =
      ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
        (M.nativeFiniteLevelH2DegreeEquivOfIso e ℓ hℓ (n + 1) a) := by
  change M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
      (finiteLevelCohomologyIso ℓ e n 2 (finiteLevelReduction X ℓ n 2 a)) =
    ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
      (M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ (n + 1)
        (finiteLevelCohomologyIso ℓ e (n + 1) 2 a))
  rw [finiteLevelCohomologyIso_reduction, nativeFiniteLevelH2DegreeEquiv_reduction]

/-- The finite degree comparison is linear for the original adic
scalar action on the original finite coefficients. -/
def nativeFiniteLevelH2DegreeLinearEquivOfIso (n : ℕ) :
    let : Module ℤ_[ℓ] (ellPowerCoefficients.{u} ℓ n) := ellPowerPadicModule ℓ n
    finiteLevelCohomology X ℓ n 2 ≃ₗ[ℤ_[ℓ]] ellPowerCoefficients.{u} ℓ n := by
  intro coefficientModule
  exact (finiteLevelCohomologyIso ℓ e n 2).trans
    (M.nativeFiniteLevelH2DegreeLinearEquiv ℓ hℓ n)

/-- Its residue coordinate is the same transported native degree. -/
theorem nativeFiniteLevelH2DegreeLinearEquivOfIso_down (n : ℕ)
    (a : finiteLevelCohomology X ℓ n 2) :
    (M.nativeFiniteLevelH2DegreeLinearEquivOfIso e ℓ hℓ n a).down =
      M.nativeFiniteLevelH2DegreeEquivOfIso e ℓ hℓ n a := rfl

/-- Degree on the original integral inverse limit, transported by the
same actual isomorphism as at the finite coefficient levels. -/
def nativeEllAdicH2DegreeEquivOfIso :
    ellAdicCohomology X ℓ 2 ≃ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  (ellAdicCohomologyIso ℓ e 2).trans (M.nativeEllAdicH2DegreeEquiv ℓ hℓ)

/-- Integral transport retains pullback by the original morphism. -/
theorem nativeEllAdicH2DegreeEquivOfIso_apply (a : ellAdicCohomology X ℓ 2) :
    M.nativeEllAdicH2DegreeEquivOfIso e ℓ hℓ a =
      M.nativeEllAdicH2DegreeEquiv ℓ hℓ (ellAdicCohomologyPullback ℓ e.hom 2 a) := rfl

/-- Every original finite projection agrees with the finite degree
comparison transported through the same scheme isomorphism. -/
theorem nativeEllAdicH2DegreeEquivOfIso_reduction
    (a : ellAdicCohomology X ℓ 2) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (M.nativeEllAdicH2DegreeEquivOfIso e ℓ hℓ a) =
      M.nativeFiniteLevelH2DegreeEquivOfIso e ℓ hℓ n (ellAdicProjection X ℓ 2 n a) := by
  change PadicInt.toZModPow (n + 1)
      (M.nativeEllAdicH2DegreeEquiv ℓ hℓ (ellAdicCohomologyIso ℓ e 2 a)) =
    M.nativeFiniteLevelH2DegreeEquiv ℓ hℓ n
      (finiteLevelCohomologyIso ℓ e n 2 (ellAdicProjection X ℓ 2 n a))
  rw [nativeEllAdicH2DegreeEquiv_reduction, ellAdicCohomologyIso_projection]

/-- The inverse transported integral comparison retains every
original finite projection. -/
theorem nativeEllAdicH2DegreeEquivOfIso_symm_projection (c : ℤ_[ℓ]) (n : ℕ) :
    ellAdicProjection X ℓ 2 n ((M.nativeEllAdicH2DegreeEquivOfIso e ℓ hℓ).symm c) =
      (M.nativeFiniteLevelH2DegreeEquivOfIso e ℓ hℓ n).symm
        (PadicInt.toZModPow (n + 1) c) := by
  apply (M.nativeFiniteLevelH2DegreeEquivOfIso e ℓ hℓ n).injective
  rw [AddEquiv.apply_symm_apply, ← nativeEllAdicH2DegreeEquivOfIso_reduction,
    LinearEquiv.apply_symm_apply]

/-- Degree on the original rational scalar extension, using the
original rational pullback through the same actual isomorphism. -/
def nativeRationalEllAdicH2DegreeEquivOfIso :
    rationalEllAdicCohomology ℓ X 2 ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ] :=
  (rationalEllAdicCohomologyIso ℓ e 2).trans (M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ)

/-- Rational transport retains pullback by the original morphism. -/
theorem nativeRationalEllAdicH2DegreeEquivOfIso_apply
    (a : rationalEllAdicCohomology ℓ X 2) :
    M.nativeRationalEllAdicH2DegreeEquivOfIso e ℓ hℓ a =
      M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
        (rationalEllAdicCohomologyPullback ℓ e.hom 2 a) := rfl

/-- On original pure tensors, the rational comparison is the scalar
extension of the integral comparison transported through the same isomorphism. -/
theorem nativeRationalEllAdicH2DegreeEquivOfIso_tmul
    (q : ℚ_[ℓ]) (a : ellAdicCohomology X ℓ 2) :
    M.nativeRationalEllAdicH2DegreeEquivOfIso e ℓ hℓ (q ⊗ₜ[ℤ_[ℓ]] a) =
      M.nativeEllAdicH2DegreeEquivOfIso e ℓ hℓ a • q := by
  change M.nativeRationalEllAdicH2DegreeEquiv ℓ hℓ
      (rationalEllAdicCohomologyIso ℓ e 2 (q ⊗ₜ[ℤ_[ℓ]] a)) =
    M.nativeEllAdicH2DegreeEquiv ℓ hℓ (ellAdicCohomologyIso ℓ e 2 a) • q
  rw [rationalEllAdicCohomologyIso_tmul, nativeRationalEllAdicH2DegreeEquiv_tmul]

include e hℓ in
/-- The original finite H² has the expected finite cyclic cardinality. -/
theorem nativeFiniteLevelH2_card_of_iso (n : ℕ) :
    Nat.card (finiteLevelCohomology X ℓ n 2) = ℓ ^ (n + 1) :=
  (Nat.card_congr (finiteLevelCohomologyIso ℓ e n 2).toEquiv).trans
    (M.nativeFiniteLevelH2_card ℓ hℓ n)

include e hℓ in
/-- The original integral H² is finite and free. -/
theorem nativeEllAdicH2_finite_free_of_iso :
    Module.Free ℤ_[ℓ] (ellAdicCohomology X ℓ 2) ∧
      Module.Finite ℤ_[ℓ] (ellAdicCohomology X ℓ 2) := by
  let b := (Module.Basis.singleton Unit ℤ_[ℓ]).map
    (M.nativeEllAdicH2DegreeEquivOfIso e ℓ hℓ).symm
  exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩

include e hℓ in
/-- The original integral H² has rank one. -/
theorem nativeEllAdicH2_finrank_of_iso : Module.finrank ℤ_[ℓ] (ellAdicCohomology X ℓ 2) = 1 :=
  (M.nativeEllAdicH2DegreeEquivOfIso e ℓ hℓ).finrank_eq.trans
    (CommSemiring.finrank_self ℤ_[ℓ])

include e hℓ in
/-- The original rational H² is finite-dimensional. -/
theorem nativeRationalEllAdicH2_finiteDimensional_of_iso :
    FiniteDimensional ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 2) :=
  Module.Finite.of_basis ((Module.Basis.singleton Unit ℚ_[ℓ]).map
    (M.nativeRationalEllAdicH2DegreeEquivOfIso e ℓ hℓ).symm)

include e hℓ in
/-- The original rational H² has dimension one. -/
theorem nativeRationalEllAdicH2_finrank_of_iso :
    Module.finrank ℚ_[ℓ] (rationalEllAdicCohomology ℓ X 2) = 1 :=
  (M.nativeRationalEllAdicH2DegreeEquivOfIso e ℓ hℓ).finrank_eq.trans
    (CommSemiring.finrank_self ℚ_[ℓ])

end AlgebraicCurve.CurveModel
