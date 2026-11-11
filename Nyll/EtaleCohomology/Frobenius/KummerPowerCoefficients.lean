/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ConstantRootsOfUnityNaturality
public import Nyll.EtaleCohomology.Classical.KummerPullback
public import Nyll.EtaleCohomology.Frobenius.KummerCoefficients
public import Nyll.SchemeTheory.Morphisms.FiniteFieldConstantAction
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Original Kummer coefficients for an arithmetic Frobenius power

Iterating the original base-twist comparison gives the actual factor
q^m for a morphism semilinear for inverse arithmetic Frobenius to the
m-th power. The morphism itself need not be a power of an endomorphism
of its source. This is required on a component fixed only by that
power of the original geometric Frobenius.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  {Y : Scheme.{u}} (c : Y ⟶ Spec (CommRingCat.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

local notation "σ" => AlgEquiv.symm (FiniteField.frobeniusAlgEquivOfAlgebraic k K)

omit [IsAlgClosed K] in
private theorem inverseFrobeniusPower_spec_succ (m : ℕ) :
    Spec.map (CommRingCat.ofHom (σ ^ (m + 1)).toRingHom) =
      Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (RingEquiv.toRingHom (AlgEquiv.toRingEquiv σ))) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change (σ ^ (m + 1)) a = (σ ^ m) (σ a)
  exact congrArg (fun t : K ≃ₐ[k] K => t a) (pow_succ σ m)

/-- The original inverse base twist to any power is cancelled by
the corresponding power of the actual finite-field cardinality. -/
theorem finiteLevelKummerCohomologyEquiv_baseInverseFrobeniusPower
    (m n i : ℕ) (a : finiteLevelCohomology Y ℓ n i) :
    (Fintype.card k ^ m) • finiteLevelKummerCohomologyEquiv
        (c ≫ Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom)) ℓ hℓ n i a =
      finiteLevelKummerCohomologyEquiv c ℓ hℓ n i a := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero]
      change 1 • finiteLevelKummerCohomologyEquiv
        (c ≫ Spec.map (𝟙 (CommRingCat.of K))) ℓ hℓ n i a = _
      rw [Spec.map_id, Category.comp_id, one_nsmul]
  | succ m ih =>
      rw [inverseFrobeniusPower_spec_succ k K m, ← Category.assoc,
        pow_succ' (Fintype.card k) m,
        mul_nsmul, finiteLevelKummerCohomologyEquiv_baseInverseFrobenius k K
          (c ≫ Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom)) ℓ hℓ n i a]
      exact ih

/-- A morphism with the actual inverse-arithmetic power on the base
acts through the original Kummer pullback with the actual factor q^m. -/
theorem finiteLevelKummerCohomologyEquiv_inverseArithmeticPower
    (m : ℕ) (f : Y ⟶ Y)
    (hf : f ≫ c = c ≫ Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom))
    (n i : ℕ) (a : finiteLevelCohomology Y ℓ n i) :
    finiteLevelKummerCohomologyEquiv c ℓ hℓ n i
        (finiteLevelCohomologyPullback ℓ f n i a) =
      (Fintype.card k ^ m) • etaleRootsOfUnityCohomologyPullback f (ℓ ^ (n + 1)) i
        (finiteLevelKummerCohomologyEquiv c ℓ hℓ n i a) := by
  calc
    _ = (Fintype.card k ^ m) • finiteLevelKummerCohomologyEquiv
        (c ≫ Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom)) ℓ hℓ n i
          (finiteLevelCohomologyPullback ℓ f n i a) :=
      (finiteLevelKummerCohomologyEquiv_baseInverseFrobeniusPower k K c ℓ hℓ m n i
        (finiteLevelCohomologyPullback ℓ f n i a)).symm
    _ = (Fintype.card k ^ m) • finiteLevelKummerCohomologyEquiv (f ≫ c) ℓ hℓ n i
        (finiteLevelCohomologyPullback ℓ f n i a) :=
      congrArg (fun d : Y ⟶ Spec (CommRingCat.of K) => (Fintype.card k ^ m) •
        finiteLevelKummerCohomologyEquiv d ℓ hℓ n i
          (finiteLevelCohomologyPullback ℓ f n i a)) hf.symm
    _ = _ := congrArg ((Fintype.card k ^ m) • ·)
      (finiteLevelKummerCohomologyEquiv_pullback f c ℓ hℓ n i a)

end EtaleCohomology
