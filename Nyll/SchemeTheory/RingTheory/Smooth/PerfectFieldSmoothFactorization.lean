/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.EssentialFiniteness

/-!
# Actual smooth factorizations with a field target

Over a perfect coefficient field, a finite-type algebra mapping to any
field factors through a smooth algebra: take its actual prime quotient
and invert a nonzero element in its generic smooth locus. Both maps and
their original composite are retained.

This is a field-target ingredient for desingularization. It does not
assert such a factorization for a completion or for an arbitrary regular
target ring.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Algebra

/-- A field-valued map of a finite-type algebra over a perfect field
factors through an actual smooth localization of its prime quotient. -/
theorem exists_smooth_localization_ker_factorization
    {K : Type u} {B : Type v} {L : Type w}
    [Field K] [PerfectField K] [CommRing B] [Field L]
    [Algebra K B] [Algebra K L] [Algebra.FiniteType K B]
    (f : B →ₐ[K] L) :
    ∃ d : B ⧸ RingHom.ker f,
      d ≠ 0 ∧ Algebra.Smooth K (Localization.Away d) ∧
        ∃ g : Localization.Away d →ₐ[K] L,
          ∀ b : B,
            g (algebraMap (B ⧸ RingHom.ker f) (Localization.Away d)
              (Ideal.Quotient.mk (RingHom.ker f) b)) = f b := by
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f.toRingHom
  let Q := B ⧸ RingHom.ker f
  have : Algebra.FinitePresentation K Q :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let F := Localization.AtPrime (⊥ : Ideal Q)
  have : IsFractionRing Q F := by
    change IsLocalization (nonZeroDivisors Q) F
    rw [← Ideal.primeCompl_bot]
    infer_instance
  let _ : Field F := IsFractionRing.toField Q
  have : Algebra.IsSmoothAt K (⊥ : Ideal Q) :=
    Algebra.FormallySmooth.of_perfectField
  obtain ⟨d, hd, hsmooth⟩ :=
    Algebra.IsSmoothAt.exists_notMem_smooth K (⊥ : Ideal Q)
  have hd0 : d ≠ 0 := by
    intro h
    apply hd
    exact (Ideal.mem_bot).mpr h
  let q : Q →ₐ[K] L := Ideal.kerLiftAlg f
  have hqd : IsUnit (q d) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    apply hd0
    exact (Ideal.kerLiftAlg_injective f) (h.trans (map_zero q).symm)
  let g : Localization.Away d →ₐ[K] L :=
    IsLocalization.Away.liftAlgHom d hqd
  refine ⟨d, hd0, hsmooth, g, fun b => ?_⟩
  change IsLocalization.Away.lift d hqd
      (algebraMap Q (Localization.Away d)
        (Ideal.Quotient.mk (RingHom.ker f) b)) = f b
  rw [IsLocalization.Away.lift_eq]
  exact Ideal.kerLiftAlg_mk f b

end Algebra
