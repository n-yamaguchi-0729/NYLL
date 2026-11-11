/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleQuotientLift
public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.NilpotentSurjectivity
public import Nyll.SchemeTheory.RingTheory.Smooth.JacobianLocalization
public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Smooth presentations of nilpotent thickenings

A standard smooth algebra lifts through a surjection of coefficient
rings by the existing coefficient-model and Jacobian-localization
construction. If a finitely presented algebra becomes standard smooth
after a nilpotent base quotient, formal smoothness lifts the resulting
presentation map. Nilpotent surjectivity makes the lift surjective; its
kernel is finitely generated and contained in the extended base ideal.

This proves the final presentation step of Stacks Project, Lemma 16.5.1:
https://stacks.math.columbia.edu/tag/07CK
It does not assume or assert smooth factorization for an arbitrary map
to a completed ring.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u₀ u v

namespace Algebra.IsStandardSmooth

/-- A standard smooth algebra lifts along a surjective coefficient map.
The existing Jacobian-model equivalence applies in every relative
dimension. -/
theorem exists_lift_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (R₀ : Type u₀) [CommRing R₀] [Algebra R₀ R]
    (h : Function.Surjective (algebraMap R₀ R)) [IsStandardSmooth R S] :
    ∃ (T : Type u₀) (_ : CommRing T) (_ : Algebra R₀ T),
      IsStandardSmooth R₀ T ∧ Nonempty (R ⊗[R₀] T ≃ₐ[R] S) := by
  let _ : Algebra R₀ S := ((algebraMap R S).comp (algebraMap R₀ R)).toAlgebra
  have : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ι, σ, _, _, ⟨Q⟩⟩ := IsStandardSmooth.out (R := R) (S := S)
  have : Q.toPresentation.HasCoeffs R₀ := ⟨fun r _ => h r⟩
  let Q₀ := Q.toPreSubmersivePresentation.ofHasCoeffs R₀
  exact ⟨Localization.Away Q₀.jacobian, inferInstance, inferInstance,
    Q₀.jacobianLocalizationPresentation.isStandardSmooth,
    ⟨Algebra.Etale.tensorJacobianModelEquiv R₀ Q⟩⟩

end Algebra.IsStandardSmooth

namespace Algebra

/-- A finitely presented algebra with standard smooth reduction modulo
a nilpotent base ideal is an actual quotient of a smooth algebra by a
finitely generated ideal contained in that extended base ideal. -/
theorem exists_smooth_surjection_of_standardSmooth_quotient
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (I : Ideal R) (hI : IsNilpotent I)
    [IsStandardSmooth (R ⧸ I) (A ⧸ I.map (algebraMap R A))] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
      Smooth R B ∧ ∃ f : B →ₐ[R] A,
        Function.Surjective f ∧ (RingHom.ker f.toRingHom).FG ∧
          RingHom.ker f.toRingHom ≤ I.map (algebraMap R B) := by
  let IA := I.map (algebraMap R A)
  obtain ⟨B, _, _, hB, ⟨e⟩⟩ :=
    IsStandardSmooth.exists_lift_of_surjective
      (R := R ⧸ I) (S := A ⧸ IA) R Ideal.Quotient.mk_surjective
  have : IsStandardSmooth R B := hB
  let IB := I.map (algebraMap R B)
  let e' : (B ⧸ IB) ≃ₐ[R] (A ⧸ IA) :=
    ((TensorProduct.quotIdealMapEquivQuotTensor B I).trans e).restrictScalars R
  let g : B →ₐ[R] A ⧸ IA := e'.toAlgHom.comp (Ideal.Quotient.mkₐ R IB)
  obtain ⟨n, hn⟩ := hI
  have hIA : IsNilpotent IA := by
    refine ⟨n, ?_⟩
    change I.map (algebraMap R A) ^ n = ⊥
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
  obtain ⟨f, hf⟩ := FormallySmooth.exists_lift IA hIA g
  have hf_surj : Function.Surjective f := by
    apply LinearMap.surjective_of_comp_surjective_of_ker_le_smul_of_pow_smul_eq_bot
      f.toLinearMap (Ideal.Quotient.mkₐ R IA).toLinearMap I n
    · change Function.Surjective ((Ideal.Quotient.mkₐ R IA).comp f)
      rw [hf]
      exact e'.surjective.comp Ideal.Quotient.mk_surjective
    · intro a ha
      rw [Ideal.smul_top_eq_map]
      exact Ideal.Quotient.eq_zero_iff_mem.mp ha
    · rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul]
  refine ⟨B, inferInstance, inferInstance, inferInstance, f, hf_surj,
    FinitePresentation.ker_fG_of_surjective f hf_surj, ?_⟩
  intro b hb
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply e'.injective
  rw [map_zero]
  change g b = 0
  rw [← hf]
  change Ideal.Quotient.mk IA (f b) = 0
  rw [show f b = 0 from hb, map_zero]

end Algebra
