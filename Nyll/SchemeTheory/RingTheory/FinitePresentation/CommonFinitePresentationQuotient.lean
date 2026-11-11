/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.FinitePresentation.FiniteSubidealSurjectivity
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Common finite-presentation refinements of affine closed models

Two finitely presented algebras surjecting onto the same algebra admit a
common finitely presented quotient of their tensor product. Both original
algebras still surject onto the common quotient, which still maps onto the
original target. Geometrically this supplies a common closed refinement of
two affine ambient models, with their original maps retained.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Algebra

private theorem surjective_quotient_of_le
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {J K : Ideal S} (hJK : J ≤ K)
    (hJ : Function.Surjective (algebraMap R (S ⧸ J))) :
    Function.Surjective (algebraMap R (S ⧸ K)) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.factor_surjective hJK y
  obtain ⟨r, rfl⟩ := hJ z
  exact ⟨r, ((Ideal.Quotient.factorₐ R hJK).commutes r).symm⟩

/-- The actual tensor-product map to a common quotient has a finite
subideal of its kernel for which both projections are still surjective. -/
theorem exists_common_finitePresentation_quotient
    {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    [FinitePresentation R A] [FinitePresentation R B]
    (α : A →ₐ[R] C) (β : B →ₐ[R] C)
    (hα : Function.Surjective α) (hβ : Function.Surjective β) :
    let q := TensorProduct.lift α β (fun a b => Commute.all (α a) (β b))
    ∃ J : Ideal (A ⊗[R] B), J ≤ RingHom.ker q.toRingHom ∧ J.FG ∧
      FinitePresentation R ((A ⊗[R] B) ⧸ J) ∧
      Function.Surjective ((Ideal.Quotient.mkₐ R J).comp TensorProduct.includeLeft) ∧
      Function.Surjective ((Ideal.Quotient.mkₐ R J).comp TensorProduct.includeRight) := by
  let T := A ⊗[R] B
  let q : T →ₐ[R] C := TensorProduct.lift α β (fun a b => Commute.all (α a) (β b))
  let I : Ideal T := RingHom.ker q.toRingHom
  have hqA (a : A) : q (algebraMap A T a) = α a := by
    change α a * β 1 = α a
    rw [map_one, mul_one]
  have hA : Function.Surjective (algebraMap A (T ⧸ I)) := by
    intro y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hα (q t)
    refine ⟨a, ?_⟩
    apply RingHom.kerLift_injective q.toRingHom
    change q (algebraMap A T a) = q t
    exact (hqA a).trans ha
  obtain ⟨J₁, hJ₁I, hJ₁fg, hJ₁⟩ := exists_fg_subideal_surjective_quotient I hA
  let : Algebra B T := TensorProduct.rightAlgebra
  have : FiniteType B T :=
    FiniteType.equiv (inferInstanceAs (FiniteType B (B ⊗[R] A)))
      (TensorProduct.commRight R B A)
  have hqB (b : B) : q (algebraMap B T b) = β b := by
    change α 1 * β b = β b
    rw [map_one, one_mul]
  have hB : Function.Surjective (algebraMap B (T ⧸ I)) := by
    intro y
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, hb⟩ := hβ (q t)
    refine ⟨b, ?_⟩
    apply RingHom.kerLift_injective q.toRingHom
    change q (algebraMap B T b) = q t
    exact (hqB b).trans hb
  obtain ⟨J₂, hJ₂I, hJ₂fg, hJ₂⟩ := exists_fg_subideal_surjective_quotient I hB
  let J : Ideal T := J₁ ⊔ J₂
  have hJfg : J.FG := Submodule.FG.sup hJ₁fg hJ₂fg
  have : FinitePresentation R T := FinitePresentation.trans R A T
  refine ⟨J, sup_le hJ₁I hJ₂I, hJfg, FinitePresentation.quotient hJfg, ?_, ?_⟩
  · exact surjective_quotient_of_le (R := A) (le_sup_left : J₁ ≤ J) hJ₁
  · exact surjective_quotient_of_le (R := B) (le_sup_right : J₂ ≤ J) hJ₂

end Algebra
