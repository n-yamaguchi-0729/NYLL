/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingOriginalQuotient
public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingReducedSmooth

/-!
# The original reduction map and the reduced lifting presentation

The iterated quotient of the actual lifting algebra is identified with the
sum-ideal quotient. Together with the original source quotient equivalence,
this identifies the constructed map from the original source modulo the
parameter with the canonical original-variable map of the reduced lifting
presentation. Every comparison is proved on actual polynomial representatives.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

/-- The actual lifting algebra modulo the parameter is the quotient by the
lifting ideal and the parameter together, preserving all representatives. -/
theorem exists_principalLifting_quotient_equiv
    {R n m k : Type*} [CommRing R] [Fintype m]
    (π : R) (f : m → MvPolynomial n R) (A : k → MvPolynomial n R)
    (H : k → m → m → MvPolynomial n R) (g : k → m → MvPolynomial n R) :
    let J := principalLiftingIdeal π f A H g
    let D := MvPolynomial (n ⊕ m) R ⧸ J
    ∃ e : (D ⧸ Ideal.span {algebraMap R D π}) ≃+*
        MvPolynomial (n ⊕ m) R ⧸ (J ⊔ Ideal.span {C π}),
      ∀ p : MvPolynomial (n ⊕ m) R,
        e (Ideal.Quotient.mk _ (Ideal.Quotient.mk J p)) =
          Ideal.Quotient.mk (J ⊔ Ideal.span {C π}) p := by
  intro J D
  let K : Ideal (MvPolynomial (n ⊕ m) R) := Ideal.span {C π}
  have hK : K.map (Ideal.Quotient.mk J) = Ideal.span {algebraMap R D π} := by
    change (Ideal.span {C π}).map (Ideal.Quotient.mk J) = _
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let e : (D ⧸ Ideal.span {algebraMap R D π}) ≃+*
      MvPolynomial (n ⊕ m) R ⧸ (J ⊔ K) :=
    (Ideal.quotEquivOfEq hK.symm).trans (DoubleQuot.quotQuotEquivQuotSup J K)
  refine ⟨e, ?_⟩
  intro p
  change DoubleQuot.quotQuotEquivQuotSup J K
      (Ideal.quotEquivOfEq hK.symm
        (Ideal.Quotient.mk _ (Ideal.Quotient.mk J p))) = Ideal.Quotient.mk (J ⊔ K) p
  rw [Ideal.quotEquivOfEq_mk]
  exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk J K p

end MvPolynomial

namespace Algebra

open MvPolynomial

/-- The actual original reduction map factors through `B/(π)`, and the
source and target quotient equivalences identify it with the canonical map
of the reduced lifting presentation. No comparison map is assumed. -/
theorem Presentation.exists_principal_lifting_reduction_comparison
    {R B n m k : Type*} [CommRing R] (π : R) [CommRing B]
    [Algebra (R ⧸ Ideal.span {π ^ 2}) B] [Fintype m]
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hf : ∀ j, map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) = P.relation j)
    (A : k → MvPolynomial n R) (H : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R) :
    let I₀ : Ideal (MvPolynomial n R) := Ideal.span (Set.range f) ⊔ Ideal.span {C π}
    let C₀ := MvPolynomial n R ⧸ I₀
    let J := principalLiftingIdeal π f A H g
    let D := MvPolynomial (n ⊕ m) R ⧸ J
    let Dbar := D ⧸ Ideal.span {algebraMap R D π}
    let D₀ := MvPolynomial (n ⊕ m) R ⧸ (J ⊔ Ideal.span {C π})
    let bπ := algebraMap (R ⧸ Ideal.span {π ^ 2}) B
      (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)
    let Bbar := B ⧸ Ideal.span {bπ}
    ∀ (γ : B →+* Dbar),
      (∀ p : MvPolynomial n R,
        γ (algebraMap P.Ring B (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) p)) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk J (rename Sum.inl p))) →
      ∃ (eC : C₀ ≃+* Bbar) (eD : Dbar ≃+* D₀) (γbar : Bbar →+* Dbar),
        (∀ p : MvPolynomial n R,
          eC (Ideal.Quotient.mk I₀ p) = Ideal.Quotient.mk (Ideal.span {bπ})
            (algebraMap P.Ring B
              (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) p))) ∧
        (∀ p : MvPolynomial (n ⊕ m) R,
          eD (Ideal.Quotient.mk _ (Ideal.Quotient.mk J p)) =
            Ideal.Quotient.mk (J ⊔ Ideal.span {C π}) p) ∧
        γbar.comp (Ideal.Quotient.mk (Ideal.span {bπ})) = γ ∧
        (eD.toRingHom.comp γbar).comp eC.toRingHom =
          (principalLiftingReductionMap π f A H g).toRingHom := by
  intro I₀ C₀ J D Dbar D₀ bπ Bbar γ hγ
  obtain ⟨eC, heC⟩ := P.exists_principal_lifting_original_quotient_equiv π f hf
  obtain ⟨eD, heD⟩ := exists_principalLifting_quotient_equiv π f A H g
  have hγπ : γ bπ = 0 := by
    have hp := hγ (C π)
    rw [map_C, P.algebraMap_apply, aeval_C, rename_C] at hp
    change γ bπ = Ideal.Quotient.mk (Ideal.span {algebraMap R D π})
      (algebraMap R D π) at hp
    rw [hp]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))
  have hker : Ideal.span {bπ} ≤ RingHom.ker γ := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact hγπ
  let γbar : Bbar →+* Dbar :=
    Ideal.Quotient.lift (Ideal.span {bπ}) γ (fun b hb => hker hb)
  have hγbar (b : B) : γbar (Ideal.Quotient.mk (Ideal.span {bπ}) b) = γ b := rfl
  refine ⟨eC, eD, γbar, heC, heD, ?_, ?_⟩
  · apply RingHom.ext
    exact hγbar
  · apply RingHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change eD (γbar (eC (Ideal.Quotient.mk I₀ p))) =
      principalLiftingReductionMap π f A H g (Ideal.Quotient.mk I₀ p)
    rw [heC, hγbar, hγ p, heD, principalLiftingReductionMap_mk]

end Algebra
