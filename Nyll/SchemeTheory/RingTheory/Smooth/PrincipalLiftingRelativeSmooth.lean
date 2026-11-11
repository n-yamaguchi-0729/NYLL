/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalLiftingReductionComparison
public import Nyll.SchemeTheory.RingTheory.Smooth.AtPrimeEquiv

/-!
# Relative smoothness for the original principal-lifting reduction map

The actual source and target quotient equivalences identify the original
reduction map with the canonical reduced presentation map. Its proved
polynomial charts therefore give smoothness over the original algebra
modulo the parameter, for the original reduction map itself.
-/

@[expose] public section

noncomputable section

namespace Algebra

open MvPolynomial

/-- A strictly-standard parameter gives relative smoothness of the original
map `B/(π) → D/(π)`. The source and target identifications are constructed
from the original presentation and the actual polynomial triangle. -/
theorem Presentation.isSmoothAt_principal_lifting_reduction_of_strictStandard
    {R B n m k κ : Type*} [CommRing R] [CommRing B]
    [Finite n] [Fintype m] [DecidableEq m] [Fintype κ] [DecidableEq κ]
    (π : R) [Algebra (R ⧸ Ideal.span {π ^ 2}) B]
    (P : Presentation (R ⧸ Ideal.span {π ^ 2}) B n m)
    (f : m → MvPolynomial n R)
    (hf : ∀ j, map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (f j) = P.relation j)
    (A : k → MvPolynomial n R) (H : k → m → m → MvPolynomial n R)
    (g : k → m → MvPolynomial n R)
    (hrel : ∀ s j, A s * f j = ∑ l, H s j l * f l + C (π ^ 2) * g s j)
    (t : k) (a : κ → m) (ha : Function.Injective a)
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hminor : map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) (A t) ∈
      P.ker ⊔ Ideal.span (Set.range fun b : κ → n =>
        ((Matrix.of fun i j => pderiv j (P.relation (a i))).submatrix _root_.id b).det)) :
    let J := principalLiftingIdeal π f A H g
    let D := MvPolynomial (n ⊕ m) R ⧸ J
    let Dbar := D ⧸ Ideal.span {algebraMap R D π}
    let bπ := algebraMap (R ⧸ Ideal.span {π ^ 2}) B
      (Ideal.Quotient.mk (Ideal.span {π ^ 2}) π)
    let Bbar := B ⧸ Ideal.span {bπ}
    ∀ (γ : B →+* Dbar),
      (∀ p : MvPolynomial n R,
        γ (algebraMap P.Ring B (map (Ideal.Quotient.mk (Ideal.span {π ^ 2})) p)) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk J (rename Sum.inl p))) →
      ∀ (γbar : Bbar →+* Dbar),
        γbar.comp (Ideal.Quotient.mk (Ideal.span {bπ})) = γ →
        let _ : Algebra Bbar Dbar := RingHom.toAlgebra (R := Bbar) (S := Dbar) γbar
        ∀ p : PrimeSpectrum Dbar,
          Ideal.Quotient.mk _ (Ideal.Quotient.mk J (rename Sum.inl (A t))) ∉ p.asIdeal →
          IsSmoothAt Bbar (A := Dbar) p.asIdeal := by
  intro J D Dbar bπ Bbar γ hγ γbar hγbar hBD p hp
  let I₀ : Ideal (MvPolynomial n R) := Ideal.span (Set.range f) ⊔ Ideal.span {C π}
  let C₀ := MvPolynomial n R ⧸ I₀
  let J₀ : Ideal (MvPolynomial (n ⊕ m) R) := J ⊔ Ideal.span {C π}
  let D₀ := MvPolynomial (n ⊕ m) R ⧸ J₀
  let ρ₀ : C₀ →ₐ[R] D₀ := principalLiftingReductionMap π f A H g
  obtain ⟨eC, eD, γbar', _heC, heD, hγbar', hcomm₀⟩ :=
    P.exists_principal_lifting_reduction_comparison π f hf A H g γ hγ
  have hbar : γbar = γbar' := by
    apply RingHom.ext
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact (RingHom.congr_fun hγbar b).trans (RingHom.congr_fun hγbar' b).symm
  have hcomm : (eD.toRingHom.comp γbar).comp eC.toRingHom = ρ₀.toRingHom := by
    rw [hbar]
    exact hcomm₀
  have hcomm' : eD.symm.toRingHom.comp ρ₀.toRingHom =
      γbar.comp eC.toRingHom := by
    apply RingHom.ext
    intro x
    apply eD.injective
    change eD (eD.symm (ρ₀ x)) = eD (γbar (eC x))
    rw [eD.apply_symm_apply]
    exact (RingHom.congr_fun hcomm x).symm
  let _ : Algebra C₀ D₀ := ρ₀.toRingHom.toAlgebra
  let q : PrimeSpectrum D₀ := PrimeSpectrum.comap eD.symm.toRingHom p
  have hq : Ideal.Quotient.mk J₀ (rename Sum.inl (A t)) ∉ q.asIdeal := by
    intro hmem
    apply hp
    change eD.symm (Ideal.Quotient.mk J₀ (rename Sum.inl (A t))) ∈ p.asIdeal at hmem
    rw [← heD (rename Sum.inl (A t)), eD.symm_apply_apply] at hmem
    exact hmem
  have hsm : IsSmoothAt C₀ q.asIdeal :=
    (principalLifting_reduced_smooth_over_original π P f (fun j => (hf j).symm)
      A H g hrel t a ha hdiag hsupport hminor).2.2 q.asIdeal inferInstance hq
  have : IsSmoothAt C₀ q.asIdeal := hsm
  exact Algebra.IsSmoothAt.of_ringEquiv
    (R := C₀) (Q := Bbar) (S := D₀) (T := Dbar) eC eD.symm hcomm' p

end Algebra
