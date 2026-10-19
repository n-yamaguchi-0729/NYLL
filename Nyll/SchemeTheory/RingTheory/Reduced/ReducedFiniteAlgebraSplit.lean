/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Algebra.Pi

/-! # Concrete splitting of a reduced finite algebra over an algebraically closed field -/

noncomputable section

universe u

namespace SchemeTheory

variable (K A : Type u) [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
  [Module.Finite K A] [IsReduced A]

/-- The actual Artinian decomposition, followed by the canonical identification of
each finite residue field with the algebraically closed coefficient field. -/
def reducedFiniteAlgebraSplit : A ≃ₐ[K] (MaximalSpectrum A → K) := by
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let e : A ≃ₐ[K] (∀ M : MaximalSpectrum A, A ⧸ M.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars K
  refine e.trans (AlgEquiv.piCongrRight fun M => ?_)
  have : Module.Finite K (A ⧸ M.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K M.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  exact (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ M.asIdeal))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))).symm

/-- The number of actual residue factors is the dimension of the whole algebra. -/
def reducedFiniteAlgebraSplitFin {n : ℕ} (hn : Module.finrank K A = n) :
    A ≃ₐ[K] (Fin n → K) := by
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let : Fintype (MaximalSpectrum A) := Fintype.ofFinite (MaximalSpectrum A)
  let e := reducedFiniteAlgebraSplit K A
  have hc : Fintype.card (MaximalSpectrum A) = n :=
    (Module.finrank_fintype_fun_eq_card (R := K) (η := MaximalSpectrum A)).symm.trans
      (e.toLinearEquiv.finrank_eq.symm.trans hn)
  exact e.trans (AlgEquiv.piCongrLeft' K (fun _ : MaximalSpectrum A => K)
    (Fintype.equivFinOfCardEq hc))

end SchemeTheory
