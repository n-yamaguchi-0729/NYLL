/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareFrameQuotient
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # A full modulus of degree zero is empty -/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)}

/-- Finite flat rank zero forces the actual whole divisor subscheme to be empty. -/
theorem isEmpty_modulus_of_degree_zero
    (D : RelEffCartierDiv c 0 (𝟙 (Spec (CommRingCat.of K)))) : IsEmpty D.I.subscheme := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  have hA : Subsingleton (modulusAlgebra D) :=
    (Module.finrank_zero_iff (R := K) (M := modulusAlgebra D)).mp (finrank_modulusAlgebra D)
  have : Subsingleton Γ(D.I.subscheme, ⊤) := hA
  have : IsAffine D.I.subscheme := isAffine_of_isAffineHom (modulusBaseMap D)
  have : IsEmpty (Spec Γ(D.I.subscheme, ⊤)) :=
    inferInstanceAs (IsEmpty (PrimeSpectrum Γ(D.I.subscheme, ⊤)))
  exact Function.isEmpty (fun x : D.I.subscheme => (Scheme.isoSpec D.I.subscheme).hom x)

end AlgebraicGeometry.GeneralizedJacobian
