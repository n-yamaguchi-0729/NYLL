/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Taking integral closure inside an intermediate integral closure

For a tower `R → S → A`, every element of `A` integral over `R` already
belongs to the integral closure of `S` in `A`. Consequently taking the
`R`-integral closure in that intermediate ring gives the same ring as
taking it directly in `A`.

There is no integrality assumption on `S / R`, and the ambient algebra
may have several components. This is used to replace the actual finite
étale algebra on an away open by its full generic algebra when forming
the relative normalization over the original base.
-/

noncomputable section

namespace SchemeTheory

universe uR uS uA

variable (R : Type uR) (S : Type uS) (A : Type uA)
  [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- Computing the original integral closure inside the closure over a
larger coefficient ring keeps exactly the same ambient elements. -/
def integralClosureInIntegralClosureAlgEquiv :
    integralClosure R (integralClosure S A) ≃ₐ[R] integralClosure R A := by
  let E := integralClosure S A
  let i : E →ₐ[R] A := IsScalarTower.toAlgHom R E A
  apply AlgEquiv.ofBijective i.mapIntegralClosure
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : integralClosure R A ↦ (z : A)) hxy
  · intro z
    let w : E := ⟨z.val, z.property.tower_top⟩
    have hw : IsIntegral R w :=
      (isIntegral_algebraMap_iff (R := R) (A := E) (B := A)).mp z.property
    exact ⟨⟨w, hw⟩, Subtype.ext rfl⟩

/-- The nested-closure comparison is induced by the original inclusion
in the ambient algebra. -/
theorem integralClosureInIntegralClosureAlgEquiv_val
    (x : integralClosure R (integralClosure S A)) :
    (integralClosureInIntegralClosureAlgEquiv R S A x : A) =
      ((x : integralClosure S A) : A) := rfl

end SchemeTheory
