/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Topology.Sheaves.Stalks

/-!
# The actual local-ring map of a geometric specialization

For a field-valued point `t` specializing to `x`, compose the ordinary stalk
specialization with the local evaluation of `t`. The resulting map from
`𝒪_{S,x}` to the original field of `t` retains its map to `S`, and composition
of specializations is composition of these same ordinary stalk maps.

When the underlying point of `t` differs from `x`, its kernel is not the
maximal ideal of `𝒪_{S,x}`. This supplies the nonclosed-point hypothesis in
the DVR realization of a geometric specialization.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The original geometric point evaluated on the ordinary stalk at a
specialization of its underlying point. -/
def stalkSpecializationToField (x : S) (t : Spec (.of Ω) ⟶ S)
    (h : t (closedPoint Ω) ⤳ x) : S.presheaf.stalk x ⟶ CommRingCat.of Ω :=
  S.presheaf.stalkSpecializes h ≫ stalkClosedPointTo t

/-- The stalk map factors the original geometric point over the original
scheme, including its morphism and not just its underlying point. -/
theorem Spec_stalkSpecializationToField_fromSpecStalk
    (x : S) (t : Spec (.of Ω) ⟶ S) (h : t (closedPoint Ω) ⤳ x) :
    Spec.map (stalkSpecializationToField x t h) ≫ S.fromSpecStalk x = t := by
  change Spec.map (S.presheaf.stalkSpecializes h ≫ stalkClosedPointTo t) ≫
    S.fromSpecStalk x = t
  rw [Spec.map_comp, Category.assoc, SpecMap_stalkSpecializes_fromSpecStalk]
  exact Spec_stalkClosedPointTo_fromSpecStalk t

/-- Passing through an intermediate specialization gives the same actual
homomorphism on the ordinary local ring. -/
theorem stalkSpecializationToField_trans {x y : S}
    (t : Spec (.of Ω) ⟶ S) (h : t (closedPoint Ω) ⤳ x) (hxy : x ⤳ y) :
    S.presheaf.stalkSpecializes hxy ≫ stalkSpecializationToField x t h =
      stalkSpecializationToField y t (h.trans hxy) := by
  change S.presheaf.stalkSpecializes hxy ≫
    (S.presheaf.stalkSpecializes h ≫ stalkClosedPointTo t) =
      S.presheaf.stalkSpecializes (h.trans hxy) ≫ stalkClosedPointTo t
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

/-- A genuine generization gives a nonclosed geometric point of the ordinary
local ring. Thus its kernel can be used directly for the nonclosed DVR case. -/
theorem ker_stalkSpecializationToField_ne_maximalIdeal
    (x : S) (t : Spec (.of Ω) ⟶ S) (h : t (closedPoint Ω) ⤳ x)
    (hne : t (closedPoint Ω) ≠ x) :
    RingHom.ker (stalkSpecializationToField x t h).hom ≠
      maximalIdeal (S.presheaf.stalk x) := by
  intro hker
  have : IsLocalHom (stalkSpecializationToField x t h).hom := by
    apply ((local_hom_TFAE (stalkSpecializationToField x t h).hom).out 5 1).mp
    rw [maximalIdeal_eq_bot]
    exact hker
  have hpoint := congrArg (fun f : Spec (.of Ω) ⟶ S => f (closedPoint Ω))
    (Spec_stalkSpecializationToField_fromSpecStalk x t h)
  change S.fromSpecStalk x
    (PrimeSpectrum.comap (stalkSpecializationToField x t h).hom (closedPoint Ω)) =
      t (closedPoint Ω) at hpoint
  rw [comap_closedPoint, fromSpecStalk_closedPoint] at hpoint
  exact hne hpoint.symm

end AlgebraicGeometry.Scheme
