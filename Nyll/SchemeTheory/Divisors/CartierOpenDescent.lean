/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Descent of effective Cartier ideals through open immersions

An affine neighbourhood in the source has an actual affine open image, with
isomorphic section rings. Thus a principal regular generator transports to
that image. This supplies the local descent used by the Rees-chart cover.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- A regular principal generator on an open source neighbourhood gives
one on its actual affine open image. -/
theorem isEffectiveCartierAt_of_comap_openImmersion
    (I : X.IdealSheafData) (j : Y ⟶ X) [IsOpenImmersion j] (y : Y)
    (h : (I.comap j).IsEffectiveCartierAt y) : I.IsEffectiveCartierAt (j y) := by
  obtain ⟨V, hy, a, ha, hI⟩ := h
  let U : X.affineOpens := ⟨j ''ᵁ V.1, V.2.image_of_isOpenImmersion j⟩
  let e : Γ(X, U.1) ≅ Γ(Y, V.1) := j.appIso V.1
  let b : Γ(X, U.1) := e.inv.hom a
  have he : Function.Injective e.hom.hom :=
    (ConcreteCategory.bijective_of_isIso e.hom).injective
  have hb : e.hom.hom b = a := by
    change (e.inv ≫ e.hom).hom a = a
    rw [e.inv_hom_id]
    rfl
  refine ⟨U, ⟨y, hy, rfl⟩, b, ?_, ?_⟩
  · apply (Commute.isRegular_iff (Commute.all b)).mpr
    intro s t hst
    apply he
    apply ha.left
    have heq := congrArg e.hom.hom hst
    simpa only [map_mul, hb] using heq
  · have hm : (I.ideal U).map e.hom.hom = Ideal.span {a} := by
      rw [Scheme.Hom.appIso_hom']
      rw [← ideal_comap_of_affineOpens I j U V (j.preimage_image_eq V.1).ge]
      exact hI
    have hi : e.inv.hom.comp e.hom.hom = RingHom.id Γ(X, U.1) := by
      change (e.hom ≫ e.inv).hom = _
      rw [e.hom_inv_id]
      rfl
    have hm' := congrArg (fun J : Ideal Γ(Y, V.1) => J.map e.inv.hom) hm
    rw [Ideal.map_map, hi, Ideal.map_id, Ideal.map_span, Set.image_singleton] at hm'
    exact hm'

end AlgebraicGeometry.Scheme.IdealSheafData
