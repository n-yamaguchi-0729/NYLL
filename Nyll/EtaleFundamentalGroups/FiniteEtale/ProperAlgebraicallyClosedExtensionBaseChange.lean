/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality
import Mathlib.Algebra.Algebra.Hom
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Coefficient maps and rational fibres in the proper comparison

The rational fibre is obtained by an actual section of the coefficient
base-change projection. Its two coordinates and the composition law for
coefficient changes are used in the closed-fibre comparison for Stacks 0A49.
-/

noncomputable section

open CategoryTheory
open SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {k A B C : Type u} [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- Coefficient pullback maps compose in the order determined by the
original algebra homomorphisms. -/
theorem coefficientPullbackMap_comp (g : A →ₐ[k] B) (h : B →ₐ[k] C) :
    coefficientPullbackMap f h ≫ coefficientPullbackMap f g =
      coefficientPullbackMap f (h.comp g) := by
  have hSpec :
      Spec.map (CommRingCat.ofHom h.toRingHom) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom) =
          Spec.map (CommRingCat.ofHom (h.comp g).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, coefficientPullbackMap_fst]
  · simp only [Category.assoc, coefficientPullbackMap_snd,
      coefficientPullbackMap_snd_assoc, hSpec]

/-- The actual map from the original scheme to its coefficient base change
defined by a rational point of the coefficient algebra. -/
def coefficientRationalPointMap (t : A →ₐ[k] k) :
    X ⟶ Limits.pullback f (coefficientMap (K := k) A) := by
  have ht : Spec.map (CommRingCat.ofHom t.toRingHom) ≫
      coefficientMap (K := k) A = 𝟙 (Spec (CommRingCat.of k)) := by
    calc
      Spec.map (CommRingCat.ofHom t.toRingHom) ≫ coefficientMap (K := k) A =
          coefficientMap (K := k) k := coefficientMap_naturality t
      _ = 𝟙 (Spec (CommRingCat.of k)) := Spec.map_id (CommRingCat.of k)
  refine Limits.pullback.lift (𝟙 X)
    (f ≫ Spec.map (CommRingCat.ofHom t.toRingHom)) ?_
  rw [Category.id_comp, Category.assoc, ht, Category.comp_id]

/-- The rational coefficient map is a section over the original scheme. -/
theorem coefficientRationalPointMap_fst (t : A →ₐ[k] k) :
    coefficientRationalPointMap f t ≫
      Limits.pullback.fst f (coefficientMap (K := k) A) = 𝟙 X :=
  Limits.pullback.lift_fst _ _ _

/-- The coefficient coordinate of the rational-fibre map is the original
rational point, composed with the structure morphism. -/
theorem coefficientRationalPointMap_snd (t : A →ₐ[k] k) :
    coefficientRationalPointMap f t ≫
      Limits.pullback.snd f (coefficientMap (K := k) A) =
        f ≫ Spec.map (CommRingCat.ofHom t.toRingHom) :=
  Limits.pullback.lift_snd _ _ _

end AlgebraicGeometry.FiniteEtale
