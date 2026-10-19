/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperSeparablyClosedExtension
import Nyll.EtaleFundamentalGroups.GaloisCategories.EquivalenceFunctoriality
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Fundamental groups under proper separably closed constant extension

The actual equivalence of finite étale covers extending Stacks 0A49 gives a continuous
group isomorphism whose forward map is the original projection homomorphism.
Changing the coefficient field or mapping the original proper schemes commutes
with this isomorphism, with the equalities of geometric points recorded explicitly.
The automorphism-group argument also applies to disconnected schemes and to
arbitrary field-valued points.
-/

noncomputable section

open CategoryTheory
open SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.FiniteEtale

universe u

variable (k K : Type u) [Field k] [IsSepClosed k] [Field K] [IsSepClosed K]
  [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {Ω : Type u} [Field Ω]

/-- The projection after extension of separably closed constants induces
an isomorphism on the automorphism groups of the specified fiber functors.
For a geometric point, these are the actual étale fundamental groups. -/
def fundamentalGroupEquivProperConstantExtension
    (xi : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f (coefficientMap (K := k) K)) :
    π₁ᵉᵗ(xi) ≃ₜ* π₁ᵉᵗ(xi ≫ Limits.pullback.fst f (coefficientMap (K := k) K)) := by
  let i : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    coefficientMap (K := k) K
  have hEquivalence : (pullback (Limits.pullback.fst f i)).IsEquivalence :=
    pullback_isEquivalence_of_isProper_of_isSepClosed_constant_extension k K f
  exact CategoryTheory.PreGaloisCategory.autEquivOfCompIsoOfEquivalence
    (pullback (Limits.pullback.fst f i)) (pullbackFiberIso (Limits.pullback.fst f i) xi)

/-- The comparison isomorphism evaluates by the canonical projection map. -/
theorem fundamentalGroupEquivProperConstantExtension_apply
    (xi : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f (coefficientMap (K := k) K))
    (a : π₁ᵉᵗ(xi)) :
    fundamentalGroupEquivProperConstantExtension k K f xi a =
      fundamentalGroupHom (Limits.pullback.fst f (coefficientMap (K := k) K)) xi a := by
  rfl

/-- Extending the coefficients a second time is compatible with the original
projection isomorphism; the map between coefficient pullbacks is the specified one. -/
theorem fundamentalGroupEquivProperConstantExtension_coefficient_naturality
    (L : Type u) [Field L] [IsSepClosed L] [Algebra k L] (g : K →ₐ[k] L)
    (xi : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f (coefficientMap (K := k) L))
    (a : π₁ᵉᵗ(xi)) :
    let pK : Limits.pullback f (coefficientMap (K := k) K) ⟶ X :=
      Limits.pullback.fst f (coefficientMap (K := k) K)
    let pL : Limits.pullback f (coefficientMap (K := k) L) ⟶ X :=
      Limits.pullback.fst f (coefficientMap (K := k) L)
    let q := coefficientPullbackMap f g
    let hpoint : (xi ≫ q) ≫ pK = xi ≫ pL :=
      (Category.assoc xi q pK).trans (congrArg (xi ≫ ·) (coefficientPullbackMap_fst f g))
    hpoint ▸ fundamentalGroupEquivProperConstantExtension k K f (xi ≫ q)
        (fundamentalGroupHom q xi a) =
      fundamentalGroupEquivProperConstantExtension k L f xi a := by
  intro pK pL q hpoint
  rw [fundamentalGroupEquivProperConstantExtension_apply,
    fundamentalGroupEquivProperConstantExtension_apply]
  exact fundamentalGroupHom_comp_of_eq q pK pL
    (coefficientPullbackMap_fst f g).symm xi hpoint a

/-- The proper constant-extension isomorphisms commute with a morphism of
the original proper schemes. Both paths use their actual geometric basepoints. -/
theorem fundamentalGroupEquivProperConstantExtension_scheme_naturality
    {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (CommRingCat.of k)) [IsProper fY]
    (g : X ⟶ Y) (hg : g ≫ fY = f)
    (xi : Spec (CommRingCat.of Ω) ⟶ Limits.pullback f (coefficientMap (K := k) K))
    (a : π₁ᵉᵗ(xi)) :
    let i := coefficientMap (K := k) K
    let pX : Limits.pullback f i ⟶ X := Limits.pullback.fst f i
    let pY : Limits.pullback fY i ⟶ Y := Limits.pullback.fst fY i
    let gK : Limits.pullback f i ⟶ Limits.pullback fY i :=
      Limits.pullback.lift (pX ≫ g) (Limits.pullback.snd f i)
        (by rw [Category.assoc, hg]; exact Limits.pullback.condition)
    let hleft : (xi ≫ gK) ≫ pY = xi ≫ pX ≫ g :=
      (Category.assoc xi gK pY).trans
        (congrArg (xi ≫ ·) (Limits.pullback.lift_fst _ _ _))
    let hright : (xi ≫ pX) ≫ g = xi ≫ pX ≫ g := Category.assoc xi pX g
    hleft ▸ fundamentalGroupEquivProperConstantExtension k K fY (xi ≫ gK)
        (fundamentalGroupHom gK xi a) =
      hright ▸ fundamentalGroupHom g (xi ≫ pX)
        (fundamentalGroupEquivProperConstantExtension k K f xi a) := by
  intro i pX pY gK hleft hright
  rw [fundamentalGroupEquivProperConstantExtension_apply,
    fundamentalGroupEquivProperConstantExtension_apply]
  have hm : pX ≫ g = gK ≫ pY := (Limits.pullback.lift_fst _ _ _).symm
  exact (fundamentalGroupHom_comp_of_eq gK pY (pX ≫ g) hm xi hleft a).trans
    (fundamentalGroupHom_comp_of_eq pX g (pX ≫ g) rfl xi hright a).symm

end AlgebraicGeometry.FiniteEtale
