/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryGenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.SchemeTheory.Affine.StalkFractionField
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The standard root cover over the actual boundary-stalk fraction ring

The root-extension field constructed in `BoundaryGenericFiber` is the
actual pullback of the original away-cover over the fraction ring of the
scheme stalk. The comparison preserves the projection and agrees, over
`Spec A`, with the canonical morphism from the stalk.

This removes the coordinate mismatch between the prime-localization model
used in the boundary ramification calculation and the actual scheme stalk
in Stacks Project, Section 58.31. It does not yet transport ramification
conditions to every field factor of the finite-etale coordinate algebra,
so it is a prerequisite for the full codimension-one assertion of `0EYF`.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial AlgebraicGeometry CategoryTheory Limits

universe u

private theorem pullback_changeFractionCoordinates
    {D K K' L : Type u} [CommRing D] [CommRing K] [CommRing K'] [CommRing L]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of D))
    (r : D →+* K) (s : K →+* L) (c : K' ≃+* K)
    (e : Spec (CommRingCat.of L) ≅ pullback g (Spec.map (CommRingCat.ofHom r)))
    (he : e.hom ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom s)) :
    ∃ e' : Spec (CommRingCat.of L) ≅
        pullback g (Spec.map (CommRingCat.ofHom (c.symm.toRingHom.comp r))),
      e'.hom ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (s.comp c.toRingHom)) := by
  let cSpec : Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of K') :=
    Scheme.Spec.mapIso c.toCommRingCatIso.op
  have hc : Spec.map (CommRingCat.ofHom r) ≫ 𝟙 _ =
      cSpec.hom ≫ Spec.map (CommRingCat.ofHom (c.symm.toRingHom.comp r)) := by
    rw [Category.comp_id]
    change Spec.map (CommRingCat.ofHom r) =
      Spec.map (CommRingCat.ofHom c.toRingHom) ≫ _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro d
    exact (c.apply_symm_apply (r d)).symm
  let eBase := asIso (pullback.map g (Spec.map (CommRingCat.ofHom r)) g
    (Spec.map (CommRingCat.ofHom (c.symm.toRingHom.comp r)))
    (𝟙 _) cSpec.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp]) hc)
  refine ⟨e ≪≫ eBase, ?_⟩
  change (e.hom ≫ eBase.hom) ≫ _ = _
  simp only [eBase, asIso_hom, pullback.map, Category.assoc, pullback.lift_snd]
  rw [← Category.assoc, he]
  change Spec.map (CommRingCat.ofHom s) ≫
    Spec.map (CommRingCat.ofHom c.toRingHom) = _
  rw [← Spec.map_comp]
  rfl

/-- At every minimal prime of the reduced Cartier boundary, the literal
root-extension field describes the original cover over the fraction ring
of the actual scheme stalk, with both its base map and projection fixed. -/
theorem standardKummerCover_boundaryStalkGenericFiber
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    {n : ℕ} (hn : 0 < n) :
    let x : PrimeSpectrum A := ⟨P, inferInstance⟩
    let R : CommRingCat.{u} := (Spec (CommRingCat.of A)).presheaf.stalk x
    let V := Localization.AtPrime P
    let C₀ := AdjoinRoot (X ^ n - C f)
    let B := AdjoinRoot (X ^ n - C (algebraMap A V f))
    let : IsRegularLocalRing V :=
      SchemeTheory.isRegularLocalRing_localizationAtPrime_of_reduced_quotient f hf P hP
    let : IsDomain V := IsRegularLocalRing.isDomain V
    let : IsDiscreteValuationRing V :=
      SchemeTheory.isDiscreteValuationRing_localizationAtPrime_of_reduced_quotient f hf P hP
    ∃ hdomain : IsDomain B,
      let : IsDomain B := hdomain
      let : Module.FaithfullyFlat V B :=
        faithfullyFlat_adjoinRoot_X_pow_sub_C hn (algebraMap A V f)
      let : Algebra (FractionRing V) (FractionRing B) :=
        FractionRing.liftAlgebra V (FractionRing B)
      ∃ r : Localization.Away f →+* FractionRing R,
        Spec.map (CommRingCat.ofHom r) ≫
            Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
            (Spec (CommRingCat.of A)).fromSpecStalk x ∧
        ∃ e : Spec (CommRingCat.of (FractionRing B)) ≅
            pullback
              (Spec.map (CommRingCat.ofHom
                (Localization.awayMap (algebraMap A C₀) f)))
              (Spec.map (CommRingCat.ofHom r)),
          e.hom ≫ pullback.snd _ _ =
            Spec.map (CommRingCat.ofHom
              ((algebraMap (FractionRing V) (FractionRing B)).comp
                (Spec.stalkFractionRingEquiv (CommRingCat.of A) x).toRingHom)) := by
  intro x R V C₀ B hregular hdomainV hdvrV
  obtain ⟨hdomainB, hgeneric⟩ :=
    standardKummerCover_boundaryGenericFiber f hf P hP hn
  refine ⟨hdomainB, ?_⟩
  intro hdomainB' hflat hfieldAlgebra
  obtain ⟨r, hr, e, he⟩ := hgeneric
  let c : FractionRing R ≃+* FractionRing V :=
    Spec.stalkFractionRingEquiv (CommRingCat.of A) x
  let r' : Localization.Away f →+* FractionRing R := c.symm.toRingHom.comp r
  refine ⟨r', ?_, ?_⟩
  · have hmap : Spec.map (CommRingCat.ofHom r) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) =
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A V)) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (CommRingCat.hom_ext hr)
    let a : Spec (CommRingCat.of (FractionRing R)) ⟶
        Spec (CommRingCat.of (FractionRing V)) :=
      Spec.map (CommRingCat.ofHom c.symm.toRingHom)
    let b : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))
    have hcomp : Spec.map (CommRingCat.ofHom r') =
        a ≫ Spec.map (CommRingCat.ofHom r) :=
      Spec.map_comp (CommRingCat.ofHom r) (CommRingCat.ofHom c.symm.toRingHom)
    calc
      Spec.map (CommRingCat.ofHom r') ≫ b =
          (a ≫ Spec.map (CommRingCat.ofHom r)) ≫ b :=
        congrArg (fun φ : Spec (CommRingCat.of (FractionRing R)) ⟶
          Spec (CommRingCat.of (Localization.Away f)) => φ ≫ b) hcomp
      _ = a ≫ (Spec.map (CommRingCat.ofHom r) ≫ b) := Category.assoc _ _ _
      _ = a ≫ (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A V))) :=
        congrArg (fun φ : Spec (CommRingCat.of (FractionRing V)) ⟶
          Spec (CommRingCat.of A) => a ≫ φ) hmap
      _ = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
          (Spec (CommRingCat.of A)).fromSpecStalk x :=
        Spec.stalkFractionRingEquiv_over_base (CommRingCat.of A) x
  · exact pullback_changeFractionCoordinates
      (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A C₀) f)))
      r (algebraMap (FractionRing V) (FractionRing B)) c e he

end EtaleFundamentalGroups.Kummer
