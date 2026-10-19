/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryStalkGenericFiber
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.BoundaryTameCover
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.SchemeTheory.Affine.StalkFractionField
import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.TameDVREquiv
import Nyll.SchemeTheory.RingTheory.Reduced.ReducedCartierDivisor
import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Tameness over the actual boundary stalk of a standard root cover

At each generic point of the reduced Cartier boundary, the actual scheme
stalk is a DVR. The original cover's generic pullback is a finite separable
field extension of its fraction field, of the original degree, and is
tamely ramified over that same stalk.

The integral closure, residue fields and ramification indices are compared
by `TameDVREquiv`; the projection is the actual scheme comparison from
`BoundaryStalkGenericFiber`. Its field algebra supplies the stalk algebra,
so these conclusions refer to the same original generic morphism.
This is the boundary-stalk calculation for Stacks Project, Example 58.31.4
(tag `0EYF`), not yet the global arbitrary-scheme codimension-one predicate.
https://stacks.math.columbia.edu/tag/0EYF
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial AlgebraicGeometry CategoryTheory Limits

universe u

/-- The generic fibre of the original standard root cover is a degree-`n`
finite separable extension, tame over the actual scheme stalk at each
minimal prime of the reduced Cartier boundary. The displayed projection
and both algebra structures come from the same coefficient map. -/
theorem standardKummerCover_tameBoundaryStalkGenericFiber
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span ({f} : Set A))]
    (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span ({f} : Set A)).minimalPrimes)
    {n : ℕ} (hn : 0 < n) (hnUnit : IsUnit (n : A)) :
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
      let eStalk : R ≃+* V := (Spec.stalkIso (CommRingCat.of A) x).commRingCatIsoToRingEquiv
      let : IsDomain R := eStalk.toMulEquiv.isDomain V
      let : IsDiscreteValuationRing R :=
        IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eStalk.symm
      let c : FractionRing R ≃+* FractionRing V :=
        Spec.stalkFractionRingEquiv (CommRingCat.of A) x
      let : Algebra (FractionRing R) (FractionRing B) :=
        ((algebraMap (FractionRing V) (FractionRing B)).comp c.toRingHom).toAlgebra
      let : Algebra R (FractionRing B) :=
        Algebra.compHom (FractionRing B) (algebraMap R (FractionRing R))
      Module.Finite (FractionRing R) (FractionRing B) ∧
        Algebra.IsSeparable (FractionRing R) (FractionRing B) ∧
        Module.finrank (FractionRing R) (FractionRing B) = n ∧
        SchemeTheory.IsTamelyRamifiedOverDVR R (FractionRing B) ∧
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
                (algebraMap (FractionRing R) (FractionRing B))) := by
  intro x R V C₀ B hregular hdomainV hdvrV
  obtain ⟨hdomainB, hdata⟩ :=
    standardKummerCover_tameBoundaryGenericFiber f hf P hP hn hnUnit
  refine ⟨hdomainB, ?_⟩
  intro hdomainB' hflat hfieldAlgebra eStalk hdomainR hdvrR c hstalkFieldAlgebra hstalkAlgebra
  let L := FractionRing B
  have : IsScalarTower V (FractionRing V) L := FractionRing.isScalarTower_liftAlgebra V L
  obtain ⟨_hfinite, hseparable, hdegree, htame, _hgeneric⟩ := hdata
  have hfield : (algebraMap (FractionRing V) L).comp c.toRingHom =
      (RingEquiv.refl L).toRingHom.comp (algebraMap (FractionRing R) L) := rfl
  have hdegree' : Module.finrank (FractionRing R) L = n :=
    (Algebra.finrank_eq_of_equiv_equiv c (RingEquiv.refl L) hfield).trans hdegree
  have hfinite' : Module.Finite (FractionRing R) L :=
    Module.finite_of_finrank_pos (by rw [hdegree']; exact hn)
  have hseparable' : Algebra.IsSeparable (FractionRing R) L :=
    (Algebra.IsSeparable.iff_of_equiv_equiv c (RingEquiv.refl L) hfield).mpr hseparable
  have hcoeff : (RingEquiv.refl L).toRingHom.comp (algebraMap V L) =
      (algebraMap R L).comp eStalk.symm.toRingHom := by
    apply RingHom.ext
    intro v
    change algebraMap V L v =
      algebraMap (FractionRing V) L (c (algebraMap R (FractionRing R) (eStalk.symm v)))
    calc
      algebraMap V L v =
          algebraMap (FractionRing V) L (algebraMap V (FractionRing V) v) :=
        IsScalarTower.algebraMap_apply V (FractionRing V) L v
      _ = algebraMap (FractionRing V) L
          (algebraMap V (FractionRing V) (eStalk (eStalk.symm v))) :=
        congrArg (fun z : V => algebraMap (FractionRing V) L
          (algebraMap V (FractionRing V) z)) (eStalk.apply_symm_apply v).symm
      _ = algebraMap (FractionRing V) L
          (c (algebraMap R (FractionRing R) (eStalk.symm v))) :=
        congrArg (algebraMap (FractionRing V) L)
          (IsFractionRing.ringEquivOfRingEquiv_algebraMap eStalk (eStalk.symm v)).symm
  refine ⟨hfinite', hseparable', hdegree',
    SchemeTheory.isTamelyRamifiedOverDVR_of_compatible_ringEquiv
      eStalk.symm (RingEquiv.refl L) hcoeff htame, ?_⟩
  obtain ⟨_hdomainB, hgeneric⟩ := standardKummerCover_boundaryStalkGenericFiber f hf P hP hn
  exact hgeneric

end EtaleFundamentalGroups.Kummer
