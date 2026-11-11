/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.LocalGeometry.ConnectedDomainStalks
public import Nyll.SchemeTheory.LocalGeometry.SmoothRegularStalks
public import Nyll.SchemeTheory.Normalization.Normal
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDomain
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalTrace
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The actual normal integral generic open of a smooth connected family

For a smooth geometrically connected scheme over a regular affine
domain, base change to any nonempty principal open is integral and
normal. Geometric connectedness and openness give connectedness of the
actual pullback. Smoothness supplies regular local rings, which are
domains and integrally closed; connectedness and local Noetherianity
then give integrality and normality.

For a DVR and its uniformizer, this constructs the normal integral
generic scheme used when restricting a global Galois cover to dense
affine charts. Integrality and normality of that generic scheme are
conclusions, not extra inputs to the specialization argument.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- An integral scheme smooth over a regular affine base is normal. The
normality is proved on its actual stalks, without changing the scheme or
its chosen function field. -/
theorem Smooth.isNormalIntegral_of_isIntegral
    {R : Type u} [CommRing R] [IsRegularRing R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [Smooth f] : IsNormalIntegral X := by
  apply IsNormalIntegral.of_stalks
  intro x
  let : IsRegularLocalRing (X.presheaf.stalk x) :=
    Smooth.isRegularLocalRing_stalk_over_spec f x
  exact SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing _

/-- The actual principal-open base change of a smooth geometrically
connected family over a regular domain is integral. -/
theorem Smooth.isIntegral_awayBaseChange_of_geometricallyConnected
    {B : Type u} [CommRing B] [IsDomain B] [IsRegularRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    [Smooth f] [GeometricallyConnected f] (r : B) (hr : r ≠ 0) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r)))
    IsIntegral (pullback f η) := by
  intro η
  let U : Scheme.{u} := pullback f η
  change IsIntegral U
  have : IsDomain (Localization.Away r) :=
    IsLocalization.Away.isDomain (Localization.Away r) hr
  have : ConnectedSpace U := inferInstance
  have : IsLocallyNoetherian U :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f η)
  apply isIntegral_of_connected_of_isDomain_stalk
  intro x
  have : IsRegularLocalRing (U.presheaf.stalk x) :=
    Smooth.isRegularLocalRing_stalk_over_spec (pullback.fst f η ≫ f) x
  exact IsRegularLocalRing.isDomain _

/-- The same actual generic open is normal, using the integrality
supplied by geometric connectedness and the regularity of its stalks. -/
theorem Smooth.isNormalIntegral_awayBaseChange_of_geometricallyConnected
    {B : Type u} [CommRing B] [IsDomain B] [IsRegularRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B))
    [Smooth f] [GeometricallyConnected f] (r : B) (hr : r ≠ 0) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r)))
    let : IsIntegral (pullback f η) :=
      Smooth.isIntegral_awayBaseChange_of_geometricallyConnected f r hr
    IsNormalIntegral (pullback f η) := by
  intro η hIntegral
  apply IsNormalIntegral.of_stalks
  intro x
  have : IsRegularLocalRing ((pullback f η).presheaf.stalk x) :=
    Smooth.isRegularLocalRing_stalk_over_spec (pullback.fst f η ≫ f) x
  exact SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing _

end AlgebraicGeometry
