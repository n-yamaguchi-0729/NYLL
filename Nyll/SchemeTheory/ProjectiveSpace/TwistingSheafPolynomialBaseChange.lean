/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Frames.PullbackFrame
import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerComparison
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerSectionMaps
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousRatios
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Original polynomial sections under coefficient base change

The actual projective chart map sends the ratio `p / X i ^ d` to
the same ratio with the coefficients mapped to the new ring. The
constructed twisting-sheaf comparison sends the original coordinate
section powers to their corresponding powers over the new ring.

Combining those two calculations on every coordinate chart proves
that the original pulled-back polynomial section is precisely the
polynomial section with changed coefficients. This retains the
actual pullback adjunction and the actual twisting-power isomorphism.
-/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Projective.Proofs
open ProjSpace_isPullback_map.AlgebraicGeometry.ProjSpace (awayMapX awayMapX_mk)

private def comparisonLocalSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
    (e : (Scheme.Modules.pullback f).obj L ≅ M)
    {U : Y.Opens} {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) (s : Γ(L, U)) : Γ(M, V) :=
  e.hom.app V (FramePullback.res ((Scheme.Modules.pullback f).obj L) h
    (FramePullback.eta f L U s))

private theorem comparisonLocalSection_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
    (e : (Scheme.Modules.pullback f).obj L ≅ M)
    {U : Y.Opens} {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) (r : Γ(Y, U)) (s : Γ(L, U)) :
    comparisonLocalSection f e h (r • s) =
      (f.appLE U V h).hom r • comparisonLocalSection f e h s := by
  change e.hom.app V
      (FramePullback.res ((Scheme.Modules.pullback f).obj L) h
        (FramePullback.eta f L U (r • s))) = _
  rw [FramePullback.eta_smul, FramePullback.res_smul, Scheme.Modules.Hom.app_smul]
  rfl

private theorem comparisonLocalSection_global
    {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
    (e : (Scheme.Modules.pullback f).obj L ≅ M)
    {U : Y.Opens} {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) (s : Γ(L, ⊤)) :
    comparisonLocalSection f e h (FramePullback.res L le_top s) =
      FramePullback.res M le_top (e.hom.app ⊤ (pullbackLocalSection f s)) := by
  change e.hom.app V
      (FramePullback.res ((Scheme.Modules.pullback f).obj L) h
        (FramePullback.eta f L U (FramePullback.res L le_top s))) = _
  rw [← FramePullback.res_eta, FramePullback.res_res]
  exact FramePullback.app_res e.hom le_top (pullbackLocalSection f s)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

private theorem awayToSection_map_chart_aux (i : Fin (n + 1))
    (y : MvPolynomial (Fin (n + 1)) A)
    (hy : (mvMapGraded R A n) (MvPolynomial.X i) = y) :
    Proj.awayToSection 𝒜R (MvPolynomial.X i) ≫
      (map R A n).appLE (standardOpen R n i) (Proj.basicOpen 𝒜A y)
        (by rw [← hy]; exact le_rfl) =
      CommRingCat.ofHom
        (hy ▸ (Away.map (mvMapGraded R A n) (MvPolynomial.X i) :
          Away 𝒜R (MvPolynomial.X i) →+*
            Away 𝒜A ((mvMapGraded R A n) (MvPolynomial.X i)))) ≫
        Proj.awayToSection 𝒜A y := by
  subst y
  exact Proj.awayToSection_comp_appLE (mvMapGraded R A n)
    (irrelevant_le_map_mvMapGraded R A n) (X_mem_one R n i)

/-- The original chart pullback sends a homogeneous ratio to the
ratio with its original coefficients mapped to the new base ring. -/
theorem homogeneousRatioSection_baseChange (d : ℕ) (p : 𝒜R d) (i : Fin (n + 1)) :
    (map R A n).appLE (standardOpen R n i) (standardOpen A n i)
        (map_preimage_basicOpen_X R A n i).ge (homogeneousRatioSection R n d p i) =
      homogeneousRatioSection A n d ((mvMapGraded R A n).gradedAddHom d p) i := by
  let z : Away 𝒜R (MvPolynomial.X i) :=
    Away.mk 𝒜R (X_mem_one R n i) d p.val (by
      simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using p.property)
  have hmap := awayToSection_map_chart_aux R A n i (MvPolynomial.X i)
    (mvMapGraded_X R A n i)
  have hpoint := congrArg
    (fun φ : CommRingCat.of (Away 𝒜R (MvPolynomial.X i)) ⟶
      Γ(Proj 𝒜A, standardOpen A n i) => φ.hom z) hmap
  have hz := awayMapX_mk R A n i d p.val (by
    simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using p.property)
  exact hpoint.trans (congrArg (Proj.awayToSection 𝒜A (MvPolynomial.X i)).hom hz)

/-- The actual twisting-power comparison sends the original pulled
coordinate section power to the corresponding original coordinate power. -/
theorem twistingPowerBaseChangeIso_hom_coordinatePower (d : ℕ) (i : Fin (n + 1)) :
    (twistingPowerBaseChangeIso R A n d).hom.app ⊤
        (pullbackLocalSection (map R A n)
          (tensorPowSection (twistingCoordinateSection R n i) d)) =
      tensorPowSection (twistingCoordinateSection A n i) d := by
  let e : (Scheme.Modules.pullback (map R A n)).obj (twistingSheaf R n) ≅
      twistingSheaf A n := twistingSheafBaseChangeIso R A n
  have hpb := pullbackTensorPowIso_hom_app_pullbackLocalSection (map R A n)
    (twistingSheaf R n) (twistingCoordinateSection R n i) d
  have hpow := tensorPowMapIso_hom_app_tensorPowSection e
    (pullbackLocalSection (map R A n) (twistingCoordinateSection R n i)) d
  have hbase : e.hom.app ⊤
      (pullbackLocalSection (map R A n) (twistingCoordinateSection R n i)) =
        twistingCoordinateSection A n i := twistingSheafBaseChangeIso_hom_coordinate R A n i
  exact (congrArg ((tensorPowMapIso e d).hom.app ⊤) hpb).trans
    (hpow.trans (congrArg (fun s : Γ(twistingSheaf A n, ⊤) => tensorPowSection s d) hbase))

/-- Original polynomial sections commute with actual coefficient
base change under the constructed twisting-power isomorphism. -/
theorem polynomialTwistingSection_baseChange (d : ℕ) (p : 𝒜R d) :
    (twistingPowerBaseChangeIso R A n d).hom.app ⊤
        (pullbackLocalSection (map R A n) (polynomialTwistingSection R n d p)) =
      polynomialTwistingSection A n d ((mvMapGraded R A n).gradedAddHom d p) := by
  let L : (Proj 𝒜R).Modules := (twistingSheaf R n).tensorPow d
  let M : (Proj 𝒜A).Modules := (twistingSheaf A n).tensorPow d
  let e : (Scheme.Modules.pullback (map R A n)).obj L ≅ M :=
    twistingPowerBaseChangeIso R A n d
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible M (twistingCover A n) ⊤
    (fun _ => le_top) (iSup_twistingCover A n).ge).1
  intro j
  let i : Fin (n + 1) := j.down
  let U : (Proj 𝒜R).Opens := standardOpen R n i
  let V : (Proj 𝒜A).Opens := standardOpen A n i
  have h : V ≤ map R A n ⁻¹ᵁ U := (map_preimage_basicOpen_X R A n i).ge
  let s : Γ(L, ⊤) := polynomialTwistingSection R n d p
  let t : Γ(L, ⊤) := tensorPowSection (twistingCoordinateSection R n i) d
  let t' : Γ(M, ⊤) := tensorPowSection (twistingCoordinateSection A n i) d
  have hs : FramePullback.res L (le_top : U ≤ ⊤) s =
      homogeneousRatioSection R n d p i • FramePullback.res L le_top t :=
    polynomialTwistingSection_restrict R n d p i
  have hc : (map R A n).appLE U V h (homogeneousRatioSection R n d p i) =
      homogeneousRatioSection A n d ((mvMapGraded R A n).gradedAddHom d p) i :=
    homogeneousRatioSection_baseChange R A n d p i
  have ht : comparisonLocalSection (map R A n) e h (FramePullback.res L le_top t) =
      FramePullback.res M (le_top : V ≤ ⊤) t' :=
    (comparisonLocalSection_global (map R A n) e h t).trans
      (congrArg (fun x : Γ(M, ⊤) => FramePullback.res M (le_top : V ≤ ⊤) x)
        (twistingPowerBaseChangeIso_hom_coordinatePower R A n d i))
  calc
    FramePullback.res M (le_top : V ≤ ⊤)
        (e.hom.app ⊤ (pullbackLocalSection (map R A n) s)) =
      comparisonLocalSection (map R A n) e h (FramePullback.res L le_top s) :=
        (comparisonLocalSection_global (map R A n) e h s).symm
    _ = comparisonLocalSection (map R A n) e h
        (homogeneousRatioSection R n d p i • FramePullback.res L le_top t) :=
      congrArg (comparisonLocalSection (map R A n) e h) hs
    _ = (map R A n).appLE U V h (homogeneousRatioSection R n d p i) •
        comparisonLocalSection (map R A n) e h (FramePullback.res L le_top t) :=
      comparisonLocalSection_smul (map R A n) e h _ _
    _ = homogeneousRatioSection A n d ((mvMapGraded R A n).gradedAddHom d p) i •
        FramePullback.res M (le_top : V ≤ ⊤) t' :=
      congrArg₂ (fun r : Γ(Proj 𝒜A, V) => fun x : Γ(M, V) => r • x) hc ht
    _ = FramePullback.res M (le_top : V ≤ ⊤)
        (polynomialTwistingSection A n d ((mvMapGraded R A n).gradedAddHom d p)) :=
      (polynomialTwistingSection_restrict A n d ((mvMapGraded R A n).gradedAddHom d p) i).symm

end AlgebraicGeometry.ProjSpace
