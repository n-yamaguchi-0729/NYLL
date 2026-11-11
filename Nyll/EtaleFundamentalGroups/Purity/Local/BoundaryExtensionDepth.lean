/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.AffineReflexiveExtension
public import Nyll.SchemeTheory.RingTheory.RegularLocal.DualRegularPair
public import Mathlib.RingTheory.Regular.Flat
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# Boundary depth of the actual extension algebra

A regular pair in the boundary ideal stays regular on the dual presentation
of the actual direct image. Its images are regular in every local ring of
the extension over the boundary. This proves depth two for the original
section algebra, without normality or flatness of the extension.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite RingTheory IsLocalRing

namespace EtaleFundamentalGroups

open AlgebraicGeometry Scheme.Modules

/-- Every regular pair on the affine base remains regular on the actual
sections of the extended finite locally free module. -/
theorem isWeaklyRegular_directImage_sections_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R] (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (V : U.toScheme.Modules) (hfree : finiteFreeLocus V = ⊤)
    {x y : R} (hxy : Sequence.IsWeaklyRegular R [x, y]) :
    Sequence.IsWeaklyRegular
      ((moduleSpecΓFunctor (R := R)).obj ((pushforward U.ι).obj V)) [x, y] := by
  obtain ⟨F, hFqc, _, _, ⟨e⟩⟩ :=
    exists_dualIso_pushforward_of_boundary_two_le_depth R U hdepth V hfree
  let eO : R ≃ₗ[R] (moduleSpecΓFunctor (R := R)).obj (𝟙_ (Spec R).Modules) :=
    (tilde.isoTop (ModuleCat.of R R)).toLinearEquiv
  have hO : Sequence.IsWeaklyRegular
      ((moduleSpecΓFunctor (R := R)).obj (𝟙_ (Spec R).Modules)) [x, y] :=
    (eO.isWeaklyRegular_congr [x, y]).mp hxy
  have hHom := SchemeTheory.isWeaklyRegular_pair_linearMap
    (M := (moduleSpecΓFunctor (R := R)).obj F) hO
  have hDual : Sequence.IsWeaklyRegular
      ((moduleSpecΓFunctor (R := R)).obj (dual F)) [x, y] :=
    ((ihomSpecSectionsLinearEquiv F (𝟙_ (Spec R).Modules)).isWeaklyRegular_congr
      [x, y]).mpr hHom
  exact (((moduleSpecΓFunctor (R := R)).mapIso e).toLinearEquiv.isWeaklyRegular_congr
    [x, y]).mp hDual

namespace AffineReflexiveExtension

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (U : (Spec R).Opens)
  {V : Scheme.{u}} (π : V ⟶ U.toScheme) [IsFinite π] [Etale π]

/-- The actual global-section algebra has boundary depth at least two
at every prime lying over a boundary point. -/
theorem two_le_depth_sectionAlgebra_atPrime
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (q : PrimeSpectrum ((Scheme.DirectImageAlgebra.sheaf (π ≫ U.ι)).obj.obj (op ⊤)))
    (hq : PrimeSpectrum.comap
      (((Scheme.ΓSpecIso R).inv ≫ (π ≫ U.ι).appTop).hom) q ∉ U) :
    (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal) := by
  let A : CommRingCat.{u} := (Scheme.DirectImageAlgebra.sheaf (π ≫ U.ι)).obj.obj (op ⊤)
  let c : R ⟶ A := (Scheme.ΓSpecIso R).inv ≫ (π ≫ U.ι).appTop
  let : Algebra R A := c.hom.toAlgebra
  let M := Scheme.RelativeSpec.underlyingModule
    (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))
  let eA : A ≃ₗ[R] (moduleSpecΓFunctor (R := R)).obj M :=
    { Equiv.refl A with
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change c r * m = r • (show Γ(M, ⊤) from m)
        rw [smul_Spec_def]
        rfl }
  obtain ⟨x, hxI, y, hyI, hx, _, hxy⟩ :=
    exists_regular_pair_in_boundary_ideal_of_two_le_depth R U hdepth
  have hpair : Sequence.IsWeaklyRegular R [x, y] :=
    .cons hx (.cons hxy (.nil R _))
  have hP := isWeaklyRegular_directImage_sections_of_boundary_two_le_depth
    R U hdepth ((pushforward π).obj (𝟙_ V.Modules))
    (finiteFreeLocus_pushforward_unit_eq_top π) hpair
  have hM : Sequence.IsWeaklyRegular ((moduleSpecΓFunctor (R := R)).obj M) [x, y] :=
    (LinearEquiv.isWeaklyRegular_congr
      ((moduleSpecΓFunctor (R := R)).mapIso (underlyingModuleIso R U π)).toLinearEquiv
      [x, y]).mpr hP
  have hA : Sequence.IsWeaklyRegular A ([x, y].map (algebraMap R A)) :=
    (Sequence.isWeaklyRegular_map_algebraMap_iff A A [x, y]).mpr
      ((eA.isWeaklyRegular_congr [x, y]).mpr hM)
  have hQ := hA.of_isLocalization (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  have hmem : ∀ r ∈ ([x, y].map (algebraMap R A)), r ∈ q.asIdeal := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    have hsI : s ∈ PrimeSpectrum.vanishingIdeal (U : Set (Spec R))ᶜ := by
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hxI
      · exact (List.mem_singleton.mp hs) ▸ hyI
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hsI
      (PrimeSpectrum.comap c.hom q) hq
  have hm : ∀ r ∈ (([x, y].map (algebraMap R A)).map
      (algebraMap A (Localization.AtPrime q.asIdeal))),
      r ∈ maximalIdeal (Localization.AtPrime q.asIdeal) := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime q.asIdeal) q.asIdeal s).mpr (hmem s hs)
  exact le_sSup ⟨_, hQ, hm, by simp only [List.length_map, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.cast_ofNat]⟩

end AffineReflexiveExtension
end EtaleFundamentalGroups
