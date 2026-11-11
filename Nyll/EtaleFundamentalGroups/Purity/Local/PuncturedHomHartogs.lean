/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.Local.DepthTwoSections
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPushforward
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Topology.NoetherianSpace

/-!
# Actual Hom extension across a depth-two local puncture

Scalar Hartogs on an affine scheme identifies the structure module with
its actual open direct image. The restriction adjunction then extends
every morphism into the structure module uniquely. For a Noetherian local
ring of depth at least two, the scalar comparison is supplied by the
proved regular-pair Hartogs theorem, rather than assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- An invertible original restriction unit gives unique extension of
all morphisms into its target. -/
theorem hom_restrict_bijective_of_unit_isIso
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M N : Y.Modules) [IsIso ((restrictAdjunction j).unit.app N)] :
    Function.Bijective (fun f : M ⟶ N => (restrictFunctor j).map f) := by
  let adj := restrictAdjunction j
  let η : N ⟶ (pushforward j).obj (N.restrict j) := adj.unit.app N
  have htrans (f : M ⟶ N) :
      adj.homEquiv M (N.restrict j) ((restrictFunctor j).map f) = f ≫ η := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality f).symm
  constructor
  · intro f g hfg
    change (restrictFunctor j).map f = (restrictFunctor j).map g at hfg
    apply (cancel_mono η).mp
    rw [← htrans f, ← htrans g, hfg]
  · intro g
    refine ⟨adj.homEquiv M (N.restrict j) g ≫ inv η, ?_⟩
    apply (adj.homEquiv M (N.restrict j)).injective
    rw [htrans, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Scalar Hartogs identifies the structure module with its actual open
direct image through the original restriction-adjunction unit. -/
theorem isIso_structure_unit_of_scalar_hartogs
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hscalar : Function.Bijective
      ((Spec R).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op)) :
    IsIso ((restrictAdjunction U.ι).unit.app
      (SheafOfModules.unit (Spec R).ringCatSheaf)) := by
  let O : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  have : IsIso O.fromTildeΓ :=
    inferInstanceAs (IsIso (fromTildeΓ
      (SheafOfModules.unit (Spec R).ringCatSheaf)))
  have : O.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ O).mpr inferInstance
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : QuasiCompact U.ι := inferInstance
  have : (O.restrict U.ι).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor U.ι O
  let P : (Spec R).Modules := (pushforward U.ι).obj (O.restrict U.ι)
  have : P.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_openImmersion U.ι (O.restrict U.ι)
  have : IsIso P.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent P
  let η : O ⟶ P := (restrictAdjunction U.ι).unit.app O
  have hscalar' (W : (Spec R).Opens) (hWU : W = U) :
      Function.Bijective
        ((Spec R).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op) := by
    subst W
    exact hscalar
  have hηtop : Function.Bijective (η.app ⊤) := by
    change Function.Bijective
      ((Spec R).presheaf.map (homOfLE (U.ι.image_preimage_le ⊤)).op)
    exact hscalar' (U.ι ''ᵁ (U.ι ⁻¹ᵁ ⊤))
      (by rw [Scheme.Hom.preimage_top, U.ι_image_top])
  have hΓ : IsIso ((moduleSpecΓFunctor (R := R)).map η) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hηtop
  have : IsIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map η)) :=
    inferInstance
  have hnat :
      (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map η) ≫ P.fromTildeΓ =
        O.fromTildeΓ ≫ η := fromTildeΓNatTrans.naturality η
  have hleft : IsIso
      ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map η) ≫ P.fromTildeΓ) :=
    IsIso.comp_isIso'
      (inferInstance : IsIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map η)))
      (inferInstance : IsIso P.fromTildeΓ)
  have hcomp : IsIso (O.fromTildeΓ ≫ η) := hnat ▸ hleft
  have : IsIso η := IsIso.of_isIso_comp_left O.fromTildeΓ η
  exact inferInstanceAs (IsIso η)

/-- On an affine Noetherian base, scalar Hartogs gives unique extension
of every actual sheaf morphism into the structure module. The proof
constructs the native open-direct-image comparison via affine QC descent. -/
theorem hom_restrict_to_structure_bijective_of_scalar_hartogs
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hscalar : Function.Bijective
      ((Spec R).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op))
    (M : (Spec R).Modules) :
    Function.Bijective (fun f : M ⟶ SheafOfModules.unit (Spec R).ringCatSheaf =>
      (restrictFunctor U.ι).map f) := by
  have : IsIso ((restrictAdjunction U.ι).unit.app
      (SheafOfModules.unit (Spec R).ringCatSheaf)) :=
    isIso_structure_unit_of_scalar_hartogs R U hscalar
  exact hom_restrict_bijective_of_unit_isIso U.ι M
    (SheafOfModules.unit (Spec R).ringCatSheaf)

/-- Every actual sheaf morphism into the structure module on a punctured
local spectrum extends uniquely when the base has depth at least two.
No integrality, normality, or additional extension premise is required. -/
theorem hom_restrict_to_structure_bijective_punctured_of_two_le_depth
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdepth : (2 : ℕ∞) ≤ Module.depth R R)
    (M : (Spec (CommRingCat.of R)).Modules) :
    Function.Bijective
      (fun f : M ⟶ SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf =>
        (restrictFunctor (Scheme.puncturedSpectrumOpen R).ι).map f) := by
  apply hom_restrict_to_structure_bijective_of_scalar_hartogs
    (CommRingCat.of R) (Scheme.puncturedSpectrumOpen R) ?_ M
  exact EtaleFundamentalGroups.restrict_punctured_finiteFlat_bijective_of_two_le_depth
    R hdepth (𝟙 (Spec (CommRingCat.of R)))

end AlgebraicGeometry.Scheme.Modules
