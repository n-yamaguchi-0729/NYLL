/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.FiniteBoundaryExtensionDepth
import Nyll.EtaleFundamentalGroups.Purity.FlatBoundaryPurity
import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecOpenRecovery
import Nyll.SchemeTheory.Modules.Functoriality.RelativeSpecFlat
import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# The canonical finite extension and its pointwise etale criterion

For a finite-etale cover of an open in a locally Noetherian scheme with
depth-two boundary, take the actual relative spectrum of the original
direct-image algebra. It is finite, recovers the given open cover, has
depth two along its own boundary, and is etale exactly where its original
stalk map is flat.
-/

noncomputable section

universe u

open CategoryTheory

namespace EtaleFundamentalGroups.FiniteBoundaryExtension

open AlgebraicGeometry Scheme.Modules

variable (X : Scheme.{u}) [IsLocallyNoetherian X]
  (U : X.Opens) {V : Scheme.{u}} (π : V ⟶ U.toScheme) [IsFinite π] [Etale π]

/-- The canonical extension is the actual relative spectrum of the
original composite direct-image algebra, with its proved quasicoherence. -/
def scheme : Scheme.{u} :=
  let : (Scheme.RelativeSpec.underlyingModule
    (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
      isQuasicoherent_underlyingModule X U π
  Scheme.RelativeSpec.scheme (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))

/-- The original structural morphism of the canonical extension. -/
def toBase : scheme X U π ⟶ X :=
  let : (Scheme.RelativeSpec.underlyingModule
    (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
      isQuasicoherent_underlyingModule X U π
  Scheme.RelativeSpec.toBase (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))

/-- The given finite-etale cover is recovered over the original open. -/
def openIso : (toBase X U π ⁻¹ᵁ U).toScheme ≅ V :=
  let : (Scheme.RelativeSpec.underlyingModule
    (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
      isQuasicoherent_underlyingModule X U π
  Scheme.DirectImageAlgebra.relativeSpecRestrictIso U π

@[reassoc]
theorem openIso_hom_toBase : (openIso X U π).hom ≫ π = toBase X U π ∣_ U :=
  let : (Scheme.RelativeSpec.underlyingModule
    (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
      isQuasicoherent_underlyingModule X U π
  Scheme.DirectImageAlgebra.relativeSpecRestrictIso_hom_toBase U π

variable (hdepth : ∀ x : X, x ∉ U →
  (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))

include hdepth

/-- The canonical extension is finite over the original base. -/
theorem isFinite_toBase : IsFinite (toBase X U π) :=
  isFinite_relativeSpec_toBase X U π hdepth

/-- The actual local rings of the canonical extension have depth two
outside the recovered cover. -/
theorem two_le_depth_boundary (y : scheme X U π) (hy : toBase X U π y ∉ U) :
    (2 : ℕ∞) ≤ Module.depth ((scheme X U π).presheaf.stalk y)
      ((scheme X U π).presheaf.stalk y) :=
  two_le_depth_relativeSpec_boundary X U π hdepth y hy

/-- Pointwise etaleness of the canonical extension is equivalent to
flatness of its original stalk map at that point. -/
theorem exists_etale_open_iff_flat_stalkMap (y : scheme X U π) :
    (∃ W : (scheme X U π).Opens, y ∈ W ∧ Etale (W.ι ≫ toBase X U π)) ↔
      ((toBase X U π).stalkMap y).hom.Flat := by
  let f := toBase X U π
  have : IsFinite f := isFinite_toBase X U π hdepth
  have : IsLocallyNoetherian (scheme X U π) := LocallyOfFiniteType.isLocallyNoetherian f
  have : Etale (f ∣_ U) := by
    rw [← openIso_hom_toBase X U π]
    infer_instance
  have : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact exists_etale_open_iff_flat_stalkMap_of_boundary_two_le_depth f (f ⁻¹ᵁ U)
    (two_le_depth_boundary X U π hdepth) y

/-- The whole canonical extension is etale if and only if it is flat. -/
theorem etale_iff_flat : Etale (toBase X U π) ↔ Flat (toBase X U π) := by
  constructor
  · intro h
    exact inferInstance
  · intro h
    let f := toBase X U π
    have : IsFinite f := isFinite_toBase X U π hdepth
    have : IsLocallyNoetherian (scheme X U π) := LocallyOfFiniteType.isLocallyNoetherian f
    have : Etale (f ∣_ U) := by
      rw [← openIso_hom_toBase X U π]
      infer_instance
    have : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [← morphismRestrict_ι]
      infer_instance
    exact etale_of_flat_of_boundary_two_le_depth f (f ⁻¹ᵁ U)
      (two_le_depth_boundary X U π hdepth)

/-- The canonical extension is etale precisely when its original
reflexive direct-image algebra has finite local bases everywhere. The
rank is allowed to vary on the base. -/
theorem etale_iff_finiteFreeLocus_eq_top : Etale (toBase X U π) ↔
    finiteFreeLocus (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))) = ⊤ := by
  have : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsQuasicoherent :=
    isQuasicoherent_underlyingModule X U π
  have : (Scheme.RelativeSpec.underlyingModule
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι))).IsFiniteType :=
    isFiniteType_underlyingModule X U π hdepth
  exact (etale_iff_flat X U π hdepth).trans
    (Scheme.RelativeSpec.flat_toBase_iff_finiteFreeLocus_eq_top
      (Scheme.DirectImageAlgebra.structureMap (π ≫ U.ι)))

end EtaleFundamentalGroups.FiniteBoundaryExtension
