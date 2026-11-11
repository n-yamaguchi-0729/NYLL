/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CanonicalFiniteExtension
import Nyll.EtaleFundamentalGroups.Purity.BoundaryExtensionHom

/-!
# Uniqueness of the canonical finite extension with its specified open cover

Every finite extension whose own boundary has depth at least two is
uniquely isomorphic to the constructed canonical extension, over the
original base and compatibly with the supplied identification of its
open restriction with the original finite-etale cover.
-/

noncomputable section

universe u

open CategoryTheory

namespace EtaleFundamentalGroups.FiniteBoundaryExtension

open AlgebraicGeometry

/-- The canonical finite extension is unique together with its specified
identification of the open part. The compatibility equation uses the
actual open immersions and the already constructed canonical `openIso`. -/
theorem existsUnique_iso_to_canonical
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    {V : Scheme.{u}} (π : V ⟶ U.toScheme) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    (hY : ∀ y : Y, f y ∉ U →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (Y.presheaf.stalk y))
    (e : (f ⁻¹ᵁ U).toScheme ≅ V) (he : e.hom ≫ π = f ∣_ U) :
    ∃! a : Y ≅ scheme X U π,
      a.hom ≫ toBase X U π = f ∧
      (f ⁻¹ᵁ U).ι ≫ a.hom =
        (e ≪≫ (openIso X U π).symm).hom ≫ (toBase X U π ⁻¹ᵁ U).ι := by
  let F := toBase X U π
  have : IsFinite F := isFinite_toBase X U π hdepth
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian (scheme X U π) := LocallyOfFiniteType.isLocallyNoetherian F
  let T := f ⁻¹ᵁ U
  let T' := F ⁻¹ᵁ U
  let eT : T.toScheme ≅ T'.toScheme := e ≪≫ (openIso X U π).symm
  have hinv : (openIso X U π).inv ≫ (F ∣_ U) = π := by
    rw [← openIso_hom_toBase X U π, Iso.inv_hom_id_assoc]
  have hres : eT.hom ≫ (F ∣_ U) = f ∣_ U := by
    change (e.hom ≫ (openIso X U π).inv) ≫ (F ∣_ U) = _
    rw [Category.assoc, hinv, he]
  have heT : (eT.hom ≫ T'.ι) ≫ F = T.ι ≫ f := by
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hres, morphismRestrict_ι]
  exact Scheme.DirectImageAlgebra.existsUnique_iso_of_boundary_two_le_depth
    f F T T' hY (two_le_depth_boundary X U π hdepth) eT heT

end EtaleFundamentalGroups.FiniteBoundaryExtension
