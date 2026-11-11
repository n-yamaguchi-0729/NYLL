/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.BoundaryExtensionUniqueness
import Nyll.SchemeTheory.Modules.Functoriality.DirectImageAlgebraHomRecovery

/-!
# Unique extension of specified morphisms across depth-two boundaries

Scalar Hartogs on the actual source extends its original direct-image
algebra maps. Relative-spectrum recovery turns the extended algebra map
into a map of the original affine schemes. Faithfulness with arbitrary
source proves that its restriction is the supplied open morphism.

For two affine extensions with depth-two boundaries, every supplied open
isomorphism over the base extends to a unique isomorphism. Uniqueness
retains the literal restriction equation, including the original choice
of open-cover identification.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.DirectImageAlgebra

variable {Y Z X : Scheme.{u}}

/-- A map to an affine extension is determined by its restriction to a
depth-two open in the original source. -/
theorem hom_ext_of_boundary_two_le_depth [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (g : Z ⟶ X) [IsAffineHom g] (T : Y.Opens)
    (hdepth : ∀ y : Y, y ∉ T →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (Y.presheaf.stalk y))
    (r s : Y ⟶ Z) (hr : r ≫ g = f) (hs : s ≫ g = f)
    (h : T.ι ≫ r = T.ι ≫ s) : r = s := by
  have : IsIso (map (T.ι ≫ f) f T.ι rfl) := isIso_boundaryMap f T hdepth
  apply hom_ext f g r s hr hs
  apply (cancel_mono (map (T.ι ≫ f) f T.ι rfl)).mp
  rw [← map_comp (T.ι ≫ f) f g T.ι r rfl hr,
    ← map_comp (T.ι ≫ f) f g T.ι s rfl hs]
  congr 1

/-- Every supplied morphism from a depth-two open extends uniquely
between the original affine schemes over the original base. -/
theorem existsUnique_hom_of_boundary_two_le_depth [IsLocallyNoetherian Y]
    (f : Y ⟶ X) (g : Z ⟶ X) [IsAffineHom f] [IsAffineHom g]
    (T : Y.Opens)
    (hdepth : ∀ y : Y, y ∉ T →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (Y.presheaf.stalk y))
    (r : T.toScheme ⟶ Z) (hr : r ≫ g = T.ι ≫ f) :
    ∃! s : Y ⟶ Z, s ≫ g = f ∧ T.ι ≫ s = r := by
  let η := map (T.ι ≫ f) f T.ι rfl
  have : IsIso η := isIso_boundaryMap f T hdepth
  let ρ := map (T.ι ≫ f) g r hr
  let φ : sheaf g ⟶ sheaf f := ρ ≫ inv η
  have hφ : structureMap g ≫ φ = structureMap f := by
    change structureMap g ≫ (ρ ≫ inv η) = structureMap f
    calc
      _ = (structureMap g ≫ ρ) ≫ inv η := (Category.assoc _ _ _).symm
      _ = structureMap (T.ι ≫ f) ≫ inv η :=
        congrArg (fun k => k ≫ inv η) (structureMap_map (T.ι ≫ f) g r hr)
      _ = (structureMap f ≫ η) ≫ inv η :=
        congrArg (fun k => k ≫ inv η) (structureMap_map (T.ι ≫ f) f T.ι rfl).symm
      _ = structureMap f := by rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  let s := homOfAlgebraMap f g φ
  have hs : s ≫ g = f := homOfAlgebraMap_toBase f g φ hφ
  have hsT : T.ι ≫ s = r := by
    apply hom_ext (T.ι ≫ f) g (T.ι ≫ s) r
      ((Category.assoc T.ι s g).trans (congrArg (fun k => T.ι ≫ k) hs)) hr
    rw [map_comp (T.ι ≫ f) f g T.ι s rfl hs,
      map_homOfAlgebraMap f g φ hφ]
    change (ρ ≫ inv η) ≫ η = ρ
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨s, ⟨hs, hsT⟩, ?_⟩
  intro s' hs'
  exact hom_ext_of_boundary_two_le_depth f g T hdepth s' s hs'.1 hs
    (hs'.2.trans hsT.symm)

/-- A supplied isomorphism of the two open parts extends uniquely over
the base, with its specified restriction retained exactly. This applies
in particular to finite extensions of a given finite etale open cover. -/
theorem existsUnique_iso_of_boundary_two_le_depth
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : Y ⟶ X) (g : Z ⟶ X) [IsAffineHom f] [IsAffineHom g]
    (T : Y.Opens) (T' : Z.Opens)
    (hdepth : ∀ y : Y, y ∉ T →
      (2 : ℕ∞) ≤ Module.depth (Y.presheaf.stalk y) (Y.presheaf.stalk y))
    (hdepth' : ∀ z : Z, z ∉ T' →
      (2 : ℕ∞) ≤ Module.depth (Z.presheaf.stalk z) (Z.presheaf.stalk z))
    (e : T.toScheme ≅ T'.toScheme)
    (he : (e.hom ≫ T'.ι) ≫ g = T.ι ≫ f) :
    ∃! a : Y ≅ Z, a.hom ≫ g = f ∧ T.ι ≫ a.hom = e.hom ≫ T'.ι := by
  have he' : (e.inv ≫ T.ι) ≫ f = T'.ι ≫ g := by
    calc
      _ = e.inv ≫ (T.ι ≫ f) := Category.assoc _ _ _
      _ = e.inv ≫ ((e.hom ≫ T'.ι) ≫ g) :=
        congrArg (fun k => e.inv ≫ k) he.symm
      _ = T'.ι ≫ g := by rw [Category.assoc, Iso.inv_hom_id_assoc]
  obtain ⟨r, hr, _⟩ :=
    existsUnique_hom_of_boundary_two_le_depth f g T hdepth (e.hom ≫ T'.ι) he
  obtain ⟨s, hs, _⟩ :=
    existsUnique_hom_of_boundary_two_le_depth g f T' hdepth' (e.inv ≫ T.ι) he'
  have hrs : r ≫ s = 𝟙 Y := by
    apply hom_ext_of_boundary_two_le_depth f f T hdepth (r ≫ s) (𝟙 Y)
      (by rw [Category.assoc, hs.1, hr.1]) (Category.id_comp f)
    rw [← Category.assoc, hr.2, Category.assoc, hs.2,
      Iso.hom_inv_id_assoc, Category.comp_id]
  have hsr : s ≫ r = 𝟙 Z := by
    apply hom_ext_of_boundary_two_le_depth g g T' hdepth' (s ≫ r) (𝟙 Z)
      (by rw [Category.assoc, hr.1, hs.1]) (Category.id_comp g)
    rw [← Category.assoc, hs.2, Category.assoc, hr.2,
      Iso.inv_hom_id_assoc, Category.comp_id]
  let a : Y ≅ Z := ⟨r, s, hrs, hsr⟩
  refine ⟨a, ⟨hr.1, hr.2⟩, ?_⟩
  intro b hb
  apply Iso.ext
  exact hom_ext_of_boundary_two_le_depth f g T hdepth b.hom a.hom hb.1 hr.1
    (hb.2.trans hr.2.symm)

end AlgebraicGeometry.Scheme.DirectImageAlgebra
