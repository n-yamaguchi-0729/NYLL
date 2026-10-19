/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.AbelianScheme
import Nyll.SchemeTheory.GroupSchemes.SplitTorus
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Split and geometric tori on actual group schemes over fields

A torus is geometrically isomorphic to the actual integral-character split model,
with a fixed finite rank. The splitting condition is imposed on algebraically closed
geometric field extensions, and is therefore preserved by every field extension.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace GroupSchemes

/-- The canonical group pullback comparison for two successive base changes. -/
def baseChangeCompIso {S S' S'' : Scheme.{u}} (f : S'' ⟶ S') (g : S' ⟶ S) :
    baseChange (f ≫ g) ≅ baseChange g ⋙ baseChange f :=
  Functor.mapCommGrpNatIso (Over.pullbackComp f g) ≪≫ Functor.mapCommGrpCompIso

end GroupSchemes

variable {K : Type u} [Field K]

/-- A split torus is an actual group scheme isomorphic to an integral-character split model. -/
class IsSplitTorus (G : CommGrp (Over (Spec (CommRingCat.of K)))) : Prop where
  /-- An actual finite-rank splitting isomorphism. -/
  exists_split : ∃ r : ℕ, Nonempty (G ≅ GroupSchemes.splitTorus K r)

/-- A torus is a finite-rank geometric form of the actual split torus group scheme. -/
class IsTorus (G : CommGrp (Over (Spec (CommRingCat.of K)))) : Prop where
  /-- A fixed finite rank and a splitting after each geometric field extension. -/
  exists_geometric_split : ∃ r : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K)),
    Nonempty ((GroupSchemes.baseChange f).obj G ≅ GroupSchemes.splitTorus Ω r)

namespace IsSplitTorus

variable {G H : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- The concrete Hopf-algebra torus is split with its specified integral character rank. -/
instance splitTorus (r : ℕ) : IsSplitTorus (GroupSchemes.splitTorus K r) :=
  ⟨r, ⟨Iso.refl _⟩⟩

/-- Splitting transports by actual group-scheme isomorphisms. -/
theorem of_iso (e : G ≅ H) [IsSplitTorus G] : IsSplitTorus H := by
  obtain ⟨r, ⟨a⟩⟩ := exists_split (G := G)
  exact ⟨r, ⟨e.symm ≪≫ a⟩⟩

/-- Actual group-scheme isomorphisms preserve and reflect split tori. -/
theorem iso_iff (e : G ≅ H) : IsSplitTorus G ↔ IsSplitTorus H :=
  ⟨fun _ => of_iso e, fun _ => of_iso e.symm⟩

end IsSplitTorus

namespace IsTorus

variable {G H : CommGrp (Over (Spec (CommRingCat.of K)))}

/-- Geometric torus structure transports by an actual group-scheme isomorphism. -/
theorem of_iso (e : G ≅ H) [IsTorus G] : IsTorus H := by
  obtain ⟨r, hr⟩ := exists_geometric_split (G := G)
  refine ⟨r, fun Ω _ _ f => ?_⟩
  obtain ⟨a⟩ := hr Ω f
  exact ⟨((GroupSchemes.baseChange f).mapIso e).symm ≪≫ a⟩

/-- Actual group-scheme isomorphisms preserve and reflect tori. -/
theorem iso_iff (e : G ≅ H) : IsTorus G ↔ IsTorus H :=
  ⟨fun _ => of_iso e, fun _ => of_iso e.symm⟩

/-- An algebraically closed geometric field extension splits an actual torus. -/
theorem geometric_split (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (f : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of K)) [IsTorus G] :
    IsSplitTorus ((GroupSchemes.baseChange f).obj G) := by
  obtain ⟨r, hr⟩ := exists_geometric_split (G := G)
  exact ⟨r, hr Ω f⟩

/-- Every field extension preserves torus structure on the actual pullback group scheme. -/
instance baseChange {L : Type u} [Field L]
    (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) [IsTorus G] :
    IsTorus ((GroupSchemes.baseChange f).obj G) := by
  obtain ⟨r, hr⟩ := exists_geometric_split (G := G)
  refine ⟨r, fun Ω _ _ g => ?_⟩
  obtain ⟨a⟩ := hr Ω (g ≫ f)
  exact ⟨((GroupSchemes.baseChangeCompIso g f).app G).symm ≪≫ a⟩

end IsTorus

end AlgebraicGeometry
