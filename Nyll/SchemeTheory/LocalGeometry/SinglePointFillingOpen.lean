/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Filling one point in an actual discrete fibre

Removing all the other points over a closed point gives an open subscheme.
Its puncture at the selected point is the original inverse image of the
punctured base, with the original inclusion retained. Applied to a finite
constant cover, this fills only the chosen rational point, rather than its
entire conjugate fibre.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [LocallyQuasiFinite f]
  (x : X) (hx : IsClosed ({x} : Set X))

include hx in
/-- Every subset of a locally quasi-finite fibre over a closed point is closed. -/
theorem isClosed_subset_discrete_fiber (S : Set Y) (hS : S ⊆ f ⁻¹' {x}) :
    IsClosed S := by
  have : DiscreteTopology (f ⁻¹' {x}) := (f.isDiscrete_preimage_singleton x).to_subtype
  have hclosed : IsClosed (f ⁻¹' ({x} : Set X)) := hx.preimage f.continuous
  have h := hclosed.isClosedEmbedding_subtypeVal.isClosedMap
    {y : f ⁻¹' ({x} : Set X) | (y : Y) ∈ S} (isClosed_discrete _)
  have he : Subtype.val '' {y : f ⁻¹' ({x} : Set X) | (y : Y) ∈ S} = S := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hy
      exact ⟨⟨y, hS hy⟩, hy, rfl⟩
  exact he ▸ h

/-- The open which restores just the selected point of the original fibre. -/
def singlePointFillingOpen (z : Y) : Y.Opens :=
  ⟨(f ⁻¹' ({x} : Set X) \ {z})ᶜ,
    (isClosed_subset_discrete_fiber f x hx _ Set.sdiff_subset).isOpen_compl⟩

/-- Membership retains the actual fibre and the selected point. -/
theorem mem_singlePointFillingOpen (z y : Y) :
    y ∈ singlePointFillingOpen f x hx z ↔ f y ≠ x ∨ y = z := by
  classical
  change ¬ (f y ∈ ({x} : Set X) ∧ y ∉ ({z} : Set Y)) ↔ _
  simp only [Set.mem_singleton_iff, not_and_or, not_not]

/-- The selected point belongs to the constructed open. -/
theorem mem_singlePointFillingOpen_self (z : Y) :
    z ∈ singlePointFillingOpen f x hx z :=
  (mem_singlePointFillingOpen f x hx z z).mpr (Or.inr rfl)

/-- The actual inverse image of the punctured base lies in the new open. -/
theorem preimage_puncture_le_singlePointFillingOpen (z : Y) :
    f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) ≤
      singlePointFillingOpen f x hx z := by
  intro y hy
  exact (mem_singlePointFillingOpen f x hx z y).mpr (Or.inl hy)

/-- The original map from the punctured inverse image to the one-point filling. -/
def singlePointFillingInclusion (z : Y) :
    (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) : Scheme) ⟶
      singlePointFillingOpen f x hx z :=
  Y.homOfLE (preimage_puncture_le_singlePointFillingOpen f x hx z)

/-- Its composition into the original cover is literally the original open inclusion. -/
@[reassoc]
theorem singlePointFillingInclusion_comp (z : Y) :
    singlePointFillingInclusion f x hx z ≫ (singlePointFillingOpen f x hx z).ι =
      (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)).ι :=
  Y.homOfLE_ι _

include hx in
/-- The selected point remains a closed point of the actual cover. -/
theorem singlePointFilling_selected_isClosed (z : Y) (hz : f z = x) :
    IsClosed ({z} : Set Y) := by
  apply isClosed_subset_discrete_fiber f x hx
  intro y hy
  have hyz : y = z := Set.mem_singleton_iff.mp hy
  exact Set.mem_singleton_iff.mpr ((congrArg f hyz).trans hz)

/-- The selected point in the actual open subscheme. -/
def singlePointFillingPoint (z : Y) : singlePointFillingOpen f x hx z :=
  ⟨z, mem_singlePointFillingOpen_self f x hx z⟩

/-- Puncturing the filling removes precisely the selected point. -/
theorem singlePointFilling_puncture_complement (z : Y) (hz : f z = x) :
    ((singlePointFillingOpen f x hx z).ι ⁻¹ᵁ
      (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)) :
        Set (singlePointFillingOpen f x hx z)) =
      ({singlePointFillingPoint f x hx z} : Set (singlePointFillingOpen f x hx z))ᶜ := by
  apply Set.ext
  intro y
  change f ((singlePointFillingOpen f x hx z).ι y) ≠ x ↔
    y ≠ singlePointFillingPoint f x hx z
  constructor
  · intro hy he
    exact hy ((congrArg (fun t : (singlePointFillingOpen f x hx z : Scheme) =>
      f ((singlePointFillingOpen f x hx z).ι t)) he).trans hz)
  · intro hy
    rcases (mem_singlePointFillingOpen f x hx z
      ((singlePointFillingOpen f x hx z).ι y)).mp y.property with h | h
    · exact h
    · exact False.elim (hy (Subtype.ext h))

/-- The puncture of the actual filling is canonically the original
punctured inverse image. -/
def singlePointFillingPunctureIso (z : Y) :
    ((singlePointFillingOpen f x hx z).ι ⁻¹ᵁ
      (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)) : Scheme) ≅
      (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) : Scheme) :=
  Opens.isoOfLE (preimage_puncture_le_singlePointFillingOpen f x hx z)

/-- The comparison keeps the inclusion into the original cover unchanged. -/
@[reassoc]
theorem singlePointFillingPunctureIso_hom_comp (z : Y) :
    (singlePointFillingPunctureIso f x hx z).hom ≫
        (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)).ι =
      ((singlePointFillingOpen f x hx z).ι ⁻¹ᵁ
        (f ⁻¹ᵁ (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens))).ι ≫
          (singlePointFillingOpen f x hx z).ι :=
  Opens.isoOfLE_hom_ι _

end AlgebraicGeometry.Scheme
