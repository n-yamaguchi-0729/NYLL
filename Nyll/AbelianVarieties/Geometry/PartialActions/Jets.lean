/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Nyll.AbelianVarieties.Geometry.PartialActions.Basic
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebraCriteria
public import Nyll.SchemeTheory.LocalGeometry.FormalNeighborhoods
public import Nyll.SchemeTheory.LocalGeometry.StalkPullbacks
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.Action
public import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.Theorems.IrreducibleIdentityComponentIndex
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.BaseChange.AffineGlobalSections
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Infinitesimal partial actions

First-order group-law identities control the action on infinitesimal neighborhoods.
The resulting compatible finite-dimensional representations detect trivial action on jets.
-/

@[expose] public section

/-- The canonical field point with its scheme carrier retained for stalk calculations. -/
noncomputable def fieldSpecPoint (k : Type*) [Field k] :
    AlgebraicGeometry.Spec (CommRingCat.of k) := IsLocalRing.closedPoint k

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.GroupLawFirstJets

universe u

open CategoryTheory.Limits hiding pair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open NeronModelInfra GoodReductionJacobian

namespace FirstOrderGroupLaw

section Algebra

open IsLocalRing

theorem mem_maximalIdeal_sq_of_slices {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    (π₁ π₂ : B →+* A) (α β : A →+* B)
    (h0 : maximalIdeal A ≤ (maximalIdeal B).map π₁ ⊔ (maximalIdeal B).map π₂)
    (hα : ∀ a ∈ maximalIdeal A, α a ∈ maximalIdeal B)
    (hβ : ∀ a ∈ maximalIdeal A, β a ∈ maximalIdeal B)
    (h1 : ∀ b, α (π₁ b) = b) (h1' : ∀ b, β (π₂ b) = b)
    (h2 : ∀ b ∈ maximalIdeal B, α (π₂ b) = 0) (h2' : ∀ b ∈ maximalIdeal B, β (π₁ b) = 0)
    {ψ : A} (hψ : ψ ∈ maximalIdeal A) (hαψ : α ψ = 0) (hβψ : β ψ = 0) :
    ψ ∈ maximalIdeal A ^ 2 := by
  have hπ₁ : ∀ b ∈ maximalIdeal B, π₁ b ∈ maximalIdeal A := by
    intro b hb
    rw [mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
    intro hu
    exact hb (by simpa only [h1] using hu.map α)
  have hπ₂ : ∀ b ∈ maximalIdeal B, π₂ b ∈ maximalIdeal A := by
    intro b hb
    rw [mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
    intro hu
    exact hb (by simpa only [h1'] using hu.map β)
  have hmap₁ : (maximalIdeal B).map π₁ ≤ maximalIdeal A :=
    Ideal.map_le_iff_le_comap.mpr fun b hb ↦ hπ₁ b hb
  have hmap₂ : (maximalIdeal B).map π₂ ≤ maximalIdeal A :=
    Ideal.map_le_iff_le_comap.mpr fun b hb ↦ hπ₂ b hb
  have hkerα : ∀ a, α a = 0 → a ∈ maximalIdeal A := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map α
    rw [ha] at this
    exact not_isUnit_zero this
  have hkerβ : ∀ a, β a = 0 → a ∈ maximalIdeal A := by
    intro a ha
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map β
    rw [ha] at this
    exact not_isUnit_zero this
  have h5 : ∀ a, a - π₁ (α a) ∈ maximalIdeal A := fun a ↦ hkerα _ (by rw [map_sub, h1, sub_self])
  have h5' : ∀ a, a - π₂ (β a) ∈ maximalIdeal A := fun a ↦ hkerβ _ (by rw [map_sub, h1', sub_self])
  let P : A → Prop := fun a ↦ a - π₁ (α a) - π₂ (β a) ∈ maximalIdeal A ^ 2
  have hP_add : ∀ a a', P a → P a' → P (a + a') := by
    intro a a' ha ha'
    have := Ideal.add_mem _ ha ha'
    change _ ∈ _
    convert this using 1
    simp only [map_add]; ring
  have hsq : ∀ u ∈ maximalIdeal A, ∀ v ∈ maximalIdeal A, u * v ∈ maximalIdeal A ^ 2 :=
    fun u hu v hv ↦ by rw [pow_two]; exact Ideal.mul_mem_mul hu hv
  have hπsq₁ : ∀ b ∈ maximalIdeal B ^ 2, π₁ b ∈ maximalIdeal A ^ 2 := by
    intro b hb
    have : (maximalIdeal B ^ 2).map π₁ ≤ maximalIdeal A ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap₁ 2
    exact this (Ideal.mem_map_of_mem _ hb)
  have hπsq₂ : ∀ b ∈ maximalIdeal B ^ 2, π₂ b ∈ maximalIdeal A ^ 2 := by
    intro b hb
    have : (maximalIdeal B ^ 2).map π₂ ≤ maximalIdeal A ^ 2 := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap₂ 2
    exact this (Ideal.mem_map_of_mem _ hb)
  have hP_smul : ∀ c a, a ∈ maximalIdeal A → P a → P (c * a) := by
    intro c a ha hPa
    change c * a - π₁ (α (c * a)) - π₂ (β (c * a)) ∈ _
    have e1 : c * a - π₁ (α (c * a)) - π₂ (β (c * a)) =
        c * (a - π₁ (α a) - π₂ (β a)) + (c - π₁ (α c)) * π₁ (α a) +
          (c - π₂ (β c)) * π₂ (β a) := by
      simp only [map_mul]; ring
    rw [e1]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hPa
    · exact hsq _ (h5 c) _ (hπ₁ _ (hα _ ha))
    · exact hsq _ (h5' c) _ (hπ₂ _ (hβ _ ha))
  have hP₁ : ∀ a ∈ (maximalIdeal B).map π₁, P a := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ ↦ P a) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨b, hb, rfl⟩
      change π₁ b - π₁ (α (π₁ b)) - π₂ (β (π₁ b)) ∈ _
      rw [h1, h2' b hb, map_zero, sub_self, zero_sub, neg_mem_iff]
      exact Ideal.zero_mem _
    · change (0 : A) - π₁ (α 0) - π₂ (β 0) ∈ _
      simpa only [map_zero, sub_zero] using (Ideal.zero_mem (maximalIdeal A ^ 2))
    · intro a a' _ _ ha ha'; exact hP_add _ _ ha ha'
    · intro c a ha' hPa
      exact hP_smul c a (hmap₁ ha') hPa
  have hP₂ : ∀ a ∈ (maximalIdeal B).map π₂, P a := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ ↦ P a) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨b, hb, rfl⟩
      change π₂ b - π₁ (α (π₂ b)) - π₂ (β (π₂ b)) ∈ _
      rw [h1', h2 b hb, map_zero, sub_zero, sub_self]
      exact Ideal.zero_mem _
    · change (0 : A) - π₁ (α 0) - π₂ (β 0) ∈ _
      simpa only [map_zero, sub_zero] using (Ideal.zero_mem (maximalIdeal A ^ 2))
    · intro a a' _ _ ha ha'; exact hP_add _ _ ha ha'
    · intro c a ha' hPa
      exact hP_smul c a (hmap₂ ha') hPa
  have hPψ : P ψ := by
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp (h0 hψ)
    exact hP_add _ _ (hP₁ u hu) (hP₂ v hv)
  simpa only [P, hαψ, hβψ, map_zero, sub_zero] using hPψ

end Algebra

section Transport

variable {X Y Z : Scheme.{u}}

/-- Transport a stalk map along a chosen equality of image points. -/
noncomputable def stalkMapOfEq (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y) :
    Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  Y.presheaf.stalkSpecializes (specializes_of_eq h) ≫ g.stalkMap x

lemma stalkMapOfEq_germ (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(Y, U)) :
    stalkMapOfEq g x y h (Y.presheaf.germ U y hy s) =
      X.presheaf.germ (g ⁻¹ᵁ U) x
          (show x ∈ g ⁻¹ᵁ U by rw [Scheme.Hom.mem_preimage, h]; exact hy) (g.app U s) := by
  simp only [stalkMapOfEq, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

lemma germ_mem_maximalIdeal_iff {U : X.Opens} (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ U x hx s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      x ∉ X.basicOpen s := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, X.mem_basicOpen s x hx]

lemma stalkMapOfEq_mem_maximalIdeal (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y)
    (a : Y.presheaf.stalk y) (ha : a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) :
    stalkMapOfEq g x y h a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨U, hy, s, rfl⟩ := Y.presheaf.exists_germ_eq a
  rw [stalkMapOfEq_germ, germ_mem_maximalIdeal_iff, ← Scheme.preimage_basicOpen,
    Scheme.Hom.mem_preimage, h]
  rwa [germ_mem_maximalIdeal_iff] at ha

lemma stalkMapOfEq_mem_maximalIdeal_iff (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y)
    (U : Y.Opens) (hy : y ∈ U) (s : Γ(Y, U)) :
    stalkMapOfEq g x y h (Y.presheaf.germ U y hy s) ∈ IsLocalRing.maximalIdeal
        (X.presheaf.stalk x) ↔
      Y.presheaf.germ U y hy s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  refine ⟨fun H ↦ ?_, stalkMapOfEq_mem_maximalIdeal g x y h _⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at H ⊢
  exact fun hu ↦ H (hu.map _)

lemma germ_app_congr {g g' : X ⟶ Y} (hg : g = g') (U : Y.Opens) (x : X) (h₁ : x ∈ g ⁻¹ᵁ U)
    (h₂ : x ∈ g' ⁻¹ᵁ U) (s : Γ(Y, U)) :
    X.presheaf.germ (g ⁻¹ᵁ U) x h₁ (g.app U s) = X.presheaf.germ (g' ⁻¹ᵁ U) x h₂ (g'.app U s) := by
  subst hg; rfl

lemma germ_id_app (U : X.Opens) (x : X) (h₁ : x ∈ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (h₂ : x ∈ U) (s : Γ(X, U)) :
    X.presheaf.germ ((𝟙 X : X ⟶ X) ⁻¹ᵁ U) x h₁ ((𝟙 X : X ⟶ X).app U s) =
      X.presheaf.germ U x h₂ s := by
  rfl

lemma stalkMapOfEq_stalkMapOfEq_germ (g : X ⟶ Y) (g' : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (h : g x = y) (h' : g' y = z) (U : Z.Opens) (hz : z ∈ U) (s : Γ(Z, U)) :
    stalkMapOfEq g x y h (stalkMapOfEq g' y z h' (Z.presheaf.germ U z hz s)) =
      X.presheaf.germ ((g ≫ g') ⁻¹ᵁ U) x
        (show x ∈ (g ≫ g') ⁻¹ᵁ U by
          rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, h, h']; exact hz)
        ((g ≫ g').app U s) := by
  rw [stalkMapOfEq_germ, stalkMapOfEq_germ]
  rfl

end Transport

section SpecField

variable {k : Type u} [Field k]

lemma germ_eq_zero_of_mem_maximalIdeal_of_field (q : Spec (CommRingCat.of k))
    (V : (Spec (CommRingCat.of k)).Opens) (hq : q ∈ V) (s : Γ(Spec (CommRingCat.of k), V))
    (hs : (Spec (CommRingCat.of k)).presheaf.germ V q hq s ∈
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of k)).presheaf.stalk q)) :
    (Spec (CommRingCat.of k)).presheaf.germ V q hq s = 0 := by
  have hF : IsField ((Spec (CommRingCat.of k)).presheaf.stalk q) := by
    obtain rfl : fieldSpecPoint k = q :=
        Subsingleton.elim _ _
    exact MulEquiv.isField (Field.toIsField k)
      (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv
  rw [IsLocalRing.isField_iff_maximalIdeal_eq] at hF
  rw [hF] at hs
  exact hs

end SpecField

section Slices

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)

/-- The identity section of the relative group law. -/
noncomputable def unit : Spec (CommRingCat.of k) ⟶ G := (L.one (𝟙 _)).1

@[reassoc (attr := simp)]
lemma unit_f : unit f L ≫ f = 𝟙 _ := (L.one (𝟙 _)).2

/-- The multiplication morphism represented by the relative group law. -/
noncomputable def mulMap : pullback f f ⟶ G :=
  (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩).1

/-- The slice with second coordinate equal to the identity. -/
noncomputable def slice₁ : G ⟶ pullback f f :=
  pullback.lift (𝟙 G) (f ≫ unit f L)
    (by rw [Category.id_comp, Category.assoc, unit_f, Category.comp_id])

/-- The slice with first coordinate equal to the identity. -/
noncomputable def slice₂ : G ⟶ pullback f f :=
  pullback.lift (f ≫ unit f L) (𝟙 G)
    (by rw [Category.id_comp, Category.assoc, unit_f, Category.comp_id])

@[reassoc (attr := simp)]
lemma slice₁_fst : slice₁ f L ≫ pullback.fst f f = 𝟙 G := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma slice₁_snd : slice₁ f L ≫ pullback.snd f f = f ≫ unit f L := pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma slice₂_fst : slice₂ f L ≫ pullback.fst f f = f ≫ unit f L := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma slice₂_snd : slice₂ f L ≫ pullback.snd f f = 𝟙 G := pullback.lift_snd _ _ _

lemma one_eq : L.one f = ⟨f ≫ unit f L,
    by rw [Category.assoc, unit_f, Category.comp_id]⟩ := by
  have h := L.one_natural (𝟙 _) f f (Category.comp_id f)
  rw [← h]
  rfl

lemma slice₁_mulMap : slice₁ f L ≫ mulMap f L = 𝟙 G := by
  have hψ : slice₁ f L ≫ pullback.fst f f ≫ f = f := by
    rw [slice₁_fst_assoc]
  have h := L.mul_natural (pullback.fst f f ≫ f) f (slice₁ f L) hψ ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩
  have h1 : schemeHomOverComp (slice₁ f L) hψ ⟨pullback.fst f f, rfl⟩ =
      (⟨𝟙 G, Category.id_comp f⟩ : SchemeHomOver f f) := Subtype.ext (slice₁_fst f L)
  have h2 : schemeHomOverComp (slice₁ f L) hψ ⟨pullback.snd f f, pullback.condition.symm⟩ =
      L.one f := by
    rw [one_eq]; exact Subtype.ext (slice₁_snd f L)
  rw [h1, h2, L.mul_one] at h
  exact congrArg Subtype.val h

lemma slice₂_mulMap : slice₂ f L ≫ mulMap f L = 𝟙 G := by
  have hψ : slice₂ f L ≫ pullback.fst f f ≫ f = f := by
    rw [slice₂_fst_assoc, unit_f, Category.comp_id]
  have h := L.mul_natural (pullback.fst f f ≫ f) f (slice₂ f L) hψ ⟨pullback.fst f f, rfl⟩
    ⟨pullback.snd f f, pullback.condition.symm⟩
  have h1 : schemeHomOverComp (slice₂ f L) hψ ⟨pullback.fst f f, rfl⟩ = L.one f := by
    rw [one_eq]; exact Subtype.ext (slice₂_fst f L)
  have h2 : schemeHomOverComp (slice₂ f L) hψ ⟨pullback.snd f f, pullback.condition.symm⟩ =
      (⟨𝟙 G, Category.id_comp f⟩ : SchemeHomOver f f) := Subtype.ext (slice₂_snd f L)
  rw [h1, h2, L.one_mul] at h
  exact congrArg Subtype.val h

/-- The pair of identity sections. -/
noncomputable def unitPair : Spec (CommRingCat.of k) ⟶ pullback f f :=
  pullback.lift (unit f L) (unit f L) rfl

@[reassoc (attr := simp)]
lemma unitPair_fst : unitPair f L ≫ pullback.fst f f = unit f L := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma unitPair_snd : unitPair f L ≫ pullback.snd f f = unit f L := pullback.lift_snd _ _ _

lemma unit_slice₁ : unit f L ≫ slice₁ f L = unitPair f L := by
  apply pullback.hom_ext
  · rw [Category.assoc, slice₁_fst, Category.comp_id, unitPair_fst]
  · rw [Category.assoc, slice₁_snd, unit_f_assoc, unitPair_snd]

lemma unit_slice₂ : unit f L ≫ slice₂ f L = unitPair f L := by
  apply pullback.hom_ext
  · rw [Category.assoc, slice₂_fst, unit_f_assoc, unitPair_fst]
  · rw [Category.assoc, slice₂_snd, Category.comp_id, unitPair_snd]

lemma unitPair_mulMap : unitPair f L ≫ mulMap f L = unit f L := by
  rw [← unit_slice₁, Category.assoc, slice₁_mulMap, Category.comp_id]

section points

lemma fst_z : pullback.fst f f (unitPair f L (fieldSpecPoint k)) = unit f L (fieldSpecPoint k) := by
  exact congrArg (fun m : Spec (CommRingCat.of k) ⟶ G => m (fieldSpecPoint k)) (unitPair_fst f L)

lemma snd_z : pullback.snd f f (unitPair f L (fieldSpecPoint k)) = unit f L (fieldSpecPoint k) := by
  exact congrArg (fun m : Spec (CommRingCat.of k) ⟶ G => m (fieldSpecPoint k)) (unitPair_snd f L)

lemma mulMap_z : mulMap f L (unitPair f L (fieldSpecPoint k)) = unit f L (fieldSpecPoint k) := by
  exact congrArg (fun m : Spec (CommRingCat.of k) ⟶ G => m (fieldSpecPoint k)) (unitPair_mulMap f L)

lemma slice₁_e : slice₁ f L (unit f L (fieldSpecPoint k)) = unitPair f L (fieldSpecPoint k) := by
  exact congrArg (fun m : Spec (CommRingCat.of k) ⟶ pullback f f => m (fieldSpecPoint k))
      (unit_slice₁ f L)

lemma slice₂_e : slice₂ f L (unit f L (fieldSpecPoint k)) = unitPair f L (fieldSpecPoint k) := by
  exact congrArg (fun m : Spec (CommRingCat.of k) ⟶ pullback f f => m (fieldSpecPoint k))
      (unit_slice₂ f L)

end points

end Slices

section Identities

variable {X Y Z : Scheme.{u}}

lemma stalkMapOfEq_id_apply (x : X) (h : (𝟙 X : X ⟶ X) x = x) (b : X.presheaf.stalk x) :
    stalkMapOfEq (𝟙 X) x x h b = b := by
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq b
  rw [stalkMapOfEq_germ]
  rfl

lemma stalkMapOfEq_congr {g g' : X ⟶ Y} (hg : g = g') (x : X) (y : Y) (h : g x = y)
    (h' : g' x = y) : stalkMapOfEq g x y h = stalkMapOfEq g' x y h' := by
  subst hg; rfl

lemma stalkMapOfEq_comp_apply (g : X ⟶ Y) (g' : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (h : g x = y) (h' : g' y = z) (b : Z.presheaf.stalk z) :
    stalkMapOfEq g x y h (stalkMapOfEq g' y z h' b) =
      stalkMapOfEq (g ≫ g') x z (by rw [Scheme.Hom.comp_apply, h, h']) b := by
  obtain ⟨U, hz, s, rfl⟩ := Z.presheaf.exists_germ_eq b
  rw [stalkMapOfEq_stalkMapOfEq_germ, stalkMapOfEq_germ]

lemma germ_appLE_eq_stalkMapOfEq (g : X ⟶ Y) (U : Y.Opens) (W : X.Opens) (hWU : W ≤ g ⁻¹ᵁ U)
    (x : X) (hx : x ∈ W) (y : Y) (hy : g x = y) (s : Γ(Y, U)) :
    X.presheaf.germ W x hx (g.appLE U W hWU s) =
      stalkMapOfEq g x y hy (Y.presheaf.germ U y (by rw [← hy]; exact hWU hx) s) := by
  rw [stalkMapOfEq_germ]
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

variable {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
  (L : RelativeGroupLaw k f)

lemma stalkMapOfEq_f_unit_apply
    (b : G.presheaf.stalk (unit f L (fieldSpecPoint k)))
    (hb : b ∈ IsLocalRing.maximalIdeal _)
    (h : (f ≫ unit f L) (unit f L (fieldSpecPoint k)) =
      unit f L (fieldSpecPoint k)) :
    stalkMapOfEq (f ≫ unit f L) (unit f L (fieldSpecPoint k))
      (unit f L (fieldSpecPoint k)) h b = 0 := by
  obtain ⟨U, he, s, rfl⟩ := G.presheaf.exists_germ_eq b
  rw [stalkMapOfEq_germ]
  have hue : unit f L (f (unit f L (fieldSpecPoint k))) =
      unit f L (fieldSpecPoint k) := by
    exact congrArg (fun m : Spec (CommRingCat.of k) ⟶ G =>
      m (fieldSpecPoint k)) (unit_f_assoc f L
          (unit f L))
  have hfe : f (unit f L (fieldSpecPoint k)) ∈ unit f L ⁻¹ᵁ U := by
    rw [Scheme.Hom.mem_preimage, hue]; exact he
  have key : G.presheaf.germ ((f ≫ unit f L) ⁻¹ᵁ U) (unit f L (fieldSpecPoint k))
      (show unit f L (fieldSpecPoint k) ∈ (f ≫ unit f L) ⁻¹ᵁ U by
        rw [Scheme.Hom.mem_preimage, h]; exact he)
      ((f ≫ unit f L).app U s) =
      f.stalkMap (unit f L (fieldSpecPoint k))
        ((Spec (CommRingCat.of k)).presheaf.germ (unit f L ⁻¹ᵁ U)
          (f (unit f L (fieldSpecPoint k))) hfe ((unit f L).app U s)) := by
    rw [Scheme.Hom.germ_stalkMap_apply]
    rfl
  rw [key, germ_eq_zero_of_mem_maximalIdeal_of_field, map_zero]
  rw [germ_mem_maximalIdeal_iff, ← Scheme.preimage_basicOpen, Scheme.Hom.mem_preimage, hue,
    ← germ_mem_maximalIdeal_iff]
  exact hb

/-- The first projection on the stalk at the pair of identity points. -/
noncomputable def π₁ := stalkMapOfEq (pullback.fst f f) (unitPair f L (fieldSpecPoint k))
  (unit f L (fieldSpecPoint k)) (fst_z f L)

/-- The second projection on the stalk at the pair of identity points. -/
noncomputable def π₂ := stalkMapOfEq (pullback.snd f f) (unitPair f L (fieldSpecPoint k))
  (unit f L (fieldSpecPoint k)) (snd_z f L)

/-- Multiplication on the stalk at the pair of identity points. -/
noncomputable def μ := stalkMapOfEq (mulMap f L) (unitPair f L (fieldSpecPoint k))
  (unit f L (fieldSpecPoint k)) (mulMap_z f L)

/-- The map on stalks induced by the first identity slice. -/
noncomputable def α := stalkMapOfEq (slice₁ f L) (unit f L (fieldSpecPoint k))
  (unitPair f L (fieldSpecPoint k)) (slice₁_e f L)

/-- The map on stalks induced by the second identity slice. -/
noncomputable def β := stalkMapOfEq (slice₂ f L) (unit f L (fieldSpecPoint k))
  (unitPair f L (fieldSpecPoint k)) (slice₂_e f L)

lemma α_π₁ (b) : α f L (π₁ f L b) = b := by
  rw [α, π₁, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₁_fst f L)
    (unit f L (fieldSpecPoint k)) (unit f L (fieldSpecPoint k)) _ rfl]
  exact stalkMapOfEq_id_apply _ _ b

lemma α_μ (b) : α f L (μ f L b) = b := by
  rw [α, μ, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₁_mulMap f L)
    (unit f L (fieldSpecPoint k)) (unit f L (fieldSpecPoint k)) _ rfl]
  exact stalkMapOfEq_id_apply _ _ b

lemma β_π₂ (b) : β f L (π₂ f L b) = b := by
  rw [β, π₂, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₂_snd f L)
    (unit f L (fieldSpecPoint k)) (unit f L (fieldSpecPoint k)) _ rfl]
  exact stalkMapOfEq_id_apply _ _ b

lemma β_μ (b) : β f L (μ f L b) = b := by
  rw [β, μ, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₂_mulMap f L)
    (unit f L (fieldSpecPoint k)) (unit f L (fieldSpecPoint k)) _ rfl]
  exact stalkMapOfEq_id_apply _ _ b

lemma f_unit_e : (f ≫ unit f L) (unit f L (fieldSpecPoint k)) =
    unit f L (fieldSpecPoint k) := by
  exact congrArg (fun m : Spec (CommRingCat.of k) ⟶ G =>
    m (fieldSpecPoint k)) (unit_f_assoc f L (unit f L))

lemma α_π₂ (b) (hb : b ∈ IsLocalRing.maximalIdeal _) : α f L (π₂ f L b) = 0 := by
  rw [α, π₂, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₁_snd f L)
    (unit f L (fieldSpecPoint k)) (unit f L (fieldSpecPoint k)) _ (f_unit_e f L)]
  exact stalkMapOfEq_f_unit_apply f L b hb _

lemma β_π₁ (b) (hb : b ∈ IsLocalRing.maximalIdeal _) : β f L (π₁ f L b) = 0 := by
  rw [β, π₁, stalkMapOfEq_comp_apply, stalkMapOfEq_congr (slice₂_fst f L)
    (unit f L (fieldSpecPoint k)) (unit f L (fieldSpecPoint k)) _ (f_unit_e f L)]
  exact stalkMapOfEq_f_unit_apply f L b hb _

lemma map_stalkMap_le_map_stalkMapOfEq (g : X ⟶ Y) (x : X) (y : Y) (h : g x = y) :
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g x))).map (g.stalkMap x).hom ≤
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).map (stalkMapOfEq g x y h).hom := by
  have hcomp : (stalkMapOfEq g x y h).hom =
      (g.stalkMap x).hom.comp (Y.presheaf.stalkSpecializes (specializes_of_eq h)).hom := rfl
  rw [hcomp, ← Ideal.map_map]
  refine Ideal.map_mono ?_
  intro t ht
  let e : Y.presheaf.stalk (g x) ≅ Y.presheaf.stalk y := Y.presheaf.stalkCongr (Inseparable.of_eq h)
  have hte : t = (Y.presheaf.stalkSpecializes (specializes_of_eq h)).hom (e.hom t) := by
    change t = (e.hom ≫ e.inv) t
    rw [Iso.hom_inv_id]; rfl
  rw [hte]
  refine Ideal.mem_map_of_mem _ ?_
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
  intro hu
  apply ht
  have := hu.map (Y.presheaf.stalkSpecializes (specializes_of_eq h)).hom
  rwa [← hte] at this

lemma maximalIdeal_le :
    IsLocalRing.maximalIdeal ((pullback f f).presheaf.stalk (unitPair f L
        (fieldSpecPoint k))) ≤
      (IsLocalRing.maximalIdeal _).map (π₁ f L).hom ⊔ (IsLocalRing.maximalIdeal _).map
          (π₂ f L).hom := by
  have hchild :=
    maximalIdeal_stalk_pullback_eq_map_stalkMap_fst_sup_map_stalkMap_snd_of_section
      f f (unit f L) (unit_f f L) (unit f L) (unit_f f L)
  refine (le_of_eq hchild).trans (sup_le_sup ?_ ?_)
  · exact map_stalkMap_le_map_stalkMapOfEq _ _ _ (fst_z f L)
  · exact map_stalkMap_le_map_stalkMapOfEq _ _ _ (snd_z f L)

end Identities

end FirstOrderGroupLaw

end AbelianVarieties.NOSProofs.GroupLawFirstJets

namespace GoodReductionJacobian.RelativeGroupLaw

universe u

open CategoryTheory.Limits hiding pair
open CategoryTheory AlgebraicGeometry NeronModelInfra
open _root_.GoodReductionJacobian
open AbelianVarieties.NOSProofs.GroupLawFirstJets.FirstOrderGroupLaw

theorem germ_mul_sub_fst_sub_snd_mem_maximalIdeal_sq
    {k : Type u} [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
        (L : RelativeGroupLaw k f)
    (U : G.Opens) (W : (pullback f f).Opens)
    (hWm : W ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
        pullback.condition.symm⟩).1 ⁻¹ᵁ U)
    (hW₁ : W ≤ pullback.fst f f ⁻¹ᵁ U) (hW₂ : W ≤ pullback.snd f f ⁻¹ᵁ U)
    (he : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (fieldSpecPoint k) ∈ U)
    (hee : pullback.lift (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (L.one (𝟙 (Spec
        (CommRingCat.of k)))).1 rfl
      (fieldSpecPoint k) ∈ W)
    (φ : Γ(G, U)) (hφ : (G.presheaf.germ U _ he).hom φ ∈ IsLocalRing.maximalIdeal
        (G.presheaf.stalk _)) :
    ((pullback f f).presheaf.germ W _ hee).hom
        (((L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f,
            pullback.condition.symm⟩).1.appLE U W hWm).hom φ
          - ((pullback.fst f f).appLE U W hW₁).hom φ - ((pullback.snd f f).appLE U W hW₂).hom φ)
      ∈ IsLocalRing.maximalIdeal ((pullback f f).presheaf.stalk _) ^ 2 := by
  change (pullback f f).presheaf.germ W (unitPair f L (fieldSpecPoint k)) hee
      ((mulMap f L).appLE U W hWm φ - (pullback.fst f f).appLE U W hW₁ φ -
        (pullback.snd f f).appLE U W hW₂ φ) ∈
    IsLocalRing.maximalIdeal ((pullback f f).presheaf.stalk (unitPair f L
        (fieldSpecPoint k))) ^ 2
  have hφ' : G.presheaf.germ U (unit f L (fieldSpecPoint k)) he φ ∈
      IsLocalRing.maximalIdeal _ := hφ
  rw [map_sub, map_sub,
    germ_appLE_eq_stalkMapOfEq (mulMap f L) U W hWm (unitPair f L (fieldSpecPoint k)) hee _
      (mulMap_z f L),
    germ_appLE_eq_stalkMapOfEq (pullback.fst f f) U W hW₁ (unitPair f L (fieldSpecPoint k))
      hee _ (fst_z f L),
    germ_appLE_eq_stalkMapOfEq (pullback.snd f f) U W hW₂ (unitPair f L (fieldSpecPoint k))
      hee _ (snd_z f L)]
  change μ f L _ - π₁ f L _ - π₂ f L _ ∈ _
  refine mem_maximalIdeal_sq_of_slices (π₁ f L).hom (π₂ f L).hom (α f L).hom (β f L).hom
    (maximalIdeal_le f L)
    (fun a ha ↦ stalkMapOfEq_mem_maximalIdeal _ _ _ _ a ha)
    (fun a ha ↦ stalkMapOfEq_mem_maximalIdeal _ _ _ _ a ha)
    (α_π₁ f L) (β_π₂ f L) (α_π₂ f L) (β_π₁ f L) ?_ ?_ ?_
  · refine Ideal.sub_mem _ (Ideal.sub_mem _ ?_ ?_) ?_ <;>
      exact stalkMapOfEq_mem_maximalIdeal _ _ _ _ _ hφ'
  · change α f L (μ f L _ - π₁ f L _ - π₂ f L _) = 0
    rw [map_sub, map_sub, α_μ, α_π₁, α_π₂ f L _ hφ', sub_self, sub_zero]
  · change β f L (μ f L _ - π₁ f L _ - π₂ f L _) = 0
    rw [map_sub, map_sub, β_μ, β_π₁ f L _ hφ', β_π₂, sub_zero, sub_self]

end GoodReductionJacobian.RelativeGroupLaw
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_eq_one_of_forall_act_jet_eq_of_subsingleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.JetFaithfulness

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open Topology

universe u

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace PartialAction
open _root_.GoodReductionJacobian.PartialAction
namespace JetFaithful
open _root_.GoodReductionJacobian.PartialAction
open _root_.GoodReductionJacobian

open AbelianVarieties.NOSProofs.InfinitesimalSections.AlgebraicGeometry.InfinitesimallyConstantH1
  (fst_injective_of_section subsingleton_primeSpectrum_quotient)

section OnePoint

variable {k : Type u} [Field k]

theorem isSchemeTheoreticallyDominant_ι {P S Y : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral P]
    (s : S ⟶ Spec (CommRingCat.of k)) (σ : Spec (CommRingCat.of k) ⟶ S) (hσ : σ ≫ s = 𝟙 _)
    [Subsingleton ↥S] (g : Y ⟶ pullback p s) [IsOpenImmersion g]
    (U : Y.Opens) (hU : (U : Set ↥Y).Nonempty) : IsSchemeTheoreticallyDominant U.ι := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  let q : Y ⟶ P := g ≫ pullback.fst p s
  have hqinj : Function.Injective q :=
    (fst_injective_of_section p s σ hσ).comp g.injective
  have hqopen : IsOpenMap q := q.isOpenMap
  let U₀ : P.Opens := ⟨q '' (U : Set ↥Y), hqopen _ U.isOpen⟩
  have hU₀ : ((U₀ : P.Opens) : Set ↥P).Nonempty := hU.image _
  have : IsDominant U₀.ι := by
    rw [isDominant_iff]
    rw [show ⇑U₀.ι = fun z => (U₀.ι : _) z from rfl]
    have : Set.range U₀.ι = (U₀ : Set ↥P) := Scheme.Opens.range_ι U₀
    rw [DenseRange, this]
    exact U₀.isOpen.dense hU₀
  have : IsSchemeTheoreticallyDominant U₀.ι := IsSchemeTheoreticallyDominant.of_isDominant _
  have H : IsSchemeTheoreticallyDominant (q ⁻¹ᵁ U₀).ι :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict q U₀)
  have hUeq : q ⁻¹ᵁ U₀ = U := by
    ext z
    constructor
    · rintro ⟨z', hz', e⟩
      rwa [← hqinj e]
    · intro hz
      exact ⟨z, hz, rfl⟩
  rwa [hUeq] at H

end OnePoint

section Jets

theorem exists_jet_factor {X P : Scheme.{u}} (π : X ⟶ P) (ξ : ↥X) (y : ↥P) (hy : π ξ = y)
    (n : ℕ) :
    ∃ g : Spec (CommRingCat.of (X.presheaf.stalk ξ ⧸
          IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n)) ⟶
        Spec (CommRingCat.of (P.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal
            (P.presheaf.stalk y) ^ n)),
      g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (P.presheaf.stalk y) ^ n))) ≫ P.fromSpecStalk y =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫ X.fromSpecStalk ξ ≫ π := by
  subst hy
  have hle : IsLocalRing.maximalIdeal (P.presheaf.stalk (π ξ)) ^ n ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n).comap (π.stalkMap ξ).hom := by
    refine le_trans (Ideal.pow_right_mono ?_ n) (Ideal.le_comap_pow _ n)
    intro a ha
    exact map_nonunit (π.stalkMap ξ).hom a ha
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (π.stalkMap ξ).hom hle)), ?_⟩
  have e1 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (π.stalkMap ξ).hom hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (P.presheaf.stalk (π ξ)) ^ n))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫ Spec.map (π.stalkMap ξ) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have e2 : Spec.map (π.stalkMap ξ) ≫ P.fromSpecStalk (π ξ) = X.fromSpecStalk ξ ≫ π :=
    Scheme.SpecMap_stalkMap_fromSpecStalk π
  calc _ = (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (π.stalkMap ξ).hom hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (P.presheaf.stalk (π ξ)) ^ n)))) ≫ P.fromSpecStalk (π ξ) :=
        (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫ Spec.map (π.stalkMap ξ)) ≫
          P.fromSpecStalk (π ξ) := e1 =≫ _
    _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫ (Spec.map (π.stalkMap ξ) ≫
          P.fromSpecStalk (π ξ)) := Category.assoc _ _ _
    _ = _ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫= e2

end Jets

section Law

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

theorem inv_natural (L : RelativeGroupLaw k f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) :=
  L.inv_natural t t' ψ hψ x

theorem eq_one_of_mul_eq (L : RelativeGroupLaw k f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x g : SchemeHomOver t f) (h : L.mul t x g = g) :
    x = L.one t := by
  calc x = L.mul t x (L.one t) := (L.mul_one t x).symm
    _ = L.mul t x (L.mul t g (L.inv t g)) := by rw [L.mul_inv_cancel]
    _ = L.mul t (L.mul t x g) (L.inv t g) := by rw [L.mul_assoc]
    _ = L.one t := by rw [h, L.mul_inv_cancel]

theorem irreducibleSpace_of_connectedSpace [IsAlgClosed k]
    (f : G ⟶ Spec (CommRingCat.of k)) [QuasiCompact f] [ConnectedSpace ↥G] [Smooth f]
    (L : RelativeGroupLaw k f) : IrreducibleSpace ↥G := by
  open AbelianVarieties.NOSProofs.PartialActionFixedPoints in
    exact GoodReductionJacobian.PartialAction.EverythingActs.irreducibleSpace_of_connectedSpace f L

end Law

section Main

variable {k : Type u} [Field k]

theorem main [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace ↥G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (x : SchemeHomOver t f)
    (hx : ∀ (n : ℕ)
      (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k)) ⧸
          IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ n))
          ⟶ P),
      jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ n))) ≫
        P.fromSpecStalk _ →
      ∃ hd : a.Defined
          (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
          (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
        (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) :
    x = L.one t := by
  rcases isEmpty_or_nonempty ↥T with hT | ⟨⟨τ₀⟩⟩
  · exact Subtype.ext ((isInitialOfIsEmpty (X := T)).hom_ext _ _)
  have : IrreducibleSpace ↥G := irreducibleSpace_of_connectedSpace f L
  have : JacobsonSpace ↥G := LocallyOfFiniteType.jacobsonSpace f
  have hτ₀c : IsClosed ({τ₀} : Set ↥T) := by
    have : ({τ₀} : Set ↥T) = Set.univ := Set.eq_univ_of_forall fun z => Subsingleton.elim z τ₀
    rw [this]; exact isClosed_univ
  let τ : Spec (CommRingCat.of k) ⟶ T := pointOfClosedPoint t τ₀ hτ₀c
  have hτt : τ ≫ t = 𝟙 _ := pointOfClosedPoint_comp t τ₀ hτ₀c
  set y : ↥P := P₀.1.base (fieldSpecPoint k) with hy_def
  set O := P.presheaf.stalk y with hO_def
  let X' : Scheme.{u} := pullback p t
  let Φ : X' ⟶ pullback f p :=
    pullback.lift (pullback.snd p t ≫ x.1) (pullback.fst p t)
      (by rw [Category.assoc, x.2]; exact pullback.condition.symm)
  have hΦ_fst : Φ ≫ pullback.fst f p = pullback.snd p t ≫ x.1 := pullback.lift_fst _ _ _
  have hΦ_snd : Φ ≫ pullback.snd f p = pullback.fst p t := pullback.lift_snd _ _ _
  let D : X'.Opens := Φ ⁻¹ᵁ a.dom
  let Xd : Scheme.{u} := D
  let Φ' : Xd ⟶ (a.dom : Scheme.{u}) := Φ ∣_ a.dom
  have hΦ' : Φ' ≫ a.dom.ι = D.ι ≫ Φ := morphismRestrict_ι Φ a.dom
  obtain ⟨actx, hactx⟩ : ∃ m : Xd ⟶ P, m = Φ' ≫ a.hom := ⟨_, rfl⟩
  obtain ⟨prx, hprx⟩ : ∃ m : Xd ⟶ P, m = D.ι ≫ pullback.fst p t := ⟨_, rfl⟩
  have hover : actx ≫ p = prx ≫ p := by
    rw [hactx, hprx, Category.assoc, a.hom_comp, ← Category.assoc Φ', hΦ', Category.assoc,
      Category.assoc, ← Category.assoc Φ, hΦ_snd]
  have hread : ∀ {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)}
      (γ : SchemeHomOver t' f) (z : SchemeHomOver t' p) (ζ : T' ⟶ X')
      (hζ : ζ ≫ Φ = pair γ z) (hd : a.Defined γ z),
      ∃ ζ' : T' ⟶ Xd, ζ' ≫ D.ι = ζ ∧ (a.act γ z hd).1 = ζ' ≫ actx := by
    intro T' t' γ z ζ hζ hd
    have hr : Set.range ζ ⊆ (D : Set ↥X') := by
      rintro _ ⟨w, rfl⟩
      change Φ (ζ w) ∈ (a.dom : Set ↥(pullback f p))
      rw [← Scheme.Hom.comp_apply, hζ]
      exact hd ⟨w, rfl⟩
    let ζ' : T' ⟶ Xd := IsOpenImmersion.lift D.ι ζ (by rw [Scheme.Opens.range_ι]; exact hr)
    have hζ' : ζ' ≫ D.ι = ζ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨ζ', hζ', ?_⟩
    have hl : a.liftDom γ z hd = ζ' ≫ Φ' := by
      rw [← cancel_mono a.dom.ι, liftDom_ι, Category.assoc, hΦ', ← Category.assoc, hζ', hζ]
    rw [act_coe, hl, Category.assoc, hactx]
  have : IsLocallyNoetherian X' :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p t ≫ t)
  have : IsLocallyNoetherian Xd := inferInstance
  have hdense : ∀ U : Xd.Opens, (U : Set ↥Xd).Nonempty → IsSchemeTheoreticallyDominant U.ι :=
    fun U hU => isSchemeTheoreticallyDominant_ι p t τ hτt D.ι U hU
  let e₀ : O ⟶ CommRingCat.of k := Scheme.stalkClosedPointTo P₀.1
  have : IsLocalHom e₀.hom :=
    Scheme.isLocalHom_stalkClosedPointTo' P₀.1
  have he₀ : ∀ b ∈ IsLocalRing.maximalIdeal O, e₀.hom b = 0 := by
    intro b hb
    have h := map_nonunit e₀.hom b hb
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at h
  have hq : ∀ b ∈ IsLocalRing.maximalIdeal O ^ 1, e₀.hom b = 0 := by
    intro b hb
    exact he₀ b (Ideal.pow_le_self one_ne_zero hb)
  let q₁ : (O ⧸ IsLocalRing.maximalIdeal O ^ 1) →+* k := Ideal.Quotient.lift _ e₀.hom hq
  obtain ⟨j1, hj1⟩ : ∃ j : Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O ^ 1)) ⟶ P,
      j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ 1))) ≫
        P.fromSpecStalk y := ⟨_, rfl⟩
  have hq₁ : Spec.map (CommRingCat.ofHom q₁) ≫ j1 = P₀.1 := by
    have e1 : Spec.map (CommRingCat.ofHom q₁) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ 1))) =
        Spec.map e₀ := by
      rw [← Spec.map_comp]
      congr 1
    calc Spec.map (CommRingCat.ofHom q₁) ≫ j1
        = Spec.map (CommRingCat.ofHom q₁) ≫ (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ 1))) ≫ P.fromSpecStalk y) := _ ≫= hj1
      _ = (Spec.map (CommRingCat.ofHom q₁) ≫ Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ 1)))) ≫ P.fromSpecStalk y :=
          (Category.assoc _ _ _).symm
      _ = Spec.map e₀ ≫ P.fromSpecStalk y := e1 =≫ _
      _ = P₀.1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk P₀.1
  have hw₁ : 𝟙 T ≫ t = (t ≫ Spec.map (CommRingCat.ofHom q₁)) ≫ (j1 ≫ p) := by
    rw [Category.id_comp, Category.assoc, ← Category.assoc (Spec.map _), hq₁, P₀.2,
      Category.comp_id]
  let lam1 : T ⟶ pullback t (j1 ≫ p) := pullback.lift (𝟙 T) (t ≫ Spec.map
      (CommRingCat.ofHom q₁)) hw₁
  obtain ⟨hd₁, -⟩ := hx 1 j1 hj1
  let P₀T : SchemeHomOver t p := GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀
  have hP₀T : P₀T.1 = t ≫ P₀.1 := rfl
  have hdef₀ : a.Defined x P₀T := by
    have hpair : pair x P₀T = lam1 ≫ pair
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (j1 ≫ p)) rfl x :
          SchemeHomOver (pullback.fst t (j1 ≫ p) ≫ t) f)
        (⟨pullback.snd t (j1 ≫ p) ≫ j1, by rw [Category.assoc, pullback.condition]⟩ :
          SchemeHomOver (pullback.fst t (j1 ≫ p) ≫ t) p) := by
      apply pullback.hom_ext
      · simp only [pair, pullback.lift_fst, Category.assoc,
          GoodReductionJacobian.schemeHomOverComp_coe]
        rw [← Category.assoc, pullback.lift_fst, Category.id_comp]
      · simp only [pair, pullback.lift_snd, Category.assoc]
        rw [← Category.assoc lam1, pullback.lift_snd, Category.assoc, hq₁, hP₀T]
    intro w hw
    rw [hpair, Scheme.Hom.comp_base] at hw
    obtain ⟨w', rfl⟩ := hw
    exact hd₁ ⟨lam1 w', rfl⟩
  let ζ₀ : T ⟶ X' := pullback.lift (t ≫ P₀.1) (𝟙 T)
    (by rw [Category.assoc, P₀.2, Category.comp_id, Category.id_comp])
  have hζ₀Φ : ζ₀ ≫ Φ = pair x P₀T := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦ_fst, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        pullback.lift_fst]
    · rw [Category.assoc, hΦ_snd, pullback.lift_fst, pullback.lift_snd, hP₀T]
  obtain ⟨ζ₀', hζ₀', -⟩ := hread x P₀T ζ₀ hζ₀Φ hdef₀
  let ξ : ↥Xd := ζ₀' τ₀
  have hξ : prx ξ = y := by
    change prx (ζ₀' τ₀) = y
    rw [← Scheme.Hom.comp_apply, hprx, ← Category.assoc, hζ₀', pullback.lift_fst,
      Scheme.Hom.comp_apply, hy_def]
    congr 1
    exact Subsingleton.elim _ _
  have hjets : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Xd.presheaf.stalk ξ) ^ n))) ≫ Xd.fromSpecStalk ξ ≫ actx =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Xd.presheaf.stalk ξ) ^ n))) ≫ Xd.fromSpecStalk ξ ≫ prx := by
    intro n
    obtain ⟨g, hg⟩ := exists_jet_factor prx ξ y hξ n
    obtain ⟨jn, hjn⟩ : ∃ j : Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O ^ n)) ⟶ P,
        j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫
          P.fromSpecStalk y := ⟨_, rfl⟩
    obtain ⟨sn, hsn⟩ : ∃ s : Spec (CommRingCat.of (Xd.presheaf.stalk ξ ⧸
        IsLocalRing.maximalIdeal (Xd.presheaf.stalk ξ) ^ n)) ⟶ Xd,
        s = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Xd.presheaf.stalk ξ) ^ n))) ≫ Xd.fromSpecStalk ξ := ⟨_, rfl⟩
    have hg' : g ≫ jn = sn ≫ prx := by rw [hjn, hsn, Category.assoc]; exact hg
    have hwσ : (sn ≫ D.ι ≫ pullback.snd p t) ≫ t = g ≫ (jn ≫ p) := by
      rw [← Category.assoc g, hg', hprx]
      simp only [Category.assoc]
      rw [pullback.condition]
    let σ : _ ⟶ pullback t (jn ≫ p) := pullback.lift (sn ≫ D.ι ≫ pullback.snd p t) g hwσ
    obtain ⟨hd, hact⟩ := hx n jn hjn
    have hpair : σ ≫ pair
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
          SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
        (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
          SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p) = sn ≫ D.ι ≫ Φ := by
      apply pullback.hom_ext
      · simp only [pair, Category.assoc, pullback.lift_fst,
          GoodReductionJacobian.schemeHomOverComp_coe]
        rw [← Category.assoc σ, pullback.lift_fst, hΦ_fst]
        simp only [Category.assoc]
      · simp only [pair, Category.assoc, pullback.lift_snd]
        rw [← Category.assoc σ, pullback.lift_snd, hg', hΦ_snd, hprx]
    have hl : σ ≫ a.liftDom _ _ hd = sn ≫ Φ' := by
      rw [← cancel_mono a.dom.ι, Category.assoc, liftDom_ι, hpair, Category.assoc, hΦ']
    have key : sn ≫ actx = sn ≫ prx := by
      calc sn ≫ actx = (sn ≫ Φ') ≫ a.hom := by rw [hactx, Category.assoc]
        _ = σ ≫ (a.act _ _ hd).1 := by rw [← hl, act_coe, Category.assoc]
        _ = σ ≫ pullback.snd t (jn ≫ p) ≫ jn := by rw [hact]
        _ = g ≫ jn := by rw [← Category.assoc, pullback.lift_snd]
        _ = sn ≫ prx := hg'
    rw [hsn, Category.assoc, Category.assoc] at key
    exact key
  have hagree : actx = prx :=
    eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
      hdense actx prx p hover ξ hjets
  let ek : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := 𝟙 _
  let x₀ : SchemeHomOver ek f := ⟨τ ≫ x.1, by rw [Category.assoc, x.2, hτt]⟩
  let x₀G : SchemeHomOver f f := GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) x₀
  let uG : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩
  let ψ : G ⟶ G := (L.mul f x₀G uG).1
  have hψ : ∀ z : SchemeHomOver ek f,
      GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.mul f x₀G uG) = L.mul ek x₀ z := by
    intro z
    have h1 : GoodReductionJacobian.schemeHomOverComp z.1 z.2 x₀G = x₀ := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, x₀G]
      rw [← Category.assoc, z.2, Category.id_comp]
    have h2 : GoodReductionJacobian.schemeHomOverComp z.1 z.2 uG = z :=
      Subtype.ext (Category.comp_id _)
    rw [L.mul_natural, h1, h2]
  have hψpt : ∀ z : SchemeHomOver ek f,
      ψ (z.1 (fieldSpecPoint k)) = (L.mul ek x₀ z).1 (fieldSpecPoint k) := by
    intro z
    exact congrArg (fun φ : SchemeHomOver ek f => φ.1 (fieldSpecPoint k)) (hψ z)
  have hVne : ((V : G.Opens) : Set ↥G).Nonempty := by
    rw [← Scheme.Opens.range_ι V]
    exact Set.range_nonempty _
  obtain ⟨g₁, hg₁V, hg₁c⟩ := nonempty_inter_closedPoints hVne V.isOpen.isLocallyClosed
  let v₁ : SchemeHomOver ek f := ⟨pointOfClosedPoint f g₁ hg₁c, pointOfClosedPoint_comp f g₁ hg₁c⟩
  have hv₁pt : v₁.1 (fieldSpecPoint k) = g₁ :=
      pointOfClosedPoint_apply f g₁ hg₁c _
  have hU : ((V ⊓ ψ ⁻¹ᵁ V : G.Opens) : Set ↥G).Nonempty := by
    have h2 : ((ψ ⁻¹ᵁ V : G.Opens) : Set ↥G).Nonempty := by
      refine ⟨(L.mul ek (L.inv ek x₀) v₁).1 (fieldSpecPoint k), ?_⟩
      change ψ _ ∈ V
      rw [hψpt, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul, hv₁pt]
      exact hg₁V
    exact nonempty_preirreducible_inter V.isOpen (ψ ⁻¹ᵁ V).isOpen hVne h2
  obtain ⟨g₀, hg₀U, hg₀c⟩ := nonempty_inter_closedPoints hU (V ⊓ ψ ⁻¹ᵁ V).isOpen.isLocallyClosed
  let v₀ : SchemeHomOver ek f := ⟨pointOfClosedPoint f g₀ hg₀c, pointOfClosedPoint_comp f g₀ hg₀c⟩
  have hv₀pt : v₀.1 (fieldSpecPoint k) = g₀ :=
      pointOfClosedPoint_apply f g₀ hg₀c _
  have hv₀V : v₀.1 (fieldSpecPoint k) ∈ V :=
      by rw [hv₀pt]; exact hg₀U.1
  have hxv₀V : (L.mul ek x₀ v₀).1 (fieldSpecPoint k) ∈ V := by
    rw [← hψpt, hv₀pt]
    exact hg₀U.2
  let vT : SchemeHomOver t f := GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) v₀
  let wT : SchemeHomOver t f := L.mul t x vT
  have hτx : GoodReductionJacobian.schemeHomOverComp τ hτt x = x₀ := Subtype.ext rfl
  have hτv : GoodReductionJacobian.schemeHomOverComp τ hτt vT = v₀ := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, vT]
    rw [← Category.assoc, hτt, Category.id_comp]
  have hτw : GoodReductionJacobian.schemeHomOverComp τ hτt wT = L.mul ek x₀ v₀ := by
    simp only [wT]
    rw [L.mul_natural, hτx, hτv]
  have hval : ∀ (g : SchemeHomOver t f) (z : ↥T),
      g.1 z = (GoodReductionJacobian.schemeHomOverComp τ hτt g).1 (fieldSpecPoint k) := by
    intro g z
    exact congrArg (fun q : T => g.1 q) (Subsingleton.elim z (τ (fieldSpecPoint k)))
  have hvT : Set.range vT.1 ⊆ (V : Set ↥G) := by
    rintro _ ⟨z, rfl⟩
    rw [hval, hτv]; exact hv₀V
  have hwT : Set.range wT.1 ⊆ (V : Set ↥G) := by
    rintro _ ⟨z, rfl⟩
    rw [hval, hτw]; exact hxv₀V
  let v : SchemeHomOver t (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift V.ι vT.1 (by rw [Scheme.Opens.range_ι]; exact hvT), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact vT.2⟩
  let w : SchemeHomOver t (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift V.ι wT.1 (by rw [Scheme.Opens.range_ι]; exact hwT), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact wT.2⟩
  have hvι : NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) = vT :=
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hwι : NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) = wT :=
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hvw : NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul t x (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
    rw [hwι, hvι]
  obtain ⟨hd, hcomp⟩ := hc t x v w hvw
  let ζv : T ⟶ X' := pullback.lift (v.1 ≫ ι) (𝟙 T)
    (by rw [Category.assoc, hι, ← Category.assoc, IsOpenImmersion.lift_fac, Category.id_comp]
        exact vT.2)
  have hζvΦ : ζv ≫ Φ = pair x (modelPoint ι hι v) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦ_fst, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        pullback.lift_fst]
    · rw [Category.assoc, hΦ_snd, pullback.lift_fst, pullback.lift_snd, modelPoint_coe]
  obtain ⟨ζv', hζv', hactv⟩ := hread x (modelPoint ι hι v) ζv hζvΦ hd
  have htriv : (a.act x (modelPoint ι hι v) hd).1 = v.1 ≫ ι := by
    rw [hactv, hagree, hprx, ← Category.assoc, hζv', pullback.lift_fst]
  have hwv : w.1 = v.1 := by
    rw [← cancel_mono ι, ← htriv, hcomp, modelPoint_coe]
  have hwTvT : L.mul t x vT = vT := by
    change wT = vT
    rw [← hwι, ← hvι, show w = v from Subtype.ext hwv]
  exact eq_one_of_mul_eq L t x vT hwTvT

end Main

end GoodReductionJacobian.PartialAction.JetFaithful

end AbelianVarieties.NOSProofs.JetFaithfulness

namespace GoodReductionJacobian.PartialAction

universe u

open CategoryTheory.Limits hiding pair
open CategoryTheory AlgebraicGeometry NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.GoodReductionJacobian.PartialAction
open AbelianVarieties.NOSProofs.JetFaithfulness.GoodReductionJacobian.PartialAction.JetFaithful

theorem eq_one_of_forall_act_jet_eq_of_subsingleton
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (x : SchemeHomOver t f)
    (hx : ∀ (n : ℕ)
      (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k)) ⧸
          IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ n))
          ⟶ P),
      jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ n))) ≫
        P.fromSpecStalk _ →
      ∃ hd : a.Defined
          (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
          (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
        (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) :
    x = L.one t :=
  main f L p V ι hι a hc P₀ t x hx

end GoodReductionJacobian.PartialAction
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_PartialAction_exists_generalLinearGroup_jet_of_forall_defined_act_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.JetRepresentations

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits hiding pair
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open TensorProduct

universe u

namespace GoodReductionJacobian
open _root_.GoodReductionJacobian
namespace PartialAction
open _root_.GoodReductionJacobian.PartialAction
namespace LinearJets
open _root_.GoodReductionJacobian.PartialAction
open _root_.GoodReductionJacobian

section Blocks

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Place a finite family of matrices into a single block-diagonal matrix. -/
noncomputable def blockHom {m : ℕ} (d : Fin m → ℕ) :
    (∀ i : Fin m, Matrix (Fin (d i)) (Fin (d i)) R) →+* Matrix (Fin (∑ i, d i)) (Fin (∑ i,
        d i)) R :=
  ((Matrix.reindexAlgEquiv R R (finSigmaFinEquiv (n := d))).toRingEquiv.toRingHom).comp
    (Matrix.blockDiagonal'RingHom (fun i => Fin (d i)) R)

theorem blockHom_apply {m : ℕ} (d : Fin m → ℕ) (M : ∀ i : Fin m, Matrix (Fin (d i)) (Fin (d i)) R) :
    blockHom d M = Matrix.reindex (finSigmaFinEquiv (n := d)) (finSigmaFinEquiv (n := d))
      (Matrix.blockDiagonal' M) := rfl

theorem blockHom_injective {m : ℕ} (d : Fin m → ℕ) : Function.Injective (blockHom (R := R) d) := by
  intro M N h
  rw [blockHom_apply, blockHom_apply] at h
  exact Matrix.blockDiagonal'_injective ((Matrix.reindex _ _).injective h)

theorem blockHom_map {m : ℕ} (d : Fin m → ℕ) (φ : R →+* S)
    (M : ∀ i : Fin m, Matrix (Fin (d i)) (Fin (d i)) R) :
    (blockHom d M).map φ = blockHom d (fun i => (M i).map φ) := by
  rw [blockHom_apply, blockHom_apply]
  have h : (Matrix.blockDiagonal' M).map φ = Matrix.blockDiagonal' fun i => (M i).map φ :=
    Matrix.blockDiagonal'_map M φ (map_zero φ)
  ext a b
  exact congrFun (congrFun h _) _

/-- Combine a finite family of invertible matrices into one invertible block matrix. -/
noncomputable def blockGL {m : ℕ} (d : Fin m → ℕ) (M : ∀ i : Fin m, GL (Fin (d i)) R) :
    GL (Fin (∑ i, d i)) R :=
  Units.map (blockHom d).toMonoidHom (MulEquiv.piUnits.symm M)

theorem blockGL_val {m : ℕ} (d : Fin m → ℕ) (M : ∀ i : Fin m, GL (Fin (d i)) R) :
    (blockGL d M : Matrix _ _ R) = blockHom d (fun i => (M i : Matrix _ _ R)) := rfl

theorem blockGL_mul {m : ℕ} (d : Fin m → ℕ) (M N : ∀ i : Fin m, GL (Fin (d i)) R) :
    blockGL d (M * N) = blockGL d M * blockGL d N := by
  simp only [blockGL, map_mul]

theorem blockGL_eq_one_iff {m : ℕ} (d : Fin m → ℕ) (M : ∀ i : Fin m, GL (Fin (d i)) R) :
    blockGL d M = 1 ↔ ∀ i, M i = 1 := by
  constructor
  · intro h i
    have hv : (blockGL d M).val = (1 : GL (Fin (∑ i, d i)) R).val := by
      rw [h]
    rw [blockGL_val, Units.val_one, ← map_one (blockHom (R := R) d)] at hv
    have h2 := congrFun (blockHom_injective d hv) i
    exact Units.ext h2
  · intro h
    have : M = 1 := funext h
    subst this
    simp only [blockGL, map_one]

theorem blockGL_map {m : ℕ} (d : Fin m → ℕ) (φ : R →+* S) (M : ∀ i : Fin m, GL (Fin (d i)) R) :
    Matrix.GeneralLinearGroup.map φ (blockGL d M) =
      blockGL d (fun i => Matrix.GeneralLinearGroup.map φ (M i)) := by
  apply Units.ext
  have h1 : (Matrix.GeneralLinearGroup.map φ (blockGL d M)).val = (blockGL d M).val.map φ := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  have h2 : (fun i => (Matrix.GeneralLinearGroup.map φ (M i)).val) =
      fun i => (M i).val.map φ := by
    funext i
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  rw [h1, blockGL_val, blockGL_val, h2, blockHom_map]

end Blocks

open AbelianVarieties.NOSProofs.InfinitesimalSections.AlgebraicGeometry.InfinitesimallyConstantH1
  (fst_injective_of_section subsingleton_primeSpectrum_quotient)

section OnePoint

variable {k : Type u} [Field k]

end OnePoint

section Coords

variable {k : Type u} [Field k]

theorem coords_bijective {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace ↥Y] [QuasiSeparatedSpace ↥Y]
    (A : Type u) [CommRing A] [Algebra k A] {ι : Type} [Fintype ι] (b : Module.Basis ι k A) :
    Function.Bijective (fun c : ι → Γ(Y, ⊤) => ∑ i,
      (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom (c i) *
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (b i))) := by
  set ΓY : Type u := Γ(Y, ⊤) with hΓY
  let algY : Algebra k ΓY := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ y.appTop).hom.toAlgebra
  have H : IsPushout (CommRingCat.ofHom (algebraMap k A)) (CommRingCat.ofHom (algebraMap k ΓY))
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop)
      (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop :=
    AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat y A
  let ε : CommRingCat.of (A ⊗[k] ΓY) ≅ Γ(pullback y (Spec.map (CommRingCat.ofHom
      (algebraMap k A))), ⊤) :=
    IsPushout.isoIsPushout _ _ (CommRingCat.isPushout_tensorProduct k A ΓY) H
  let εr : A ⊗[k] ΓY →+* Γ(pullback y (Spec.map (CommRingCat.ofHom (algebraMap k A))), ⊤) :=
    ε.hom.hom
  have hεbij : Function.Bijective εr := ε.commRingCatIsoToRingEquiv.bijective
  have hεl : ∀ a : A, εr (a ⊗ₜ 1) =
      (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) := by
    intro a
    have h := IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct k A ΓY) H
    have h' := congr($(h).hom a)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at h'
    exact h'
  have hεr' : ∀ s : ΓY, εr (1 ⊗ₜ s) =
      (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom s := by
    intro s
    have h := IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct k A ΓY) H
    have h' := congr($(h).hom s)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at h'
    exact h'
  let bY : Module.Basis ι ΓY (ΓY ⊗[k] A) := Algebra.TensorProduct.basis ΓY b
  let sw : ΓY ⊗[k] A ≃ₐ[k] A ⊗[k] ΓY := Algebra.TensorProduct.comm k ΓY A
  have hfun : (fun c : ι → ΓY => ∑ i,
      (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom (c i) *
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k A)))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (b i))) =
      fun c => εr (sw (bY.equivFun.symm c)) := by
    funext c
    rw [Module.Basis.equivFun_symm_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : c i • bY i = c i ⊗ₜ[k] b i := by
      simp only [bY, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul,
          mul_one]
    rw [h1]
    have h2 : sw (c i ⊗ₜ[k] b i) = b i ⊗ₜ[k] c i := rfl
    have hsplit : b i ⊗ₜ[k] c i = (b i ⊗ₜ[k] (1 : ΓY)) * ((1 : A) ⊗ₜ[k] c i) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h2, hsplit, map_mul, hεl, hεr', mul_comm]
  rw [hfun]
  exact hεbij.comp (sw.bijective.comp bY.equivFun.symm.bijective)

end Coords

section Precomp

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

theorem defined_of_pair_eq (a : PartialAction k f p)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (z : SchemeHomOver t p) (hd : a.Defined γ z)
    (γ' : SchemeHomOver t' f) (z' : SchemeHomOver t' p) (θ : T' ⟶ T)
    (h : pair γ' z' = θ ≫ pair γ z) : a.Defined γ' z' := by
  intro w hw
  rw [h, Scheme.Hom.comp_base] at hw
  obtain ⟨w', rfl⟩ := hw
  exact hd ⟨θ w', rfl⟩

theorem act_coe_of_pair_eq (a : PartialAction k f p)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (z : SchemeHomOver t p) (hd : a.Defined γ z)
    (γ' : SchemeHomOver t' f) (z' : SchemeHomOver t' p) (θ : T' ⟶ T)
    (h : pair γ' z' = θ ≫ pair γ z) (hd' : a.Defined γ' z') :
    (a.act γ' z' hd').1 = θ ≫ (a.act γ z hd).1 := by
  have hl : a.liftDom γ' z' hd' = θ ≫ a.liftDom γ z hd := by
    rw [← cancel_mono a.dom.ι, liftDom_ι, Category.assoc, liftDom_ι, h]
  rw [act_coe, act_coe, hl, Category.assoc]

theorem act_coe_congr (a : PartialAction k f p)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (z₁ z₂ : SchemeHomOver t p) (h : z₁ = z₂)
    (h₁ : a.Defined γ z₁) (h₂ : a.Defined γ z₂) :
    (a.act γ z₁ h₁).1 = (a.act γ z₂ h₂).1 := by
  subst h; rfl

theorem pair_comp {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec
    (CommRingCat.of k)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (γ : SchemeHomOver t f) (z : SchemeHomOver t p) :
    pair (GoodReductionJacobian.schemeHomOverComp ψ hψ γ)
        (GoodReductionJacobian.schemeHomOverComp ψ hψ z) =
      ψ ≫ pair γ z := by
  apply pullback.hom_ext
  · simp only [pair, pullback.lift_fst, Category.assoc, GoodReductionJacobian.schemeHomOverComp_coe]
  · simp only [pair, pullback.lift_snd, Category.assoc, GoodReductionJacobian.schemeHomOverComp_coe]

end Precomp

section Small

theorem comp_appTop_apply {X Y Z : Scheme.{u}} (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (s : Γ(Z, ⊤)) :
    (g₁ ≫ g₂).appTop.hom s = g₁.appTop.hom (g₂.appTop.hom s) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem sum_swap {R : Type u} [CommRing R] {ι : Type} [Fintype ι] (x : ι → R) (y : ι → ι → R)
    (s : ι → R) : ∑ i, x i * ∑ l, y l i * s l = ∑ l, (∑ i, y l i * x i) * s l := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sum_one_apply_mul {R : Type u} [CommRing R] {d : ℕ} (s : Fin d → R) (j : Fin d)
    {S : Type u} [CommRing S] (ψ : S →+* R) :
    ∑ i, ψ ((1 : Matrix (Fin d) (Fin d) S) i j) * s i = s j := by
  rw [Finset.sum_eq_single j]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro i _ hij
    rw [Matrix.one_apply_ne hij, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

end Small

section MainPos

variable {k : Type u} [Field k]

theorem main_zero {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    (a : PartialAction k f p)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p) :
    ∃ (d : ℕ) (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin d) Γ(T, ⊤)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ t (L.mul t x y) = ρ t x * ρ t y) ∧
      (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base
                (fieldSpecPoint k))) ^ 0))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ 0))) ≫
        P.fromSpecStalk _ →
        ρ t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by
  refine ⟨0, fun _ _ => 1, fun _ _ _ => (mul_one _).symm, fun _ _ _ _ _ => (map_one _).symm, ?_⟩
  intro T t x jn hjn _
  have : Subsingleton (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k)) ⧸
      IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  have hE : IsEmpty (PrimeSpectrum (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k)) ⧸
      IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ 0)) :=
    inferInstance
  have : IsEmpty ↥(pullback t (jn ≫ p)) := @Function.isEmpty _ _ hE (pullback.snd t (jn ≫ p))
  refine ⟨?_, (isInitialOfIsEmpty (X := pullback t (jn ≫ p))).hom_ext _ _⟩
  rintro _ ⟨w, rfl⟩
  exact isEmptyElim w

/-- An action on a finite affine jet induces a natural general linear representation.
The inputs are the already constructed jet action and its restriction formula. -/
private theorem representationOfFiniteJet {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (A : Type u) [CommRing A] [Algebra k A] (dA : ℕ) (b : Module.Basis (Fin dA) k A)
    (sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (hsA : sA = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (jA : Spec (CommRingCat.of A) ⟶ P) [Mono jA] (hjs : jA ≫ p = sA)
    (β : pullback f sA ⟶ Spec (CommRingCat.of A))
    (hβs : β ≫ sA = pullback.fst f sA ≫ f)
    (hθw : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)), βT ≫ sA = t → γ.1 ≫ f = βT ≫ sA)
    (hzw : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
      (βT : T ⟶ Spec (CommRingCat.of A)), βT ≫ sA = t → (βT ≫ jA) ≫ p = t)
    (S1 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t),
      a.Defined γ ⟨βT ≫ jA, hzw βT hβT⟩)
    (S2 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t)
      (hd : a.Defined γ ⟨βT ≫ jA, hzw βT hβT⟩),
      (a.act γ ⟨βT ≫ jA, hzw βT hβT⟩ hd).1 = (pullback.lift γ.1 βT (hθw γ βT hβT) ≫ β) ≫ jA)
    : ∃ (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin dA) Γ(T, ⊤)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ t (L.mul t x y) = ρ t x * ρ t y) ∧
      (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        ρ t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jA ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jA ≫ p) ≫ t) f)
            (⟨pullback.snd t (jA ≫ p) ≫ jA, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jA ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jA ≫ p) ≫ jA) := by
  have : CompactSpace ↥G := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace ↥G := quasiSeparatedSpace_of_quasiSeparated f
  let bt : Fin dA → Γ(Spec (CommRingCat.of A), ⊤) := fun i =>
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (b i)
  have hsc : ∀ r : k, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (algebraMap k A r) =
      sA.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r) := by
    intro r
    have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k A))
    rw [← hsA] at h
    exact congr($(h).hom r)
  have hbt : ∀ s : Γ(Spec (CommRingCat.of A), ⊤), s = ∑ i,
      sA.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
        (b.repr ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s) i)) * bt i := by
    intro s
    have h1 : s = (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s) := by
      change s = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ (Scheme.ΓSpecIso
          (CommRingCat.of A)).inv).hom s
      rw [Iso.hom_inv_id]; rfl
    conv_lhs => rw [h1, ← b.sum_repr ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom s)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, hsc]
  have hΘG := coords_bijective f A b
  rw [← hsA] at hΘG
  let ΘG : (Fin dA → Γ(G, ⊤)) ≃ Γ(pullback f sA, ⊤) := Equiv.ofBijective _ hΘG
  let c : Matrix (Fin dA) (Fin dA) Γ(G, ⊤) := fun i j => ΘG.symm (β.appTop.hom (bt j)) i
  have hc : ∀ j, β.appTop.hom (bt j) = ∑ i, (pullback.fst f sA).appTop.hom (c i j) *
      (pullback.snd f sA).appTop.hom (bt i) := by
    intro j
    exact (ΘG.apply_symm_apply (β.appTop.hom (bt j))).symm
  have S2s : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t),
      (pullback.lift γ.1 βT (hθw γ βT hβT) ≫ β) ≫ sA = t := by
    intro T t γ βT hβT
    rw [Category.assoc, hβs, ← Category.assoc, pullback.lift_fst, γ.2]
  have S3 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t) (j : Fin dA),
      (pullback.lift γ.1 βT (hθw γ βT hβT) ≫ β).appTop.hom (bt j) =
        ∑ i, γ.1.appTop.hom (c i j) * βT.appTop.hom (bt i) := by
    intro T t γ βT hβT j
    rw [comp_appTop_apply, hc j, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← comp_appTop_apply, ← comp_appTop_apply, pullback.lift_fst, pullback.lift_snd]
  let f₂ : pullback f f ⟶ Spec (CommRingCat.of k) := pullback.fst f f ≫ f
  have : CompactSpace ↥(pullback f f) := QuasiCompact.compactSpace_of_compactSpace f₂
  have : QuasiSeparatedSpace ↥(pullback f f) := quasiSeparatedSpace_of_quasiSeparated f₂
  let p₁ : SchemeHomOver f₂ f := ⟨pullback.fst f f, rfl⟩
  let p₂ : SchemeHomOver f₂ f := ⟨pullback.snd f f, pullback.condition.symm⟩
  obtain ⟨μ, hμ⟩ : ∃ m : pullback f f ⟶ G, m = (L.mul f₂ p₁ p₂).1 := ⟨_, rfl⟩
  have hΘW := coords_bijective f₂ A b
  rw [← hsA] at hΘW
  have E3 : ∀ l j : Fin dA, μ.appTop.hom (c l j) =
      ∑ i, (pullback.snd f f).appTop.hom (c l i) * (pullback.fst f f).appTop.hom (c i j) := by
    let tW : pullback f₂ sA ⟶ Spec (CommRingCat.of k) := pullback.fst f₂ sA ≫ f₂
    let γ₁ : SchemeHomOver tW f := GoodReductionJacobian.schemeHomOverComp
        (pullback.fst f₂ sA) rfl p₁
    let γ₂ : SchemeHomOver tW f := GoodReductionJacobian.schemeHomOverComp
        (pullback.fst f₂ sA) rfl p₂
    have hγ₁ : γ₁.1 = pullback.fst f₂ sA ≫ pullback.fst f f := rfl
    have hγ₂ : γ₂.1 = pullback.fst f₂ sA ≫ pullback.snd f f := rfl
    have hγ12 : (L.mul tW γ₁ γ₂).1 = pullback.fst f₂ sA ≫ μ := by
      have h := L.mul_natural f₂ tW (pullback.fst f₂ sA) rfl p₁ p₂
      rw [hμ, ← congrArg Subtype.val h, GoodReductionJacobian.schemeHomOverComp_coe]
    have hβW : pullback.snd f₂ sA ≫ sA = tW := pullback.condition.symm
    have hd₁ := S1 γ₂ (pullback.snd f₂ sA) hβW
    have hβ' := S2s γ₂ (pullback.snd f₂ sA) hβW
    have hz' : a.act γ₂ ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₁ =
        ⟨(pullback.lift γ₂.1 (pullback.snd f₂ sA) (hθw γ₂ _ hβW) ≫ β) ≫ jA, hzw _ hβ'⟩ :=
      Subtype.ext (S2 γ₂ (pullback.snd f₂ sA) hβW hd₁)
    have hd₂ : a.Defined γ₁ (a.act γ₂ ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₁) := by
      rw [hz']; exact S1 γ₁ _ hβ'
    obtain ⟨hd₃, hassoc⟩ := ha tW γ₁ γ₂ ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₁ hd₂
    have hL : (a.act γ₁ (a.act γ₂ ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₁) hd₂).1 =
        (pullback.lift γ₁.1 _ (hθw γ₁ _ hβ') ≫ β) ≫ jA := by
      rw [act_coe_congr a γ₁ _ _ hz' hd₂ (S1 γ₁ _ hβ'), S2 γ₁ _ hβ']
    have hR : (a.act (L.mul tW γ₁ γ₂) ⟨pullback.snd f₂ sA ≫ jA, hzw _ hβW⟩ hd₃).1 =
        (pullback.lift (L.mul tW γ₁ γ₂).1 (pullback.snd f₂ sA) (hθw _ _ hβW) ≫ β) ≫ jA :=
      S2 _ (pullback.snd f₂ sA) hβW hd₃
    have E1 : pullback.lift γ₁.1 _ (hθw γ₁ _ hβ') ≫ β =
        pullback.lift (L.mul tW γ₁ γ₂).1 (pullback.snd f₂ sA) (hθw _ _ hβW) ≫ β := by
      rw [← cancel_mono jA, ← hL, ← hR, hassoc]
    intro l j
    have hβeval := congrArg
      (fun φ : pullback f₂ sA ⟶ Spec (CommRingCat.of A) => φ.appTop.hom (bt j)) E1
    have E2 :=
      (S3 γ₁ (pullback.lift γ₂.1 (pullback.snd f₂ sA) (hθw γ₂ _ hβW) ≫ β) hβ' j).symm.trans
        (hβeval.trans (S3 (L.mul tW γ₁ γ₂) (pullback.snd f₂ sA) hβW j))
    rw [hγ₁, hγ12] at E2
    simp_rw [S3 γ₂ (pullback.snd f₂ sA) hβW, hγ₂, comp_appTop_apply] at E2
    rw [sum_swap] at E2
    simp_rw [← map_mul, ← map_sum] at E2
    have hinj := hΘW.1 E2
    exact (congrFun hinj l).symm
  have hC : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      c.map (L.mul t x y).1.appTop.hom = c.map y.1.appTop.hom * c.map x.1.appTop.hom := by
    intro T t x y
    let xy : T ⟶ pullback f f := pullback.lift x.1 y.1 (by rw [x.2, y.2])
    have hxy : xy ≫ f₂ = t := by
      change xy ≫ pullback.fst f f ≫ f = t
      rw [← Category.assoc, pullback.lift_fst, x.2]
    have hx : GoodReductionJacobian.schemeHomOverComp xy hxy p₁ = x :=
        Subtype.ext (pullback.lift_fst _ _ _)
    have hy : GoodReductionJacobian.schemeHomOverComp xy hxy p₂ = y :=
        Subtype.ext (pullback.lift_snd _ _ _)
    have hm : (L.mul t x y).1 = xy ≫ μ := by
      have h := L.mul_natural f₂ t xy hxy p₁ p₂
      rw [hx, hy] at h
      rw [← h, GoodReductionJacobian.schemeHomOverComp_coe, hμ]
    ext i j
    rw [Matrix.map_apply, hm, comp_appTop_apply, E3, map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← comp_appTop_apply, ← comp_appTop_apply, pullback.lift_snd, pullback.lift_fst,
      Matrix.map_apply, Matrix.map_apply]
  have hΘk := coords_bijective (𝟙 (Spec (CommRingCat.of k))) A b
  rw [← hsA] at hΘk
  have E5 : c.map (L.one (𝟙 (Spec (CommRingCat.of k)))).1.appTop.hom = 1 := by
    have hone1 : (L.one sA).1 = sA ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 :=
      (congrArg Subtype.val (L.one_natural (𝟙 _) sA sA (Category.comp_id sA))).symm
    have hβ1 : 𝟙 (Spec (CommRingCat.of A)) ≫ sA = sA := Category.id_comp _
    have hd1 := S1 (L.one sA) (𝟙 _) hβ1
    have hunit := hu sA ⟨𝟙 _ ≫ jA, hzw _ hβ1⟩ hd1
    have E4 : pullback.lift (L.one sA).1 (𝟙 _) (hθw _ _ hβ1) ≫ β = 𝟙 _ := by
      rw [← cancel_mono jA, ← S2 (L.one sA) (𝟙 _) hβ1 hd1, hunit]
    have E4' : ∀ j, ∑ i, sA.appTop.hom ((L.one (𝟙 (Spec (CommRingCat.of k)))).1.appTop.hom
        (c i j)) *
        bt i = bt j := by
      intro j
      have h := S3 (L.one sA) (𝟙 _) hβ1 j
      rw [E4, hone1] at h
      simp_rw [comp_appTop_apply] at h
      have h__af := h.symm
      simp only [Scheme.Hom.id_appTop] at h__af
      exact h__af
    ext i j
    have hcond : pullback.fst (𝟙 (Spec (CommRingCat.of k))) sA ≫ 𝟙 _ = pullback.snd (𝟙 _) sA ≫ sA :=
      pullback.condition
    have key : (fun i => (L.one (𝟙 (Spec (CommRingCat.of k)))).1.appTop.hom (c i j)) =
        fun i => (1 : Matrix (Fin dA) (Fin dA) Γ(Spec (CommRingCat.of k), ⊤)) i j := by
      apply hΘk.1
      simp only
      have h2 := congrArg (fun s => (pullback.snd (𝟙 (Spec
          (CommRingCat.of k))) sA).appTop.hom s) (E4' j)
      have hsf : ∀ v, (pullback.snd (𝟙 (Spec (CommRingCat.of k))) sA).appTop.hom (sA.appTop.hom v) =
          (pullback.fst (𝟙 (Spec (CommRingCat.of k))) sA).appTop.hom v := fun v => by
        rw [← comp_appTop_apply, ← hcond, comp_appTop_apply, Scheme.Hom.id_appTop]; rfl
      simp only [map_sum, map_mul, hsf] at h2
      rw [sum_one_apply_mul _ j]
      exact h2
    have := congrFun key i
    rw [Matrix.map_apply, this]
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      c.map (L.one t).1.appTop.hom = 1 := by
    intro T t
    have h1 : (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 :=
      (congrArg Subtype.val (L.one_natural (𝟙 _) t t (Category.comp_id t))).symm
    have h2 : c.map (L.one t).1.appTop.hom =
        (c.map (L.one (𝟙 (Spec (CommRingCat.of k)))).1.appTop.hom).map t.appTop.hom := by
      ext i j
      simp only [Matrix.map_apply]
      rw [h1, comp_appTop_apply]
    rw [h2, E5, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv1 : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      c.map x.1.appTop.hom * c.map (L.inv t x).1.appTop.hom = 1 := by
    intro T t x
    rw [← hC, L.inv_mul_cancel, hone]
  have hinv2 : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      c.map (L.inv t x).1.appTop.hom * c.map x.1.appTop.hom = 1 := by
    intro T t x
    rw [← hC, L.mul_inv_cancel, hone]
  let ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin dA) Γ(T, ⊤) := fun t x =>
    ⟨(c.map x.1.appTop.hom).transpose, (c.map (L.inv t x).1.appTop.hom).transpose,
      by rw [← Matrix.transpose_mul, hinv2, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, hinv1, Matrix.transpose_one]⟩
  have hρval : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      (ρ t x).val = (c.map x.1.appTop.hom).transpose := fun _ _ => rfl
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro T t x y
    apply Units.ext
    rw [Units.val_mul, hρval, hρval, hρval, hC, Matrix.transpose_mul]
  · intro T T' t t' ψ hψ x
    apply Units.ext
    rw [hρval]
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hρval, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.transpose_apply, Matrix.map_apply, GoodReductionJacobian.schemeHomOverComp_coe,
      comp_appTop_apply]
  · intro T t x h1
    have hCx : c.map x.1.appTop.hom = 1 := by
      have h2 := congrArg (fun U : GL (Fin dA) Γ(T, ⊤) => U.val.transpose) h1
      simp only [hρval, Matrix.transpose_transpose, Units.val_one, Matrix.transpose_one] at h2
      exact h2
    have hβT : pullback.snd t (jA ≫ p) ≫ sA = pullback.fst t (jA ≫ p) ≫ t :=
      ((pullback.condition (f := t) (g := jA ≫ p)).trans (pullback.snd t (jA ≫ p) ≫= hjs)).symm
    refine ⟨S1 (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jA ≫ p)) rfl x)
      (pullback.snd t (jA ≫ p)) hβT, ?_⟩
    rw [S2 _ _ hβT]
    congr 1
    apply ext_of_isAffine
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    have hgen : ∀ (θ : pullback t (jA ≫ p) ⟶ Spec (CommRingCat.of A)),
        θ ≫ sA = pullback.fst t (jA ≫ p) ≫ t →
        (∀ j, θ.appTop.hom (bt j) = (pullback.snd t (jA ≫ p)).appTop.hom (bt j)) →
        θ.appTop.hom s = (pullback.snd t (jA ≫ p)).appTop.hom s := by
      intro θ hθ hθb
      rw [hbt s, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, hθb i, ← comp_appTop_apply, ← comp_appTop_apply, hθ, hβT]
    apply hgen _ (S2s _ _ hβT)
    intro j
    rw [S3 _ _ hβT j]
    simp_rw [GoodReductionJacobian.schemeHomOverComp_coe, comp_appTop_apply]
    have hx1 : ∀ i, x.1.appTop.hom (c i j) = (1 : Matrix (Fin dA) (Fin dA) Γ(T, ⊤)) i j := by
      intro i
      have := congrFun (congrFun hCx i) j
      rwa [Matrix.map_apply] at this
    simp_rw [hx1]
    exact sum_one_apply_mul _ j (pullback.fst t (jA ≫ p)).appTop.hom

/-- A partial action fixing a rational point induces an action on its actual finite jet. -/
private theorem actionOnPointJet {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    (a : PartialAction k f p)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀)
    (n : ℕ) :
    let O : CommRingCat.{u} := P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))
    let A : Type u := O ⧸ IsLocalRing.maximalIdeal O ^ n
    ∀ (sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
      (jA : Spec (CommRingCat.of A) ⟶ P)
      (_ : jA = Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫ P.fromSpecStalk _)
      (σ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
      (_ : σ ≫ sA = 𝟙 _) (_ : σ ≫ jA = P₀.1) (hjs : jA ≫ p = sA),
      ∃ β : pullback f sA ⟶ Spec (CommRingCat.of A),
        β ≫ sA = pullback.fst f sA ≫ f ∧
        ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
          (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t),
          ∃ hd : a.Defined γ
              ⟨βT ≫ jA, by rw [Category.assoc, hjs, hβT]⟩,
            (a.act γ ⟨βT ≫ jA, by rw [Category.assoc, hjs, hβT]⟩ hd).1 =
              (pullback.lift γ.1 βT (γ.2.trans hβT.symm) ≫ β) ≫ jA := by
  intro O A sA jA hjA σ hσs hσj hjs
  have : Subsingleton ↥(Spec (CommRingCat.of A)) :=
    subsingleton_primeSpectrum_quotient O n
  let uA : SchemeHomOver (pullback.fst f sA ≫ f) f := ⟨pullback.fst f sA, rfl⟩
  let zA : SchemeHomOver (pullback.fst f sA ≫ f) p :=
    ⟨pullback.snd f sA ≫ jA, by rw [Category.assoc, hjs]; exact pullback.condition.symm⟩
  have huA : uA.1 = pullback.fst f sA := rfl
  have hzA : zA.1 = pullback.snd f sA ≫ jA := rfl
  have hlw : 𝟙 G ≫ f = (f ≫ σ) ≫ sA := by
    rw [Category.assoc, hσs, Category.comp_id, Category.id_comp]
  let lam : G ⟶ pullback f sA := pullback.lift (𝟙 G) (f ≫ σ) hlw
  have hlam_fst : lam ≫ pullback.fst f sA = 𝟙 G := pullback.lift_fst _ _ _
  have hlam_snd : lam ≫ pullback.snd f sA = f ≫ σ := pullback.lift_snd _ _ _
  have hlamf : lam ≫ (pullback.fst f sA ≫ f) = f := by
    rw [← Category.assoc, hlam_fst, Category.id_comp]
  have hlamsurj : ∀ w : ↥(pullback f sA), ∃ w', lam w' = w := fun w =>
    ⟨pullback.fst f sA w, fst_injective_of_section f sA σ hσs (by
      rw [← Scheme.Hom.comp_apply, hlam_fst]; rfl)⟩
  let P₀G : SchemeHomOver f p := GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) P₀
  let γ₀ : SchemeHomOver f f := GoodReductionJacobian.schemeHomOverComp lam hlamf uA
  have hzA0 : GoodReductionJacobian.schemeHomOverComp lam hlamf zA = P₀G := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe,
        GoodReductionJacobian.schemeHomOverComp_coe, hzA,
      ← Category.assoc, hlam_snd, Category.assoc, hσj]
  have hpair0 : pair γ₀ P₀G = lam ≫ pair uA zA := by
    rw [← hzA0]; exact pair_comp lam hlamf uA zA
  obtain ⟨hd0, hact0⟩ := hall f γ₀
  have hdA : a.Defined uA zA := by
    rintro _ ⟨w₁, rfl⟩
    obtain ⟨w', rfl⟩ := hlamsurj w₁
    apply hd0
    exact ⟨w', by rw [hpair0]; rfl⟩
  obtain ⟨α, hα⟩ : ∃ α' : pullback f sA ⟶ P, α' = (a.act uA zA hdA).1 := ⟨_, rfl⟩
  have hαp : α ≫ p = pullback.fst f sA ≫ f := by rw [hα]; exact (a.act uA zA hdA).2
  have hια : lam ≫ α = f ≫ P₀.1 := by
    have h1 := act_coe_of_pair_eq a uA zA hdA γ₀ P₀G lam hpair0 hd0
    rw [hact0] at h1
    rw [hα, ← h1]
    rfl
  have : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace G := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨β, hβ⟩ : ∃ β : pullback f sA ⟶ Spec (CommRingCat.of A), β ≫ jA = α :=
    AlgebraicGeometry.exists_comp_specMap_quotient_maximalIdeal_pow_eq_of_section_comp_eq
      p P₀.1 P₀.2 n jA hjA sA hjs σ hσj f lam hlam_fst hlam_snd α hια
  have hβs : β ≫ sA = pullback.fst f sA ≫ f := by
    have h : β ≫ (jA ≫ p) = pullback.fst f sA ≫ f := by rw [← Category.assoc, hβ, hαp]
    rwa [hjs] at h
  have hθw : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)), βT ≫ sA = t → γ.1 ≫ f = βT ≫ sA :=
    fun γ βT hβT => by rw [γ.2, hβT]
  have hzw : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
      (βT : T ⟶ Spec (CommRingCat.of A)), βT ≫ sA = t → (βT ≫ jA) ≫ p = t :=
    fun βT hβT => by rw [Category.assoc, hjs, hβT]
  have S1 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t),
      a.Defined γ ⟨βT ≫ jA, hzw βT hβT⟩ := by
    intro T t γ βT hβT
    refine defined_of_pair_eq a uA zA hdA γ _ (pullback.lift γ.1 βT (hθw γ βT hβT)) ?_
    apply pullback.hom_ext
    · simp only [pair, Category.assoc, pullback.lift_fst, huA]
    · simp only [pair, Category.assoc, pullback.lift_snd, hzA]
      rw [← Category.assoc, pullback.lift_snd]
  have S2 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t)
      (hd : a.Defined γ ⟨βT ≫ jA, hzw βT hβT⟩),
      (a.act γ ⟨βT ≫ jA, hzw βT hβT⟩ hd).1 = (pullback.lift γ.1 βT (hθw γ βT hβT) ≫ β) ≫ jA := by
    intro T t γ βT hβT hd
    have hpair : pair γ ⟨βT ≫ jA, hzw βT hβT⟩ = pullback.lift γ.1 βT (hθw γ βT hβT) ≫
        pair uA zA := by
      apply pullback.hom_ext
      · simp only [pair, Category.assoc, pullback.lift_fst, huA]
      · simp only [pair, Category.assoc, pullback.lift_snd, hzA]
        rw [← Category.assoc, pullback.lift_snd]
    rw [act_coe_of_pair_eq a uA zA hdA γ _ (pullback.lift γ.1 βT (hθw γ βT hβT)) hpair hd, ← hα,
        ← hβ,
      Category.assoc]
  refine ⟨β, hβs, ?_⟩
  intro T t γ βT hβT
  exact ⟨S1 γ βT hβT, S2 γ βT hβT (S1 γ βT hβT)⟩

theorem main_pos {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (d : ℕ) (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin d) Γ(T, ⊤)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ t (L.mul t x y) = ρ t x * ρ t y) ∧
      (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base
                (fieldSpecPoint k))) ^ n))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ n))) ≫
        P.fromSpecStalk _ →
        ρ t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  set y₀ : ↥P := P₀.1.base (fieldSpecPoint k) with hy₀
  set O : CommRingCat.{u} := P.presheaf.stalk y₀ with hO
  let e₀ : O ⟶ CommRingCat.of k := Scheme.stalkClosedPointTo P₀.1
  have : IsLocalHom e₀.hom :=
    Scheme.isLocalHom_stalkClosedPointTo' P₀.1
  have he₀ : ∀ b : O, b ∈ IsLocalRing.maximalIdeal O ↔ e₀.hom b = 0 := by
    intro b
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff e₀.hom b,
        isUnit_iff_ne_zero,
      not_not]
  let kO : CommRingCat.of k ⟶ O :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ P.presheaf.germ ⊤ y₀ trivial
  have hSkO : Spec.map kO = P.fromSpecStalk y₀ ≫ p := by
    have h1 : Spec.map (P.presheaf.germ ⊤ y₀ trivial) = P.fromSpecStalk y₀ ≫ P.toSpecΓ :=
      (Scheme.fromSpecStalk_toSpecΓ P y₀).symm
    have h2 : P.toSpecΓ ≫ Spec.map p.appTop = p ≫ (Spec (CommRingCat.of k)).toSpecΓ :=
      (Scheme.toSpecΓ_naturality p).symm
    have h3 : (Spec (CommRingCat.of k)).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso
        (CommRingCat.of k)).inv =
        𝟙 _ := by
      rw [← AlgebraicGeometry.SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
    calc Spec.map kO
        = Spec.map (P.presheaf.germ ⊤ y₀ trivial) ≫ Spec.map p.appTop ≫
            Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
          simp only [kO, Spec.map_comp, Category.assoc]
      _ = P.fromSpecStalk y₀ ≫ (P.toSpecΓ ≫ Spec.map p.appTop) ≫
            Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
          rw [h1]; simp only [Category.assoc]
      _ = P.fromSpecStalk y₀ ≫ p ≫ ((Spec (CommRingCat.of k)).toSpecΓ ≫
            Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv) := by
          rw [h2]; simp only [Category.assoc]
      _ = P.fromSpecStalk y₀ ≫ p := by rw [h3, Category.comp_id]
  have hkO : kO ≫ e₀ = 𝟙 _ := by
    apply Spec.map_injective
    have he : Spec.map e₀ ≫ P.fromSpecStalk y₀ = P₀.1 :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk P₀.1
    rw [Spec.map_comp, Spec.map_id, hSkO, ← Category.assoc, he]
    exact P₀.2
  have hkO' : ∀ c : k, e₀.hom (kO.hom c) = c := fun c => by
    change (kO ≫ e₀).hom c = c
    rw [hkO]; rfl
  let algO : Algebra k O := kO.hom.toAlgebra
  let A : Type u := O ⧸ IsLocalRing.maximalIdeal O ^ n
  have halgA : ∀ c : k, algebraMap k A c = Ideal.Quotient.mk _ (kO.hom c) := fun c => rfl
  have hq : ∀ b ∈ IsLocalRing.maximalIdeal O ^ n, e₀.hom b = 0 := by
    intro b hb
    exact (he₀ b).mp (Ideal.pow_le_self (Nat.one_le_iff_ne_zero.mp hn) hb)
  let q : A →+* k := Ideal.Quotient.lift _ e₀.hom hq
  have hqalg : ∀ c : k, q (algebraMap k A c) = c := fun c => by
    rw [halgA]; exact hkO' c
  obtain ⟨sA, hsA⟩ : ∃ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k),
      s = Spec.map (CommRingCat.ofHom (algebraMap k A)) := ⟨_, rfl⟩
  let σ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom q)
  have hσs : σ ≫ sA = 𝟙 _ := by
    rw [hsA]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  obtain ⟨jA, hjA⟩ : ∃ j : Spec (CommRingCat.of A) ⟶ P,
      j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫
        P.fromSpecStalk y₀ := ⟨_, rfl⟩
  have hσj : σ ≫ jA = P₀.1 := by
    have e1 : σ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal O ^ n))) =
        Spec.map e₀ := by
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      congr 1
    calc σ ≫ jA
        = σ ≫ (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫ P.fromSpecStalk y₀) := _ ≫= hjA
      _ = (σ ≫ Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)))) ≫ P.fromSpecStalk y₀ :=
          (Category.assoc _ _ _).symm
      _ = Spec.map e₀ ≫ P.fromSpecStalk y₀ := e1 =≫ _
      _ = P₀.1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk P₀.1
  have hjs : jA ≫ p = sA := by
    have e1 : (CommRingCat.ofHom (algebraMap k A) : CommRingCat.of k ⟶ CommRingCat.of A) =
        kO ≫ CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)) := rfl
    calc jA ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal O ^ n))) ≫
          (P.fromSpecStalk y₀ ≫ p) := by rw [hjA, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫
          Spec.map kO := by rw [hSkO]
      _ = Spec.map (kO ≫ CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) :=
          (Spec.map_comp _ _).symm
      _ = sA := by rw [← e1, hsA]
  have : Mono jA := by
    rw [hjA]
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have : Subsingleton ↥(Spec (CommRingCat.of A)) := subsingleton_primeSpectrum_quotient O n
  have : IsLocalHom (algebraMap k O) := by
    refine ⟨fun c hc => ?_⟩
    by_contra h0
    rw [isUnit_iff_ne_zero, not_not] at h0
    rw [h0, map_zero] at hc
    exact not_isUnit_zero hc
  have hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap k O)) := by
    intro r
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine ⟨IsLocalRing.residue k (e₀.hom o), ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    change IsLocalRing.residue O (kO.hom (e₀.hom o)) = IsLocalRing.residue O o
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, he₀, map_sub, hkO', sub_self]
  have : Module.Finite k A :=
    IsLocalRing.moduleFinite_quotient_maximalIdeal_pow_of_residueField_map_surjective hres n
  let dA : ℕ := Module.finrank k A
  let b : Module.Basis (Fin dA) k A := Module.finBasis k A
  obtain ⟨β, hβs, hβact⟩ :=
    actionOnPointJet f p a P₀ hall n sA jA hjA σ hσs hσj hjs
  have hθw : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)), βT ≫ sA = t → γ.1 ≫ f = βT ≫ sA :=
    fun γ βT hβT => by rw [γ.2, hβT]
  have hzw : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
      (βT : T ⟶ Spec (CommRingCat.of A)), βT ≫ sA = t → (βT ≫ jA) ≫ p = t :=
    fun βT hβT => by rw [Category.assoc, hjs, hβT]
  have S1 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t),
      a.Defined γ ⟨βT ≫ jA, hzw βT hβT⟩ := by
    intro T t γ βT hβT
    exact (hβact γ βT hβT).choose
  have S2 : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
      (βT : T ⟶ Spec (CommRingCat.of A)) (hβT : βT ≫ sA = t)
      (hd : a.Defined γ ⟨βT ≫ jA, hzw βT hβT⟩),
      (a.act γ ⟨βT ≫ jA, hzw βT hβT⟩ hd).1 = (pullback.lift γ.1 βT (hθw γ βT hβT) ≫ β) ≫ jA := by
    intro T t γ βT hβT hd
    exact (hβact γ βT hβT).choose_spec
  obtain ⟨ρ, hρmul, hρnat, hρact⟩ :=
    representationOfFiniteJet f L p a hu ha A dA b sA hsA jA hjs β hβs hθw hzw S1 S2
  refine ⟨dA, ρ, hρmul, hρnat, ?_⟩
  intro T t x jn hjn h1
  obtain rfl : jn = jA := hjn.trans hjA.symm
  exact hρact t x h1

theorem main_all {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀)
    (n : ℕ) :
    ∃ (d : ℕ) (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin d) Γ(T, ⊤)),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ t (L.mul t x y) = ρ t x * ρ t y) ∧
      (∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x)) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base
                (fieldSpecPoint k))) ^ n))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ n))) ≫
        P.fromSpecStalk _ →
        ρ t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by
  rcases n with _ | n
  · exact main_zero f L p a P₀
  · exact main_pos f L p a hu ha P₀ hall (n + 1) (Nat.succ_pos n)

end MainPos

end GoodReductionJacobian.PartialAction.LinearJets

end AbelianVarieties.NOSProofs.JetRepresentations

namespace GoodReductionJacobian.PartialAction

universe u

open CategoryTheory.Limits hiding pair
open CategoryTheory AlgebraicGeometry NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.GoodReductionJacobian.PartialAction
open AbelianVarieties.NOSProofs.JetRepresentations.GoodReductionJacobian.PartialAction.LinearJets

theorem exists_generalLinearGroup_jet_of_forall_defined_act_eq
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) :
    ∃ (d : ℕ → ℕ)
      (ρ : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin (d n)) Γ(T, ⊤)),
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ n t (L.mul t x y) = ρ n t x * ρ n t y) ∧
      (∀ (n : ℕ) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ n t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ n t x)) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        ρ (n + 1) t x = 1 → ρ n t x = 1) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base
                (fieldSpecPoint k))) ^ n))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (fieldSpecPoint k))) ^ n))) ≫
        P.fromSpecStalk _ →
        ρ n t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by
  choose d ρ hmul hnat hfaith using fun n => main_all f L p a hu ha P₀ hall n
  refine ⟨fun n => ∑ i : Fin (n + 1), d i,
    fun n {T} t x => blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t x), ?_, ?_, ?_, ?_⟩
  · intro n T t x y
    change blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t (L.mul t x y)) =
      blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t x) *
        blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t y)
    rw [← blockGL_mul]
    congr 1
    funext i
    exact hmul i t x y
  · intro n T T' t t' ψ hψ x
    change blockGL (fun i : Fin (n + 1) => d i)
        (fun i => ρ i t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) =
      Matrix.GeneralLinearGroup.map ψ.appTop.hom
        (blockGL (fun i : Fin (n + 1) => d i) (fun i => ρ i t x))
    rw [blockGL_map]
    congr 1
    funext i
    exact hnat i t t' ψ hψ x
  · intro n T t x h
    rw [blockGL_eq_one_iff] at h ⊢
    intro i
    exact h (Fin.castSucc i)
  · intro n T t x jn hjn h
    rw [blockGL_eq_one_iff] at h
    exact hfaith n t x jn hjn (h (Fin.last n))

end GoodReductionJacobian.PartialAction
end
