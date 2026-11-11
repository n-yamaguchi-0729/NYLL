/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Rigidity of scheme morphisms

Equality of morphisms detected by an unramified diagonal, a generic stalk, or local test schemes.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace Reduction_Support_Schemes_EqOfCompEqOfFormallyUnramifiedOfPreconnectedSpace


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace P2mUnramifiedRigidity

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

theorem isOpen_range_diagonal [FormallyUnramified g] [LocallyOfFiniteType g] :
    IsOpen (Set.range (pullback.diagonal g).base) :=
  (pullback.diagonal g).isOpenEmbedding.isOpen_range

theorem isClosed_range_diagonal [IsSeparated g] :
    IsClosed (Set.range (pullback.diagonal g).base) := by
  have : IsClosedImmersion (pullback.diagonal g) := IsSeparated.isClosedImmersion_diagonal
  exact (pullback.diagonal g).isClosedEmbedding.isClosed_range

variable {g}

theorem comp_lift_eq_comp_diagonal {T Z : Scheme.{u}} (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) (hp : p ≫ u₁ = p ≫ u₂) :
    p ≫ pullback.lift u₁ u₂ hg = (p ≫ u₁) ≫ pullback.diagonal g := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
      Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
      Category.comp_id, hp]

theorem eq_of_comp_eq {T Z : Scheme.{u}} [FormallyUnramified g] [LocallyOfFiniteType g]
    [IsSeparated g] [PreconnectedSpace T]
    (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) : u₁ = u₂ := by
  set v : T ⟶ pullback g g := pullback.lift u₁ u₂ hg with hv
  set W : Set T := v.base ⁻¹' Set.range (pullback.diagonal g).base with hW
  have hWclopen : IsClopen W :=
    ⟨(isClosed_range_diagonal g).preimage v.base.hom.continuous,
      (isOpen_range_diagonal g).preimage v.base.hom.continuous⟩
  have hWne : W.Nonempty := by
    obtain ⟨z⟩ := ‹Nonempty Z›
    refine ⟨p.base z, ?_⟩
    change v.base (p.base z) ∈ Set.range (pullback.diagonal g).base
    refine ⟨u₁.base (p.base z), ?_⟩
    have h := comp_lift_eq_comp_diagonal u₁ u₂ hg p hp
    have h' := congrArg (fun φ : Z ⟶ pullback g g => φ.base z) h
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at h'
    exact h'.symm
  have hWuniv : W = Set.univ := by
    rcases isClopen_iff.mp hWclopen with h | h
    · exact absurd h hWne.ne_empty
    · exact h
  have hrange : Set.range v.base ⊆ Set.range (pullback.diagonal g).base := by
    rintro _ ⟨t, rfl⟩
    have ht : t ∈ W := by rw [hWuniv]; exact Set.mem_univ t
    exact ht
  set l : T ⟶ X := IsOpenImmersion.lift (pullback.diagonal g) v hrange with hl
  have hlv : l ≫ pullback.diagonal g = v := IsOpenImmersion.lift_fac _ _ hrange
  have h1 : u₁ = l := by
    calc u₁ = v ≫ pullback.fst g g := by rw [hv, pullback.lift_fst]
      _ = (l ≫ pullback.diagonal g) ≫ pullback.fst g g := by rw [hlv]
      _ = l := by rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have h2 : u₂ = l := by
    calc u₂ = v ≫ pullback.snd g g := by rw [hv, pullback.lift_snd]
      _ = (l ≫ pullback.diagonal g) ≫ pullback.snd g g := by rw [hlv]
      _ = l := by rw [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  rw [h1, h2]

end P2mUnramifiedRigidity

theorem _root_.AlgebraicGeometry.eq_of_comp_eq_of_formallyUnramified_of_preconnectedSpace
    {X Y T Z : Scheme.{u}} (g : X ⟶ Y) [FormallyUnramified g] [LocallyOfFiniteType g]
    [IsSeparated g] [PreconnectedSpace T]
    (u₁ u₂ : T ⟶ X) (hg : u₁ ≫ g = u₂ ≫ g)
    (p : Z ⟶ T) [Nonempty Z] (hp : p ≫ u₁ = p ≫ u₂) :
    u₁ = u₂ :=
  P2mUnramifiedRigidity.eq_of_comp_eq u₁ u₂ hg p hp

end Reduction_Support_Schemes_EqOfCompEqOfFormallyUnramifiedOfPreconnectedSpace
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_eq_of_fromSpecStalk_genericPoint_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace Reduction_Support_Schemes_SchemeHomEqOfFromSpecStalkGenericPointCompEq


universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem _root_.AlgebraicGeometry.Scheme.Hom.eq_of_fromSpecStalk_genericPoint_comp_eq
    {U H S : Scheme.{u}} [IsIntegral U] (sU : U ⟶ S) (sH : H ⟶ S) [IsSeparated sH]
    (f g : U ⟶ H) (hf : f ≫ sH = sU) (hg : g ≫ sH = sU)
    (h : U.fromSpecStalk (genericPoint U) ≫ f = U.fromSpecStalk (genericPoint U) ≫ g) :
    f = g := by
  have : IsDominant (U.fromSpecStalk (genericPoint U)) := by
    constructor
    have hmem : genericPoint U ∈ Set.range (U.fromSpecStalk (genericPoint U)).base :=
      ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense ({genericPoint U} : Set U) := by
      rw [dense_iff_closure_eq]
      exact genericPoint_closure U
    exact hd.mono (Set.singleton_subset_iff.mpr hmem)
  exact ext_of_isDominant_of_isSeparated sH (hf.trans hg.symm) (U.fromSpecStalk (genericPoint U)) h

end Reduction_Support_Schemes_SchemeHomEqOfFromSpecStalkGenericPointCompEq
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties
namespace NOSProofs
namespace Reduction_Support_Schemes_EqCompOfForallAppTopEqZeroOfForallSubsingleton


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open Topology TopologicalSpace

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace ArtinianPointsDetect
open _root_.AlgebraicGeometry

section Sections

variable {X Y : Scheme.{u}}

theorem app_res_top (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, ⊤)) :
    (f.app U).hom ((Y.presheaf.map (homOfLE (le_top (a := U))).op).hom s) =
      (X.presheaf.map (homOfLE (le_top (a := f ⁻¹ᵁ U))).op).hom (f.appTop.hom s) := by
  have h := f.naturality (homOfLE (le_top (a := U))).op
  have h' := congrArg (fun φ => φ.hom s) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
  rw [h']
  rfl

theorem appTop_eq_zero_of_forall_app (f : X ⟶ Y) (s : Γ(Y, ⊤))
    (h : ∀ U : Y.affineOpens,
      (f.app U.1).hom ((Y.presheaf.map (homOfLE (le_top (a := U.1))).op).hom s) = 0) :
    f.appTop.hom s = 0 := by
  let V : Y.affineOpens → X.Opens := fun U => f ⁻¹ᵁ U.1
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    obtain ⟨U, hU, hxU⟩ : ∃ U : Y.Opens, IsAffineOpen U ∧ f x ∈ U := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
      exact ⟨U, hU, hxU⟩
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf V ⊤ (fun U => homOfLE le_top) hcover
  intro U
  have hU := h U
  rw [app_res_top] at hU
  have h0 : (X.presheaf.map (homOfLE (le_top (a := f ⁻¹ᵁ U.1))).op).hom 0 = 0 := map_zero _
  exact hU.trans h0.symm

theorem ofIdealTop_le_ker (f : X ⟶ Y) (S : Set Γ(Y, ⊤)) (hS : ∀ s ∈ S, f.appTop.hom s = 0) :
    Scheme.IdealSheafData.ofIdealTop (Ideal.span S) ≤ f.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro s hs
  rw [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker, app_res_top, hS s hs, map_zero]

theorem subschemeι_appTop_eq_zero (S : Set Γ(Y, ⊤)) (s : Γ(Y, ⊤)) (hs : s ∈ S) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span S)).subschemeι.appTop.hom s = 0 := by
  set I := Scheme.IdealSheafData.ofIdealTop (X := Y) (Ideal.span S) with hI
  apply appTop_eq_zero_of_forall_app
  intro U
  have h1 : (Y.presheaf.map (homOfLE (le_top (a := U.1))).op).hom s ∈ I.ideal U := by
    rw [hI, Scheme.IdealSheafData.ofIdealTop_ideal]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span hs)
  have h2 : I.ideal U ≤ RingHom.ker (I.subschemeι.app U.1).hom := by
    have h := Scheme.Hom.ideal_ker_le I.subschemeι U
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h
  exact h2 h1

end Sections

section Main

theorem main
    (k : Type u) [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] (S : Set Γ(Z, ⊤))
    (e : Spec (CommRingCat.of k) ⟶ Z)
    (hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
    (hs : ∀ s ∈ S, x.appTop.hom s = 0) : x = t ≫ e := by
  set I := Scheme.IdealSheafData.ofIdealTop (X := Z) (Ideal.span S) with hI
  let Z' : Scheme.{u} := I.subscheme
  let ι' : Z' ⟶ Z := I.subschemeι
  let q' : Z' ⟶ Spec (CommRingCat.of k) := ι' ≫ q
  have hι'S : ∀ s ∈ S, ι'.appTop.hom s = 0 := fun s hs => subschemeι_appTop_eq_zero S s hs
  have : JacobsonSpace Z' := LocallyOfFiniteType.jacobsonSpace q'
  have hclosed : ∀ z : Z', IsClosed ({z} : Set Z') → ι' z = e (IsLocalRing.closedPoint k) := by
    intro z hz
    let kz := pointOfClosedPoint q' z hz
    have h1 : (kz ≫ ι') ≫ q = 𝟙 _ := by
      rw [Category.assoc]; exact pointOfClosedPoint_comp q' z hz
    have h2 : ∀ s ∈ S, (kz ≫ ι').appTop.hom s = 0 := by
      intro s hs
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hι'S s hs, map_zero]
    have h3 : kz ≫ ι' = 𝟙 _ ≫ e := hart (𝟙 _) (kz ≫ ι') h1 h2
    rw [Category.id_comp] at h3
    let p : Spec (CommRingCat.of k) := IsLocalRing.closedPoint k
    have hp : kz p = z := pointOfClosedPoint_apply q' z hz p
    calc
      ι' z = ι' (kz p) := congrArg (fun y : Z' => ι' y) hp.symm
      _ = (kz ≫ ι') p := (Scheme.Hom.comp_apply kz ι' p).symm
      _ = e p := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ Z => φ p) h3
  have : Subsingleton ↥Z' := by
    constructor
    intro z₁ z₂
    have hinj : Function.Injective ι' := ι'.isClosedEmbedding.injective
    have hcp : ∀ c ∈ closedPoints Z', closedPoints Z' = {c} := by
      intro c hc
      ext z
      constructor
      · intro hz
        exact hinj ((hclosed z hz).trans (hclosed c hc).symm)
      · rintro rfl; exact hc
    have hz₁ : z₁ ∈ closure (closedPoints Z') := by rw [closure_closedPoints]; trivial
    have hz₂ : z₂ ∈ closure (closedPoints Z') := by rw [closure_closedPoints]; trivial
    have hne : (closedPoints Z').Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, closure_empty] at hz₁
      exact hz₁
    obtain ⟨c, hc⟩ := hne
    rw [hcp c hc, (mem_closedPoints_iff.mp hc).closure_eq] at hz₁ hz₂
    rw [Set.mem_singleton_iff] at hz₁ hz₂
    rw [hz₁, hz₂]
  have hι' : ι' = q' ≫ e := hart q' ι' rfl hι'S
  have hker : ι'.ker ≤ x.ker := by
    change I.subschemeι.ker ≤ x.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ofIdealTop_le_ker x S hs
  let x' : T ⟶ Z' := IsClosedImmersion.lift ι' x hker
  have hx' : x' ≫ ι' = x := IsClosedImmersion.lift_fac _ _ _
  calc x = x' ≫ ι' := hx'.symm
    _ = x' ≫ q' ≫ e := by rw [← hι']
    _ = (x' ≫ ι') ≫ q ≫ e := by simp only [q', Category.assoc]
    _ = t ≫ e := by rw [hx', ← Category.assoc, hx]

end Main

end AlgebraicGeometry.ArtinianPointsDetect

theorem _root_.AlgebraicGeometry.eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
    (k : Type u) [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] (S : Set Γ(Z, ⊤))
    (e : Spec (CommRingCat.of k) ⟶ Z)
    (hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
    (hs : ∀ s ∈ S, x.appTop.hom s = 0) : x = t ≫ e :=
  AlgebraicGeometry.ArtinianPointsDetect.main k q S e hart t x hx hs

end Reduction_Support_Schemes_EqCompOfForallAppTopEqZeroOfForallSubsingleton
end NOSProofs
end AbelianVarieties
end
