/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Nyll.SchemeTheory.Modules.Frames.FrameBridge
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackIsoUnit
public import Nyll.SchemeTheory.Modules.Frames.LocallyFreeBasis
public import Nyll.SchemeTheory.Modules.Differentials.Sections
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.BasisMapEqIsAffineOpen
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnSheafificationAdjunctionUnitIotaMulti
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.OpenImmersionUnit
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections

/-! # Local bases and frames of differential forms -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.RestrictionFrames


open _root_.CategoryTheory
open _root_.Opposite
open _root_.AlgebraicGeometry

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
namespace Restriction
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)

lemma bij (W : X.Opens) (hW : W ≤ U) :
    Function.Bijective (fun s : Γ(M, W) => pullbackLocalSection U.ι s) :=
  bijective_unit_app_of_le_opensRange U.ι M W (hW.trans (Scheme.Opens.opensRange_ι U).ge)

lemma app_bij (W : X.Opens) (hW : W ≤ U) : Function.Bijective (fun g : Γ(X, W) => U.ι.app W g) := by
  have : IsIso (U.ι.app W) :=
    Scheme.Hom.isIso_app U.ι W (hW.trans (Scheme.Opens.opensRange_ι U).ge)
  exact ConcreteCategory.bijective_of_isIso (U.ι.app W)

end AlgebraicGeometry.Scheme.Modules.Restriction

end AbelianVarieties.NOSProofs.RestrictionFrames

open CategoryTheory Opposite AlgebraicGeometry
open AbelianVarieties.NOSProofs.RestrictionFrames.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

theorem bijective_pullbackLocalSection_opensInclusion_and_isFrameOn_iff {X : Scheme.{u}} (M :
    X.Modules) (U : X.Opens) :
    Function.Bijective (fun s : Γ(M, U) => Scheme.Modules.pullbackLocalSection U.ι s) ∧
      ∀ s : Γ(M, U), Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection U.ι s) ⊤ ↔
        Scheme.Modules.IsFrameOn s U := by
  refine ⟨Restriction.bij M U U le_rfl, fun s => ⟨fun h => ?_, fun h => ?_⟩⟩
  · intro W hWU _
    have hle : U.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ U := fun _ hx => hWU hx
    have h1 : Function.Bijective fun g' : Γ(↑U, U.ι ⁻¹ᵁ W) =>
        g' • Scheme.Modules.pullbackLocalSection U.ι (M.presheaf.map (homOfLE hWU).op s) := by
      have h0 := h hle le_top
      rw [Scheme.Modules.map_homOfLE_pullbackLocalSection U.ι hWU s] at h0
      exact h0
    have h2 : (fun g : Γ(X, W) => Scheme.Modules.pullbackLocalSection U.ι (g • M.presheaf.map
        (homOfLE hWU).op s)) =
        (fun g' : Γ(↑U, U.ι ⁻¹ᵁ W) => g' • Scheme.Modules.pullbackLocalSection U.ι (M.presheaf.map
            (homOfLE hWU).op s)) ∘
          (fun g : Γ(X, W) => U.ι.app W g) := by
      funext g
      simp only [Function.comp_apply, Scheme.Modules.pullbackLocalSection_smul]
    have h3 : Function.Bijective
        (fun g : Γ(X, W) => Scheme.Modules.pullbackLocalSection U.ι (g • M.presheaf.map (homOfLE
            hWU).op s)) := by
      rw [h2]; exact h1.comp (Restriction.app_bij U W hWU)
    exact (Function.Bijective.of_comp_iff' (Restriction.bij M U W hWU)
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s)).1 h3
  · exact Scheme.Modules.IsFrameOn.of_inf ((h.pullbackLocalSection U.ι).mono inf_le_right)

end AlgebraicGeometry.Scheme.Modules

end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_existsUnique_forall_map_eq_of_forall_affineOpens.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.AffineGluing


open CategoryTheory Opposite AlgebraicGeometry

universe u

open TopologicalSpace

namespace AffineSections

theorem map_map {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V) (k : W ⟶
    U)
    (x : Γ(M, U)) : M.presheaf.map g.op (M.presheaf.map f.op x) = M.presheaf.map k.op x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  congr 2

theorem sec_ext {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (Wi : ι → X.Opens) (V : X.Opens)
    (hle : ∀ i, Wi i ≤ V) (hcover : ∀ x ∈ V, ∃ i, x ∈ Wi i) (s t : Γ(M, V))
    (h : ∀ i, M.presheaf.map (homOfLE (hle i)).op s = M.presheaf.map (homOfLE (hle i)).op t) : s =
        t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, Scheme.Modules.isSheaf M⟩ Wi V (fun i => homOfLE (hle
      i))
    (fun x hx => by obtain ⟨i, hi⟩ := hcover x hx; exact Opens.mem_iSup.mpr ⟨i, hi⟩) s t h

theorem sec_ext_affine {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) (s t : Γ(M, V))
    (h : ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ V),
      M.presheaf.map (homOfLE hU).op s = M.presheaf.map (homOfLE hU).op t) : s = t := by
  refine sec_ext M (fun i : {U : X.affineOpens // (U : X.Opens) ≤ V} => (i.1 : X.Opens)) V
    (fun i => i.2) ?_ s t (fun i => h i.1 i.2)
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

end AffineSections

theorem _root_.AlgebraicGeometry.Scheme.Modules.existsUnique_forall_map_eq_of_forall_affineOpens
    {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (s : ∀ U : X.affineOpens, (U : X.Opens) ≤ W → Γ(M, U))
    (hs : ∀ (U V : X.affineOpens) (hU : (U : X.Opens) ≤ W) (hVU : (V : X.Opens) ≤ U),
      M.presheaf.map (homOfLE hVU).op (s U hU) = s V (hVU.trans hU)) :
    ∃! t : Γ(M, W), ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W),
      M.presheaf.map (homOfLE hU).op t = s U hU := by
  let ι : Type u := {U : X.affineOpens // (U : X.Opens) ≤ W}
  let Ui : ι → X.Opens := fun i => (i.1 : X.Opens)
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  have hcover : W ≤ iSup Ui := by
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUW⟩, hxU⟩
  let sf : ∀ i : ι, Γ(M, Ui i) := fun i => s i.1 i.2
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf Ui sf := by
    intro i j
    apply AffineSections.sec_ext_affine
    intro V hV
    rw [AffineSections.map_map M _ _ (homOfLE (hV.trans inf_le_left)),
      AffineSections.map_map M _ _ (homOfLE (hV.trans inf_le_right))]
    change M.presheaf.map (homOfLE _).op (s i.1 i.2) = M.presheaf.map (homOfLE _).op (s j.1 j.2)
    rw [hs i.1 V i.2 (hV.trans inf_le_left), hs j.1 V j.2 (hV.trans inf_le_right)]
  obtain ⟨t, ht, huniq⟩ :=
    F.existsUnique_gluing' Ui W (fun i => homOfLE i.2) hcover sf hcompat
  refine ⟨t, fun U hU => ht ⟨U, hU⟩, fun t' ht' => huniq t' (fun i => ht' i.1 i.2)⟩

end AbelianVarieties.NOSProofs.AffineGluing
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsLocallyFreeOfRank_exists_basis.AlgebraicGeometry.Scheme.Modules
  (freeIsoPiPow)

namespace AbelianVarieties.NOSProofs.FreeFrames


universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry.Scheme.Modules

attribute [local instance]
  Scheme_Modules_IsLocallyFreeOfRank_exists_basis.PresheafOfModules.instModulePiPowAb
  _root_.AlgebraicGeometry.Scheme.Modules.tensorSectionsPresheafModule

variable {X : Scheme.{u}}

lemma isIso_of_bijective_app (W : X.Opens) {P Q : ((W : X.Opens) : Scheme.{u}).Modules} (ψ : P ⟶ Q)
    (hb : ∀ W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ, Function.Bijective (ψ.val.app W')) :
    IsIso ψ := by
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W'
    have : IsIso ((CategoryTheory.forget Ab).map
        (((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)).app W')) :=
      (isIso_iff_bijective _).2 (hb W')
    exact isIso_of_reflects_iso _ (CategoryTheory.forget Ab)
  have : IsIso ((SheafOfModules.forget _).map ψ) :=
    isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ) (PresheafOfModules.toPresheaf _)
  exact (SheafOfModules.fullyFaithfulForget _).isIso_of_isIso_map ψ

section sumSmul

variable (N : X.Modules) (W : X.Opens) {n : ℕ} (τ : Fin n → Γ(N, W))

/-- The morphism determined by a finite family of local sections. -/
def sumSmulHom : piPow ((W : X.Opens) : Scheme.{u}) n ⟶
    (_root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor' W).obj N :=
  ⟨{ app := fun W' => by
       change ModuleCat.of Γ(X, W.ι ''ᵁ W'.unop) (Fin n → Γ(X, W.ι ''ᵁ W'.unop)) ⟶
         ModuleCat.of Γ(X, W.ι ''ᵁ W'.unop) Γ(N, W.ι ''ᵁ W'.unop)
       exact ModuleCat.ofHom
        { toFun := fun g : (Fin n → Γ((W : X.Opens), W'.unop)) =>
            (∑ i, FrameBridge.secX W W'.unop (g i) • N.presheaf.map (homOfLE (FrameBridge.image_le W
                W'.unop)).op (τ i) :
              Γ(N, W.ι ''ᵁ W'.unop))
          map_add' := fun g g' => by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => add_smul (FrameBridge.secX W W'.unop (g i))
              (FrameBridge.secX W W'.unop (g' i)) _
          map_smul' := fun r g => by
            rw [RingHom.id_apply, Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ => mul_smul (FrameBridge.secX W W'.unop r)
              (FrameBridge.secX W W'.unop (g i)) _ }
     naturality := fun {W' W''} i => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro g
       change (∑ k, FrameBridge.secX W W''.unop (X.presheaf.map (W.ι.opensFunctor.map i.unop).op
              (FrameBridge.secX W W'.unop (g k))) •
           N.presheaf.map (homOfLE (FrameBridge.image_le W W''.unop)).op (τ k)) =
         N.presheaf.map (W.ι.opensFunctor.map i.unop).op
           (∑ k, FrameBridge.secX W W'.unop (g k) • N.presheaf.map (homOfLE (FrameBridge.image_le W
               W'.unop)).op (τ k))
       rw [map_sum]
       refine Finset.sum_congr rfl fun k _ => ?_
       rw [Scheme.Modules.map_smul]
       congr 1
       change _ = (N.presheaf.map _ ≫ N.presheaf.map _) (τ k)
       rw [← N.presheaf.map_comp]
       rfl }⟩

lemma sumSmulHom_app_apply (W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ) (g : Fin n → Γ((W :
    X.Opens), W'.unop)) :
    (sumSmulHom N W τ).val.app W' (show (piPow ((W : X.Opens) : Scheme.{u}) n).val.obj W' from g) =
      ∑ i, FrameBridge.secX W W'.unop (g i) • N.presheaf.map (homOfLE (FrameBridge.image_le W
          W'.unop)).op (τ i) := rfl

end sumSmul

theorem nonempty_pullback_iso_free_of_forall_exists_basis'
    {n : ℕ} (M : X.Modules) (U : X.Opens) (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :=
        by
  have : IsIso (sumSmulHom M U e) := by
    apply isIso_of_bijective_app
    intro W'
    obtain ⟨b, hb⟩ := he (U.ι ''ᵁ W'.unop) (FrameBridge.image_le U W'.unop)
    have hfun : (fun g : (Fin n → Γ((U : X.Opens), W'.unop)) =>
        ((sumSmulHom M U e).val.app W' (show (piPow ((U : X.Opens) : Scheme.{u}) n).val.obj W' from
            g) :
          Γ(M, U.ι ''ᵁ W'.unop))) = fun g => b.equivFun.symm g := by
      funext g
      rw [sumSmulHom_app_apply]
      let g' : Fin n → Γ(X, U.ι ''ᵁ W'.unop) := g
      calc
        _ = ∑ i, g' i • b i := Finset.sum_congr rfl fun i _ => by rw [hb i]
        _ = b.equivFun.symm g' := (Module.Basis.equivFun_symm_apply b g').symm
    exact (show Function.Bijective (fun g : (Fin n → Γ((U : X.Opens), W'.unop)) =>
        ((sumSmulHom M U e).val.app W' (show (piPow ((U : X.Opens) : Scheme.{u}) n).val.obj W' from
            g) :
          Γ(M, U.ι ''ᵁ W'.unop))) from hfun ▸ b.equivFun.symm.bijective)
  exact ⟨((_root_.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'IsoPullback
      U).symm.app M) ≪≫ (asIso (sumSmulHom M U e)).symm ≪≫
    (freeIsoPiPow ((U : X.Opens) : Scheme.{u}) n).symm⟩

end AlgebraicGeometry.Scheme.Modules

end

theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis
    {X : Scheme.{u}} {n : ℕ} (M : X.Modules) (U : X.Opens) (e : Fin n → Γ(M, U))
    (he : ∀ (W : X.Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin n) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))) :=
  AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis' M U e he

end AbelianVarieties.NOSProofs.FreeFrames
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace AbelianVarieties.NOSProofs.DifferentialFrames


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule
  AlgebraicGeometry.Scheme.Modules.tensorSectionsPresheafModule

namespace WedgeFrame

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- Restrict a presheaf differential to a smaller open. -/
noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type
    u)) :
    (f.kaehlerPresheaf.obj (op W') : Type u) :=
  (f.kaehlerPresheaf.map (homOfLE i).op).hom w

/-- Restrict a sheaf differential to a smaller open. -/
noncomputable abbrev res {W' W : X.Opens} (i : W' ≤ W) (s : (Γ(f.kaehler, W) : Type u)) :
    (Γ(f.kaehler, W') : Type u) :=
  f.kaehler.val.presheaf.map (homOfLE i).op s

lemma res_toSh {W' W : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    res f i (f.kaehlerToSections W w) = f.kaehlerToSections W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf)).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

lemma algebraMap_sections_eq {U W : X.Opens} (h : W ≤ U) (a : A) :
    let _ : Algebra A Γ(X, U) := f.sectionsAlgebra U
    let _ : Algebra A Γ(X, W) := f.sectionsAlgebra W
    algebraMap A Γ(X, W) a = (X.presheaf.map (homOfLE h).op).hom (algebraMap A Γ(X, U) a) := by
  have := congrArg (fun φ => φ.hom a) (f.constToPresheaf.naturality (homOfLE h).op)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp]
      at this
  exact this

end WedgeFrame

open WedgeFrame in
theorem _root_.AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U : X.Opens} (_hU : IsAffineOpen U) :
    let _ : Algebra A Γ(X, U) := f.sectionsAlgebra U
    ∀ (η : Fin d → Ω[Γ(X, U)⁄A]),
      (∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        let _ : Algebra A Γ(X, W) := f.sectionsAlgebra W
        let _ : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
        ∀ [IsScalarTower A Γ(X, U) Γ(X, W)],
          ∃ b : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]),
            ∀ i, b i = KaehlerDifferential.map A A Γ(X, U) Γ(X, W) (η i)) →
      Scheme.Modules.IsFrameOn (f.topToSections d U (exteriorPower.ιMulti Γ(X, U) d η)) U := by
  intro algU η hη
  classical
  let e : Fin d → Γ(f.kaehler, U) := fun i =>
    f.kaehlerToSections U (show (f.kaehlerPresheaf.obj (op U) : Type u) from η i)
  have he : ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(f.kaehler, W),
        ∀ i, b i = f.kaehler.presheaf.map (homOfLE hW).op (e i) := by
    intro W hW hWaff
    let algW : Algebra A Γ(X, W) := f.sectionsAlgebra W
    let algUW : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
    have : IsScalarTower A Γ(X, U) Γ(X, W) :=
      IsScalarTower.of_algebraMap_eq fun a => algebraMap_sections_eq f hW a
    obtain ⟨b, hb⟩ := hη W hW hWaff
    have hbij := AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hWaff
    let τ : (Ω[Γ(X, W)⁄A]) ≃ₗ[Γ(X, W)] (Γ(f.kaehler, W) : Type u) :=
      LinearEquiv.ofBijective (f.kaehlerToSectionsₗ W) hbij
    refine ⟨b.map τ, fun i => ?_⟩
    rw [Module.Basis.map_apply, hb]
    change f.kaehlerToSections W (pmap f hW (show (f.kaehlerPresheaf.obj (op U) : Type u) from η
        i)) = _
    rw [← res_toSh]
    rfl
  have he' := AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen
      f.kaehler e he
  have h9 := AlgebraicGeometry.Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := f.kaehler) (U := U) e he'
  have hts : f.topToSections d U (exteriorPower.ιMulti Γ(X, U) d η) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
        (show ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val).obj (op U) from
          exteriorPower.ιMulti Γ(X, U) d e) := by
    change (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
        (exteriorPower.map d (f.kaehlerToSectionsₗ U) (exteriorPower.ιMulti Γ(X, U) d η)) = _
    exact congrArg
      ((((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom)
      (exteriorPower.map_apply_ιMulti (f.kaehlerToSectionsₗ U) η)
  rw [hts]
  exact h9

end AbelianVarieties.NOSProofs.DifferentialFrames
end
